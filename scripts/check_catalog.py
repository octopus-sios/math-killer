#!/usr/bin/env python3
"""Validate octopus-sios/math-killer catalog, anti-sprawl invariants, private-leak
guards, and Lean 4 static anti-cheat hygiene.

Exits 0 iff all checks pass; exits 1 with clear diagnostics otherwise.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REQUIRED_COLUMNS = ("#", "Problem & Result", "Status", "Links")
VALID_BADGES = frozenset({"✅", "🟢", "🟡", "⬜"})
MAX_WORKFLOWS = 2
MAX_SCRIPTS = 6
MAX_LEAN_STRING_BYTES = 65_536

FORBIDDEN_PRIVATE_NAMES = frozenset({
    "journal.md",
    "GLOBAL_BRIEF.md",
    "BRIEF.md",
    "AGENTS.md",
})

FORBIDDEN_LEAN_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("sorryAx", re.compile(r"\bsorryAx\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"\baxiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("Lean.ofReduceBool", re.compile(r"\b(?:Lean\.)?ofReduceBool\b")),
    ("Lean.trustCompiler", re.compile(r"\b(?:Lean\.)?trustCompiler\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"(?:@\[[^\]]*\bextern\b|\bextern\b)")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("debug.skipKernelTC", re.compile(r"\bdebug\.skipKernelTC\b")),
    ("#eval", re.compile(r"(?m)^\s*#eval\b")),
    ("elab", re.compile(r"(?m)^\s*(?:private\s+|local\s+)?elab(?:_rules)?\b")),
    ("macro", re.compile(r"(?m)^\s*(?:private\s+|local\s+)?macro(?:_rules)?\b")),
    ("syntax", re.compile(r"(?m)^\s*(?:private\s+|local\s+)?syntax\b")),
    ("run_cmd", re.compile(r"\brun_cmd\b")),
    ("run_elab", re.compile(r"\brun_elab\b")),
]


def strip_lean_comments_and_strings(source: str) -> tuple[str, int]:
    """Strip Lean comments & string literals, returning (cleaned_code, max_string_len)."""
    out: list[str] = []
    i, n = 0, len(source)
    depth = 0
    line_c = False
    in_s = False
    cur_s_len = 0
    max_s_len = 0
    while i < n:
        c = source[i]
        nxt = source[i + 1] if i + 1 < n else ""
        if line_c:
            if c == "\n":
                line_c = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            elif c == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
        elif in_s:
            if c == "\\" and i + 1 < n:
                cur_s_len += 2
                out.append(" " if nxt != "\n" else " \n")
                i += 2
            elif c == '"':
                in_s = False
                max_s_len = max(max_s_len, cur_s_len)
                cur_s_len = 0
                out.append(" ")
                i += 1
            elif c == "\n":
                cur_s_len += 1
                out.append("\n")
                i += 1
            else:
                cur_s_len += 1
                out.append(" ")
                i += 1
        elif c == "-" and nxt == "-":
            line_c = True
            out.append("  ")
            i += 2
        elif c == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
        elif c == '"':
            in_s = True
            cur_s_len = 0
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out), max_s_len


def split_md_row(line: str) -> list[str]:
    stripped = line.strip()
    if stripped.startswith("|"):
        stripped = stripped[1:]
    if stripped.endswith("|"):
        stripped = stripped[:-1]
    cells: list[str] = []
    cur: list[str] = []
    i = 0
    while i < len(stripped):
        if stripped[i] == "\\" and i + 1 < len(stripped) and stripped[i + 1] == "|":
            cur.append("|")
            i += 2
        elif stripped[i] == "|":
            cells.append("".join(cur).strip())
            cur = []
            i += 1
        else:
            cur.append(stripped[i])
            i += 1
    cells.append("".join(cur).strip())
    return cells


def check_lean_hygiene(repo_root: Path) -> list[str]:
    errors: list[str] = []
    lean_dir = repo_root / "lean"
    if not lean_dir.is_dir():
        return ["Missing lean/ directory"]

    conjectures_root = lean_dir / "Conjectures.lean"
    if not conjectures_root.is_file():
        errors.append("Missing lean/Conjectures.lean")
        root_imports: set[str] = set()
    else:
        root_imports = set(
            re.findall(r"(?m)^\s*import\s+(Conjectures\.[A-Za-z0-9_.]+)\s*$", conjectures_root.read_text(encoding="utf-8"))
        )

    conjectures_dir = lean_dir / "Conjectures"
    if conjectures_dir.is_dir():
        for p in sorted(conjectures_dir.rglob("*.lean")):
            rel = p.relative_to(lean_dir).with_suffix("")
            mod_name = ".".join(rel.parts)
            if mod_name not in root_imports:
                errors.append(f"lean/Conjectures.lean is missing 'import {mod_name}' (required for ProofAudit)")

    for p in sorted(lean_dir.rglob("*.lean")):
        if p.name == "ProofAudit.lean" or ".lake" in p.parts:
            continue
        raw = p.read_text(encoding="utf-8")
        cleaned, max_str = strip_lean_comments_and_strings(raw)
        if max_str > MAX_LEAN_STRING_BYTES:
            errors.append(f"{p.relative_to(repo_root)}: oversized string literal ({max_str} bytes > {MAX_LEAN_STRING_BYTES})")
        for lineno, line in enumerate(cleaned.splitlines(), 1):
            for label, rx in FORBIDDEN_LEAN_PATTERNS:
                if rx.search(line):
                    errors.append(f"{p.relative_to(repo_root)}:{lineno}: forbidden Lean construct '{label}'")
    return errors


def parse_results_table(readme_text: str) -> tuple[list[dict[str, str]], list[str]]:
    errors: list[str] = []
    lines = readme_text.splitlines()
    section_idx = next((i for i, line in enumerate(lines) if re.match(r"^##\s+Results\s*$", line.strip())), None)
    if section_idx is None:
        return [], ["README.md is missing a '## Results' section"]

    table_lines: list[tuple[int, str]] = []
    for idx in range(section_idx + 1, len(lines)):
        raw = lines[idx].strip()
        if raw.startswith("## "):
            break
        if raw.startswith("|"):
            table_lines.append((idx + 1, raw))
        elif table_lines:
            break

    if len(table_lines) < 2:
        return [], ["README.md '## Results' section is missing a Markdown table"]

    header_line_no, header_raw = table_lines[0]
    headers = split_md_row(header_raw)
    if tuple(headers) != REQUIRED_COLUMNS:
        errors.append(f"README.md:{header_line_no}: expected columns {list(REQUIRED_COLUMNS)}, found {headers}")

    sep_line_no, sep_raw = table_lines[1]
    sep_cells = split_md_row(sep_raw)
    if len(sep_cells) != len(headers) or not all(re.fullmatch(r":?-{3,}:?", c) for c in sep_cells):
        errors.append(f"README.md:{sep_line_no}: malformed Markdown table separator")

    rows: list[dict[str, str]] = []
    for line_no, raw in table_lines[2:]:
        cells = split_md_row(raw)
        if len(cells) != len(headers):
            errors.append(f"README.md:{line_no}: expected {len(headers)} cells, got {len(cells)}")
            continue
        row = dict(zip(headers, cells))
        if row.get("#") in ("—", "-") and "Awaiting first" in row.get("Problem & Result", ""):
            continue
        rows.append(row)
    return rows, errors


def check_anti_sprawl_and_privacy(repo_root: Path) -> list[str]:
    errors: list[str] = []
    wf_dir = repo_root / ".github" / "workflows"
    if wf_dir.is_dir():
        wfs = sorted(p for p in wf_dir.iterdir() if p.is_file() and p.suffix in (".yml", ".yaml"))
        if len(wfs) > MAX_WORKFLOWS:
            errors.append(f".github/workflows has {len(wfs)} workflow(s); strict limit is <= {MAX_WORKFLOWS}")

    scripts_dir = repo_root / "scripts"
    if scripts_dir.is_dir():
        sc = sorted(p for p in scripts_dir.iterdir() if p.is_file() and not p.name.startswith("."))
        if len(sc) > MAX_SCRIPTS:
            errors.append(f"scripts/ has {len(sc)} file(s); strict limit is <= {MAX_SCRIPTS}")

    for forbidden_dir in ("problems", "briefs", "references"):
        if (repo_root / forbidden_dir).exists():
            errors.append(f"Private directory '{forbidden_dir}/' must never be committed to public repository")

    for p in repo_root.rglob("*"):
        if ".git" in p.parts or ".lake" in p.parts or "__pycache__" in p.parts:
            continue
        if p.is_file() and p.name in FORBIDDEN_PRIVATE_NAMES:
            errors.append(f"Forbidden private/internal file committed: {p.relative_to(repo_root)}")
    return errors


def validate_repo(repo_root: Path) -> list[str]:
    errors: list[str] = []
    errors.extend(check_anti_sprawl_and_privacy(repo_root))
    errors.extend(check_lean_hygiene(repo_root))

    readme_path = repo_root / "README.md"
    catalog_path = repo_root / "CATALOG.json"
    if not readme_path.is_file():
        return errors + ["Missing README.md"]
    if not catalog_path.is_file():
        return errors + ["Missing CATALOG.json"]

    try:
        catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
        entries = catalog.get("entries")
        if not isinstance(entries, list):
            errors.append("CATALOG.json: 'entries' must be a JSON array")
            entries = []
    except Exception as exc:
        errors.append(f"CATALOG.json: invalid JSON ({exc})")
        entries = []

    rows, table_errors = parse_results_table(readme_path.read_text(encoding="utf-8"))
    errors.extend(table_errors)

    catalog_slugs: set[str] = set()
    for idx, entry in enumerate(entries, start=1):
        slug = entry.get("slug")
        status = entry.get("status")
        if not isinstance(slug, str) or not slug:
            errors.append(f"CATALOG.json entry #{idx}: missing slug")
            continue
        if slug in catalog_slugs:
            errors.append(f"CATALOG.json: duplicate slug '{slug}'")
        catalog_slugs.add(slug)
        if status not in VALID_BADGES:
            errors.append(f"CATALOG.json '{slug}': invalid status '{status}' (must be one of {sorted(VALID_BADGES)})")
        res_dir = repo_root / "results" / slug
        if not (res_dir / "PROOF.md").is_file():
            errors.append(f"results/{slug}: missing PROOF.md")
        if not (res_dir / "SOURCE.tex").is_file():
            errors.append(f"results/{slug}: missing SOURCE.tex")
        if status == "🟢" and not (res_dir / "verify.py").is_file():
            errors.append(f"results/{slug}: status 🟢 requires results/{slug}/verify.py")
        if status == "✅":
            lean_file = entry.get("lean_file")
            if not isinstance(lean_file, str) or not (repo_root / lean_file).is_file():
                errors.append(f"results/{slug}: status ✅ requires valid existing 'lean_file' path")

    link_re = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
    readme_slugs: set[str] = set()
    for i, row in enumerate(rows, start=1):
        status_cell = row.get("Status", "")
        if not any(b in status_cell for b in VALID_BADGES):
            errors.append(f"README row {i}: Status cell '{status_cell}' must include one of {sorted(VALID_BADGES)}")
        links = link_re.findall(row.get("Problem & Result", "") + " " + row.get("Links", ""))
        found_slug = None
        for target in links:
            if target.startswith(("http://", "https://", "#")):
                continue
            clean = target.split("#", 1)[0].rstrip("/")
            if not (repo_root / clean).exists():
                errors.append(f"README row {i}: broken relative link '{target}'")
            m = re.match(r"^results/([^/]+)(?:/.*)?$", clean)
            if m:
                found_slug = m.group(1)
        if found_slug is None:
            errors.append(f"README row {i}: must link to results/<slug>/")
        else:
            readme_slugs.add(found_slug)

    results_dir = repo_root / "results"
    disk_slugs = {
        p.name for p in results_dir.iterdir() if p.is_dir() and not p.name.startswith(".")
    } if results_dir.is_dir() else set()

    for slug in sorted(disk_slugs - catalog_slugs):
        errors.append(f"results/{slug}: present on disk but missing from CATALOG.json")
    for slug in sorted(catalog_slugs - readme_slugs):
        errors.append(f"CATALOG.json '{slug}': missing from README.md Results table")
    for slug in sorted(readme_slugs - catalog_slugs):
        errors.append(f"README.md '{slug}': present in table but missing from CATALOG.json")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate octopus-sios/math-killer integrity.")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--lean-only", action="store_true", help="Run only static Lean anti-cheat hygiene checks.")
    args = parser.parse_args()

    errs = check_lean_hygiene(args.repo) if args.lean_only else validate_repo(args.repo)
    if errs:
        for e in errs:
            print(f"ERROR: {e}", file=sys.stderr)
        return 1
    print("check_catalog.py: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
