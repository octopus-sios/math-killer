#!/usr/bin/env python3
"""Check GitHub Markdown + LaTeX math formatting across README.md and results/*/PROOF.md.

Catches unbalanced $ / $$ delimiters, unescaped pipes inside table math, and broken
code fences. Pass `--gh-api` to additionally verify HTML rendering via `gh api markdown`.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path


def check_file_offline(path: Path, repo_root: Path) -> list[str]:
    errors: list[str] = []
    rel = path.relative_to(repo_root)
    lines = path.read_text(encoding="utf-8").splitlines()
    in_fence = False
    in_display_math = False
    display_start = 0

    for lineno, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue

        # Strip inline code spans before checking math delimiters
        no_code = re.sub(r"`[^`]*`", "", line)

        # Handle standalone $$ display math blocks
        if stripped == "$$":
            in_display_math = not in_display_math
            if in_display_math:
                display_start = lineno
            continue

        if in_display_math:
            continue

        # Strip single-line $$...$$ blocks and escaped \$
        cleaned = re.sub(r"\$\$.*?\$\$", "", no_code)
        cleaned = cleaned.replace(r"\$", "")

        if "$$" in cleaned:
            errors.append(f"{rel}:{lineno}: unbalanced display-math '$$' delimiter")
        else:
            dollar_count = cleaned.count("$")
            if dollar_count % 2 != 0:
                errors.append(f"{rel}:{lineno}: unbalanced inline-math '$' delimiter")

        # Catch unescaped `|` inside inline math within Markdown tables
        if stripped.startswith("|") and "$" in cleaned:
            for m in re.finditer(r"\$([^$]+)\$", cleaned):
                body = m.group(1)
                if re.search(r"(?<!\\)\|", body):
                    errors.append(f"{rel}:{lineno}: unescaped '|' inside table inline math (use \\mid or \\|)")

    if in_fence:
        errors.append(f"{rel}: unclosed fenced code block")
    if in_display_math:
        errors.append(f"{rel}:{display_start}: unclosed '$$' display-math block")
    return errors


def check_file_gh_api(path: Path, repo_root: Path) -> list[str]:
    if shutil.which("gh") is None:
        return ["`--gh-api` requested but `gh` CLI is not installed"]
    rel = path.relative_to(repo_root)
    source = path.read_text(encoding="utf-8")
    payload = json.dumps({"text": source, "mode": "gfm"})
    res = subprocess.run(
        ["gh", "api", "markdown", "--input", "-"],
        input=payload,
        text=True,
        capture_output=True,
    )
    if res.returncode != 0:
        return [f"{rel}: `gh api markdown` failed ({res.stderr.strip()})"]
    html = res.stdout
    if "math-error" in html or "katex-error" in html:
        return [f"{rel}: GitHub markdown renderer reported math rendering errors"]
    return check_rendered_html(source, html, rel)


def count_escaped_prose_dollars(source: str) -> int:
    """Count intentionally escaped `\\$` occurrences outside code fences, code spans, and math."""
    count = 0
    in_fence = False
    in_display_math = False
    for line in source.splitlines():
        stripped = line.strip()
        if stripped.startswith(("```", "~~~")):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if stripped == "$$":
            in_display_math = not in_display_math
            continue
        if in_display_math:
            continue
        no_code = re.sub(r"`[^`]*`", "", line)
        no_display = re.sub(r"\$\$.*?\$\$", "", no_code)
        no_inline = re.sub(r"(?<!\\)\$(?!\$)(?:\\.|[^$\\])+?(?<!\\)\$", "", no_display)
        count += len(re.findall(r"(?<!\\)(?:\\\\)*\\\$", no_inline))
    return count


def check_rendered_html(source: str, html: str, rel: Path) -> list[str]:
    """Detect Markdown emphasis corruption and unrendered `$` / `$$` in GitHub HTML."""
    errors: list[str] = []

    # 1. Catch HTML/Markdown tags leaking inside a <math-renderer> element.
    for m in re.finditer(r"<math-renderer\b[^>]*>(.*?)</math-renderer>", html, flags=re.S | re.I):
        if re.search(r"<(?:em|strong|del|code|a)\b", m.group(1), flags=re.I):
            errors.append(f"{rel}: HTML/Markdown tag corrupted rendered <math-renderer> block")
            break

    # 2. Inspect HTML outside <pre>, <code>, and <math-renderer> for broken/unrendered math.
    outside_html = re.sub(
        r"<(pre|code|math-renderer)\b[^>]*>.*?</\1>",
        " ",
        html,
        flags=re.S | re.I,
    )
    outside_text = re.sub(r"<[^>]+>", "", outside_html)

    if "$$" in outside_text:
        errors.append(f"{rel}: unrendered '$$' display-math delimiter left in GitHub HTML")

    escaped_dollars = count_escaped_prose_dollars(source)
    outside_dollars = outside_text.count("$")
    if outside_dollars > escaped_dollars:
        # Split on block boundaries so emphasis corruption checks stay local to a block.
        blocks = re.split(r"</?(?:p|li|td|th|h[1-6]|blockquote|div|tr|br)\b[^>]*>", outside_html, flags=re.I)
        emphasis_corrupted = any(
            re.search(r"\$[^$]*<(?:em|strong|del)\b[^>]*>.*?</(?:em|strong|del)>[^$]*\$", blk, flags=re.S | re.I)
            for blk in blocks
        )
        if emphasis_corrupted:
            errors.append(
                f"{rel}: Markdown emphasis (<em>/<strong>/<del>) corrupted inline math in GitHub HTML "
                f"(found {outside_dollars} unrendered '$' vs {escaped_dollars} escaped '\\$')"
            )
        else:
            errors.append(
                f"{rel}: unrendered/stray '$' delimiter(s) left outside <math-renderer> in GitHub HTML "
                f"(found {outside_dollars} vs {escaped_dollars} escaped '\\$')"
            )

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate GitHub Markdown math rendering.")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--gh-api", action="store_true", help="Also render through `gh api markdown`.")
    args = parser.parse_args()

    targets: list[Path] = []
    if (args.repo / "README.md").is_file():
        targets.append(args.repo / "README.md")
    results_dir = args.repo / "results"
    if results_dir.is_dir():
        targets.extend(sorted(results_dir.glob("*/PROOF.md")))

    errors: list[str] = []
    for t in targets:
        errors.extend(check_file_offline(t, args.repo))
        if args.gh_api:
            errors.extend(check_file_gh_api(t, args.repo))

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        return 1
    print(f"check_github_math.py: PASS ({len(targets)} file(s) checked)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
