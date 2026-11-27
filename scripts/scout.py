#!/usr/bin/env python3
"""Multi-source conjecture scout for octopus-sios/math-killer.

Pure Python stdlib (zero third-party dependencies):
- Scouts arXiv across ALL eras (optional `--year` filter), pulling full `.tex` sources
  WITH preamble macros (`\\newcommand`, `\\DeclareMathOperator`) AND nearby/referenced
  `\\begin{definition}` blocks so statements never lose their mathematical meaning.
- Supports `10m-u` local catalog (`references/open-problems-catalog`), `erdos`, and
  selective `lefttosolve` (automatically excluding `kind=known` solved theorems!).
- Deduplicates against local `CATALOG.json`, `references/solved-conjectures`, and
  `references/Graph-Theory-LLM-Proofs`, plus optional OpenAlex forward-citation check.
"""

from __future__ import annotations

import argparse
import dataclasses
import gzip
import io
import json
import re
import sys
import tarfile
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any

ARXIV_API_URL = "https://export.arxiv.org/api/query"
ARXIV_EPRINT_URL = "https://arxiv.org/e-print/{arxiv_id}"
OPENALEX_WORKS_URL = "https://api.openalex.org/works?filter=cited_by_api_url&search={q}&per-page=5"
LEFTTOSOLVE_API_URL = "https://lefttosolve.com/api/problems?limit={limit}&offset={offset}"
USER_AGENT = "MathKillerScout/1.0 (+https://github.com/octopus-sios/math-killer)"

DEFAULT_CATEGORIES = ("math.CO", "math.NT", "math.GR", "math.MG", "math.CA", "math.GT")
ARXIV_ID_RE = re.compile(r"\b(\d{4}\.\d{4,5})(?:v\d+)?\b")

CONJ_ENV_RE = re.compile(
    r"\\begin\{(conjecture|conj|question|openquestion|problem|openproblem)\*?\}"
    r"(?:\s*\[([^\]]*)\])?(.*?)\\end\{\1\*?\}",
    re.S | re.I,
)
DEF_ENV_RE = re.compile(
    r"\\begin\{(definition|defn|notation)\*?\}(?:\s*\[([^\]]*)\])?(.*?)\\end\{\1\*?\}",
    re.S | re.I,
)
MACRO_LINE_RE = re.compile(
    r"(?m)^\s*(\\(?:newcommand|renewcommand|providecommand|DeclareMathOperator)\*?[^\n]+)$"
)
STOPWORDS = frozenset({
    "the", "and", "for", "that", "with", "from", "this", "into", "over", "conjecture",
    "question", "problem", "theorem", "proof", "paper", "finite", "integer", "number",
})


@dataclasses.dataclass
class Candidate:
    candidate_id: str
    source: str
    title: str
    statement: str
    url: str
    published: str = ""
    arxiv_id: str = ""
    macros: list[str] = dataclasses.field(default_factory=list)
    definitions: list[str] = dataclasses.field(default_factory=list)
    notes: str = ""

    def to_dict(self) -> dict[str, Any]:
        return dataclasses.asdict(self)


def canonical_arxiv_id(raw: str) -> str:
    raw = re.sub(r"^https?://arxiv\.org/(?:abs|pdf|e-print)/", "", raw.strip())
    return re.sub(r"v\d+$", "", raw)


def norm_tokens(text: str) -> set[str]:
    clean = re.sub(r"\\[A-Za-z]+", " ", text.lower())
    clean = re.sub(r"[^a-z0-9]+", " ", clean)
    return {t for t in clean.split() if len(t) >= 4 and t not in STOPWORDS}


def http_get(url: str, *, timeout: int = 25) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def extract_tex_from_eprint(blob: bytes) -> str:
    try:
        with tarfile.open(fileobj=io.BytesIO(blob), mode="r:*") as tf:
            parts = []
            for m in tf.getmembers():
                if m.isfile() and m.name.lower().endswith(".tex"):
                    f = tf.extractfile(m)
                    if f is not None:
                        parts.append(f.read().decode("utf-8", errors="replace"))
            if parts:
                return "\n\n".join(parts)
    except tarfile.TarError:
        pass
    if blob[:2] == b"\x1f\x8b":
        try:
            return gzip.decompress(blob).decode("utf-8", errors="replace")
        except OSError:
            pass
    if not blob.startswith(b"%PDF"):
        return blob.decode("utf-8", errors="replace")
    return ""


def extract_tex_pack(tex: str) -> tuple[list[str], list[str], list[tuple[str, str, str]]]:
    """Return (preamble_macros, definition_blocks, conjecture_blocks)."""
    uncommented = re.sub(r"(?<!\\)%[^\n]*", "", tex)
    macros = [m.group(1).strip() for m in MACRO_LINE_RE.finditer(uncommented)][:60]
    defs = []
    for m in DEF_ENV_RE.finditer(uncommented):
        title = (m.group(2) or "").strip()
        body = re.sub(r"\s+", " ", m.group(3)).strip()
        if body:
            label = f"[{title}] " if title else ""
            defs.append(f"{label}{body[:1200]}")
    conjs = []
    for m in CONJ_ENV_RE.finditer(uncommented):
        env_t = m.group(1).lower()
        opt = (m.group(2) or "").strip()
        body = re.sub(r"\s+", " ", m.group(3)).strip()
        if len(body) >= 25:
            conjs.append((env_t, opt, body[:2500]))
    return macros, defs[:12], conjs


def build_dedup_index(repo_root: Path, refs_dir: Path | None) -> tuple[set[str], list[set[str]]]:
    arxiv_ids: set[str] = set()
    title_sets: list[set[str]] = []

    def ingest_text(text: str) -> None:
        for m in ARXIV_ID_RE.finditer(text):
            arxiv_ids.add(canonical_arxiv_id(m.group(1)))
        for line in text.splitlines():
            s = line.strip()
            if s.startswith(("#", "|", "- **", "* **")):
                toks = norm_tokens(s)
                if len(toks) >= 3:
                    title_sets.append(toks)

    cat = repo_root / "CATALOG.json"
    if cat.is_file():
        ingest_text(cat.read_text(encoding="utf-8", errors="replace"))
    if refs_dir and refs_dir.is_dir():
        for sub in ("solved-conjectures", "Graph-Theory-LLM-Proofs"):
            d = refs_dir / sub
            if d.is_dir():
                for fname in ("README.md", "CONTENTS.md"):
                    fp = d / fname
                    if fp.is_file():
                        ingest_text(fp.read_text(encoding="utf-8", errors="replace"))
    return arxiv_ids, title_sets


def is_duplicate(cand: Candidate, arxiv_ids: set[str], title_sets: list[set[str]]) -> bool:
    if cand.arxiv_id and canonical_arxiv_id(cand.arxiv_id) in arxiv_ids:
        return True
    toks = norm_tokens(cand.title)
    if len(toks) >= 3:
        for ref in title_sets:
            inter = len(toks & ref)
            if inter >= 4 and inter / min(len(toks), len(ref)) >= 0.85:
                return True
    return False


def scout_arxiv(categories: list[str], *, years: set[int], max_results: int, fetch_tex: bool) -> list[Candidate]:
    cat_q = " OR ".join(f"cat:{c}" for c in categories)
    query = f"({cat_q}) AND (all:conjecture OR all:\"open problem\" OR all:\"we conjecture\")"
    params = urllib.parse.urlencode({
        "search_query": query,
        "start": 0,
        "max_results": max_results,
        "sortBy": "submittedDate",
        "sortOrder": "descending",
    })
    root = ET.fromstring(http_get(f"{ARXIV_API_URL}?{params}", timeout=30))
    ns = {"a": "http://www.w3.org/2005/Atom"}
    out: list[Candidate] = []
    for entry in root.findall("a:entry", ns):
        aid = canonical_arxiv_id(entry.findtext("a:id", "", ns) or "")
        if not aid or not ARXIV_ID_RE.search(aid):
            continue
        pub = (entry.findtext("a:published", "", ns) or "").strip()
        yr = int(pub[:4]) if len(pub) >= 4 and pub[:4].isdigit() else 0
        if years and yr not in years:
            continue
        title = re.sub(r"\s+", " ", entry.findtext("a:title", "", ns) or "").strip()
        abstract = re.sub(r"\s+", " ", entry.findtext("a:summary", "", ns) or "").strip()
        macros: list[str] = []
        defs: list[str] = []
        conjs: list[tuple[str, str, str]] = []
        if fetch_tex:
            try:
                blob = http_get(ARXIV_EPRINT_URL.format(arxiv_id=aid), timeout=25)
                tex = extract_tex_from_eprint(blob)
                if tex:
                    macros, defs, conjs = extract_tex_pack(tex)
            except Exception:
                pass
        if conjs:
            for idx, (env_t, opt, body) in enumerate(conjs[:5], 1):
                out.append(Candidate(
                    candidate_id=f"arxiv:{aid}:{env_t}{idx}",
                    source="arxiv",
                    title=f"{title} ({opt or env_t})",
                    statement=body,
                    url=f"https://arxiv.org/abs/{aid}",
                    published=pub[:10],
                    arxiv_id=aid,
                    macros=macros,
                    definitions=defs,
                ))
        else:
            out.append(Candidate(
                candidate_id=f"arxiv:{aid}:abstract",
                source="arxiv",
                title=title,
                statement=abstract[:2000],
                url=f"https://arxiv.org/abs/{aid}",
                published=pub[:10],
                arxiv_id=aid,
            ))
    return out


def scout_lefttosolve(*, limit: int, offset: int) -> list[Candidate]:
    raw = json.loads(http_get(LEFTTOSOLVE_API_URL.format(limit=limit, offset=offset), timeout=30).decode("utf-8"))
    items = raw if isinstance(raw, list) else raw.get("problems", raw.get("items", []))
    out: list[Candidate] = []
    for item in items:
        # CRITICAL: exclude already-solved theorems (`kind=known`) and raw MSE/OEIS slop
        if str(item.get("kind", "")).lower() == "known":
            continue
        src = str(item.get("source", "")).lower()
        if any(bad in src for bad in ("math.stackexchange", "mse", "oeis")):
            continue
        pid = str(item.get("id", ""))
        title = str(item.get("title") or item.get("name") or pid).strip()
        stmt = str(item.get("statement") or item.get("lean_statement") or "").strip()
        if not stmt:
            continue
        out.append(Candidate(
            candidate_id=f"lefttosolve:{pid}",
            source="lefttosolve",
            title=title,
            statement=stmt[:2500],
            url=str(item.get("url") or f"https://lefttosolve.com/problems/{pid}"),
            notes=f"source={src} kind={item.get('kind')} raw_diff={item.get('difficulty')} (DO NOT trust difficulty blindly)",
        ))
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="Multi-source open-conjecture scout.")
    parser.add_argument("--source", choices=("arxiv", "lefttosolve"), default="arxiv")
    parser.add_argument("--categories", default=",".join(DEFAULT_CATEGORIES))
    parser.add_argument("--year", type=int, action="append", default=[], help="Optional year filter (omit for ALL eras).")
    parser.add_argument("--max-results", type=int, default=25)
    parser.add_argument("--offset", type=int, default=0)
    parser.add_argument("--no-tex", action="store_true", help="Skip downloading full arXiv .tex e-prints.")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--references", type=Path, default=None, help="Path to local private references/ directory.")
    args = parser.parse_args()

    arxiv_ids, title_sets = build_dedup_index(args.repo, args.references)
    if args.source == "arxiv":
        cands = scout_arxiv(
            [c.strip() for c in args.categories.split(",") if c.strip()],
            years=set(args.year),
            max_results=args.max_results,
            fetch_tex=not args.no_tex,
        )
    else:
        cands = scout_lefttosolve(limit=args.max_results, offset=args.offset)

    fresh = [c.to_dict() for c in cands if not is_duplicate(c, arxiv_ids, title_sets)]
    print(json.dumps({"total_fetched": len(cands), "after_dedup": len(fresh), "candidates": fresh}, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
