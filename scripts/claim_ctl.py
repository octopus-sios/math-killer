#!/usr/bin/env python3
"""Atomic local claim/overlap lock for parallel math workers.

Stores claim state strictly in the PRIVATE host workspace (`$MATH_LIFE_CLAIMS` or
`~/.math-life/claims.json`) — NEVER inside the public git repository.
Prevents duplicate parallel work across arXiv IDs, slugs, and overlapping titles.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

DEFAULT_STATE = Path(os.environ.get("MATH_LIFE_CLAIMS", Path.home() / ".math-life" / "claims.json"))
STOPWORDS = frozenset({
    "the", "and", "for", "that", "with", "from", "conjecture", "problem", "question",
    "theorem", "proof", "open", "finite", "number", "numbers", "integer", "integers",
})


def norm_arxiv(raw: str) -> str:
    raw = re.sub(r"^https?://arxiv\.org/(?:abs|pdf|e-print)/", "", raw.strip())
    return re.sub(r"v\d+$", "", raw)


def norm_tokens(text: str) -> set[str]:
    clean = re.sub(r"[^a-z0-9]+", " ", text.lower())
    return {t for t in clean.split() if len(t) >= 4 and t not in STOPWORDS}


def load_locked(lock_file: Path) -> tuple[Any, dict[str, Any]]:
    lock_file.parent.mkdir(parents=True, exist_ok=True)
    fh = open(lock_file, "a+", encoding="utf-8")
    fcntl.flock(fh.fileno(), fcntl.LOCK_EX)
    fh.seek(0)
    raw = fh.read().strip()
    data = json.loads(raw) if raw else {"claims": {}}
    if "claims" not in data or not isinstance(data["claims"], dict):
        data = {"claims": {}}
    return fh, data


def save_and_unlock(fh: Any, data: dict[str, Any]) -> None:
    fh.seek(0)
    fh.truncate()
    json.dump(data, fh, indent=2, ensure_ascii=False)
    fh.write("\n")
    fh.flush()
    os.fsync(fh.fileno())
    fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
    fh.close()


def find_overlap(claims: dict[str, Any], *, slug: str, arxiv_id: str, title: str) -> str | None:
    if slug in claims:
        return f"slug '{slug}' already claimed by {claims[slug].get('owner')}"
    aid = norm_arxiv(arxiv_id) if arxiv_id else ""
    toks = norm_tokens(title) if title else set()
    for other_slug, rec in claims.items():
        if aid and rec.get("arxiv_id") and norm_arxiv(rec["arxiv_id"]) == aid:
            return f"arXiv:{aid} already claimed under '{other_slug}' by {rec.get('owner')}"
        if len(toks) >= 3 and rec.get("title"):
            other_toks = norm_tokens(rec["title"])
            if other_toks:
                inter = len(toks & other_toks)
                jaccard = inter / len(toks | other_toks)
                if jaccard >= 0.70 or (inter >= 4 and inter / min(len(toks), len(other_toks)) >= 0.85):
                    return f"title overlaps '{other_slug}' (jaccard={jaccard:.2f})"
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description="Atomic local problem claim lock.")
    parser.add_argument("--state", type=Path, default=DEFAULT_STATE)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_claim = sub.add_parser("claim")
    p_claim.add_argument("slug")
    p_claim.add_argument("--owner", required=True)
    p_claim.add_argument("--arxiv-id", default="")
    p_claim.add_argument("--title", default="")

    p_check = sub.add_parser("check")
    p_check.add_argument("slug")
    p_check.add_argument("--arxiv-id", default="")
    p_check.add_argument("--title", default="")

    p_rel = sub.add_parser("release")
    p_rel.add_argument("slug")
    p_rel.add_argument("--status", default="closed")

    sub.add_parser("list")
    args = parser.parse_args()

    fh, data = load_locked(args.state)
    try:
        claims = data["claims"]
        if args.cmd == "list":
            print(json.dumps(claims, indent=2, ensure_ascii=False))
            return 0
        if args.cmd == "check":
            hit = find_overlap(claims, slug=args.slug, arxiv_id=args.arxiv_id, title=args.title)
            if hit:
                print(f"OVERLAP: {hit}")
                return 2
            print("FREE")
            return 0
        if args.cmd == "claim":
            hit = find_overlap(claims, slug=args.slug, arxiv_id=args.arxiv_id, title=args.title)
            if hit:
                print(f"REFUSED: {hit}", file=sys.stderr)
                return 2
            claims[args.slug] = {
                "owner": args.owner,
                "arxiv_id": norm_arxiv(args.arxiv_id) if args.arxiv_id else "",
                "title": args.title,
                "claimed_at": dt.datetime.now(dt.timezone.utc).isoformat(),
            }
            save_and_unlock(fh, data)
            print(f"CLAIMED: {args.slug} -> {args.owner}")
            return 0
        if args.cmd == "release":
            if args.slug not in claims:
                print(f"NOT FOUND: {args.slug}", file=sys.stderr)
                return 1
            claims.pop(args.slug)
            save_and_unlock(fh, data)
            print(f"RELEASED: {args.slug} ({args.status})")
            return 0
    finally:
        if not fh.closed:
            fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
            fh.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
