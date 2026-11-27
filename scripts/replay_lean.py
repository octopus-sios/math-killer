#!/usr/bin/env python3
"""Independent Lean 4 kernel replay via `leanchecker` across all built project modules.

Auto-discovers Warmup, Conjectures, and every module under `lean/Conjectures/*.lean`
— zero hardcoded theorem lists.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path


def discover_modules(lean_dir: Path) -> list[str]:
    mods = ["Warmup", "Conjectures"]
    conj_dir = lean_dir / "Conjectures"
    if conj_dir.is_dir():
        for p in sorted(conj_dir.rglob("*.lean")):
            rel = p.relative_to(lean_dir).with_suffix("")
            mods.append(".".join(rel.parts))
    return mods


def main() -> int:
    parser = argparse.ArgumentParser(description="Replay Lean 4 modules with leanchecker.")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()

    lean_dir = args.repo / "lean"
    modules = discover_modules(lean_dir)

    if shutil.which("lake") is None:
        print("ERROR: `lake` not found on PATH", file=sys.stderr)
        return 1

    # Resolve leanchecker inside the active toolchain via `lake env leanchecker`
    for mod in modules:
        print(f"=== leanchecker replay: {mod} ===")
        res = subprocess.run(
            ["lake", "env", "leanchecker", mod],
            cwd=lean_dir,
            text=True,
        )
        if res.returncode != 0:
            print(f"ERROR: leanchecker failed on module {mod} (exit {res.returncode})", file=sys.stderr)
            return res.returncode

    print(f"replay_lean.py: PASS ({len(modules)} module(s) replayed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
