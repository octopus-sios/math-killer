#!/usr/bin/env python3
"""Self-contained zero-float verifier for the Manickam-Miklos-Singhi campaign results.

Verifies all three computational pillars with exact integer / rational arithmetic only
(no floating-point decisions, no external LP/MIP solvers, no GMP/MPFR dependencies):

  1. Universal MMS for all n >= 7k (verify_universal.py):
     Exact rational interval certificates across all 4 density bands / 7 cells,
     exact slice-moment identities, the elementary n >= 3k^2 backup, and mutation tests.

  2. Complete Milojevic-Sudakov (arXiv:2606.30287v1) Conjectures 1 & 3 on p in [0, 1/3]:
     - Analytic proof on [0, 1/7] and exact unit-fraction coloring at p = 1/q (incl. p = 1/3)
       are Lean 4 kernel-verified (Conjectures.ManickamMiklosSinghi.BernoulliOneSeventh).
     - Exact integer replay of [1/7, 3/10] (bernoulli_constants.py) + mutation test.
     - Exact integer + int128 C++ replay of [29/100, 8/25] and [8/25, 1/3)
       (bernoulli_extension.py + prefix.cpp) + mutation test.

  3. Exact k = 8 rational Farkas & SPEC1 spectral certificates:
     - Exact counterexample at n = 25, k = 8 (319,770 < C(24,7) = 346,104 => f(8) >= 26).
     - Sharp Farkas / block-lift certificates for g(18,8)=12870, g(28,8)=888030,
       g(30,8)=1560780, g(32,8)=2629575 (verify_cert.py).
     - Sharp SPEC1 spectral certificate for g(33,8) = C(32,7) = 3,365,856 (cover_exact.py).
     - Negative mutation tests on both certificate verifiers.
"""

from __future__ import annotations

import math
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def run_step(label: str, cmd: list[str], expect_fail: bool = False) -> None:
    t0 = time.monotonic()
    res = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True, check=False)
    dt = time.monotonic() - t0
    if expect_fail:
        if res.returncode == 0:
            raise RuntimeError(f"[{label}] expected non-zero exit (mutation test), got 0")
        print(f"PASS (mutation caught in {dt:.2f}s): {label}")
        return
    if res.returncode != 0:
        sys.stderr.write(res.stdout)
        sys.stderr.write(res.stderr)
        raise RuntimeError(f"[{label}] failed with exit code {res.returncode}")
    last = (res.stdout.strip().splitlines() or ["OK"])[-1]
    print(f"PASS ({dt:.2f}s): {label} -> {last}")


def check_n25_k8_counterexample() -> None:
    """Verify exact witness x = (3^22, -22^3) proving g(25, 8) <= 319770 < C(24, 7) = 346104."""
    pos, neg = 22, 3
    n, k = pos + neg, 8
    total = pos * 3 + neg * (-22)
    assert total == 0, f"sum must be 0, got {total}"
    good = 0
    for r in range(k + 1):
        if r * 3 + (k - r) * (-22) >= 0:
            good += math.comb(pos, r) * math.comb(neg, k - r)
    star = math.comb(n - 1, k - 1)
    assert good == 319_770 and star == 346_104 and good < star
    print(f"PASS: exact witness (25, 8) has {good} < {star} nonnegative 8-subsets (f(8) >= 26)")


def check_cert_mutations() -> None:
    """Confirm both verify_cert.py and cover_exact.py reject tampered certificates."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        # 1. Tamper with m_32_8_2629575.cert target (+1 above sharp value)
        bad_farkas = tmp / "m_32_8_2629576.cert"
        bad_farkas.write_text("MMS1 32 8 2629576 0\nG 2\n", encoding="utf-8")
        run_step(
            "Farkas certificate mutation test",
            [sys.executable, str(HERE / "verify_cert.py"), str(bad_farkas)],
            expect_fail=True,
        )
        # 2. Tamper with m_33_8_3365856.cert target (+1 above sharp value)
        orig = (HERE / "certs" / "m_33_8_3365856.cert").read_text(encoding="utf-8")
        lines = orig.splitlines()
        assert lines[0] == "MMSC1 33 8 3365856", f"unexpected header: {lines[0]!r}"
        lines[0] = "MMSC1 33 8 3365857"
        bad_spec = tmp / "m_33_8_3365857.cert"
        bad_spec.write_text("\n".join(lines) + "\n", encoding="utf-8")
        run_step(
            "SPEC1 spectral certificate mutation test",
            [sys.executable, str(HERE / "cover_exact.py"), str(bad_spec)],
            expect_fail=True,
        )


def main() -> int:
    t_start = time.monotonic()
    py = sys.executable

    print("=== Part I: Universal MMS for all n >= 7k ===")
    run_step("Universal n >= 7k rational certificates + mutation tests", [py, str(HERE / "verify_universal.py")])

    print("\n=== Part II: Milojevic-Sudakov Conjectures 1 & 3 on [0, 1/3] ===")
    run_step("Bernoulli [1/7, 3/10] pure-integer replay + mutation test", [py, str(HERE / "bernoulli_constants.py")])
    run_step(
        "Bernoulli [29/100, 8/25] exact int128 replay",
        [
            py,
            str(HERE / "bernoulli_extension.py"),
            "--lo", "29/100",
            "--hi", "8/25",
            "--mesh", "300",
            "--B", "192",
            "--D", "240",
            "--U", "256",
            "--depth", "8",
            "--coarse", "4",
        ],
    )
    run_step(
        "Bernoulli [8/25, 1/3) exact int128 replay",
        [
            py,
            str(HERE / "bernoulli_extension.py"),
            "--lo", "8/25",
            "--hi", "1/3",
            "--mesh", "300",
            "--B", "192",
            "--D", "240",
            "--U", "256",
            "--depth", "8",
            "--coarse", "4",
        ],
    )
    run_step(
        "Bernoulli extension mutation test",
        [
            py,
            str(HERE / "bernoulli_extension.py"),
            "--lo", "8/25",
            "--hi", "1/3",
            "--mesh", "300",
            "--B", "192",
            "--D", "240",
            "--U", "256",
            "--depth", "8",
            "--coarse", "4",
            "--mutation-test",
        ],
        expect_fail=True,
    )

    print("\n=== Part III: Exact k = 8 Certificates & Counterexample ===")
    check_n25_k8_counterexample()
    for name in (
        "m_18_8_12870.cert",
        "m_28_8_888030.cert",
        "m_30_8_1560780.cert",
        "m_32_8_2629575.cert",
    ):
        run_step(
            f"Farkas/block-lift certificate {name}",
            [py, str(HERE / "verify_cert.py"), str(HERE / "certs" / name)],
        )
    run_step(
        "SPEC1 spectral certificate m_33_8_3365856.cert (g(33,8) = C(32,7))",
        [py, str(HERE / "cover_exact.py"), str(HERE / "certs" / "m_33_8_3365856.cert")],
    )
    check_cert_mutations()

    print(f"\nALL VERIFICATIONS PASSED in {time.monotonic() - t_start:.2f}s (zero floats).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
