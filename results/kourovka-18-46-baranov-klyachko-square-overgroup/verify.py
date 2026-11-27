#!/usr/bin/env python3
"""Check degree-4096 data and a mutation, not the CFSG argument."""

import argparse
from math import factorial


class Invalid(ValueError):
    pass


def require(test, message):
    if not test:
        raise Invalid(message)


def perm(n, *cycles):
    out = list(range(n))
    used = set()
    for cycle in cycles:
        for i, x in enumerate(cycle):
            require(0 <= x < n and x not in used, "invalid cycle data")
            used.add(x)
            out[x] = cycle[(i + 1) % len(cycle)]
    return out


def check_witness(g):
    n = len(g)
    require(sorted(g) == list(range(n)), "not a permutation")
    seen = set()
    count = 0
    for x in range(n):
        if x not in seen:
            count += 1
            while x not in seen:
                seen.add(x)
                x = g[x]
    require((n - count) % 2 == 0, "not in alternating group")
    require(sum(x != g[x] and g[g[x]] == x for x in range(n)) == 2,
            "not a unique two-cycle")


def check_bounds(n):
    j = n.bit_length() - 1
    require(n >= 4096 and j >= 12, "outside proved range")
    require(1 << j >= 288 * (j + 1), "dyadic estimate")
    d = n // 5 + 1
    require(d > 248 and 6 * (d - 2) >= n, "projective degree bound")
    a = ((d - 2) ** 2 + 3) // 4
    require(a >= 2 * n * (j + 1), "classical order exponent")
    size = factorial(n) // 2
    require(size > 10 ** 54, "sporadic cutoff")
    require(1 << a > 2 * size ** 2, "classical order cutoff")
    require(factorial(2 * n) // 2 > 2 * size ** 2, "alternating cutoff")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corrupt", action="store_true",
                        help="supply a genuine square instead (must fail)")
    args = parser.parse_args()
    n = 4096
    g = perm(n, (0, 1, 2, 3), (4, 5))
    # Pair both even cycles with a second copy; this remains even but is a square.
    bad = perm(n, (0, 1, 2, 3), (4, 5), (6, 7, 8, 9), (10, 11))
    root = perm(n, (0, 6, 1, 7, 2, 8, 3, 9), (4, 10, 5, 11))
    require([root[root[x]] for x in range(n)] == bad, "bad mutation root")
    check_witness(bad if args.corrupt else g)
    check_bounds(n)
    try:
        check_witness(bad)
    except Invalid as exc:
        require(str(exc) == "not a unique two-cycle", "wrong rejection reason")
    else:
        raise Invalid("accepted a genuine square")
    print("PASS: A_4096 witness, size inequalities, and square mutation control")


if __name__ == "__main__":
    try:
        main()
    except Invalid as exc:
        raise SystemExit("FAIL: " + str(exc))
