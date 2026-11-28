#!/usr/bin/env python3
"""Exact finite checks for the proof at p=3. No character-table software needed."""
from collections import defaultdict
from itertools import product
from math import factorial, gcd, isqrt, prod


def check(ok, msg):
    if not ok:
        raise ValueError(msg)


def divide(a, b):
    q, r = divmod(a, b)
    check(r == 0, "inexact character-degree division")
    return q


def threepart(n):
    """3-part of n!, by Legendre's formula."""
    v = 0
    while n:
        n //= 3
        v += n
    return 3**v


def target(n):
    return factorial(n) // threepart(n)


def ordinary(lam):
    """Frobenius form of the hook-length formula, beta_i=lambda_i+L-i."""
    beta = [a + len(lam)-1-i for i, a in enumerate(lam)]
    return divide(factorial(sum(lam)) * prod(x-y for i, x in enumerate(beta)
                                             for y in beta[i+1:]),
                  prod(factorial(x) for x in beta))


def spin(lam):
    """Degree of ONE ordinary spin character labelled by a strict partition."""
    n, l = sum(lam), len(lam)
    pairs = [(a, b) for i, a in enumerate(lam) for b in lam[i+1:]]
    return divide(2**((n-l)//2) * factorial(n) * prod(a-b for a, b in pairs),
                  prod(factorial(x) for x in lam) * prod(a+b for a, b in pairs))


def core_candidates(spin_sector, cap):
    """Only sound witnesses, not completeness of the enumeration, are needed."""
    if spin_sector:
        yield ()
        for r in (1, 2):
            for l in range(1, isqrt(cap)+2):
                nu = tuple(3*i+r for i in reversed(range(l)))
                if sum(nu) <= cap:
                    yield nu
        return
    R = isqrt(cap)+3
    for a, b in product(range(-R, R+1), repeat=2):
        c = -a-b
        if 3*(a*a+b*b+c*c)//2 + b + 2*c > cap:
            continue
        h = -min(a, b, c)
        beads = sorted((3*j+i for i, v in enumerate((a, b, c))
                        for j in range(h+v)), reverse=True)
        yield tuple(x for j, y in enumerate(beads)
                    if (x := y-len(beads)+j+1) > 0)


def add_one(spin_sector, nu):
    """Add one 3-(bar) hook; the parent nu is a core."""
    if spin_sector:
        for i, x in enumerate(nu):
            if x+3 not in nu:
                yield tuple(sorted(nu[:i]+(x+3,)+nu[i+1:], reverse=True))
        if 3 not in nu:
            yield tuple(sorted(nu+(3,), reverse=True))
        if 1 not in nu and 2 not in nu:
            yield tuple(sorted(nu+(1, 2), reverse=True))
    else:
        L = len(nu)+3
        beta = [x+L-1-i for i, x in enumerate(nu+(0, 0, 0))]
        for i, b in enumerate(beta):
            if b+3 not in beta:
                s = sorted(beta[:i]+[b+3]+beta[i+1:], reverse=True)
                yield tuple(x for j, y in enumerate(s) if (x := y-L+1+j) > 0)


def check_weight(n, d, w):
    """For w=0,1 the valuation deficit counts the 3-divisible (bar) hooks."""
    P = threepart(n)
    check(w in (0, 1) and d > 0 and 3**w * gcd(P, d) == P,
          f"wrong (bar) weight at rank {n}")


def small_bounds(sp, cap):
    """Three times a lower bound on the sector mass in each group."""
    degree = spin if sp else ordinary
    labels = {}
    for nu in core_candidates(sp, cap):
        n = sum(nu)
        check(0 <= n <= cap, "core size")
        if n >= 4:
            check(labels.setdefault(nu, 0) == 0, "label overlap")
        if 4 <= n+3 <= min(cap, 64):
            for lam in add_one(sp, nu):
                check(sum(lam) == n+3, "wrong hook size")
                check(labels.setdefault(lam, 1) == 1, "label overlap")
    mass = defaultdict(int)
    for lam, w in labels.items():
        n = sum(lam)
        check(all(a > 0 for a in lam) and
              all(a > b if sp else a >= b for a, b in zip(lam, lam[1:])), "partition")
        multiplicity = 1 + (n-len(lam)) % 2 if sp else 1
        d = degree(lam)
        check_weight(n, d, w)
        mass[n] += (3 if w == 0 else 1) * multiplicity * d**2
    return mass


# CTblLib: complete 3-modular degrees in the indicated A_n sector.
ATLAS = {(False, 7): (1, 6, 10, 10, 13, 15),
         (True, 8): (8, 24, 24, 48),
         (True, 9): (8, 48, 104)}


def check_atlas(n, degrees):
    check(2*sum(d*d for d in degrees) >= target(n), "insufficient alternating-sector mass")


def size(sp, l):
    return l*(3*l-1)//2 if sp else l*(l+1)


def stairs(sp, l):
    return tuple(3*i-2 if sp else 2*i for i in range(l, 0, -1))


def small_ranks(sp, end):
    B = small_bounds(sp, end+7)
    best = B[4]
    atlas_used = set()
    for n in range(5, end+1):
        rhs = 3*target(n)
        best = max(best, B[n])
        if best >= rhs:
            continue
        # Descend from at most seven further ranks, dividing by the index SQUARED.
        if any(B[m] >= rhs * prod(range(n+1, m+1))**2
               for m in range(n+1, n+8)):
            continue
        check((sp, n) in ATLAS, f"uncovered rank {n}, spin={sp}")
        check_atlas(n, ATLAS[sp, n])
        atlas_used.add((sp, n))
    return atlas_used


def tail(sp, start):
    degree = spin if sp else ordinary
    m0 = size(sp, 64)
    D0 = degree(stairs(sp, 64))
    F0 = factorial(m0)
    # Base for the uniform, slightly coarser bound used beyond l=255.
    check(D0**2 * 3**m0 >= F0 * 2**m0, "normalized base")
    for l in range(start, 256):
        m, M = size(sp, l), size(sp, l+1)-1
        if l < 64:
            d = degree(stairs(sp, l))
            check_weight(m, d, 0)
            check(d*d >= target(M), f"exact endpoint {l}")
        else:
            # R_l = D_l^2/m! >= R_64 (2/3)^(m-m0); compare at M.
            h = m-m0
            check(D0**2 * 2**h * threepart(M) >=
                  F0 * 3**h * prod(range(m+1, M+1)), f"bounded endpoint {l}")


def mutated_checks():
    for test in (lambda: check_weight(6, ordinary((3, 3)), 0),
                 lambda: check_weight(6, spin((6,)), 1),
                 lambda: check_atlas(9, (8, 4, 10))):
        try:
            test()
        except ValueError:
            continue
        raise AssertionError("corrupted witness accepted")


def main():
    check(5**64 * factorial(64) <= 128**64, "factorial base")
    check(8**512 >= 7**512 * (2*258**2)**5, "large-range base")
    check(8**2 * 258**10 >= 7**2 * 259**10, "large-range induction")
    used = set()
    for sp, L in ((False, 43), (True, 27)):
        end = size(sp, L)-1
        used.update(small_ranks(sp, end))
        tail(sp, L)
        print(f'{"spin" if sp else "ordinary"}: ranks 5..{end}; '
              f'staircase endpoint checks {L}..255 passed')
    check(used == set(ATLAS), "unexpected table-exception set")
    mutated_checks()
    print("PASS: finite coverage, analytic base constants, and mutation controls")


if __name__ == "__main__":
    main()
