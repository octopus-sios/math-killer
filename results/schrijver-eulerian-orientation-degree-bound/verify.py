#!/usr/bin/env python3
"""Finite local certificate for the degree-six Eulerian orientation bound.

Run: python3 -I verify.py. Only Python's exact integers and rational numbers.
"""
from fractions import Fraction as Q
from functools import cache
from itertools import combinations
from math import comb, gcd, lcm

M = ((2, 1, 0, 1), (1, 1, 1, 0), (0, 1, 2, 1), (1, 0, 1, 1))
COLORS = range(4)
DEGREES = (0, 2, 4, 6)
BETA = (Q(1), Q(3, 4), Q(1, 2), Q(1, 3), Q(1, 5))


def initial(r):
    return (1, 2**(r//2), 1, 2**(r//2))


def pin(u, x):
    return tuple(u[i]*M[x][i] for i in COLORS)


def primitive(u):
    g = gcd(*u)
    return tuple(v//g for v in u) if g else u


def lists():
    F = [set() for _ in range(7)]
    for r in DEGREES:
        F[r].add(initial(r))
    for k in range(6, 0, -1):
        for u in F[k]:
            for x in COLORS:
                child = pin(u, x)
                if any(child):
                    F[k-1].add(primitive(child))
    return F


@cache
def clique(s, u):
    """Integer partition sum for K_s: one occupied color or an adjacent pair."""
    def mono(i, t):
        return u[i]**t * M[i][i]**(t*(t-1)//2)
    val = sum(mono(i, s) for i in COLORS)
    for i in COLORS:
        j = (i+1) % 4
        for t in range(1, s):
            val += comb(s, t)*mono(i, t)*mono(j, s-t)
    return val


@cache
def potential(k, u, beta):
    """Return (N,s) representing the nonnegative s-th root of N."""
    support = tuple(i for i in COLORS if u[i])
    if support in ((0, 2), (1, 3)):
        i, j = support
        if k >= len(beta) or u[i] != u[j]:
            raise ValueError(("unexpected opposite list", k, u))
        y = beta[k] + (Q(k, 2) if i == 0 else 0)
        return u[i]**y.denominator * 2**y.numerator, y.denominator
    return clique(k+1, u), k+1


def floor_root(n, m):
    """Largest integer y such that y**m <= n."""
    if m == 1 or n < 2:
        return n
    lo, hi = 0, 1 << ((n.bit_length()+m-1)//m)
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**m <= n:
            lo = mid
        else:
            hi = mid
    return lo


def compare_roots(nums, den, m):
    """Sign of sum (N/den)^(1/m) - 1. Never decide from rounded equality."""
    scale = 1 << 24
    lo = hi = 0
    for n in nums:
        nn = n*scale**m
        y = floor_root(nn//den, m)
        lo += y
        hi += y + (y**m*den != nn)
    if hi < scale:
        return -1
    if lo > scale:
        return 1
    # On the boundary try *exact* rational roots, checked by powering back.
    exact = Q(0)
    for n in nums:
        q = Q(n, den)
        a = floor_root(q.numerator, m)
        b = floor_root(q.denominator, m)
        if a**m != q.numerator or b**m != q.denominator:
            raise ArithmeticError("root interval inconclusive")
        exact += Q(a, b)
    return (exact > 1) - (exact < 1)


def local(a, u, b, v, beta=BETA):
    """Compare sum_x u_x P_{b-1}(v*M_x)^a to P_a(u) P_b(v)^a."""
    A, i = potential(a, u, beta)
    B, j = potential(b, v, beta)
    children = [potential(b-1, pin(v, x), beta) for x in COLORS]
    m = lcm(i, j, *(k for _, k in children))
    den = A**(m//i) * B**(a*(m//j))
    nums = [u[x]**m * C**(a*(m//k)) for x, (C, k) in enumerate(children)]
    return compare_roots(nums, den, m)


@cache
def tournaments(needs):
    """Count labeled tournaments with this list of required outdegrees."""
    if not needs:
        return 1
    n = len(needs)
    if any(v < 0 or v >= n for v in needs):
        return 0
    val = 0
    for out in combinations(range(1, n), needs[0]):
        val += tournaments(tuple(needs[j] - (j not in out) for j in range(1, n)))
    return val


def main():
    for r, claimed in zip(DEGREES, (1, 2, 24, 2640)):
        s = r+1
        t = tournaments((r//2,)*s)
        if t != claimed or clique(s, initial(r)) != 4**s*t:
            raise ValueError(("clique benchmark", r, t))
        print(f"epsilon(K{s}) = {t}")

    F = lists()
    for u in F[0]:
        c, k = potential(0, u, BETA)
        if sum(u)**k != c:
            raise ValueError(("isolated vertex", u))
    total = equal = 0
    print("Field counts by residual degree 0..6:", [len(f) for f in F])
    for a in range(1, 7):
        for b in range(1, a+1):
            for u in sorted(F[a]):
                for v in sorted(F[b]):
                    sign = local(a, u, b, v)
                    if sign > 0:
                        raise ValueError(("local inequality failed", a, u, b, v))
                    total += 1
                    equal += (sign == 0)
    print(f"{total} local inequalities: {total-equal} strict, {equal} equal")

    # The two strictness tests used to classify extremizers.
    for a in (2, 4, 6):
        for b in (2, 4):
            if b < a and local(a, initial(a), b, initial(b)) >= 0:
                raise ValueError("nonregular strictness")
        for x in COLORS:
            if local(a, initial(a), a-1, pin(initial(a), x)) >= 0:
                raise ValueError("nonclique strictness")
    print("Strict witnesses for unequal original degrees and induced 2-paths: OK")

    # Corrupt the opposite-pair potential at residual degree 3. The altered
    # certificate must give a strictly reversed inequality on admissible lists.
    bad = BETA[:3] + (Q(1, 4),) + BETA[4:]
    u, v = initial(4), (1, 0, 1, 0)
    if u not in F[4] or v not in F[3] or local(4, u, 3, v, bad) != 1:
        raise ValueError("mutation was not rejected")
    print("Mutation beta[3] = 1/4 rejected: inequality is strictly reversed.")


if __name__ == "__main__":
    main()
