#!/usr/bin/env python3
"""Exact cross-checks for the uniform overlap theorem (the all-rank proof is in PROOF.md)."""

from itertools import combinations, combinations_with_replacement
from math import comb, gcd


def board_z(lam, mu):
    """Marked Motzkin model via height and a threshold on all chosen columns."""
    r = len(lam)
    m = r - 1
    hi = lam[1] - 1  # largest column of the board of 2-by-2 squares
    # Evaluate the gamma-polynomial at 2**bits; no carries are possible.
    # There are <=3**r paths and <=sum binom(m,k)binom(hi,k) placements.
    bits = (3**r * comb(hi + m, m)).bit_length()
    # v[h][c] includes placements all of whose columns are > c.
    v = [[1] * (hi + 1)]
    for j in range(1, r + 1):
        u = []
        for h in range(min(j, r-j) + 1):
            f = v[h].copy() if h < len(v) else [0] * (hi + 1)  # level step
            if h:  # up-step; weight 2**bits
                f = [a + (b << bits) for a, b in zip(f, v[h-1])]
            if h+1 < len(v):  # down-step
                f = [a + b for a, b in zip(f, v[h+1])]
            if h:
                # No rook, or a rook in an eligible column d > c with
                # all earlier columns > d. Accumulate the latter in 'tail'.
                low, high = mu[j-1]+1, lam[j]-1
                tail = 0
                for c in range(high, -1, -1):
                    old = f[c]
                    f[c] += tail
                    if c >= low:
                        tail += old
            u.append(f)
        v = u
    value, mask = v[0][0], (1 << bits) - 1
    z = [0] * (r + 1)
    for k in range(r//2 + 1):
        gamma = value & mask
        value >>= bits
        for a in range(r-2*k + 1):
            z[k+a] += gamma * comb(r-2*k, a)
    if value:
        raise ArithmeticError("unexpected gamma degree")
    return z


def flats_z(lam, mu):
    """Independent computation from bases, ranks and intervals in the flat lattice."""
    r = len(lam)
    n = r + lam[0]
    bases = [sum(1 << (b-1) for b in B) for B in combinations(range(1, n+1), r)
             if all(i + mu[-i] <= b <= i + lam[-i] for i, b in enumerate(B, 1))]
    rank = [max((a & b).bit_count() for b in bases) for a in range(1 << n)]
    flats = [a for a in range(1 << n)
             if all((a >> i) & 1 or rank[a | (1 << i)] > rank[a] for i in range(n))]
    # P for the contraction at each flat. The rank bound on P and the
    # palindromicity of Z uniquely recover the missing bottom summand.
    kl = {}
    for f in reversed(flats):  # every strict superset precedes f
        d = r - rank[f]
        if not d:
            kl[f] = [1]
            continue
        z = [0] * (d + 1)
        for g, p in kl.items():
            if f & g == f:
                for j, c in enumerate(p, rank[g]-rank[f]):
                    z[j] += c
        p = [z[d-j] - z[j] for j in range((d+1)//2)]
        kl[f] = p
        for j, val in enumerate(p):
            z[j] += val
        if z != z[::-1] or p[0] != 1:
            raise ArithmeticError("flat-lattice recursion")
        if f == 0:
            return z
    raise ValueError("expected a positive-rank loopless matroid")


def primitive(v):
    """Strip high zeros and divide by POSITIVE content only."""
    while v and not v[-1]:
        v.pop()
    if not v:
        return []
    g = gcd(*v)
    return [a//g for a in v]


def has_interlacer(f):
    """Positive-leading signed remainder chain: degrees r,r-1,...,0."""
    r = len(f)-1
    b = [comb(r-1, j)**2 for j in range(r)]
    a = f[:]
    while b:
        if a[-1] <= 0 or b[-1] <= 0 or len(a) != len(b)+1:
            return False
        if len(b) == 1:
            return True
        while len(a) >= len(b):
            d, high = len(a)-len(b), a[-1]
            a = [c * b[-1] for c in a]  # positive multiple of a
            for i, c in enumerate(b):
                a[i+d] -= high*c
            a = primitive(a)
        a, b = b, [-c for c in a]
    return False


def check_equal(label, a, b):
    if a != b:
        raise ValueError(f"{label}: {a} != {b}")


def main():
    straight = skew = 0
    # Every normalized connected positive shape of rank >=2 on at most 7 elements.
    for n in range(3, 8):
        for r in range(2, n):
            w = n-r
            for tail in combinations_with_replacement(range(1, w+1), r-1):
                lam = (w,) + tail[::-1]
                for prefix in combinations_with_replacement(range(w), r-1):
                    mu = prefix[::-1] + (0,)
                    if any(u >= v for u, v in zip(mu, lam[1:])):
                        continue
                    check_equal((lam, mu), board_z(lam, mu), flats_z(lam, mu))
                    if mu[0]:
                        skew += 1
                    else:
                        straight += 1
    print(f"Flat lattice = rook/path model: {straight} straight and {skew} skew shapes.")

    # Outside the theorem, D_3 does not strictly interlace the circuit polynomial.
    thin = board_z((1,)*4, (0,)*4)
    check_equal("circuit", thin, [1, 10, 20, 10, 1])
    check_equal("thin-board boundary", has_interlacer(thin), False)
    corrupt = thin[:]
    corrupt[2] += 1  # preserve symmetry, degree, endpoints and positivity
    try:
        check_equal("mutated witness", corrupt, flats_z((1,)*4, (0,)*4))
    except ValueError:
        pass
    else:
        raise AssertionError("mutation not detected")

    r = 36
    lam = tuple(30*(r-1) + (r-i)**2 for i in range(1, r+1))
    a = board_z(lam, (0,)*r)
    # A skew board at the same rank, equally thick overlaps but no common
    # column across all rows (the intervals slide 40 columns per row).
    mu = tuple(40*i for i in reversed(range(r)))
    lam_skew = tuple(u + 40 + 30*(r-1) for u in mu)
    b = board_z(lam_skew, mu)
    for label, z in [("Ferrers", a), ("skew", b), ("mixture", [p+2*q for p, q in zip(a,b)])]:
        check_equal(label + " symmetry", z, z[::-1])
        check_equal(label + " signed remainders", has_interlacer(z), True)
    print("Degree 36: exact strict D_35 interlacing for straight, skew and their 1:2 mixture.")
    print("Thin-board boundary and corrupted-coefficient rejection: OK.")


if __name__ == "__main__":
    main()
