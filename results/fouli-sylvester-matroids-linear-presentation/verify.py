"""Exact 15-point counterexample to Fouli et al., Conjecture 4.1.

The binary labels only define incidence. All cochain values are integers,
and the pairing is one, so the certificate applies over Q.
"""

from math import gcd
from itertools import combinations, combinations_with_replacement

E = tuple(range(15))
AFF = tuple(range(8))
D = frozenset(range(8, 15))  # d_h is 7+h
U = frozenset(range(4))
T = U | {8, 9, 10}
LINES = (D,) + tuple(
    frozenset((x, y, 7 + (x ^ y))) for x, y in combinations(AFF, 2)
)
SMALL = frozenset(L for L in LINES if L <= T)


# A second rank-three matroid: here every line has exactly three points.
STEINER = tuple(map(frozenset, (
    (0, 1, 2), (0, 3, 11), (0, 4, 12), (0, 5, 6), (0, 7, 8),
    (0, 9, 13), (0, 10, 14), (1, 3, 5), (1, 4, 6), (1, 7, 9),
    (1, 8, 10), (1, 11, 13), (1, 12, 14), (2, 3, 8), (2, 4, 11),
    (2, 5, 14), (2, 6, 9), (2, 7, 10), (2, 12, 13), (3, 4, 7),
    (3, 6, 12), (3, 9, 10), (3, 13, 14), (4, 5, 9), (4, 8, 14),
    (4, 10, 13), (5, 7, 13), (5, 8, 11), (5, 10, 12), (6, 7, 14),
    (6, 8, 13), (6, 10, 11), (7, 11, 12), (8, 9, 12), (9, 11, 14),
)))


def check(ok, message):
    if not ok:
        raise ValueError(message)


def incidence(lines):
    check(len(set(lines)) == len(lines), "duplicate line")
    through = {}
    for L in lines:
        check(len(L) >= 3 and L < set(E), "invalid line")
        for a, b in combinations(sorted(L), 2):
            check((a, b) not in through, "nonunique pair-line")
            through[a, b] = through[b, a] = L
    check(all((a, b) in through for a, b in combinations(E, 2)), "uncovered pair")
    return through


def quadratic_hilbert(through, k):
    """Count surviving components of degree-k monomials modulo the quadrics."""
    mons = list(combinations_with_replacement(E, k))
    parent = {m: m for m in mons}

    def find(m):
        while parent[m] != m:
            parent[m] = parent[parent[m]]
            m = parent[m]
        return m

    for m in mons:
        for i, j in combinations(range(k), 2):
            a, b = m[i], m[j]
            if a == b:
                continue
            rest = m[:i] + m[i+1:j] + m[j+1:]
            for pair in combinations(through[a, b], 2):
                other = tuple(sorted(rest + pair))
                parent[find(other)] = find(m)
    killed = {find(m) for m in mons if len(set(m)) < k}
    return len({find(m) for m in mons} - killed)


def phi(L, i, j, affine=U, points=T, small=SMALL):
    if L not in small:
        return 0
    return int(i in points - L) * int(j in affine) - int(j in points - L) * int(i in affine)


def check_koszul(through, functional, lines=LINES, pair=(0, 1), other=(4, 5), wedge=(9, 2)):
    L, Lp = through[pair], through[other]
    i, j = wedge
    d2z = [0] * len(E)
    for sign, F in ((1, L), (-1, Lp)):
        d2z[j] += sign * int(i not in F)
        d2z[i] -= sign * int(j not in F)
    check(not any(d2z), "not a 2-cycle")
    for F in lines:
        for a in E:
            for b in E:
                check(functional(F, a, b) == -functional(F, b, a), "not alternating")

    def term(t, a, b, c):
        return 0 if t == a else functional(through[t, a], b, c)

    count = 0
    for t in E:
        for a, b, c in combinations(E, 3):
            val = term(t, a, b, c) - term(t, b, a, c) + term(t, c, a, b)
            check(val == 0, f"nonzero boundary pairing at {(t, a, b, c)}: {val}")
            count += 1

    pairing = functional(L, i, j) - functional(Lp, i, j)
    check(pairing == 1, "cycle not separated by the stated unit pairing")
    return count


def rational_rank(columns):
    """Column echelon elimination over Q, using only primitive integer vectors."""
    pivots = {}
    for col in columns:
        while col:
            j = min(col)
            if j not in pivots:
                pivots[j] = col
                break
            row = pivots[j]
            a, b = row[j], col[j]
            g = gcd(a, b)
            a, b = a // g, b // g
            col = {i: a * v for i, v in col.items()}
            for i, v in row.items():
                col[i] = col.get(i, 0) - b * v
                if not col[i]:
                    del col[i]
            g = gcd(*col.values())
            if g > 1:
                col = {i: v // g for i, v in col.items()}
    return len(pivots)


def betti24(through, lines):
    pairs = tuple(combinations(E, 2))
    rows = {(L, a, b): i * len(lines) + j
            for i, (a, b) in enumerate(pairs) for j, L in enumerate(lines)}

    def d3():
        for t in E:
            for a, b, c in combinations(E, 3):
                yield {rows[through[t, x], y, z]: s
                       for x, y, z, s in ((a,b,c,1), (b,a,c,-1), (c,a,b,1))
                       if t != x}

    def d2():
        for L, a, b in rows:
            yield {i: s for i, x, s in ((b, a, 1), (a, b, -1)) if x not in L}

    return len(rows), rational_rank(d2()), rational_rank(d3())


def main():
    check(len(LINES) == 29 and len(SMALL) == 6, "direction line data")
    through = incidence(LINES)
    print("15 points, 29 lines; all 105 pairs lie on a unique line of size >= 3")
    h = tuple(quadratic_hilbert(through, k) for k in range(5))
    check(h == (1, 15, 29, 1, 0), "quadratic quotient has wrong Hilbert function")
    print("Hilbert function of the quadratic quotient in degrees 0..4:", h)
    count = check_koszul(through, phi)
    print(f"d2(z)=0; Phi kills all {count} columns of d3; Phi(z)=1")

    dim, r2, r3 = betti24(through, LINES)
    check((dim, r2, r3) == (3045, 15, 3010), "unexpected rational ranks")
    print(f"over Q: dim K2_4={dim}, ranks d2={r2}, d3={r3}, beta_2,4={dim-r2-r3}")

    def corrupted(L, i, j):
        delta = int((i, j) == (9, 2)) - int((i, j) == (2, 9))
        return phi(L, i, j) + int(L == through[0, 1]) * delta

    try:
        check_koszul(through, corrupted)
    except ValueError as err:
        check(str(err).startswith("nonzero boundary pairing"), "unexpected mutation failure")
        print("Corrupted cochain rejected:", err)
    else:
        raise RuntimeError("corrupted cochain passed")

    check(len(STEINER) == 35 and all(len(L) == 3 for L in STEINER), "Steiner line data")
    st = incidence(STEINER)
    affine = frozenset((1, 6, 10, 13))
    points = affine | {4, 8, 11}
    small = frozenset(L for L in STEINER if L <= points)
    check(len(small) == 6, "missing six-line configuration")
    def st_phi(L, i, j):
        return phi(L, i, j, affine, points, small)
    cols = check_koszul(st, st_phi, STEINER, (1, 6), (0, 1), (8, 10))
    print(f"Steiner cycle: Phi kills all {cols} columns and pairs to 1")
    h = tuple(quadratic_hilbert(st, k) for k in range(5))
    check(h == (1, 15, 35, 1, 0), "nonquadratic Steiner example")
    dim, r2, r3 = betti24(st, STEINER)
    check((dim, r2, r3) == (3675, 15, 3656), "Steiner rational ranks")
    print("Steiner system: Hilbert function", h,
          f"; dim K2_4={dim}, ranks d2={r2}, d3={r3}, beta_2,4={dim-r2-r3}")


if __name__ == "__main__":
    main()
