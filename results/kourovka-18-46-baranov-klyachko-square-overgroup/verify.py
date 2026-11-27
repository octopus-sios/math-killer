#!/usr/bin/env python3
"""Check the D8 square-coset exclusion and A_4096 witness arithmetic."""

import argparse
from itertools import product
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


def composition(f, g):
    return tuple(f[j] for j in g)


def inner_maps(t):
    n = len(t)
    inv = [row.index(0) for row in t]
    return [tuple(t[t[a][x]][inv[a]] for x in range(n)) for a in range(n)]


def automorphisms(t):
    # Multiplication table in normal form r^i s^j u^k, i<4, j,k<2;
    # labels encode i+4*j+8*k. For D8, omit u.
    n = len(t)
    generators = (1, 4) if n == 8 else (1, 4, 8)
    for image in product(range(1, n), repeat=len(generators)):
        r, s, *rest = image
        rp = [0, r, t[r][r], t[t[r][r]][r]]
        if len(set(rp)) < 4 or t[s][s] or s in rp:
            continue
        f = rp + [t[a][s] for a in rp]
        if rest:
            u, = rest
            f += [t[a][u] for a in f]
        if len(set(f)) == n and all(
                f[t[x][g]] == t[f[x]][y] for g, y in zip(generators, image)
                for x in range(n)):
            yield tuple(f)


def data(t, autos):
    # x^2=a and conjugation by x is f on the table group K.
    inn = inner_maps(t)
    for f in autos:
        ff = composition(f, f)
        for a, c in enumerate(inn):
            if f[a] == a and ff == c:
                yield f, a


def index_two(t, f, a):
    n = len(t)
    def mul(i, j):
        e, u = divmod(i, n)
        d, v = divmod(j, n)
        w = t[u][f[v] if e else v]
        return t[w][a] if e and d else (e ^ d) * n + w
    return [tuple(mul(i, j) for j in range(2*n)) for i in range(2*n)]


def possible_covers(t, required):
    # Test necessary conditions for K normal with quotient V4 or S3.
    n = len(t)
    aut = list(automorphisms(t))
    inn = set(inner_maps(t))
    outer = {f:min(composition(i, f) for i in inn) for f in aut}
    basesq = {t[u][u] for u in range(n)}
    missing = set(required) - basesq
    possibilities = {}
    maybe96 = False
    for f, a in data(t, aut):
        squares = {t[t[k][f[k]]][a] for k in range(n)}
        label = outer[f]
        possibilities.setdefault(label,set()).add(frozenset(squares & missing))
        if len(aut)%3 == 0:
            orbit = {h[y] for h in aut for y in squares}
            if missing <= orbit:
                maybe96 = True
    maybe64 = False
    for o,p in product(possibilities,repeat=2):
        op = outer[composition(o,p)]
        if op not in possibilities or op != outer[composition(p,o)]:
            continue
        for a,b,c in product(possibilities[o],possibilities[p],possibilities[op]):
            if missing <= a | b | c:
                maybe64 = True
    return maybe64,maybe96


def check_dihedral(corrupt=False):
    d = [[(i//4 ^ j//4)*4 + (i%4+(-1)**(i//4)*(j%4))%4
          for j in range(8)] for i in range(8)]
    number = 0
    admits_rotations = False
    for f, a in data(d, list(automorphisms(d))):
        table = index_two(d, f, a)
        require(all(table[table[x][y]][z] == table[x][table[y][z]]
                    for x,y,z in product(range(16), repeat=3)), "nonassociative table")
        possible64, possible96 = possible_covers(table, range(4 if corrupt else 8))
        require(not possible64, "surviving V4 square-coset cover")
        require(not possible96, "surviving S3 square-coset cover")
        if not admits_rotations:
            admits_rotations = possible_covers(table, range(4))[0]
        number += 1
    require(number == 16, "missing labelled extension")
    require(admits_rotations, "failed to detect a cover of the rotation subgroup")
    print("PASS: all 16 marked kernel tables; no V4 or S3 cover of D8; rotations control accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corrupt", action="store_true",
                        help="supply a genuine square instead (must fail)")
    parser.add_argument("--rotations-only", action="store_true",
                        help="weaken the dihedral target (the exclusion must fail)")
    args = parser.parse_args()
    check_dihedral(args.rotations_only)
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
