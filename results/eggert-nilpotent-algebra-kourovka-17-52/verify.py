#!/usr/bin/env python3
"""Exact regression checks for the characteristic-two proof (no external packages).

Multiplication tables are over F_2. N,I,J are supplied as coordinate
subspaces. We verify N=rad H and J=I^perp over the generic field by
zero products (inclusions) and a matching nonzero minor after specialization.
No test of examples replaces the universal proof in PROOF.md.
"""
import sys


class Invalid(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise Invalid(message)


def bits(a):
    while a:
        t = a & -a
        yield t.bit_length() - 1
        a ^= t


def echelon(rows):
    piv = {}
    for v in rows:
        while v:
            j = v.bit_length() - 1
            if j not in piv:
                piv[j] = v
                break
            v ^= piv[j]
    return tuple(piv.values())


def product(table, a, b):
    ans = 0
    for i in bits(a):
        for j in bits(b):
            ans ^= table[i][j]
    return ans


def chains(lengths):
    # Orthogonal branches x_i, with their terminal powers identified.
    keys = [(i, j) for i, m in enumerate(lengths) for j in range(1, m)]
    soc = len(keys)
    ix = {k: j for j, k in enumerate(keys)}
    table = [[0] * (soc + 1) for _ in range(soc + 1)]
    for a, (i, j) in enumerate(keys):
        for b, (k, h) in enumerate(keys):
            n = j + h
            if i == k and n <= lengths[i]:
                table[a][b] = 1 << (soc if n == lengths[i] else ix[i, n])
    return (table, [soc],
            [v for v, (i, j) in enumerate(keys) if 2*j > lengths[i]] + [soc],
            [v for v, (i, j) in enumerate(keys) if 2*j >= lengths[i]] + [soc],
            soc, sum((n-1)//2 for n in lengths) + int(any(n % 2 == 0 for n in lengths)))


def interval(m, top):
    # Span of t^m,...,t^top in F_2[t]/(t^(top+1)).
    exps = range(m, top + 1)
    table = [[1 << (x+y-m) if x+y <= top else 0 for y in exps] for x in exps]
    return (table, [x-m for x in exps if x+m > top],
            [x-m for x in exps if 2*x > top], [x-m for x in exps if 2*x >= top],
            top-m, sum(2*x <= top for x in exps))


def check(certificate):
    table, N, I, J, top, expected = certificate
    d = len(table)
    e = [1 << j for j in range(d)]
    mask = lambda s: sum(1 << j for j in s)
    for S in (N, I, J):
        require(len(set(S)) == len(S) and all(0 <= j < d for j in S), "bad coordinate subspace")
    nmask, imask = mask(N), mask(I)
    require(set(N) <= set(I) <= set(J), "N,I,J not nested")
    require(all(len(row) == d and all(0 <= z < (1 << d) for z in row) for row in table),
            "bad multiplication table")
    for i in range(d):
        for j in range(d):
            require(table[i][j] == table[j][i], "not commutative")
            for k in range(d):
                require(product(table, table[i][j], e[k]) == product(table, e[i], table[j][k]),
                        "not associative")
    P = tuple(e)
    for _ in range(d):
        P = echelon(product(table, v, u) for v in P for u in e)
        if not P:
            break
    require(not P, "not nilpotent")
    r = len(echelon(table[i][i] for i in range(d)))
    require(r == expected, "wrong Frobenius rank")
    # Zeros here are vector zeros, so the inclusions hold for every functional.
    require(all(not table[i][j] for i in N for j in range(d)), "N not radical")
    require(all(not table[i][j] for i in I for j in J), "J not perpendicular")
    # The functional extracting the specified terminal coordinate witnesses
    # a minor of the required rank; that minor is nonzero generically.
    def gram_rank(rows):
        return len(echelon(sum(((table[i][j] >> top) & 1) << j for j in range(d)) for i in rows))
    require(gram_rank(range(d)) == d-len(N), "bad radical dimension witness")
    require(gram_rank(I) == d-len(J), "bad perpendicular dimension witness")
    require(all(not (table[x][j] & ~imask) for x in range(d) for j in J), "RJ not in I")
    require(all(not table[i][i] for i in I), "I contains nonsquare-zero vector")
    require(all(not (table[j][j] & ~nmask) for j in J), "square of J not in N")
    require(r <= len(I) <= d-r and len(I) == len(N)+d-len(J), "dimension bounds failed")
    return d, r, (len(N), len(I), len(J))


def main():
    # Nonhomogeneous terminal identifications, and a separate multi-socle family.
    for label, c in [('chains(4,5,7,9)', chains([4, 5, 7, 9])),
                     ('interval(3,18)', interval(3, 18)),
                     ('monogenic length 12', interval(1, 12))]:
        d, r, dims = check(c)
        print(f'{label}: dim={d}, square rank={r}, (dim N,I,J)={dims}, excess={d-2*r}')
    bad = chains([4, 5, 7, 9])
    bad[0][1][1] = 0  # erase (x_0^2)^2, but leave x_0*x_0^3 unchanged
    if sys.argv[1:] == ['--corrupt']:
        check(bad)  # deliberately fails
    require(not sys.argv[1:], "usage: verify.py [--corrupt]")
    try:
        check(bad)
    except Invalid as err:
        require(str(err) == 'not associative', "mutation rejected for wrong reason")
        print('negative control: corrupted fourth power rejected (not associative)')
    else:
        raise Invalid("corrupted table passed")
    print('PASS: exact example and generic-dimension certificates')


if __name__ == '__main__':
    main()
