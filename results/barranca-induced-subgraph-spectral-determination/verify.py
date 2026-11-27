#!/usr/bin/env python3
"""Exact cospectral witnesses. Standard Python 3.10+, no downloads.

A graph is a tuple of adjacency bitmasks; a host is a tuple of disjoint
graphs. witness(H) constructs a pair for any nonempty nonexceptional H.
For the generic connected case its size can be exponential in |H|.
"""
from collections import Counter
from functools import cache
from itertools import combinations


def graph(n, edges=()):
    rows = [0] * n
    for i, j in edges:
        assert 0 <= i < n and 0 <= j < n and i != j
        rows[i] |= 1 << j
        rows[j] |= 1 << i
    return tuple(rows)


def compact(n, pairs):
    return graph(n, [(int(t[0]), int(t[1])) for t in pairs.split()])


def edges(G):
    return [(i, j) for i, j in combinations(range(len(G)), 2) if G[i] >> j & 1]


def clique(n):
    return graph(n, combinations(range(n), 2))


def bip(a, b):
    return graph(a+b, ((i, a+j) for i in range(a) for j in range(b)))


def book(d):
    t = d * (d-1) // 2
    return graph(2+t, [(0, 1)] + [(i, j) for i in (0, 1) for j in range(2, 2+t)])


def union(L):
    rows = []
    for G in L:
        k = len(rows)
        rows.extend(r << k for r in G)
    return tuple(rows)


def components(G):
    unused = set(range(len(G)))
    while unused:
        stack = [unused.pop()]
        comp = []
        while stack:
            v = stack.pop()
            comp.append(v)
            more = {u for u in unused if G[u] >> v & 1}
            unused -= more
            stack.extend(more)
        yield graph(len(comp), [(i, j) for i, j in combinations(range(len(comp)), 2)
                                if G[comp[i]] >> comp[j] & 1])


def occurs(H, G):
    """Backtrack induced injections; candidates match every earlier edge and nonedge."""
    m, n = len(H), len(G)
    if m > n:
        return False
    order = sorted(range(m), key=lambda v: -H[v].bit_count())

    def extend(image, free):
        if len(image) == m:
            return True
        v = order[len(image)]
        opts = free
        for w, x in zip(order, image):
            opts &= G[x] if H[v] >> w & 1 else ~G[x]
        while opts:
            b = opts & -opts
            if extend(image + [b.bit_length()-1], free ^ b):
                return True
            opts ^= b
        return False

    return extend([], (1 << n)-1)


@cache
def charpoly(G):
    """High coefficient first, via Newton identities and integer walk counts."""
    n = len(G)
    nbr = [[j for j in range(n) if row >> j & 1] for row in G]
    W = [[int(i == j) for j in range(n)] for i in range(n)]
    c, tr = [1], [n]
    for k in range(1, n+1):
        W = [[sum(W[u][j] for u in nbr[i]) for j in range(n)] for i in range(n)]
        tr.append(sum(W[i][i] for i in range(n)))
        a = -sum(c[k-i]*tr[i] for i in range(1, k+1))
        q, r = divmod(a, k)
        assert r == 0
        c.append(q)
    return tuple(c)


def mul(f, g):
    h = [0] * (len(f)+len(g)-1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                h[i+j] += a*b
    return tuple(h)


def host_poly(L):
    # Compute x^k only once, including zeros inside blocks.
    h, z = (1,), 0
    for G in L:
        f = charpoly(G)
        k = len(f)
        while f[k-1] == 0:
            k -= 1
        z += len(f)-k
        h = mul(h, f[:k])
    return h + (0,) * z


def eigen_poly(ev):
    h = (1,)
    for a in ev:
        h = mul(h, (1, -a))
    return h


def hull(H):
    n = 1 << len(H)
    s = [(1 << i) ^ (1 << j) for i, j in edges(H)]
    X = tuple(sum(1 << (x ^ k) for k in s) for x in range(n))
    eig = [sum(1 if (u & k).bit_count() % 2 == 0 else -1 for k in s) for u in range(n)]
    return X, eig


def integral_trade(X, ev):
    L, R = [X], []
    for a in ev:
        if a < 0:
            L += [clique(1-a)] + [clique(1)] * (a*a-1)
            R += [bip(1, a*a)]
        else:
            R += [clique(a+1)]
    return tuple(L), tuple(R)


def pad_equal(L, R):
    diff = sum(map(len, L)) - sum(map(len, R))
    return L + (clique(1),) * max(0, -diff), R + (clique(1),) * max(0, diff)


K1, K2, P3, K3 = clique(1), clique(2), bip(1, 2), clique(3)
TYPES = dict(i=K1, e=K2, p=P3, t=K3)
# key: i=K1, e=K2, p=P3, t=K3. Edges ij on 0,...,n-1.
SEEDS = {
    'ei': (5, '03 04 13 14', '04 14 24 34'),
    'ip': (5, '03 04 13 14', '04 14 24 34'),
    'ep': (6, '04 15 25 35', '03 05 14 15'),
    'ee': (6, '03 14 15 24 25', '04 14 25 35 45'),
    'et': (6, '03 14 15 24 25 45', '03 05 14 15 35 45'),
    'it': (6, '03 04 05 13 24 35 45', '03 05 14 15 25 35 45'),
    'pp': (7, '04 06 14 16 25 26 35 46', '04 06 15 16 25 35 46 56'),
    'iii': (7, '03 04 05 06 14 15 16 24 25 26 34 35 36 45 46 56',
            '02 03 04 05 06 12 13 14 15 16 24 25 26 45 46 56'),
    'pt': (8, '05 07 16 26 37 47 57', '05 07 15 26 27 36 57'),
    'tt': (8, '04 05 16 17 26 27 36 37 45 67', '03 04 07 15 16 25 26 34 37 47'),
}


def small_type(C):
    return next((k for k, T in TYPES.items() if len(C) == len(T) and occurs(T, C)), None)


def connected_witness(C):
    n = len(C)
    if len(edges(C)) == n*(n-1)//2:
        assert n >= 4
        d = n-1
        return pad_equal((clique(n), bip(d-1, d-1)), (clique(d), book(d)))
    if n >= 4 and max(r.bit_count() for r in C) == n-1 and len(edges(C)) == n-1:
        m = n-1
        return pad_equal((bip(1, 2*(m-1)),), (bip(2, m-1),))
    return integral_trade(*hull(C))


def witness(H):
    parts = list(components(H))
    names = [small_type(C) for C in parts]
    if None in names:
        idx = names.index(None)
        L, R = connected_witness(parts.pop(idx))
    else:
        have = Counter(names)
        seed = next((s for s in SEEDS if not (Counter(s)-have)), None)
        if seed is None:
            raise ValueError("null or one of the five exceptional patterns")
        n, g, b = SEEDS[seed]
        L, R = (compact(n, g),), (compact(n, b),)
        for k in seed:
            idx = names.index(k)
            parts.pop(idx)
            names.pop(idx)
    return L + tuple(parts), R + tuple(parts)


def check(H, L, R):
    assert host_poly(L) == host_poly(R), "characteristic polynomial differs"
    if len(list(components(H))) == 1:
        inside = lambda host: any(occurs(H, C) for C in host)
    else:
        inside = lambda host: occurs(H, union(host))
    assert inside(L) and not inside(R), "wrong induced-subgraph status"


def main():
    for s in SEEDS:
        H = union(TYPES[k] for k in s)
        check(H, *witness(H))
    print("10 disconnected seeds: exact charpolys and induced injections OK")
    for n in range(4, 9):
        for H in [clique(n), bip(1, n-1)]:
            check(H, *witness(H))
    for H in [bip(2, 2), compact(4, '01 12 23'), compact(4, '01 12 20 23'),
              compact(5, '01 12 23 34 40')]:
        X, ev = hull(H)
        assert eigen_poly(ev) == charpoly(X)
        check(H, *witness(H))
    for s, extra in [('ep', clique(4)), ('ii'+'i', bip(1, 2)), ('tt', bip(2, 2))]:
        H = union(TYPES[k] for k in s)
        n, a, b = SEEDS[s]
        check(union([H, extra]), (compact(n, a), extra), (compact(n, b), extra))
    print("clique, star, cubelike, and disjoint-extension constructions OK")

    n, a, b = SEEDS['ep']
    L, R = compact(n, a), compact(n, b)
    toggle = list(R)
    toggle[0] ^= 1 << 1
    toggle[1] ^= 1
    for good, bad, expected in [(L, tuple(toggle), "characteristic polynomial differs"),
                                (R, L, "wrong induced-subgraph status")]:
        try:
            check(union([P3, K2]), (good,), (bad,))
        except AssertionError as e:
            assert str(e) == expected
        else:
            raise AssertionError("corrupt witness accepted")
    print("mutation controls: changed edge and reversed cospectral witnesses rejected")


if __name__ == '__main__':
    main()
