#!/usr/bin/env python3
"""Exact finite lemma for the A6 components; tests of the commutator lifting boundary.

No libraries beyond the standard library. Group element 0 is always the identity
in a Cayley table. Permutations compose as functions (rightmost applied first).
"""
from collections import Counter
from itertools import permutations, product
from math import lcm


def compose(a, b):
    return tuple(a[i] for i in b)


def even(g):
    return sum(a > b for i, a in enumerate(g) for b in g[i+1:]) % 2 == 0


def two_power(n):
    return n > 0 and (n & (n - 1)) == 0


def orbit(f, v):
    out = [v]
    w = f[v]
    while w != v:
        out.append(w)
        w = f[w]
    return out


def perm_order(f):
    seen, n = set(), 1
    for i in range(len(f)):
        if i not in seen:
            cycle = orbit(f, i)
            seen.update(cycle)
            n = lcm(n, len(cycle))
    return n


def table(elements, multiply):
    index = {a: i for i, a in enumerate(elements)}
    assert len(index) == len(elements)
    return [[index[multiply(a, b)] for b in elements] for a in elements]


def orders(m):
    out = []
    for i in range(len(m)):
        n, a = 1, i
        while a:
            a = m[a][i]
            n += 1
            assert n <= len(m)
        out.append(n)
    return out


def tree(m, gens):
    """Closure and spanning tree on positive words; sufficient in a finite group."""
    seen, queue, edges = {0}, [0], []
    for u in queue:
        for j, g in enumerate(gens):
            v = m[u][g]
            if v not in seen:
                seen.add(v)
                queue.append(v)
                edges.append((u, j, v))
    return seen, edges


def a6_lemma():
    G = [g for g in permutations(range(6)) if even(g)]
    assert len(G) == 360 and G[0] == tuple(range(6))
    m = table(G, compose)
    o = orders(m)
    pairs = [(i, j) for i in range(360) if o[i] == 2
             for j in range(360) if o[j] == 4 and o[m[i][j]] == 5]
    a, b = next(pair for pair in pairs if len(tree(m, pair)[0]) == 360)
    edges = tree(m, (a, b))[1]
    odd = [i for i in range(1, 360) if o[i] % 2 == 1]
    twos = [i for i, n in enumerate(o) if two_power(n)]
    rows = Counter()
    aut = 0
    for c, d in pairs:
        image = (c, d)
        f = [0] * 360
        for u, j, v in edges:
            f[v] = m[f[u]][image[j]]
        if len(set(f)) != 360:
            continue
        if not all(f[m[u][v]] == m[f[u]][w]
                   for u in range(360) for v, w in zip((a, b), image)):
            continue
        aut += 1
        n = perm_order(f)
        if not two_power(n):
            continue
        # A cyclically permuted orbit commutes pairwise iff v commutes
        # with all its images. A commuting orbit of odd elements generates
        # an abelian odd-order subgroup, and any element of one is eligible.
        found = any(all(m[v][w] == m[w][v] for w in orbit(f, v)) for v in odd)
        if not found:
            D = [v for v in twos if all(two_power(o[m[v][w]]) for w in orbit(f, v))]
            subgroup, _ = tree(m, D)
            assert len(subgroup) == 8
        rows[n, found] += 1
    assert aut == 1440
    assert rows == {(1, True): 1, (2, True): 111, (4, True): 360,
                    (8, True): 180, (8, False): 180}
    # Negative control: without the orbit-product test, the 2-elements
    # need not stay in a 2-group.
    assert len(tree(m, twos)[0]) == 360
    print("A6: 1440 automorphisms, 832 of 2-power order; all 180 residual cases give order 8.")


def mm(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return ((a*e+b*g) % 3, (a*f+b*h) % 3, (c*e+d*g) % 3, (c*f+d*h) % 3)


def commutator(m):
    inv = [row.index(0) for row in m]
    return lambda x, g: m[m[m[inv[x]][inv[g]]][x]][g]


def twisted_lifts():
    # SL2(3) acts on the Heisenberg group (v,z), with central correction
    # (1/2)det(v,w). Add twice the carry cocycle from SL2(3)/Q8 = C3.
    I = (1, 0, 0, 1)
    L = [I] + [A for A in product(range(3), repeat=4)
               if A != I and (A[0]*A[3] - A[1]*A[2]) % 3 == 1]
    mL = table(L, mm)
    oL = orders(mL)
    Q = [i for i, n in enumerate(oL) if n in (1, 2, 4)]
    s = L.index((1, 1, 0, 1))
    eps = {mL[v][power]: i for i, power in enumerate((0, s, mL[s][s])) for v in Q}
    assert len(L) == 24 and len(Q) == 8 and len(eps) == 24
    assert all(eps[mL[i][j]] == (eps[i]+eps[j]) % 3 for i in range(24) for j in range(24))
    # Distinct subgroups of order three in L guarantee O_3(L)=1.
    assert len({frozenset(tree(mL, (i,))[0]) for i, n in enumerate(oL) if n == 3}) > 1

    el = list(product(range(3), range(3), range(3), range(24)))

    def times(v, w):
        a, b, z, i = v
        c, d, t, j = w
        k, l, r, s = L[i]
        e, f = (k*c+l*d) % 3, (r*c+s*d) % 3
        carry = (eps[i] + eps[j]) // 3
        return ((a+e) % 3, (b+f) % 3, (z+t+2*(a*f-b*e)+2*carry) % 3, mL[i][j])

    m = table(el, times)
    o = orders(m)
    comm = commutator(m)
    X = [i for i, v in enumerate(el) if v[3] and o[i] == 3]
    assert len(el) == 648 and len(X) == 144
    for x in X:
        assert any((n := o[comm(x, g)]) != 1 and n % 3 != 0 for g in range(len(el)))

    x = el.index((0, 1, 0, L.index((0, 1, 2, 2))))
    good = el.index((0, 0, 0, L.index((0, 1, 2, 0))))
    bad = el.index((0, 0, 0, L.index((2, 0, 1, 2))))
    fixed_image = el[comm(x, good)][3]
    assert x in X and oL[fixed_image] == 4

    def validate(g):
        w = comm(x, g)
        if el[w][3] != fixed_image or o[w] == 1 or o[w] % 3 == 0:
            raise ValueError("not a nontrivial 3-regular commutator over the prescribed element")

    validate(good)
    assert el[comm(x, bad)][3] == fixed_image and (o[comm(x, good)], o[comm(x, bad)]) == (4, 12)
    try:
        validate(bad)
    except ValueError:
        pass
    else:
        raise AssertionError("mixed-order mutation accepted")
    print("Extraspecial 3-core: all 144 outside elements of order 3 have witnesses;"
          " order-12 mutation over the same order-4 element rejected.")


def prime_order_boundary():
    # The prime-order condition on x in Theorem A cannot be dropped.
    I = (1, 0, 0, 1)
    G = [I] + [A for A in product(range(3), repeat=4)
               if A != I and (A[0]*A[3] - A[1]*A[2]) % 3]
    m = table(G, mm)
    o = orders(m)
    c = commutator(m)
    x = o.index(8)
    assert {o[c(x, g)] for g in range(len(G))} == {1, 4, 6}
    # If x belonged to O_2 all its commutators would be 2-elements, not order 6.
    print("GL2(3) negative control: an element of order 8 has commutator orders 1, 4, 6.")


if __name__ == "__main__":
    twisted_lifts()
    prime_order_boundary()
    a6_lemma()
