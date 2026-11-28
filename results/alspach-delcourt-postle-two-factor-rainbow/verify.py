#!/usr/bin/env python3
"""Exact checks of the oriented-cut reduction (not a proof of the asymptotic matching theorem).
All cuts are enumerated on K7 and on a doubled K4 with monochromatic 4-cycles.
No third-party packages and no floating point.
"""
from fractions import Fraction as Q
from itertools import combinations, permutations, product


def orientations(factors):
    """A factor is a list of vertex-disjoint cyclic lists."""
    count = sum(map(len, factors))
    for signs in product((1, -1), repeat=count):
        it = iter(signs)
        perms = []
        for factor in factors:
            pi = {}
            for cyc in factor:
                step = next(it)
                for k, v in enumerate(cyc):
                    assert v not in pi and len(cyc) >= 3
                    pi[v] = cyc[(k + step) % len(cyc)]
            perms.append(pi)
        yield perms


def validate(pis, n):
    V = set(range(n))
    edges = set()
    for pi in pis:
        if set(pi) != V or set(pi.values()) != V:
            raise ValueError("not a spanning permutation")
        for x, y in pi.items():
            e = tuple(sorted((x, y)))
            if x == y or e in edges:
                raise ValueError("loop or repeated undirected edge")
            edges.add(e)


def inverse(pis):
    return [{w: v for v, w in pi.items()} for pi in pis]


def outsets(pis, V):
    return [{pi[x] for pi in pis} for x in V]


def orientation_moments(factors, n):
    """Same-factor wedges contribute zero; different-factor wedges contribute 1/4."""
    V = range(n)
    total = dict.fromkeys(combinations(V, 2), 0)
    rev_total = total.copy()
    col = {}
    for i, factor in enumerate(factors):
        for cyc in factor:
            for j, x in enumerate(cyc):
                y = cyc[j - 1]
                col[x, y] = col[y, x] = i
    samples = 0
    for pis in orientations(factors):
        validate(pis, n)
        out, inc = outsets(pis, V), outsets(inverse(pis), V)
        for x, y in total:
            total[x, y] += len(out[x] & out[y])
            rev_total[x, y] += len(inc[x] & inc[y])
        samples += 1
    for x, y in total:
        diff = sum((x, w) in col and (y, w) in col and col[x, w] != col[y, w] for w in V)
        assert 4 * total[x, y] == 4 * rev_total[x, y] == samples * diff
    return samples, total


def cut_test(factors, n):
    V = set(range(n))
    d = len(factors)
    I = range(d)
    pis = next(orientations(factors))
    validate(pis, n)
    inv = inverse(pis)
    out, inc = outsets(pis, range(n)), outsets(inv, range(n))
    pairs_v, pairs_i = list(combinations(sorted(V), 2)), list(combinations(I, 2))
    a, b = Q(d, n), 1 - Q(d, n)

    def expected():
        yield from (n * a * b for _ in I)
        for _ in sorted(V):
            yield d * b
            yield d * a
        for _ in pairs_i:
            yield n * a * b * b
            yield n * b * a * a
        for x, y in pairs_v:
            yield d * b * b
            yield d * a * a
            yield b * len(out[x] & out[y])
            yield a * len(inc[x] & inc[y])

    means = list(expected())
    sums = [0] * len(means)
    hits = 0
    nonrainbow_assignments = 0
    complete = []
    for tails in product(range(n), repeat=d):
        heads = tuple(pi[x] for pi, x in zip(pis, tails))
        if len(set(tails + heads)) == 2 * d:
            complete.append(tails)
    assert complete
    for mask in range(1 << n):
        X = {x for x in V if (mask >> x) & 1}
        Y = V - X
        e = [(i, x, pis[i][x]) for i in I for x in X if pis[i][x] in Y]
        # Build all shadows from the actual triples, rather than assuming linearity.
        for j, k in combinations(range(3), 2):
            assert len({(row[j], row[k]) for row in e}) == len(e)
        T = [{x for j, x, y in e if j == i} for i in I]
        H = [{y for j, x, y in e if j == i} for i in I]
        F = [{i for i in I if pis[i][v] in Y} for v in range(n)]
        R = [{i for i in I if inv[i][v] in X} for v in range(n)]
        measures = [len(T[i]) for i in I]
        assert all(len(T[i]) == len(H[i]) for i in I)
        for v in sorted(V):
            measures.extend((len(F[v]), len(R[v])))
            if v in X:
                assert F[v] == {i for i, x, y in e if x == v}
            else:
                assert R[v] == {i for i, x, y in e if y == v}
        for i, j in pairs_i:
            measures.extend((len(T[i] & T[j]), len(H[i] & H[j])))
        for x, y in pairs_v:
            measures.extend((len(F[x] & F[y]), len(R[x] & R[y]),
                             len(Y & out[x] & out[y]), len(X & inc[x] & inc[y])))
        assert len(measures) == len(sums)
        weight = d ** len(X) * (n - d) ** len(Y)
        for k, value in enumerate(measures):
            sums[k] += weight * value
        if len(X) == d:
            expected_tails = {t for t in complete if set(t) == X
                              and all(pis[i][t[i]] in Y for i in I)}
            accepted = set()
            labels = {(i, x): y for i, x, y in e}
            for tails in permutations(X):
                if all((i, tails[i]) in labels for i in I):
                    heads = {labels[i, tails[i]] for i in I}
                    if len(heads) == d:
                        accepted.add(tails)
                    else:
                        nonrainbow_assignments += 1
            assert accepted == expected_tails
            hits += len(accepted)
    assert all(Q(x, n ** n) == mu for x, mu in zip(sums, means))
    assert hits == len(complete) and hits > 0
    return hits, nonrainbow_assignments


def main():
    cyclic = [[[(k * step) % 7 for k in range(7)]] for step in (1, 2, 3)]
    twins = []
    for i in (1, 2, 3):
        twins.append([[2*x, 2*(x ^ i), 2*x+1, 2*(x ^ i)+1]
                      for x in range(4) if x < (x ^ i)])
    for factors, n in ((cyclic, 7), (twins, 8)):
        k, counts = orientation_moments(factors, n)
        h, rejected = cut_test(factors, n)
        # Omitting the distinct-head check would accept spurious matchings.
        assert rejected > 0
        if n == 8:
            assert counts[0, 1] == 0  # twin codegree is zero for every orientation
        print(f"n={n}: {k} orientations, {2**n} cuts on one orientation; "
              f"{h} original matchings transferred exactly, "
              f"{rejected} non-rainbow assignments rejected")
    pis = next(orientations(cyclic))
    try:
        validate([pis[0], pis[0], pis[2]], 7)
    except ValueError as exc:
        assert str(exc) == "loop or repeated undirected edge"
    else:
        raise AssertionError("duplicate-factor mutation passed")
    print("All exact shadow moments, transfer checks and negative controls passed.")


if __name__ == "__main__":
    main()
