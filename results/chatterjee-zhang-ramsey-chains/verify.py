#!/usr/bin/env python3
"""Construct and check full Ramsey chains with one prescribed linear-forest link.

No dependencies. With no arguments test each linear-forest type on 3..22
vertices. With arguments n l1 ... lc print the chain for paths of the given
edge lengths laid out consecutively on vertices 0,...,n-1.
"""

from itertools import combinations, pairwise


def edge(u, v):
    return (u, v) if u < v else (v, u)


def paths(edges):
    """Recover ordered vertex lists of the nontrivial components, or reject."""
    adj = {}
    for u, v in edges:
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    if any(len(ns) > 2 for ns in adj.values()):
        raise ValueError("branch")
    seen, out = set(), []
    for u in sorted(adj):
        if len(adj[u]) != 1 or u in seen:
            continue
        run, prev, cur = [], None, u
        while cur is not None:
            run.append(cur)
            seen.add(cur)
            ns = [v for v in adj[cur] if v != prev]
            prev, cur = cur, next(iter(ns), None)
        out.append(run)
    if len(seen) != len(adj):
        raise ValueError("cycle")
    return sorted(out, key=lambda r: (len(r), r))


def large_blocks(lengths, holes):
    """Single-run blocks and paired odd blocks, with any zero gap last."""
    gaps = [1] * len(lengths)
    if holes == len(gaps) - 1:
        gaps[-1] = 0
    else:
        extra = holes - len(gaps)
        for j, l in enumerate(lengths):
            add = min(extra, l - 1)
            gaps[j] += add
            extra -= add
        assert extra == 0
    blocks = list(zip(lengths, gaps))
    groups = [[x] for x in blocks if sum(x) % 2 == 0]
    odd = [x for x in blocks if sum(x) % 2]
    special = next((x for x in odd if x[1] != 1), odd[0])
    odd.remove(special)
    groups.append([special])
    assert len(odd) % 2 == 0 and all(l % 2 == 0 and g == 1 for l, g in odd)
    groups.extend(odd[i:i+2] for i in range(0, len(odd), 2))
    return sorted(groups, key=lambda group: group[-1][1] == 0)


def cut_order(L, lengths):
    """First i positions in this order give the small cut S_i."""
    k, t = L // 2, sum(lengths)
    middle, first = "", ""    # A/B word; mandatory initial subset of A marked 1
    if t <= k:
        for j, l in enumerate(lengths):
            a = l + (k - t if j == 0 else 0)
            b = a + (j == 0)
            middle += "B" * b + "A" * a
            first += "0" * b + "1" * l + "0" * (a - l)
    else:
        for group in large_blocks(lengths, L - t):
            h = sum(l + g for l, g in group)
            first += "".join("0" * l + "1" * g for l, g in group)
            if len(group) == 1:
                middle += "B" * ((h + 1) // 2) + "A" * (h // 2)
            else:
                l = group[0][0]
                middle += "BA" * (l // 2) + "AB" + "BA" * ((h - l - 2) // 2)
    assert len(first) == len(middle) == L and middle.count("A") == k
    assert all(a == "A" for a, bit in zip(middle, first) if bit == "1")
    return [j for bit in "10" for j in range(L) if middle[j] == "A" and first[j] == bit]


def construct(n, red):
    """Red is a set of ordered pairs u<v of labels from range(n)."""
    if not red:  # vacuously monochromatic whatever the chosen forest link
        return construct(n, {(0, 1)})
    target_paths = paths(red)
    m = n // 2
    odd = n % 2
    L = 2 * m - 1 + 2 * odd
    order = cut_order(L, [len(p) - 1 for p in target_paths])
    chain = [set() for _ in range(n)]
    for x in range(m):
        vs = [x]
        for j in range(1, m):
            vs.extend(((x - j) % (2*m), (x + j) % (2*m)))
        vs.append(x + m)
        if odd:
            vs = [2*m] + vs + [2*m]
        es = [edge(u, v) for u, v in pairwise(vs)]
        i = x + odd
        chain[i] = {es[j] for j in order[:i]}
        chain[L-i] = set(es) - chain[i]

    # Send the distinguished copy onto the *given* edges, not just its type.
    source_paths = paths(chain[len(red)])
    assert list(map(len, source_paths)) == list(map(len, target_paths))
    perm = {u: v for p, q in zip(source_paths, target_paths) for u, v in zip(p, q)}
    unused = set(range(n))
    perm.update(zip(sorted(unused - perm.keys()), sorted(unused - set(perm.values()))))
    return [{edge(perm[u], perm[v]) for u, v in part} for part in chain[1:]]


def embeds_by_deletion(small, big):
    """All possible path-length multisets on deleting one edge."""
    for j, l in enumerate(big):
        others = big[:j] + big[j+1:]
        for left in range((l - 1) // 2 + 1):
            split = [r for r in (left, l - left - 1) if r]
            if sorted(others + split) == small:
                return True
    return False


def check(n, red, chain):
    """Use only the graph definition; no dependence on factors or cut_order."""
    if len(chain) != n - 1:
        raise ValueError("length")
    covered, prev = set(), []
    for i, es in enumerate(chain, 1):
        if len(es) != i or covered & es:
            raise ValueError("size or overlap")
        covered.update(es)
        if (i == len(red) and es != red) or (i != len(red) and es & red):
            raise ValueError("prescribed link")
        lengths = sorted(len(p) - 1 for p in paths(es))
        if not embeds_by_deletion(prev, lengths):
            raise ValueError("no embedding at size " + str(i))
        prev = lengths
    if covered != set(combinations(range(n), 2)) or prev != [n - 1]:
        raise ValueError("not a Hamilton-path-ending decomposition of K_n")


def labelled_forest(n, lengths):
    if n < 3 or any(l < 1 for l in lengths) or sum(lengths) + len(lengths) > n:
        raise ValueError("need n >= 3 and disjoint nonempty paths fitting on n vertices")
    start, red = 0, set()
    for l in lengths:
        red.update((j, j+1) for j in range(start, start+l))
        start += l + 1
    return red


def partitions(n, least=1):
    if n == 0:
        yield ()
    for first in range(least, n + 1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def test():
    count = 0
    for n in range(3, 23):
        for orders in partitions(n):
            red = labelled_forest(n, [s-1 for s in orders if s > 1])
            check(n, red, construct(n, red))
            count += 1
    print(f"PASS: {count} forest types (including empty), 3 <= n <= 22.")
    # Swap a red edge and a blue one. Sizes, disjointness and coverage survive.
    red = labelled_forest(9, [2, 2, 2])
    bad = construct(9, red)
    x, y = bad[0].pop(), bad[5].pop()
    bad[0].add(y)
    bad[5].add(x)
    try:
        check(9, red, bad)
    except ValueError as exc:
        if str(exc) != "prescribed link":
            raise
    else:
        raise AssertionError("accepted a corrupted witness")
    print("PASS: the checker rejected the colour-breaking edge swap.")


if __name__ == "__main__":
    import sys
    if len(sys.argv) == 1:
        test()
    else:
        n, *lengths = map(int, sys.argv[1:])
        red = labelled_forest(n, lengths)
        chain = construct(n, red)
        check(n, red, chain)
        for i, es in enumerate(chain, 1):
            print(i, "red" if es == red else "blue", sorted(es))
