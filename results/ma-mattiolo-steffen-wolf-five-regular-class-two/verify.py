#!/usr/bin/env python3
"""Finite voltage checks for PROOF.md. Python standard library, exact integers."""
from itertools import combinations, product
from pathlib import Path

# Oriented outer rim, inner rim, spokes, in that order.
P = ([(i, (i+1) % 5) for i in range(5)]
     + [(5+i, 5+(i+2) % 5) for i in range(5)]
     + [(i, 5+i) for i in range(5)])
CHORD = [4, 9, 11, 12, 13, 14]
TREE = [e for e in range(15) if e not in CHORD]
ZERO = (0,)*6


def check(ok, msg):
    if not ok:
        raise ValueError(msg)


def col_ok(edges, colors, k):
    if len(colors) != len(edges):
        return False
    seen = set()
    for (u, v), c in zip(edges, colors):
        if not (0 <= c < k) or (u, c) in seen or (v, c) in seen or u == v:
            return False
        seen.update(((u, c), (v, c)))
    return True


def color3(edges):
    """Complete edge-color search, with color symmetry fixed at vertex zero."""
    n = 1 + max(max(e) for e in edges)
    mask = [0]*n
    colors = [-1]*len(edges)
    rest = []
    count = 0
    for i, (u, v) in enumerate(edges):
        if 0 in (u, v):
            colors[i] = count
            mask[u] |= 1 << count
            mask[v] |= 1 << count
            count += 1
        else:
            rest.append(i)

    def dfs(h):
        if h == len(rest):
            return True
        m = 4
        for j in range(h, len(rest)):
            u, v = edges[rest[j]]
            bits = 7 & ~(mask[u] | mask[v])
            if not bits:
                return False
            size = bits.bit_count()
            if size < m:
                best, choices, m = j, bits, size
                if size == 1:
                    break
        rest[h], rest[best] = rest[best], rest[h]
        i = rest[h]
        u, v = edges[i]
        while choices:
            b = choices & -choices
            choices ^= b
            colors[i] = b.bit_length()-1
            mask[u] ^= b
            mask[v] ^= b
            if dfs(h+1):
                return True
            mask[u] ^= b
            mask[v] ^= b
        rest[h], rest[best] = rest[best], rest[h]
        return False

    if dfs(0):
        check(col_ok(edges, colors, 3), "incorrect purported cubic coloring")
        return colors
    return None


def lift(lists, p):
    return [(p*u+j, p*v+(j+a) % p)
            for (u, v), ls in zip(P, lists) for a in ls for j in range(p)]


def rep(x):
    s = [0]*15
    for e, a in zip(CHORD, x):
        s[e] = a
    return s


def potentials(edges, s, p):
    """Tree/path integration. For a connected cyclic subgraph, return None on conflict."""
    pot = {P[edges[0]][0]: 0}
    for _ in range(10):
        for e in edges:
            u, v = P[e]
            if u in pot and v in pot and (pot[u]+s[e]-pot[v]) % p:
                return None
            if u in pot:
                pot[v] = (pot[u]+s[e]) % p
            elif v in pot:
                pot[u] = (pot[v]-s[e]) % p
    check(len(pot) == len({v for e in edges for v in P[e]}), "not connected")
    return pot


def normal(s, p):
    h = potentials(TREE, s, p)
    return tuple((s[e]+h[P[e][0]]-h[P[e][1]]) % p for e in CHORD)


def add(x, y, p, a=1):
    return tuple((u+a*v) % p for u, v in zip(x, y))


def edge_maps():
    """All vertex permutations preserving adjacency; give signed images of oriented edges."""
    adj = {frozenset(uv): i for i, uv in enumerate(P)}
    def rec(part):
        i = len(part)
        if i == 10:
            ans = []
            for u, v in P:
                u, v = part[u], part[v]
                j = adj[frozenset((u, v))]
                ans.append((j, 1 if P[j] == (u, v) else -1))
            yield tuple(ans)
            return
        for j in range(10):
            if j not in part and all((frozenset((i, k)) in adj) ==
                                     (frozenset((j, z)) in adj)
                                     for k, z in enumerate(part)):
                yield from rec(part + (j,))
    return list(rec(()))


AUT = edge_maps()
CORE = [[f for f, uv in enumerate(P) if set(uv).isdisjoint(P[e])] for e in range(15)]


def profile(p):
    D = [normal([int(j == i) for j in range(15)], p) for i in range(15)]
    mats = [list(zip(*[tuple(sign*z for z in D[j]) for j, sign in
                       (a[e] for e in CHORD)])) for a in AUT]

    def orbit(x):
        for mat in mats:
            y = [sum(v*w for v, w in zip(x, col)) % p for col in mat]
            for scalar in range(1, p):
                yield tuple(scalar*v % p for v in y)

    # Classes represented by a voltage supported on a single star.
    # On switching, one incident edge may be made zero.
    hard = set()
    for v in range(10):
        i, j, _ = [e for e, uv in enumerate(P) if v in uv]
        for a, b in product(range(p), repeat=2):
            hard.add(add(add(ZERO, D[i], p, a), D[j], p, b))
    stars = len(hard)
    covered = hard.copy()
    orbits = 0
    for digits in product(range(p), repeat=6):
        x = digits[::-1]
        if x in covered:
            continue
        ox = set(orbit(x))
        check(x in ox and not (ox & covered), "cubic orbit overlap")
        covered.update(ox)
        if color3(lift([[a] for a in rep(x)], p)) is None:
            hard.update(ox)
        orbits += 1
    check(len(covered) == p**6, "incomplete cubic profile")
    print(f"p={p}: {p**6} signatures; {stars} star classes; {orbits} nonstar orbits;"
          f" {len(hard)} noncolorable signatures", flush=True)
    return hard, D


def rectangles(p, hard, D):
    for e, d in enumerate(D):
        # Overall nonzero scaling normalizes the change on e to 1.
        line = {x for x in hard if add(x, d, p) in hard}
        for x in line:
            check(potentials(CORE[e], rep(x), p) is not None, "bad pair has nonflat core")
        for f, t in enumerate(D):
            if not set(P[f]).isdisjoint(P[e]):
                continue
            for a in range(1, p):
                check(all(add(x, t, p, a) not in line for x in line), "bad rectangle")


M0 = [10, 11, 12, 13, 14]
PM = [set(m) for m in combinations(range(15), 5) if len({v for e in m for v in P[e]}) == 10]
M1 = sorted(next(m for m in PM if 10 in m and m != set(M0)))


def key_of(lists):
    means = [sum(ds)*pow(len(ds), -1, 5) % 5 for ds in lists]
    return (normal(means, 5),
            tuple(tuple(sorted((d-h) % 5 for d in ds)) for ds, h in zip(lists, means)))


def quintic_rows(mult):
    """Check every supplied color word. Register only explicitly isomorphic forms."""
    group = [a for a in AUT if all(mult[i] == mult[j] for i, (j, _) in enumerate(a))]
    check(len(AUT) == 15*len(group), "distinct matching orbit")
    table = set()
    nrows = 0
    data = Path(__file__).with_name("data") / "five-colors.txt"
    for row in data.read_text().splitlines():
        key, word = row.split()
        nrows += 1
        s = rep(tuple(map(int, key[:6])))
        offset = 6
        L = []
        for e, n in enumerate(mult):
            ds = [0] if n == 1 else list(map(int, key[offset:offset+n]))
            offset += n if n > 1 else 0
            check(n == len(ds) and max(ds) < 5 and sum(ds) % 5 == 0, "bad deviations")
            L.append([(a+s[e]) % 5 for a in ds])
        check(offset == len(key), "malformed key")
        check(col_ok(lift(L, 5), [int(c)-1 for c in word], 5), "bad quintic certificate")
        for action in group:
            renamed = [None]*15
            for e, (j, sign) in enumerate(action):
                renamed[j] = [sign*d for d in L[e]]
            for a in range(1, 5):
                table.add(key_of([[a*v % 5 for v in ds] for ds in renamed]))
    print(f"p=5: {nrows} checked quintic certificates")
    return table


def small_keys(mult):
    # All assignments which can be switched to at most two nonzero copies.
    copies = [(e, j) for e, n in enumerate(mult) for j in range(n)]
    small = set()
    for (e, j), (f, k) in combinations(copies, 2):
        for a, b in product(range(5), repeat=2):
            ls = [[0]*m for m in mult]
            ls[e][j], ls[f][k] = a, b
            small.add(key_of(ls))
    return small


def check_five(hard, D, r):
    mult = [1 + int(e in M0) + int(e in (M0 if r else M1)) for e in range(15)]
    table = set() if r else quintic_rows(mult) | small_keys(mult)
    t = 10
    # For repeated M the stabilizer of M acts transitively on its five edges.
    if r:
        ims = {g[t][0] for g in AUT if {g[i][0] for i in M0} == set(M0)}
        check(ims == set(M0), "repeated matching not transitive")
    others = [i for i in range(15) if i != t and mult[i] > 1]
    tested = 0
    offsets = [[0] for _ in range(15)]
    for x in hard:
        s = rep(x)

        def visit(j, xs, other_split):
            nonlocal tested
            if not all(z in hard for z in xs):
                return  # at least one cubic choice supplies a coloring
            if j == len(others):
                if not r and not other_split and potentials(CORE[t], s, 5) is not None:
                    return  # not one of our sufficient conditions
                key = key_of([[(s[e]+d) % 5 for d in ds] for e, ds in enumerate(offsets)])
                check(key in table, "missing quintic coloring or small-support form")
                tested += 1
                return
            e = others[j]
            for a in range(5):
                for b in (range(a, 5) if r else [0]):
                    if r and a == b == 0:
                        continue  # every triple is required to split in this case
                    offsets[e] = [0, a, b] if r else [0, a]
                    nxt = {add(y, D[e], 5, v) for y in xs for v in offsets[e]}
                    visit(j+1, nxt, other_split or a != 0 or b != 0)

        for b in range(5):
            offsets[t] = [0, 1, b]
            visit(0, {add(x, D[t], 5, v) for v in offsets[t]}, False)
    print(f"p=5 surviving normalized descriptions: {tested}")
    return tested


def carving():
    """A finite table proving the induction for all carving trees of width 5..7."""
    from functools import lru_cache
    from itertools import permutations

    templates = {
        5: [
            "01234"],
        6: [
            "012012 012021 012102 012120 012201 012210",
            "010212 010221 011202 011220 012012 012021 012102 012120"],
        7: [
            "0120034 0120304 0120340 0121134 0121314 0121341 0122234 0122324 0122342",
            "0120304 0120340 0121314 0121341 0122324 0122342 0123004 0123040 0123114 0123141 0123224 0123242",
            "0010234 0012304 0012340 0100234 0102304 0102340 0120034 0123114 0123141 0123224 0123242 0123334 0123343",
            "0010234 0012034 0012304 0012340 0100234 0102034 0102304 0102340 0120304 0120340 0123004 0123040"],
    }

    def canon(word):
        names = {}
        return tuple(names.setdefault(v, len(names)) for v in word)

    def patterns(n, w=()):
        if len(w) == n:
            if all(w.count(c) % 2 == n % 2 for c in range(5)):
                yield w
        else:
            for c in range(min(5, 2+max(w, default=-1))):
                yield from patterns(n, w+(c,))

    W = {n: list(patterns(n)) for n in templates}
    ids = {n: {w:i for i,w in enumerate(ws)} for n,ws in W.items()}
    masks = {n: [sum(1 << ids[n][tuple(map(int, w))] for w in t.split()) for t in ts]
             for n,ts in templates.items()}

    @lru_cache(None)
    def rename(n, s, p):
        return sum(1 << ids[n][canon(w[i] for i in p)]
                   for b,w in enumerate(W[n]) if (s >> b) & 1)

    @lru_cache(None)
    def orbit(n, s):
        return {rename(n, s, u) for u in permutations(range(n))}

    targets = {n: set().union(*(orbit(n, s) for s in ss)) for n,ss in masks.items()}

    @lru_cache(None)
    def orientations(n, s, m, left):
        # No need to permute exposed ports: target templates allow all renamings.
        # Fix the order of the joining ports at left, try each bijection at right.
        ans = set()
        for I in combinations(range(n), m):
            rem = tuple(v for v in range(n) if v not in I)
            for J in ([I] if left else permutations(I)):
                ans.add(rename(n, s, rem+J if left else J+rem))
        return ans

    checks = 0
    for i, j, k in product(templates, repeat=3):
        if j < i or (i+j-k) % 2:
            continue
        m = (i+j-k)//2
        # For each parent word enumerate every assignment to the glued edges.
        pairs = [set() for _ in W[k]]
        for h, w in enumerate(W[k]):
            for mid in product(range(5), repeat=m):
                a = ids[i].get(canon(w[:i-m]+mid))
                b = ids[j].get(canon(mid+w[i-m:]))
                if a is not None and b is not None:
                    pairs[h].add((a,b))
        for A, B in product(masks[i], masks[j]):
            for a in orientations(i, A, m, True):
                compatible = [sum(1 << y for y in {v for u,v in ps if (a >> u) & 1})
                              for ps in pairs]
                for b in orientations(j, B, m, False):
                    out = sum(1 << z for z, r in enumerate(compatible) if r & b)
                    check(any((out & t) == t for t in targets[k]), "failed carving join")
                    checks += 1
    for n in templates:
        check(min((a & b).bit_count() for a in masks[n] for b in targets[n]) == {5:1,6:2,7:1}[n],
              "failed carving root")
    check(checks == 20979, "carving table regression")
    print(f"carving widths 5..7: {checks} oriented template joins, every root compatible")


def main():
    check(len(AUT) == 120 and len(PM) == 6, "incorrect Petersen data")
    check(all(len(a & b) == 1 for a, b in combinations(PM, 2)), "matching intersection")
    check(len({frozenset(g[i][0] for i in M0) for g in AUT}) == 6, "matching orbit")
    for mask in range(1, 1023):
        cut = sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in P)
        check(cut >= (3 if mask.bit_count() in (1, 9) else 4), "nontrivial small cut")
    check(color3(P) is None, "Petersen negative control")
    E = lift([[1]]*15, 2)
    c = color3(E)
    check(c is not None, "bipartite double cover positive control")
    u, v = [i for i, e in enumerate(E) if 0 in e][:2]
    c[u] = c[v]
    check(not col_ok(E, c, 3), "corrupted coloring accepted")
    carving()
    for p in (2, 3, 5, 7):
        hard, D = profile(p)
        check(len(hard) == {2:16, 3:51, 5:901, 7:391}[p], "profile regression")
        if p == 5:
            check(check_five(hard, D, 0) == 4908, "distinct regression")
            check(check_five(hard, D, 1) == 0, "equal regression")
        else:
            rectangles(p, hard, D)
    print("PASS: all four primes, both matching types, corruption rejected.")


if __name__ == "__main__":
    main()
