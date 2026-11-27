#!/usr/bin/env python3
"""Exact checks of the pivot interfaces and the sharpness example. No dependencies."""
from itertools import product

R, B = 0, 1


def edge(x, y, c):
    return (x, y, c)


def linear(edges):
    """Check the two colors by incremental degree counts and disjoint sets."""
    degree, parent = {}, {}

    def find(vc):
        while parent.setdefault(vc, vc) != vc:
            vc = parent[vc]
        return vc

    seen = set()
    for x, y, c in edges:
        pair = frozenset((x, y))
        if c not in (R, B) or x == y or pair in seen:
            return False
        seen.add(pair)
        a, b = find((x, c)), find((y, c))
        if a == b:
            return False
        parent[a] = b
        for key in ((x, c), (y, c)):
            degree[key] = degree.get(key, 0) + 1
            if degree[key] > 2:
                return False
    return True


def defects(edges, vertices):
    colors = {v: [] for v in vertices}
    for x, y, c in edges:
        for v in (x, y):
            if v in colors:
                colors[v].append(c)
    return {v for v, cs in colors.items() if len(cs) == 2 and cs[0] == cs[1]}


def partitions(xs):
    if not xs:
        yield []
        return
    x, *tail = xs
    for blocks in partitions(tail):
        yield [[x]] + blocks
        for j in range(len(blocks)):
            yield blocks[:j] + [[x] + blocks[j]] + blocks[j+1:]


def representatives(d, c):
    """All connectivities of one linear forest at named positive-degree ports.

    Only the connected partition and old degrees can affect a future cycle or
    degree excess. A path block contains at most two degree-one ports. Realize
    each block with private intermediate vertices (including for split arms).
    """
    active = [x for x in d if d[x]]
    for blocks in partitions(active):
        if any(sum(d[x] == 1 for x in block) > 2 for block in blocks):
            continue
        edges = []
        for j, block in enumerate(blocks):
            ends = [x for x in block if d[x] == 1]
            while len(ends) < 2:
                ends.append((c, j, 'end', len(ends)))
            path = ends[:1] + [x for x in block if d[x] == 2] + ends[1:]
            for i, (x, y) in enumerate(zip(path, path[1:])):
                a, b = (c, j, i, 0), (c, j, i, 1)
                edges += [edge(x, a, c), edge(a, b, c), edge(b, y, c)]
        yield edges


def exteriors(degrees, red):
    ds = dict(zip(degrees, red))
    blue = {v: d-ds[v] for v, d in degrees.items()}
    for x, y in product(representatives(ds, R), representatives(blue, B)):
        old = x + y
        assert linear(old)
        yield old


def attach(old, pairs, palette):
    return old + [(x, y, c) for (x, y), c in zip(pairs, palette, strict=True)]


def check_fan():
    # Keys are red counts of two old edges at a,b. Other rows by symmetry.
    table = {(2, 2): (B,R,B, B,R,B), (2, 0): (B,R,B, R,B,R),
             (1, 1): (R,R,B, B,B,R), (1, 2): (R,B,B, B,R,B)}
    arcs = [('v','a'),('v','u'),('a','u'),('v','b'),('v','w'),('b','w')]
    tested = 0
    for (i,j), row in table.items():
        for flip, swap in product((0,1), repeat=2):
            nr = [2-i, 2-j] if flip else [i,j]
            colors = tuple(c ^ flip for c in row)
            if swap:
                colors = colors[3:] + colors[:3]
                nr.reverse()
            for old in exteriors({'a':2, 'b':2}, nr):
                new = attach(old, arcs, colors)
                assert linear(new)
                before, after = defects(old, 'ab'), defects(new, 'uw')
                assert len(after) <= 1
                assert 'u' not in after or 'b' in before
                assert 'w' not in after or 'a' in before
                tested += 1
    return tested


def check_twins():
    count = 0
    arcs = [('v','u'),('u','x'),('v','w'),('w','x')]
    for i,j in product(range(3), repeat=2):
        for old in exteriors({'v':2, 'x':2}, (i,j)):
            before = defects(old, 'vx')
            lifts = [g for p in product((R,B), repeat=4)
                     if linear(g := attach(old, arcs, p))]
            assert bool(lifts) == (i != j or i == 1)
            if len(before) <= 1:
                assert any(len(defects(g,'uw')) <= len(before) for g in lifts)
            count += 1
    return count


def check_fusion():
    count = 0
    arcs = [('v','u'),('v','w')]
    for r, s, t in product(range(3), range(2), range(2)):
        for old in exteriors({'v':2,'u':1,'w':1}, (r,s,t)):
            fused = [('u' if x=='w' else x, 'u' if y=='w' else y, c)
                     for x,y,c in old]
            if not linear(fused):
                continue
            before = defects(fused, 'vu')
            lifts = [g for p in product((R,B), repeat=2)
                     if linear(g := attach(old, arcs, p))]
            assert lifts
            assert any(len(defects(g,'uw')) <= len(before) for g in lifts)
            count += 1
    return count


def peel2(vertices, edges):
    nb = {x: set() for x in vertices}
    for x,y in edges:
        nb[x].add(y)
        nb[y].add(x)
    while nb:
        v = next((x for x in nb if len(nb[x]) <= 2), None)
        if v is None:
            return False
        for w in nb.pop(v):
            nb[w].remove(v)
    return True


def sharpness():
    pairs = [(0,1),(1,2),(2,0)]
    for i in range(3):
        a,b = 3+2*i, 4+2*i
        pairs += [(i,a),(i,b),(a,b)]
    assert len(pairs) == 2*9-6 and peel2(range(9), pairs)
    assert max(sum(v in e for e in pairs) for v in range(9)) == 4
    totals = {}
    for palette in product((R,B), repeat=len(pairs)):
        edges = attach([], pairs, palette)
        if linear(edges):
            m = len(defects(edges, range(9)))
            totals[m] = totals.get(m, 0) + 1
    assert set(totals) == {2}
    witness = [R if i in (0,1,3,5,8,9,11) else B for i in range(12)]
    assert linear(attach([], pairs, witness))
    # Corrupt the third central edge: now the whole central triangle is red.
    witness[2] = R
    assert not linear(attach([], pairs, witness))
    # Test cycle rejection independently of degree rejection.
    assert not linear(attach([], pairs[:3], (B,B,B)))
    assert not linear([(0,i,R) for i in (1,2,3)])
    return totals[2]


def examples():
    k = 5
    pts = [(i,j) for i in range(k) for j in range(k)]
    grid = [(p,q) for p in pts for q in pts if q > p and
            abs(p[0]-q[0])+abs(p[1]-q[1]) == 1]
    assert all((sum(p)^sum(q)) & 1 for p,q in grid)
    grid.append(((0,1),(1,0)))
    assert len(grid) < 2*len(pts)-5 and peel2(pts,grid)
    # Twice-subdivided K4, with a pendant leaf on each subdivision vertex.
    tree_edges = []
    t = 4
    for i in range(4):
        for j in range(i):
            tree_edges += [(i,t),(t,t+1),(t+1,j),(t,t+2),(t+1,t+3)]
            t += 4
    line = [(i,j) for i,e in enumerate(tree_edges)
            for j,f in enumerate(tree_edges[:i]) if set(e) & set(f)]
    vertices = list(range(len(tree_edges)))
    assert (len(vertices),len(line)) == (30,48) and peel2(vertices,line)
    nb = {v:{x^y^v for x,y in line if v in (x,y)} for v in vertices}
    for ns in nb.values():
        assert len(ns) <= 4
        if len(ns) == 4:
            assert any((ns-{x,y}) == {a,b} for x,y in line if {x,y} <= ns
                       for a,b in line)


if __name__ == '__main__':
    print('Paired-neighborhood fan: PASS (%d boundary/symmetry cases)' % check_fan())
    print('Twin four-cycle: PASS (%d boundary cases)' % check_twins())
    print('Distinct-arm fusion: PASS (%d liftable input cases)' % check_fusion())
    print('Sharpness graph: %d valid colorings of 4096; every one has two defects.'
          % sharpness())
    examples()
    print('Example graph checks and corrupted-coloring controls: PASS')
