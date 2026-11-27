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
                for protect in 'uw':
                    assert any(protect not in defects(g,'uw') for g in lifts)
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




def long_ears():
    cases = 0
    for length in range(3, 13):
        for first, last, protect in product((R,B), (R,B), (1,2)):
            # Repeat opposite the protected internal vertex, if needed.
            repeat = 3-protect if (first ^ ((length-1) % 2)) != last else -1
            word = [first]
            for i in range(1,length):
                word.append(word[-1] ^ int(i != repeat))
            assert word[-1] == last and len(set(word)) == 2
            assert word[protect-1] != word[protect]
            assert sum(a == b for a,b in zip(word,word[1:])) <= 1
            cases += 1
    return cases


def sparse_checks():
    """Reduced exterior path states for the three-arm move and parity overlay."""
    tips = 'uwt'
    arm = 0
    for rs in product(range(2), repeat=3):
        for old in exteriors(dict.fromkeys('v'+tips, 1), (0,)+rs):
            assert any(linear(attach(old, [('v',x) for x in tips], p))
                       for p in ((B,R,R),(R,B,R),(R,R,B)))
            arm += 1

    def word(length, first, repeat):
        w = [first]
        for i in range(1,length):
            w.append(w[-1] ^ int(i not in repeat))
        return w

    def joins(w, cycle, marks):
        # At a marked high vertex there is no old edge of its repeat color.
        size = len(w) if cycle else len(w)+1
        nb = {k:[] for k in range(size)}
        for i,c in enumerate(w):
            j = (i+1) % size
            nb[i].append((j,c))
            nb[j].append((i,c))
        merged = []
        for c in (R,B):
            unseen = set(nb)
            while unseen:
                v = unseen.pop()
                live = [v]
                comp = {v}
                for u in live:
                    for x,col in nb[u]:
                        if col == c and x in unseen:
                            unseen.remove(x)
                            comp.add(x)
                            live.append(x)
                if len(comp) < 2:
                    continue
                old = {x for x in comp if x % 2 == 0 and
                       not (x in marks and nb[x][0][1] == c)}
                if len(old)>1:
                    merged.append((c,old))
        return merged

    rings = paths = delayed = 0
    for h in range(2,8):
        for bits in product((0,1), repeat=h):
            mark = {2*i for i in range(h) if bits[i]}
            repeat = set(mark)
            if len(mark)%2:
                repeat.add(min(mark)+1)
            w = word(2*h, R, repeat)
            assert (w[-1] == w[0]) == (0 in mark)
            assert not joins(w, True, mark)
            rings += 1

        length = 2*(h-1)
        for bits in product((0,1), repeat=h-2):
            mark = {2*(i+1) for i in range(h-2) if bits[i]}
            for first, last in product((R,B),repeat=2):
                w = word(length, first, mark)
                if w[-1] != last:
                    if not mark:
                        continue  # delayed paths checked separately below
                    w = word(length, first, mark | {min(mark)-1})
                assert w[-1] == last and not joins(w,False,mark)
                paths += 1
        if h >= 3:
            for part in partitions(list(range(h))):
                if max(map(len,part))>2:
                    continue
                loc = {x:i for i,group in enumerate(part) for x in group}
                i = next(i for i in range(h-1) if loc[i] != loc[i+1])
                for first in (R,B):
                    w = word(length, first, {2*i+1})
                    assert w[-1] == first
                    assert joins(w,False,set()) == [(first,{2*i,2*i+2})]
                    delayed += 1
    return arm,rings,paths,delayed


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
    print('Ear extension: PASS (%d endpoint/protection checks)' % long_ears())
    print('Sparse overlay: PASS (%d three-arm, %d cyclic, %d prescribed path, %d delayed path states)'
          % sparse_checks())
    print('Sharpness graph: %d valid colorings of 4096; every one has two defects.'
          % sharpness())
    examples()
    print('Example graph checks and corrupted-coloring controls: PASS')
