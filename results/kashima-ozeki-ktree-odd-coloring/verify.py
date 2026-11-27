#!/usr/bin/env python3
"""Finite reducibility certificate for odd six-coloring of all 4-trees.

No SAT solver, external packages, floating point, input files, or graph order cutoff.
Run: python3 verify.py
"""
from functools import cache
from itertools import combinations, permutations, product


# A forest is a sorted tuple of branches at the same ordered four-clique.
# A branch is a tuple of four child forests. In face i replace slot i by
# the new central vertex, retaining the other three slots.
EMPTY = ()
def branch(*children):
    slots = [EMPTY] * 4
    for i, child in children:
        slots[i] = child
    return (tuple(slots),)  # singleton forest

def join(f, g):
    return tuple(sorted(f + g))

LEAF = branch()
PATH2 = branch((3, LEAF))
STRAIGHT3 = branch((3, PATH2))
REPRESENTATIVES = (
    EMPTY, LEAF, PATH2, join(LEAF, PATH2),
    STRAIGHT3, branch((3, branch((2, LEAF)))),
    branch((2, LEAF), (3, LEAF)), join(LEAF, STRAIGHT3),
    branch((2, LEAF), (3, branch((1, branch((0, LEAF)))))),
    branch((2, LEAF), (3, branch((0, LEAF), (1, LEAF)))),
)

def relabel(forest, perm):
    def move(b):
        result = [EMPTY] * 4
        for i, f in enumerate(b):
            result[perm[i]] = relabel(f, perm)
        return tuple(result)
    return tuple(sorted(move(b) for b in forest))

@cache
def size(f):
    return sum(1 + sum(map(size, b)) for b in f)


@cache
def rows(forest, base=(0, 1, 2, 3), width=4):
    """Every signature induced on the core by an internally odd coloring.
    The core is a width-clique, precolored identically. The attachment
    base lists four of its vertices. Interior colors range from 0 to 5.
    """
    parents = []
    def unfold(f, face):
        for b in f:
            u = width + len(parents)
            parents.append(face)
            for i, child in enumerate(b):
                unfold(child, face[:i] + (u,) + face[i+1:])
    unfold(forest, base)
    n = width + len(parents)
    # Core-core edges omitted: core rows record contributions, not totals.
    adj = [[] for _ in range(n)]
    for u, face in enumerate(parents, width):
        for v in face:
            adj[u].append(v)
            adj[v].append(u)
    col = list(range(width)) + [-1] * len(parents)
    result = set()
    def visit(u):
        if u == n:
            masks = []
            for v, nbrs in enumerate(adj):
                p = 0
                for w in nbrs:
                    p ^= 1 << col[w]
                if v >= width and p == 0:
                    return  # internal vertex not odd
                masks.append(p)
            result.add(tuple(masks[:width]))
            return
        banned = {col[v] for v in parents[u-width]}
        for c in range(6):
            if c not in banned:
                col[u] = c
                visit(u+1)
    visit(width)
    return tuple(sorted(result))


def avoidable(states, width, *, nonzero):
    """True iff every admissible tuple of forbidden rows can be avoided.

    Dually, try to cover the states by fixing one forbidden entry per
    coordinate. At an uncovered state, a cover must fix one of that
    state's still available entries. An empty remaining family is covered.
    """
    states = tuple(states)
    if not states:
        return False
    grouped = [{} for _ in range(width)]
    for j, s in enumerate(states):
        for i, x in enumerate(s):
            if x or not nonzero:
                d = grouped[i]
                d[x] = d.get(x, 0) | (1 << j)
    def covered(rem, coords):
        if rem == 0:
            return True
        s = states[(rem & -rem).bit_length() - 1]
        for i in coords:
            if s[i] or not nonzero:
                if covered(rem & ~grouped[i][s[i]], coords - {i}):
                    return True
        return False
    return not covered((1 << len(states)) - 1, set(range(width)))


@cache
def reducible(f):
    return avoidable(rows(f), 4, nonzero=True)

def subforests(f):
    for n in range(1, len(f)+1):
        yield from combinations(f, n)

def strong_pair(f, g):
    # Core (0,1,2,3,4), center 4. Faces omit 0 and 1 respectively.
    a = rows(f, (4, 1, 2, 3), 5)
    b = rows(g, (0, 4, 2, 3), 5)
    seen = set()
    for s in a:
        for t in b:
            row = tuple(x ^ y for x, y in zip(s, t))
            if row not in seen:
                seen.add(row)
                # A subfamily that cannot be covered certifies the whole family.
                if len(seen) in (8, 16, 32, 64, 128, 256) and avoidable(seen, 5, nonzero=False):
                    return True
    return avoidable(seen, 5, nonzero=False)

def needs_pair(sizes):
    return sum(n >= 2 for n in sizes) >= 2 and max(sizes) >= 3

def check_single(children, table):
    f = (tuple(children),)
    if f not in table and not reducible(f):
        raise ValueError("unlisted irreducible single branch")
    return f

def verify():
    table = {relabel(f, p) for f in REPRESENTATIVES for p in permutations(range(4))}
    # Failure test: corrupt the certificate by removing a five-vertex pattern.
    missing = REPRESENTATIVES[-1]
    try:
        check_single(missing[0], table - {missing})
    except ValueError:
        pass
    else:
        raise RuntimeError("corrupted table not rejected")
    print("PASS: missing five-vertex pattern rejected by the closure test")

    groups = {n: tuple(sorted(f for f in table if size(f) == n)) for n in range(6)}
    assert set(table) == set().union(*groups.values())
    print("Table by interior order:", [len(g) for g in groups.values()])

    # Terminal checks: restore the core K4, precolored 0,1,2,3.
    for f in table:
        if not any(all(x != (15 ^ (1 << i)) for i, x in enumerate(s)) for s in rows(f)):
            raise ValueError("cannot finish at K4")
    print(f"PASS: {len(table)} terminal forests colorable")

    # The grammar adds one single branch to an existing forest.
    pairs = {join(f, g) for f in table for g in table if len(g) == 1}
    for fg in pairs - table:
        if not any(reducible(h) for h in subforests(fg)):
            raise ValueError("sibling closure failed")
    print(f"PASS: {len(pairs)} distinct sibling unions")

    # For every qualifying ordered pair check robustness on a five-clique.
    # The table is closed under simultaneous permutations of its four slots.
    count = 0
    for f in table:
        for g in table:
            if needs_pair((size(f), size(g))):
                if not strong_pair(f, g):
                    raise ValueError("two-face certificate failed")
                count += 1
    print(f"PASS: {count} ordered strong pairs on distinct faces")

    # All other tuples of four child forests: direct extension check.
    count = 0
    for sizes in product(groups, repeat=4):
        if not needs_pair(sizes):
            for children in product(*(groups[n] for n in sizes)):
                check_single(children, table)
                count += 1
    print(f"PASS: {count} remaining ordered four-face tuples")
    print("PASS: closure for all 4-trees (six colors)")
if __name__ == "__main__":
    verify()
