#!/usr/bin/env python3
"""Exact n = 4, 6, 8 checks for the Petr–Turek bound; Python 3.10+, no dependencies."""
from itertools import combinations, permutations, product
from math import comb


def bits(x):
    """Positions of the set bits."""
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


def valid(n, family):
    return (len(set(family)) == len(family)
            and all(0 < a < 1 << n for a in family)
            and all(a & b for a, b in combinations(family, 2))
            and all(sum(b & a == b for b in family) <= 1 + a.bit_count()
                    for a in family))


def lightning(n):
    k = n // 2
    return [a for a in range(1 << n)
            if (a.bit_count() == k and a & 1) or a.bit_count() == k + 1
            or (a.bit_count() == k + 2 and not a & 1)]


def completable(n, fixed, left, target):
    """Choose from the pairs (a,complement(a)), a in left, extending fixed.
    Inclusion and intersection are checked on actual bitmask sets. Return
    feasibility, not a numerical objective estimate.
    """
    if not valid(n, fixed):
        return False
    full = (1 << n) - 1
    m = len(left)
    lo = (1 << m) - 1
    pool = left + [full ^ a for a in left]
    assert len(set(fixed + pool)) == len(fixed) + len(pool)
    def mask(predicate):
        return sum(1 << i for i, a in enumerate(pool) if predicate(a))
    disjoint = [mask(lambda b: not a & b) for a in pool]
    subsets = [mask(lambda b: a != b and a & b == b) for a in pool + fixed]
    cap = [a.bit_count() - sum(a != b and a & b == b for b in fixed)
           for a in pool + fixed]
    fixed_ids = list(range(2*m, 2*m + len(fixed)))
    # Relaxation: add the subset budgets of all fixed members and pay one
    # per incidence with a chosen member. A pair costs its cheaper live side.
    cost = [sum((subsets[j] >> i) & 1 for j in fixed_ids) for i in range(2*m)]
    cheap = [sum(1 << i for i, d in enumerate(cost) if d <= t)
             for t in range(max(cost, default=0))]
    budget = sum(cap[j] for j in fixed_ids)
    def owners(s):
        return (s & lo) | (s >> m)
    def search(on, live, spent):
        while True:
            for j in (*fixed_ids, *bits(on)):
                count = (subsets[j] & on).bit_count()
                if count > cap[j]:
                    return False
                if count == cap[j]:
                    live &= ~subsets[j]
            need = target - len(fixed) - on.bit_count()
            if need <= 0:
                return True
            for i in bits(live):
                if (subsets[i] & on).bit_count() > cap[i]:
                    live ^= 1 << i
            count = owners(live).bit_count()
            if count < need:
                return False
            # Sum of the 'need' smallest pair costs by integer thresholds.
            if spent + sum(max(0, need - owners(live & s).bit_count())
                           for s in cheap) > budget:
                return False
            alone = (live & lo) ^ (live >> m)
            if count > need or not alone:
                break
            forced = (alone | (alone << m)) & live
            forbid = 0
            for i in bits(forced):
                forbid |= disjoint[i]
                spent += cost[i]
            if forbid & forced:
                return False
            on |= forced
            live &= ~(forced | forbid)
        i = max(bits(live), key=lambda i: (disjoint[i] & live).bit_count())
        b = 1 << i
        return (search(on | b, live & ~(b | disjoint[i]), spent + cost[i])
                or search(on, live ^ b, spent))
    return search(0, mask(lambda a: all(a & b for b in fixed)), 0)


def edge_index(i, j):
    if i > j:
        i, j = j, i
    return j*(j-1)//2 + i


def adjacencies(n, g):
    return [sum(1 << j for j in range(n) if i != j and g >> edge_index(i,j) & 1)
            for i in range(n)]


def canonical(n, g):
    # Sort by degree and try every ordering within each degree class.
    adj = adjacencies(n, g)
    classes = [[i for i, a in enumerate(adj) if a.bit_count() == d] for d in range(n)]
    best = None
    for blocks in product(*(permutations(c) for c in classes if c)):
        order = sum(blocks, ())
        code = 0
        for j, v in enumerate(order):
            for i in range(j):
                if adj[v] >> order[i] & 1:
                    code |= 1 << edge_index(i, j)
        if best is None or code < best:
            best = code
    return best


def extend_graphs(n, parents):
    """Glue a last vertex, with arbitrary neighbourhood, onto every parent."""
    off = (n-1)*(n-2)//2
    for g in parents:
        for hood in range(1 << (n-1)):
            yield g | (hood << off)


def possible_graphs(left):
    reps = {0}
    for n in range(2, 8):
        reps = {canonical(n,g) for g in extend_graphs(n,reps)}
    assert len(reps) == 1044
    edges = [1 << i | 1 << j for j in range(8) for i in range(j)]
    contained = [sum(1 << i for i,e in enumerate(edges) if e & a == e) for a in range(256)]
    pairs = [(contained[a], contained[255 ^ a]) for a in left]
    survivors = set()
    for g in extend_graphs(8, reps):
        c = g.bit_count()
        if not 8 <= c <= 20:
            continue
        # Baseline cut with all edges red. Recolouring an intersecting set
        # of edges blue can only remove choices or lower the budget: a legal
        # chosen set hits every blue, so its surviving incidence cost is unchanged.
        costs = sorted(min((g & a).bit_count(), (g & b).bit_count()) for a,b in pairs)
        if sum(costs[:99-c]) <= 6*c:
            survivors.add(canonical(8,g))
    return edges, survivors


def colourings(edges):
    blues = [()]
    for e in edges:
        blues += [b + (e,) for b in blues if all(v & e for v in b)]
    return blues


def upper_eight():
    left = [a for a in range(256) if a.bit_count() == 3 or (a.bit_count() == 4 and a < 128)]
    edges, graphs = possible_graphs(left)
    cases = 0
    for g in graphs:
        chosen = [edges[i] for i in bits(g)]
        for blue in colourings(chosen):
            red = set(chosen).difference(blue)
            cap = 6 * len(red) - sum(not (a & b) for a in red for b in blue)
            costs = []
            for a in left:
                good = [sum(not (x & e) for e in red)
                        for x in (a, 255 ^ a) if all(x & e for e in blue)]
                if good:
                    costs.append(min(good))
            need = 99 - len(chosen)
            if len(costs) < need or sum(sorted(costs)[:need]) > cap:
                continue
            cases += 1
            fixed = list(blue) + [255 ^ e for e in red]
            assert not completable(8, fixed, left, 99), (g, blue)
    assert len(graphs) == 5
    print(f"n=8: {len(graphs)} graph types after incidence cut; "
          f"{cases} surviving colourings; no extension to 99")


def main():
    for n, want in [(4,7), (6,26), (8,98)]:
        f = lightning(n)
        k = n//2
        assert len(f) == want == comb(n,k)//2 + comb(n,k+1) + comb(n-1,k+2)
        assert valid(n,f)
        # Size-preserving mutation: the full set sees too many proper members.
        bad = f[1:] + [(1 << n)-1]
        assert len(set(bad)) == want and not valid(n,bad)
    print("Lightning sizes 7, 26, 98 verified; all three corrupted families rejected")
    for n, bound in [(4,7), (6,26)]:
        # Singleton and full-set cases are bounded in the proof. Fix the
        # co-singletons up to permutation. Everything else forms paired choices.
        full = (1 << n)-1
        left = [a for a in range(1, full) if a < (full ^ a)
                and 2 <= a.bit_count() <= n-2]
        for t in range(n+1):
            fixed = [full ^ (1 << i) for i in range(t)]
            assert not completable(n, fixed, left, bound+1)
        print(f"n={n}: no extension to {bound+1}")
    # Positive control for the completion routine, not just for valid().
    f = lightning(8)
    fixed = [a for a in f if a.bit_count() == 6]
    left = [a for a in f if a.bit_count() in (4,5)]
    assert completable(8,fixed,left,98)
    upper_eight()
    print("PASS: unrestricted maxima on [4], [6], [8] are 7, 26, 98")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: all proof checks must be enabled")
    main()
