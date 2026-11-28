#!/usr/bin/env python3
"""Exact finite remainder of the FC equality classification (Python 3, no dependencies)."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations


def check(condition, msg):
    if not condition:
        raise AssertionError(msg)


def diagram(kind):
    family, r = kind[0], int(kind[1:])
    edges = [(i, i+1, 3) for i in range(r-1)]
    if family == "B":
        edges[-1] = (r-2, r-1, 4)
    elif family == "D":
        edges[-1] = (r-3, r-1, 3)
    elif family == "E":
        edges[-1] = (2, r-1, 3)
    elif family == "F":
        edges[1] = (1, 2, 4)
    elif family == "H":
        edges[0] = (0, 1, 5)
    elif family == "G":
        edges = [(0, 1, 6)]
    adj = [{} for _ in range(r)]
    for s,t,m in edges:
        adj[s][t] = adj[t][s] = m
    return adj


def transpose(dn):
    n = len(dn)
    return tuple(sum(1<<j for j in range(n) if dn[j]>>i & 1) for i in range(n))


def template(n, covers):
    # Input is bottom-to-top numbered. Rows include the diagonal.
    dn = [1<<j for j in range(n)]
    for i,j in sorted(covers, key=lambda p:p[1]):
        check(i < j, "template not in topological order")
        dn[j] |= dn[i]
    return tuple(dn)


P2 = template(2, [(0,1)])
P4 = template(4, [(0,2),(1,2),(2,3)])
P7 = template(7, [(0,3),(1,3),(1,4),(2,4),(3,5),(4,5),(5,6)])
TYPES = {2:(P2,), 4:(P4,transpose(P4)), 7:(P7,transpose(P7))}


def isom(dn, target):
    # Equal ranks in a point's principal ideal and filter are necessary, but
    # acceptance checks EVERY ordered pair under the same permutation.
    if len(dn) != len(target):
        return False
    n = len(dn)
    def signatures(ds):
        return [(a.bit_count(),b.bit_count()) for a,b in zip(ds,transpose(ds))]
    sg, tg = signatures(dn), signatures(target)
    if sorted(sg) != sorted(tg):
        return False
    for p in permutations(range(n)):
        if all(sg[i] == tg[p[i]] for i in range(n)) and all(
            ((dn[j]>>i) ^ (target[p[j]]>>p[i])) & 1 == 0
            for j in range(n) for i in range(n)
        ):
            return True
    return False


def verify_shape(dn):
    check(any(isom(dn, t) for t in TYPES.get(len(dn), ())),
          "connected equality heap not among templates or their order duals")


def ideal_counts(dn, up):
    full = (1<<len(dn))-1
    @lru_cache(None)
    def count(mask):
        if not mask:
            return 1
        # Split on membership of a point in the induced subposet.
        i = (mask & -mask).bit_length()-1
        return count(mask & ~dn[i]) + count(mask & ~up[i])
    z = count(full)
    nums = [count(full & ~d) for d in dn]
    return z, nums


def connected(dn, up):
    seen = 1
    while True:
        old = seen
        for i,(d,u) in enumerate(zip(dn,up)):
            if seen>>i & 1:
                seen |= d | u
        if seen == old:
            return seen == (1<<len(dn))-1


def enumerate_fc(kind):
    adj = diagram(kind)
    r = len(adj)
    dep = [sum(1<<a for a in adj[s]) | (1<<s) for s in range(r)]
    total, eq = 0, Counter()

    def visit(word, dn, up, occ, tops):
        nonlocal total
        total += 1
        n = len(word)
        if n and connected(dn,up):
            z, nums = ideal_counts(dn,up)
            v = max(min(k,z-k) for k in nums)
            check(3*v >= z, f"below one third: {kind} {word}")
            if 3*v == z:
                verify_shape(dn)
                eq[n] += 1
        for s in range(r):
            old_tops = tops & ~dep[s]
            if old_tops >> (s+1):  # new point must have greatest maximal label
                continue
            if (tops>>s) & 1:     # old maximal point with label s would be covered
                continue
            bit = 1<<n
            d = bit                # principal ideal of the added point
            for a in (*adj[s], s):
                if occ[a]:
                    d |= dn[occ[a].bit_length()-1]
            bad = False
            for a,m in adj[s].items():
                both = occ[a] | occ[s]
                # Look for an alternating suffix on a,s ending at the new s.
                for k in range(1,m):
                    i = both.bit_length()-1
                    if i < 0 or word[i] != (a if k%2 else s):
                        break
                    both ^= 1<<i
                else:
                    # The old part of [i,new point] consists of m-1 points
                    # exactly when no off-chain point obstructs the braid.
                    if (up[i] & d).bit_count() == m-1:
                        bad = True
                        break
            if bad:
                continue
            new_up = tuple((u|bit) if (d>>i & 1) else u for i,u in enumerate(up))
            visit(word+(s,), dn+(d,), new_up+(bit,),
                  tuple(v|bit if i==s else v for i,v in enumerate(occ)), old_tops | (1<<s))

    visit((), (), (), (0,)*r, 0)
    return (total, eq[2], eq[4], eq[7])


EXPECTED = {
    "B5":(293,8,2,0), "D5":(167,8,6,0),
    "E6":(662,10,6,2), "E7":(2670,12,6,2), "E8":(10846,14,6,2),
    "F4":(106,6,4,0), "G2":(11,2,0,0), "H3":(44,4,2,0), "H4":(195,6,2,0)
}


def cube_controls():
    # Regression checks for the type-D cube proof, not a rank cutoff.
    # The D chamber is the union of two ordered-coordinate simplices.
    for r in range(4, 17):
        vs = [tuple((sgn if i == r-1 else 1) * int(i < k) for i in range(r))
              for sgn in (-1, 1) for k in range(r+1)]
        scaled = [Fraction(sum(x[i] for x in vs), 2) for i in range(r)]
        check(scaled == list(range(r, 1, -1)) + [0], "signed cube centroid")
        roots = [tuple(int(i == j) - int(i == j+1) for i in range(r))
                 for j in range(r-1)]
        roots.append(tuple(int(i >= r-2) for i in range(r)))
        ds = [1]*(r-2) + [Fraction(1, 2)]*2
        total = [sum(d*a[i] for d,a in zip(ds,roots)) for i in range(r)]
        check(total == [1]+[0]*(r-1) and sum(ds) == r-1, "wall budget")
        check(all(max(sum(x*y for x,y in zip(v,a)) for v in vs) >= 1
                  for a in roots), "cube projection extent")
    # For exp(7/6), bound the tail starting at degree four by a geometric
    # series (successive ratios <= (7/6)/5). No floating-point arithmetic.
    x = Fraction(7, 6)
    cubic = 1+x+x*x/2+x**3/6
    check(3 < cubic < cubic + x**4/24/(1-x/5) < 4, "exponential bounds")


def controls():
    cube_controls()
    for ds in [P2,P4,P7,transpose(P4),transpose(P7)]:
        verify_shape(ds)
        z, nums = ideal_counts(ds,transpose(ds))
        check(3*max(min(k,z-k) for k in nums)==z, "template balance")
        # Independent check: directly filter all bit strings by downward closure.
        ideals = [m for m in range(1<<len(ds)) if all(
            not (m>>i & 1) or m & d == d for i,d in enumerate(ds))]
        check((len(ideals), [sum(m>>i & 1 for m in ideals) for i in range(len(ds))])
              == (z,nums), "direct template enumeration")
    check(not isom(P4,transpose(P4)), "order duality is needed")
    # Mutation: move one predecessor of the middle point to its successor.
    mutant = template(4, [(0,2),(1,3),(2,3)])
    try:
        verify_shape(mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError("corrupted cover relation accepted")
    z, nums = ideal_counts(mutant,transpose(mutant))
    check(3*max(min(k,z-k) for k in nums)!=z, "mutant should lose equality")


if __name__ == "__main__":
    controls()
    print("cube / template / direct ideal counts / mutation controls: passed")
    print("type  FC incl. empty   connected equality (2,4,7 points)")
    for kind, expected in EXPECTED.items():
        row = enumerate_fc(kind)
        check(row == expected, f"{kind}: observed {row} != {expected}")
        print(f"{kind:4}  {row[0]:7}            {row[1:]}")
