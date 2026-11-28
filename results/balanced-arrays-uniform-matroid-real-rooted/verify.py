#!/usr/bin/env python3
"""Exact Newton positivity certificate and two-height root-order checks.

Run with python3 -I verify.py. The proof for all parameters is in PROOF.md.
No numerical root approximations or external packages are used.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial, gcd, prod


def check(condition, message):
    if not condition:
        raise ValueError(message)


def row_tables(d, r, last):
    """Powers of the row polynomial, retaining every mixed-margin coefficient."""
    steps = [S for s in range(r + 1) for S in combinations(range(d), s)]
    t = {(0,) * d: 1}
    yield t
    for _ in range(last):
        u = defaultdict(int)
        for v, weight in t.items():
            for S in steps:
                w = list(v)
                for i in S:
                    w[i] += 1
                u[tuple(w)] += weight
        t = dict(u)
        yield t


def hist_count(h, d, r, k):
    """Add labeled columns, counting row choices by current load."""
    def transitions(b, i, left, s, mult):
        if i == r:
            if left == 0:
                dest = (b[0] - s[0],) + tuple(
                    b[j] + s[j - 1] - s[j] for j in range(1, r)
                ) + (b[r] + s[-1],)
                yield dest, mult
            return
        for m in range(max(0, left - sum(b[i+1:r])), min(left, b[i]) + 1):
            yield from transitions(b, i + 1, left - m, s + (m,), mult * comb(b[i], m))

    t = {(h,) + (0,) * r: 1}
    for _ in range(d):
        u = defaultdict(int)
        for b, count in t.items():
            for dest, choices in transitions(b, 0, k, (), 1):
                u[dest] += count * choices
        t = u
    return sum(t.values())


def hist_poly(h, d, r):
    return [hist_count(h, d, r, k) for k in range(h * r // d + 1)]


def rank_two_pair(n, d):
    """Independent matching count: add a color class of k labeled occurrences.

    A p-edge matching leaves c*k-2*p choices of free old endpoints in total.
    Edges and unmatched singletons then inject as blocks into row labels.
    """
    output = [[], []]
    for k in range(2 * (n+1) // d + 1):
        match = [1]
        facts = [factorial(s) for s in range(k+1)]
        for c in range(d):
            new = [0] * ((c+1) * k // 2 + 1)
            for p, M in enumerate(match):
                if not M:
                    continue
                free = c * k - 2 * p
                for s in range(min(free, k) + 1):
                    new[p+s] += M * comb(free, s) * comb(k, s) * facts[s]
            match = new
        for j, h in enumerate((n, n+1)):
            if d * k > 2 * h:
                continue
            labeled = sum(M * comb(h, d*k-p) * factorial(d*k-p)
                          for p, M in enumerate(match) if d*k-p <= h)
            a, rem = divmod(labeled, facts[k] ** d)
            check(rem == 0, "nonintegral delabeling")
            output[j].append(a)
    return output


def sandwich(a, b, n, d):
    """Cross-multiplied sharp bounds (1), including the top coefficients."""
    N = n + 1
    for k in range(1, len(a)):
        check(b[k] * a[k-1] * (N-k)**d >= a[k] * b[k-1] * (N-k+1)**d,
              f"zero-bit bound at {k}")
        if k + 1 < len(b):
            check(a[k] * b[k] * k**d >= a[k-1] * b[k+1] * (k+1)**d,
                  f"one-bit bound at {k}")


def primitive(p):
    while p and not p[-1]:
        p.pop()
    g = 0
    for c in p:
        g = gcd(g, c)
    return [c // g for c in p] if g else []


def strict_alternation(a, b):
    """Signed Euclidean chain. F encloses G iff the chain has full degrees
    and positive leading terms (for the inputs below with positive leads).
    Indeed F is a negative multiple of the next remainder term at each
    zero of G; induct up the chain, using the signs at both infinities.
    """
    if len(b) == len(a):
        f, g = [0] + a, b       # z*A encloses B; 0 is the extra endpoint
    elif len(b) == len(a) + 1:
        f, g = b, a              # B encloses A
    else:
        return False
    while len(g) > 1:
        rem = f[:]
        while len(rem) >= len(g):
            shift, lead = len(rem) - len(g), rem[-1]
            rem = [x * g[-1] for x in rem]
            for i, x in enumerate(g):
                rem[shift + i] -= lead * x
            rem = primitive(rem)  # divisions only by positive integers
        if len(rem) != len(g)-1 or rem[-1] >= 0:
            return False
        f, g = g, [-x for x in rem]
    return len(g) == 1 and g[0] > 0


def unit(v, i):
    return v[:i] + (v[i]+1,) + v[i+1:]


def mixed_checks(t, u, n):
    N = n+1
    trials = 0
    for v, a in t.items():
        w = tuple(x+1 for x in v)
        for i, x in enumerate(v):
            p, q = unit(v, i), unit(w, i)
            if p not in t:
                continue
            check((N-x-1) * u[p] * a >= (N-x) * u[v] * t[p], "zero bit")
            check((x+2) * u.get(q, 0) * a <= (x+1) * u.get(w, 0) * t[p], "one bit")
            trials += 1
    return trials


def nonempty_rows(d, r):
    """Coefficient of x^v in (e_1+...+e_r)^ell for every ell.
    g[i] counts named columns with i+1 units of margin remaining.
    Removing the last nonempty row reduces every selected margin by one.
    """
    @lru_cache(None)
    def fiber(g):
        total = sum((i+1)*h for i, h in enumerate(g))
        if total == 0:
            return (1,)
        values = [0] * (total + 1)
        for b in product(*(range(h+1) for h in g)):
            if not 1 <= sum(b) <= r:
                continue
            mult = prod(comb(h, s) for h, s in zip(g, b))
            rem = tuple(h-s+t for h, s, t in zip(g, b, b[1:] + (0,)))
            for j, count in enumerate(fiber(rem)):
                values[j+1] += mult * count
        return tuple(values)

    result = [fiber((0,)*(k-1) + (d,)) for k in (1, 2, 3)]
    fiber.cache_clear()
    return result


def labeled_block_counter(r):
    """Independent columnwise inclusion-exclusion on labeled occurrences.

    In one column the three monomials for k=3 encode 3 singles,
    a double/single (3 choices, sign -), or a triple (net weight +2).
    """
    @lru_cache(None)
    def assign(a, b, c):
        if a == b == c == 0:
            return (1,)
        v = [0] * (1+a+b+c)
        for z in range(min(c, r//3)+1):
            for y in range(min(b, (r-3*z)//2)+1):
                for x in range(int(y == z == 0), min(a, r-3*z-2*y)+1):
                    ways = comb(a,x) * comb(b,y) * comb(c,z)
                    for i, h in enumerate(assign(a-x, b-y, c-z)):
                        v[i+1] += ways * h
        return tuple(v)

    patterns = {1: [(1,0,0,1)],
                2: [(2,0,0,1), (0,1,0,-1)],
                3: [(3,0,0,1), (1,1,0,-3), (0,0,1,2)]}

    def by_blocks(d, k):
        coeff = {(0,0,0): 1}
        for _ in range(d):
            nxt = defaultdict(int)
            for (a,b,c), weight in coeff.items():
                for x,y,z,sign in patterns[k]:
                    nxt[a+x,b+y,c+z] += weight * sign
            coeff = nxt
        out = [0] * (d*k+1)
        for counts, weight in coeff.items():
            for i, h in enumerate(assign(*counts)):
                out[i] += weight * h
        labels = factorial(k)**d
        check(all(h % labels == 0 for h in out), "inclusion-exclusion delabeling")
        return tuple(h // labels for h in out)
    return by_blocks


def positive_differences(values):
    """Strictly positive Newton coefficients at the first sample point."""
    while values:
        if values[0] <= 0:
            return False
        values = [y-x for x,y in zip(values, values[1:])]
    return True


def two_root_certificate():
    count = systems = 0
    for r in range(1, 13):
        by_blocks = labeled_block_counter(r)
        for d in range(max(4, r), 13):
            coeffs = nonempty_rows(d, r)
            check(coeffs == [by_blocks(d,k) for k in (1, 2, 3)],
                  "independent binomial-basis coefficient mismatch")
            start = (2*d+r-1)//r
            rows = [tuple(sum(comb(h,j)*c for j,c in enumerate(f) if j <= h)
                          for f in coeffs)
                    for h in range(start, start+5*d+1)]
            # Independent labeled-column count, with a third quota whenever feasible.
            for k in (1, 2, 3):
                check(rows[0][k-1] == hist_count(start, d, r, k), "basis/count mismatch")
            for p, q in ((3, 4), (3, 2)):
                samples = []
                for (a1,a2,a3), (b1,b2,b3) in zip(rows, rows[1:]):
                    samples.append(-(b1-a1)*(q*a2)**2 + (b2-a2)*p*q*a1*a2
                                   - (b3-a3)*(p*a1)**2)
                check(len(samples) == 5*d and positive_differences(samples),
                      f"Newton certificate failed at {(d,r,p,q)}")
                count += len(samples)
            systems += 1
    check((systems, count) == (72, 6360), "domain incomplete")
    check(not positive_differences([1, 3, 4]), "negative second difference accepted")
    print(f"{count} strictly positive Newton coefficients; {systems} independently reconstructed systems")


def main():
    two_root_certificate()
    pairs = mixed = 0
    for d in range(1, 5):
        for r in range(1, d+1):
            ts = list(row_tables(d, r, 6))
            for n, (t, u) in enumerate(zip(ts, ts[1:])):
                a, b = ([v[(k,)*d] for k in range(h*r//d + 1)]
                        for h, v in ((n, t), (n+1, u)))
                check(hist_poly(n+1, d, r) == b, "row/column count mismatch")
                sandwich(a, b, n, d)
                mixed += mixed_checks(t, u, n)
                if d >= 2:
                    check(strict_alternation(a, b), "small exact root order")
                pairs += 1
    print(f"{pairs} small adjacent pairs; {mixed} feasible mixed-margin extensions")

    # Wide sector, both degree changes; two rank-two sectors with d<n/2;
    # final example needs the empty-last-row comparison for the prefix.
    for n, d, r in ((9, 6, 4), (10, 6, 4), (150, 40, 2),
                    (50, 13, 2), (200, 20, 2)):
        a, b = (hist_poly(h, d, r) for h in (n, n+1))
        if r == 2:
            check([a, b] == rank_two_pair(n, d), "matching/column count mismatch")
        sandwich(a, b, n, d)
        check(strict_alternation(a, b), "exact signed remainder chain")
        print(f"(n,r,d)={(n,r,d)}: strict root order, degrees {len(a)-1},{len(b)-1}")

    check(3**13 >= 64*3*2**13 and 4**20 >= 64*4*3**20, "prefix examples")
    a, b = ([comb(h,k)**4 for k in range(h+1)] for h in (4,5))
    sandwich(a, b, 4, 4)
    b[1] -= 1  # destroys the sharp equality in the first bound
    try:
        sandwich(a, b, 4, 4)
    except ValueError:
        pass
    else:
        raise ValueError("failed to reject corrupted full-rank coefficient")
    check(not strict_alternation([1,1], [1,2,1]), "common root was accepted")
    print("corrupted coefficient and common-root controls rejected")


if __name__ == "__main__":
    main()
