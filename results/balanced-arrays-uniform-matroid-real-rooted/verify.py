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


FOUR_START = 533
S = 1 << 72
TOP = S << 52

def matches(k):
    cur = [1]
    for c in range(4):
        v = [0]*((c+1)*k//2+1)
        for p, count in enumerate(cur):
            if not count:
                continue
            free = c*k-2*p
            # Track count * binom(free,j) * (k)_j directly.
            h = count
            for j in range(min(k,free)+1):
                v[p+j] += h
                h = h * ((free-j)*(k-j)) // (j+1)
        cur = v
    return cur

def four_rows(last, max_low):
    """All quotas through height 533, low quotas through the last Newton sample."""
    rows = [[] for _ in range(last+1)]
    facts = [factorial(i) for i in range(last+1)]
    for k in range(FOUR_START//2+1):
        stop = last if k <= max_low else FOUR_START
        m = matches(k)
        # Forward differences at zero.  A choice of j nonempty rows has
        # m[4k-j] ways to pair the labeled occurrences, then j! assignments.
        diff = [0]*(min(stop,4*k)+1)
        div = facts[k]**4
        for j in range(2*k,len(diff)):
            diff[j], rem = divmod(facts[j]*m[4*k-j],div)
            if rem: raise ValueError('pair delabeling')
        for n in range(stop+1):
            if n>=2*k: rows[n].append(diff[0])
            diff[:-1] = [a+b for a,b in zip(diff,diff[1:])]
    return rows

class Evaluator:
    def __init__(self, row):
        self.row=row
        self.asc = [a << 24 for a in row]
        self.desc = self.asc[::-1]
        self.cache={}
    def __call__(self, x):
        if x not in self.cache:
            self.cache[x]=self.sign(x)
        return self.cache[x]
    def sign(self, x):
        rev=x>S
        P=self.asc if rev else self.desc
        a,b=(S,x) if rev else (x,S)
        v=P[0]
        if not rev:
            for c in P[1:]: v=c-((x*v)>>72)
        else:
            for c in P[1:]: v=c-((a*v)//b)
        if abs(v)<=len(P):
            # |a/b| <= 1, so all floor errors combined are at most the degree
            # in the 2^24-scaled value. Exact near-zero fallback.
            v=P[0]
            den=1
            for c in P[1:]:
                den*=b
                v=c*den-a*v
        return ((v>0)-(v<0))*(-1 if rev and len(P)%2==0 else 1)

def finite_four(rows):
    # Inductively cells are disjoint sign brackets for all old roots.
    # Refine each old bracket until the new row has the assigned sign at
    # BOTH ends. The complementary gaps then exhaust the new degree.
    old = Evaluator(rows[0])
    cells = []
    count = 0
    for n in range(FOUR_START):
        A, B = old, Evaluator(rows[n+1])
        gaps = []
        end = 0
        check(len(cells) == n//2, "old degree mismatch")
        for j, (L,U) in enumerate(cells,1):
            sg = (-1)**j
            while B(L) != sg or B(U) != sg:
                mid = (L+U)//2
                check(L < mid < U, f"unseparated at {(n,j)}")
                s = A(mid)
                if not s:
                    L = U = mid
                elif s == sg:
                    U = mid
                else:
                    L = mid
            check(end < L <= U <= TOP, "four-column bracket order")
            check((A(L) == A(U) == 0) if L == U else (A(L) == -sg and A(U) == sg),
                  "old bracket signs")
            gaps.append((end,L))
            end = U
            count += 1
        if len(rows[n+1]) > len(rows[n]):
            gaps.append((end, TOP))
        check(B(0) == 1 and B(TOP) == (-1)**((n+1)//2), "outer signs")
        old, cells = B, gaps
    check(count == 70756, "four-column prefix incomplete")
    print(f"four columns: {FOUR_START} consecutive pairs; {count} old roots bracketed")


# Integer nodes t=y/(16n-s), listed as (left y,s, right y,s).
# The right endpoints use ProgramComputer's four-column lower grid.
FOUR_GRID = (
    (13,0,24,17),
    (31,38,42,30),
    (49,1,60,42),
    (67,-10,78,55),
    (84,90,96,68),
    (102,77,113,80),
    (120,72,131,93),
    (138,71,149,105),
    (156,74,167,118),
    (173,128,184,130),
    (191,130,202,143),
    (209,134,220,156),
    (227,140,238,168),
    (244,181,255,181),
    (262,187,273,193),
    (280,194,291,206),
    (298,202,309,218),
    (315,237,327,231),
    (333,245,344,243),
    (351,254,362,256),
    (369,263,380,269),
    (387,273,398,281),
    (404,304,415,294),
    (422,314,433,306),
    (440,324,451,319),
    (458,335,469,331),
    (475,364,486,344),
    (493,375,504,357),
    (511,387,522,369),
    (529,399,540,382),
    (546,426,558,394),
    (564,438,575,407),
    (582,451,593,419),
    (600,464,611,432),
    (618,477,629,445),
    (635,503,646,457),
    (653,516,664,470),
    (671,530,682,482),
    (689,543,700,495),
    (706,569,718,507),
)


def low_four(rows):
    base = FOUR_START
    signs = entries = 0
    last_y, last_s = 0, 0
    for j, (yl,sl,yr,sr) in enumerate(FOUR_GRID, 1):
        for y, s, desired in ((yl,sl,(-1)**(j-1)), (yr,sr,(-1)**j)):
            check(s >= -16 and 16*base > s and y > last_y and
                  y*(16*base-last_s) > last_y*(16*base-s), "unordered nodes")
            last_y, last_s = y, s
            for delta, sign in ((0,desired),(1,(-1)**j)):
                M = 3*y//16 + 10
                if (-1)**M == sign:
                    M += 1
                check(M*(M+1)**3*(16*base-s)**4 > (y*(base+1))**4, "tail ratio")
                degree = 4*M-delta
                weights = [(-y**4)**k for k in range(M+1)]
                values = []
                for n in range(base, base+degree+1):
                    den = (16*n-s)**4
                    v = 0
                    for k, w in enumerate(weights):
                        a = rows[n][k]
                        if delta:
                            a = rows[n+1][k]-a
                        v = den*v + w*a
                    values.append(sign*v)
                check(positive_differences(values), f"uniform low sign {(j,y,s,delta)}")
                signs += 1
                entries += degree + 1
    check((signs, entries) == (160, 50320), "low sign domain incomplete")
    print(f"four columns: {entries} positive Newton entries certify all {signs} low signs")


def four_certificate():
    m = 3*max(row[2] for row in FOUR_GRID)//16 + 11
    rows = four_rows(FOUR_START+4*m+1, m)
    finite_four(rows)
    low_four(rows)


def five_column_projection_check():
    for r, target in ((2,[1,24,23040]), (3,[1,12,2778,6144])):
        t = {(0,0,0,0): 1}
        for h in range(4):
            u = defaultdict(int)
            for v,b in t.items():
                for s in range(r+1):
                    for bit in combinations(range(4),s):
                        w = tuple(v[i]+(i in bit) for i in range(4))
                        u[w] += b*(-4 if s==r else 1)
            t=u
        p = [t.get((k,)*4,0) for k in range(r+1)]
        check(p==target and p[1]**2 < 2*p[0]*p[2], "marked-column specialization")


def main():
    five_column_projection_check()
    four_certificate()
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
