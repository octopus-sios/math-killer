#!/usr/bin/env python3
"""Exact local certificates for Schrijver's regular degrees 8 and 10.
Also checks the mixed triangle-free biclique comparisons. Standard library only.
"""
from functools import cache
from itertools import combinations
from math import factorial, prod

Q = 5
B = 987
ROW = (2*B, 1597, 610, 610, 1597)
C = range(Q)
ZERO = (0,)*Q
RT = {0: 1, 2: 2, 4: 24, 6: 2640, 8: 3230080, 10: 48251508480}


def require(test, reason):
    if not test:
        raise ValueError(reason)


def compositions(n, k):
    if k == 1:
        yield (n,)
    else:
        for i in range(n+1):
            for rest in compositions(n-i, k-1):
                yield (i,) + rest


@cache
def rep(s):
    return min(t[i:]+t[:i] for t in (s, s[::-1]) for i in C)


@cache
def field(s):
    return tuple(prod(ROW[(i-x) % Q]**s[i] for i in C) for x in C)


@cache
def child(s, x):
    return s[:x]+(s[x]+1,)+s[x+1:]


def dot(u, v):
    return sum(x*y for x, y in zip(u, v))


def floor_root(n, r):
    """Integer Newton iteration from above, with exact termination."""
    if n < 2 or r == 1:
        return n
    x = 1 << ((n.bit_length()+r-1)//r)
    while True:
        y = ((r-1)*x + n//x**(r-1))//r
        if y >= x:
            return x
        x = y


def ceil_ratio_root(n, den, r):
    x = floor_root(n//den, r)
    return x + (den*x**r < n)


@cache
def tournaments(seq):
    # Label the vertices. Sorting the remaining target scores only relabels
    # that subproblem; distinct choices of the first outneighbor set are counted.
    if not seq:
        return 1
    n = len(seq)
    if seq[0] < 0 or seq[-1] >= n:
        return 0
    return sum(tournaments(tuple(sorted(seq[j] - (j not in out)
                                        for j in range(1, n))))
               for out in combinations(range(1, n), seq[0]))


def build(d):
    F = [tuple(compositions(d-k, Q)) for k in range(d+1)]
    reps = [sorted({rep(s) for s in seq}) for seq in F]
    # H(k,s) is the integer partition sum of the (k+1)-clique with field s.
    @cache
    def H(k, s):
        if not k:
            return sum(field(s))
        return dot(field(s), [H(k-1, rep(child(s, x))) for x in C])
    lower = {s: floor_root(H(k, rep(s)), k+1)
             for k in range(d+1) for s in F[k]}
    P = {s: sum(field(s)) for s in F[0]}
    # Construct one integer potential per pin multiset. In a fixed layer,
    # use clique lower bounds as deterministic denominators, not an LP solver.
    for b in range(1, d+1):
        for t in reps[b]:
            vals = [P[child(t, x)] for x in C]
            p = lower[t]
            for a in range(b, d+1):
                powers = [v**a for v in vals]
                best, den, same = 0, 1, 0
                for s in F[a]:
                    z = dot(field(s), powers)
                    if a == b and rep(s) == t:
                        same = max(same, z)
                    elif z*den > best*lower[s]:
                        best, den = z, lower[s]
                p = max(p, ceil_ratio_root(best, den, a),
                        ceil_ratio_root(same, 1, a+1))
            P[t] = p
        for t in F[b]:
            P[t] = P[rep(t)]
    return F, P


def verify_regular(d):
    F, P = build(d)
    count = improved = 0
    for s in F[0]:
        require(P[s] == sum(field(s)), ('base', d, s))
    for b in range(1, d+1):
        for t in F[b]:  # no symmetry quotient in the actual verification
            vals = [P[child(t, x)] for x in C]
            for a in range(b, d+1):
                powers = [v**a for v in vals]
                vpower = P[t]**a
                for s in F[a]:
                    lhs = dot(field(s), powers)
                    rhs = P[s]*vpower
                    require(lhs <= rhs, ('local', d, a, b, s, t))
                    count += 1
                    if a == d and b < d:
                        require(100**d*lhs <= 99**d*rhs, ('repeat', d, b, t))
                        improved += 1
    p = P[ZERO]
    require((1000*p)**(d+1) <= RT[d]*(1001*Q*B**(d//2))**(d+1),
            ('initial budget', d, p))
    require(99*1001**d < 100*1000**d, ('Brooks budget', d))
    # Mutate the claimed saving to 3% at the first repeated pin.
    t = child(ZERO, 0)
    z = sum(P[child(t, x)]**d for x in C)
    require(100**d*z > 97**d*p*P[t]**d, ('mutation undetected', d))
    print(f'd={d}: P(full)={p}; {count} local comparisons; '
          f'{improved} repeat comparisons; 97/100 mutation rejected')


def five_clique(n):
    """Coefficients in Z[phi] of the unnormalized abs and signed sums."""
    absolute = [0, 0]
    signed = [0, 0]
    for s in compositions(n, Q):
        w = factorial(n)//prod(factorial(i) for i in s)
        w *= 2**sum(i*(i-1)//2 for i in s)
        exponent = neg = 0
        for i in C:
            for j in range(i):
                edges = s[i]*s[j]
                exponent += edges if i-j in (1, 4) else -edges
                neg += edges if i-j >= 3 else 0
        x, y = 1, 0
        for _ in range(abs(exponent)):
            x, y = (y, x+y) if exponent > 0 else (y-x, x)
        for i, v in enumerate((x, y)):
            absolute[i] += w*v
            signed[i] += (-w if neg % 2 else w)*v
    return tuple(absolute), tuple(signed)


def biclique(a, b):
    # Four-phase integral on K_(a,b), with denominator 4**(a+b).
    M = ((2, 1, 0, 1), (1, 1, 1, 0), (0, 1, 2, 1), (1, 0, 1, 1))
    def L(k):
        return (1, 2**(k//2), 1, 2**(k//2))
    z = 0
    for s in compositions(a, 4):
        ways = factorial(a)//prod(factorial(i) for i in s)
        u = prod(t**i for t, i in zip(L(b), s))
        star = sum(L(a)[j]*prod(M[i][j]**s[i] for i in range(4))
                   for j in range(4))
        z += ways*u*star**b
    return z


def main():
    # The upper convergent dominates phi, so both off-diagonal magnitudes
    # are bounded from above (phi and phi-1, respectively).
    require(ROW[1]**2-ROW[1]*B-B*B == 1 and ROW[2] == ROW[1]-B,
            'golden-ratio upper bound')
    for d, value in RT.items():
        require(tournaments((d//2,)*(d+1)) == value, ('tournament count', d))
    print('Regular tournament counts:', list(RT.values()))
    for n, expected in ((5, (59240, 13600)), (7, (172254640, 23418080)),
                        (9, (5494352186240, 515005501440))):
        absolute, signed = five_clique(n)
        require(absolute == expected and signed == (5**n*RT[n-1], 0),
                ('five-phase clique', n, absolute, signed))
    print('Five-phase K5, K7, K9 absolute and signed polynomials verified')
    for d in (8, 10):
        verify_regular(d)
    tests = 0
    for a in range(2, 11, 2):
        for b in range(a, 11, 2):
            power = (a+1)*(b+1)
            z = biclique(a, b)
            require(z**power < 4**((a+b)*power)
                    * RT[a]**(b*(b+1))*RT[b]**(a*(a+1)), ('biclique', a, b))
            tests += 1
    print(f'{tests} strict four-phase biclique comparisons')


if __name__ == '__main__':
    main()
