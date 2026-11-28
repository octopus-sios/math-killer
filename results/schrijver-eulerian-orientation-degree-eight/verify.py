#!/usr/bin/env python3
"""Exact Schrijver certificates: mixed degrees through 8 and regular degree 10.
Also checks the mixed triangle-free biclique comparisons. Standard library only.
"""
from functools import cache
from itertools import combinations
from math import comb, factorial, gcd, isqrt, prod
from pathlib import Path

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
            require(x**r <= n < (x+1)**r, 'incorrect integer root')
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


# Mixed-degree certificate. Type 4 is used on degrees at most 6; type 5 on 8.
MD = 10**12                      # common rational edge denominator
GRID = 2**58                     # rational stored potential mantissas
TYPES = (4, 5)
PURE, HIGH_PINS, INITIAL = 1, 2, 4
N4 = ((2, 1, 0, 1), (1, 1, 1, 0), (0, 1, 2, 1), (1, 0, 1, 1))


def ceildiv(x, y):
    return -(-x//y)


def exact_matrices():
    # Upper enclosures in units 1/U. h denotes a projective angle h*pi/20.
    U = 1 << 180
    g = (U+isqrt(5*U*U))//2       # floor(U*phi)
    c = ((2*U, 2*U), (g, g+1), (g-U, g+1-U), (U-g-1, U-g),
         (-g-1, -g), (-2*U, -2*U))
    cosine = c+c[-2::-1]           # 2 cos(h*pi/5), 0 <= h <= 10
    def upper_sqrt(x):
        s = isqrt(x)
        return s+(s*s < x)
    def cross(h):
        lo, hi = cosine[h]
        # 2 cos(h*pi/10); choose the correct sign before halving again.
        y = upper_sqrt((2*U+hi)*U) if h <= 5 else -isqrt((2*U+lo)*U)
        # 2 cos(h*pi/20) / S_i; S_i^2 is 2 iff h is odd.
        w = upper_sqrt(ceildiv((2*U+y)*U, 1+(h % 2)))
        return ceildiv(MD*w, U)
    ph = ceildiv(MD*(g+1), U)
    row = (2*MD, ph, ph-MD, ph-MD, ph)
    cross_row = [cross(h) for h in range(11)]
    require(cross_row == [2000000000000, 1396802246668, 1902113032591,
                          1260073510671, 1618033988750, 1000000000000,
                          1175570504585, 642039521921, 618033988750,
                          221231742083, 0] and ph == 1618033988750,
            'integer phase matrix transcription')
    mat = {(4, 4): tuple(tuple(x*MD for x in r) for r in N4),
           (5, 5): tuple(tuple(row[(j-i) % 5] for j in C) for i in C)}
    mat[4, 5] = tuple(tuple(cross_row[min((5*i-4*j) % 20, (4*j-5*i) % 20)]
                            for j in C) for i in range(4))
    mat[5, 4] = tuple(zip(*mat[4, 5]))
    return mat


def reflection(u):
    return (u[0],) + u[:0:-1]


def canonical(u):
    return min(u, reflection(u))


def mfields():
    M = exact_matrices()
    F = {(b, h): {} for b in range(9) for h in TYPES}
    # The initial low fields absorb the S_i on each incident edge.
    for b in (0, 2, 4, 6):
        F[b, 4][(1, 2**(b//2), 1, 2**(b//2))] = PURE|HIGH_PINS|INITIAL
    F[8, 5][(1,)*5] = HIGH_PINS|INITIAL
    @cache
    def pin(t, h, x):
        v = tuple(i*j for i, j in zip(t, M[h, len(t)][x]))
        scale = gcd(*v)
        if not scale:
            return None, 0
        return tuple(z//scale for z in v), scale
    for b in range(8, 0, -1):
        for ttype in TYPES:
            for t, flags in F[b, ttype].items():
                dest = F[b-1, ttype]
                for h, mask in ((4, PURE), (5, HIGH_PINS)):
                    for x in range(h):
                        v, _ = pin(t, h, x)
                        if v is not None:
                            dest[v] = dest.get(v, 0) | (flags & mask)
    return F, pin


def low_radical(b, u):
    # Return A,k for the unscaled integer-field potential A**(1/k).
    # For the homogeneous four-color fields this is the degree-six potential.
    supp = tuple(i for i in range(4) if u[i])
    if supp in ((0, 2), (1, 3)):
        require(b <= 4 and u[supp[0]] == u[supp[1]], ('opposite', b, u))
        num, den = ((1, 1), (3, 4), (1, 2), (1, 3), (1, 5))[b]
        if supp[0] == 0:
            num, den = 2*num+b*den, 2*den
        return u[supp[0]]**den * 2**num, den
    k = b+1
    def mono(i, j):
        return u[i]**j * N4[i][i]**(j*(j-1)//2)
    A = sum(mono(i, k) for i in range(4))
    for i in range(4):
        for j in range(1, k):
            A += comb(k, j)*mono(i, j)*mono((i+1) % 4, k-j)
    return A, k


def fixed_p(b, h, u, flags):
    # Return numerator, root index, divisor for the NORMALIZED potential
    # p = P(u)/(MD**(b/2)*max(u)); or None for a free rational witness.
    if b == 0:
        return sum(u), 1, max(u)
    if h == 4 and flags & PURE:
        A, k = low_radical(b, u)
        return A, k, max(u)
    if b == 8:
        m = floor_root(RT[8]*(GRID*626*5)**9//625**9, 9)
        return m, 1, GRID
    return None


def mixed_potentials(F, data):
    # p stored as numerator**(1/index) / divisor.
    P = {}
    entries = 0
    for b in range(9):
        for h in TYPES:
            nums = iter(data[f'{b},{h}'])
            for u in sorted(v for v in F[b, h] if canonical(v) == v):
                p = fixed_p(b, h, u, F[b, h][u])
                if p is None:
                    z = int(next(nums))
                    require(z > 0, ('bad positive weight', b, u))
                    p = z, 1, GRID
                    entries += 1
                P[b, u] = p
                P[b, reflection(u)] = p
            require(next(nums, None) is None, ('extra table entries', b, h))
    return P, entries


def rad_bounds(p, scale):
    # Lower/upper integer bounds, in units 1/scale.
    n, k, d = p
    if k == 1:
        return n*scale//d, ceildiv(n*scale, d)
    z = n*scale**k
    den = d**k
    w = floor_root(z//den, k)
    return w, w+(w**k*den != z)


def literal_local(a, u, b, t, pin, P, repeat):
    # Only needed when the fast outward rational intervals touch. In the
    # equality cases divide by the right side and recover exact rational roots.
    from fractions import Fraction as R
    from math import lcm
    p, j, e = P[a, u]
    q, k, f = P[b, t]
    children = [pin(t, len(u), x) for x in range(len(u))]
    r = lcm(j, k, *(P[b-1, v][1] for v, _ in children if v))
    goal = R(987, 1000)**a if repeat else R(1)
    exact = R(0)
    for count, (v, g) in zip(u, children):
        if not count or not v:
            continue
        z, i, h = P[b-1, v]
        # [ (u_x/max(u)) ((g max(v)/(MD max(t))) p_child)^a
        #     / (p_source p_target^a goal) ]^r.
        term = (R(count*e, max(u))/goal)**r / p**(r//j)
        term *= R(g*max(v)*f, MD*max(t)*h)**(a*r)
        term *= R(z**(a*(r//i)), q**(a*(r//k)))
        num = floor_root(term.numerator, r)
        den = floor_root(term.denominator, r)
        require(num**r == term.numerator and den**r == term.denominator,
                ('inconclusive root comparison', a, b, u, t))
        exact += R(num, den)
    return exact <= 1


def verify_mixed():
    import json
    # The recorded integers are a witness, not premises: they are checked
    # against every comparison. No floating-point fit is run or trusted here.
    data = json.loads((Path(__file__).resolve().parent/'data'/
                       'mixed-potentials.json').read_text())
    F, pin = mfields()
    for layer in F.values():
        require(all(layer.get(reflection(u)) == flags for u, flags in layer.items()),
                'reflection does not preserve state flags')
    P, entries = mixed_potentials(F, data)
    sc = 1 << 78
    bounds = {key: rad_bounds(value, sc) for key, value in P.items()}
    def up_u(u):
        m = max(u)
        return tuple(ceildiv(v*sc, m) for v in u)
    sources = {(a, h): [(u, up_u(u), bounds[a, u][0]) for u in F[a, h]]
               for a in range(1, 9) for h in TYPES}
    tests = repeats = exact = 0
    for b in range(1, 9):
        for ht in TYPES:
            for t, flags in F[b, ht].items():
                if t != canonical(t):
                    continue
                for h in TYPES:
                    hi = []
                    for x in range(h):
                        v, g = pin(t, h, x)
                        hi.append(0 if not v else ceildiv(
                            g*max(v)*bounds[b-1, v][1], MD*max(t)))
                    for a in range(b, 9):
                        src = sources[a, h]
                        if not src:
                            continue
                        repeat = a == 8 and b < 8 and flags & HIGH_PINS
                        factor = 1000**a if repeat else 1
                        c = [factor*z**a for z in hi]
                        right = bounds[b, t][0]**a * (987**a if repeat else 1)
                        # Fixed dimension; avoid making millions of generators.
                        if h == 4:
                            c0, c1, c2, c3 = c
                            unsure = [u for u, w, lo in src if
                                      c0*w[0]+c1*w[1]+c2*w[2]+c3*w[3] > lo*right]
                        else:
                            c0, c1, c2, c3, c4 = c
                            unsure = [u for u, w, lo in src if
                                      c0*w[0]+c1*w[1]+c2*w[2]+c3*w[3]+c4*w[4]
                                      > lo*right]
                        for u in unsure:
                            require(literal_local(a, u, b, t, pin, P, repeat),
                                    ('mixed local comparison', a, b, u, t))
                        exact += len(unsure)
                        tests += len(src)
                        repeats += len(src)*bool(repeat)
    for h in TYPES:
        for u in F[0, h]:
            n, k, den = P[0, u]
            require(n*max(u)**k == (sum(u)*den)**k, ('mixed base', u))
    for b in range(0, 8, 2):
        u = (1, 2**(b//2), 1, 2**(b//2))
        n, k, den = P[b, u]
        # (max(u)*p)^(b+1) == 4^(b+1) * epsilon(K_(b+1)).
        require(n**(b+1)*max(u)**(k*(b+1))
                == den**(k*(b+1))*4**(k*(b+1))*RT[b]**k, ('initial 4', b))
    n, k, den = P[8, (1,)*5]
    require(k == 1 and (625*n)**9 <= (626*5*den)**9*RT[8], 'initial 5')
    require(987*626**8 < 1000*625**8, 'mixed Brooks budget')
    # Mutate the actual table entry for a once-pinned high vertex.
    v, _ = pin((1,)*5, 5, 0)
    z, k, den = P[7, v]
    require(k == 1 and den == GRID, 'expected a free table weight')
    lhs_lower = 0
    for x in range(5):
        w, g = pin(v, 5, x)
        child_lower = g*max(w)*bounds[6, w][0]//(MD*max(v))
        lhs_lower += (sc*v[x]//max(v))*child_lower**7
    mutated_upper = ceildiv(sc*z, 2*den)
    require(lhs_lower > mutated_upper**8, 'halved mixed weight not rejected')
    print('Halving the once-pinned five-color table weight reverses its self-test')
    print(f'Mixed certificate: {entries} table weights, {tests} local tests '
          f'({repeats} strengthened); {exact} exact-root fallbacks')


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
    verify_mixed()
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
