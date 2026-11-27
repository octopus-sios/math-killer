#!/usr/bin/env python3
"""Exact arithmetic certificate for the almost-simple case of Herzog--Schönheim.

Tables from Garonzi--Margolis (GM), Byott and the GAP Character Table Library
are cited in PROOF.md. No CAS, network, floating point or group databases.
"""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from math import gcd, isqrt, prod


def require(condition, message):
    if not condition:
        raise ValueError(message)


@cache
def factors(n):
    require(n >= 1, "positive integer required")
    d, ps = 2, []
    while d * d <= n:
        a = 0
        while n % d == 0:
            n //= d
            a += 1
        if a:
            ps.append((d, a))
        d += 1 if d == 2 else 2
    if n > 1:
        ps.append((n, 1))
    return tuple(ps)


def divisors(n):
    ds = [1]
    for p, e in factors(n):
        ds = [a * p**j for a in ds for j in range(e + 1)]
    return ds


@cache
def capacity(o):
    ds = divisors(o)
    return max(sum(F(b, h) for h in ds if h >= b) for b in ds)


@cache
def primorial_bound(bits):
    """Upper bound for product p/(p-1), p|N, whenever N < 2**bits."""
    P, k, p = F(1), 1, 2
    while True:
        if factors(p) == ((p, 1),):
            k *= p
            if k >= 1 << bits:
                return P
            P *= F(p, p - 1)
        p += 1


def divisor_tail(N, m):
    return F(sum(s for s in divisors(N) if s*m <= N), N)


def maximal_order_bound(N, indices):
    require(all(i > 1 and N % i == 0 for i in indices), "invalid maximal index")
    orders = set().union(*(divisors(N//i) for i in indices))
    return F(sum(orders), N)


# All distinct maximal indices from the indicated CTblLib entries (repetitions discarded).
CTBL = {
    "L3(3)": (13, 144, 234),
    "L3(4)": (21, 56, 120, 280),
    "L4(3)": (40, 117, 130, 2106, 8424, 10530),
    "L5(2)": (31, 155, 64512),
    "L6(2)": (63, 651, 1395, 13888, 55552, 357120, 1904640),
    "M12": (12, 66, 144, 220, 396, 495, 1320),
    "M22": (22, 77, 176, 231, 330, 616, 672),
}

# GM Table 3: bound on number of maximal isomorphism types minus omega(f).
# Columns n=2,...,12; 0 denotes a missing row, not an upper bound.
TABLE3 = {
    'L': (5,9,14,12,23,14,20,21,29,21,31),
    'U': (0,8,13,10,20,11,17,16,25,16,26),
    'S': (0,0,9,0,17,0,18,0,16,0,24),
    'O': (0,0,0,0,0,12,0,21,0,19,0),
    '+': (0,0,0,0,0,0,22,0,20,0,31),
    '-': (0,0,0,0,0,0,10,0,19,0,21),
}


def valid(kind, n):
    return (kind == 'L' and n >= 2 or kind == 'U' and n >= 3
            or kind == 'S' and n >= 4 and n % 2 == 0
            or kind == 'O' and n >= 7 and n % 2 == 1
            or kind in ('+', '-') and n >= 8 and n % 2 == 0)


def parameters(kind, n, q, f):
    """Order N, lower bound on minimal index m (GM Table 2), multiple o of |Out|."""
    r = n//2
    if kind in ('L', 'U'):
        sign = 1 if kind == 'L' else -1
        d = gcd(n, q-sign)
        N = q**(n*(n-1)//2)*prod(q**i-sign**i for i in range(2,n+1))//d
        if kind == 'L':
            m = 6 if (n,q) == (2,9) else q**(n-1)
        elif (n,q) == (3,5):
            m = 50
        elif n == 4:
            m = (q+1)*(q**3+1)
        else:
            m = q**(2*n-2)//(q+1)
        return N, m, d*f*(1 if n==2 else 2)
    if kind in ('S','O'):
        d = gcd(2,q-1)
        N = q**(r*r)*prod(q**(2*i)-1 for i in range(1,r+1))//d
        m = q**(n-2 if kind == 'O' or q == 2 else n-1)
        return N, m, (2 if kind == 'S' and n == 4 and q % 2 == 0 else d)*f
    sign = 1 if kind == '+' else -1
    d = gcd(4,q**r-sign)
    N = q**(r*(r-1))*(q**r-sign)*prod(q**(2*i)-1 for i in range(1,r))//d
    return N, q**(n-2), d*(6 if kind=='+' and n==8 else 2)*f


def uniform(n,t):
    """Numerator, denominator of coarse bound for n >= 3; t=floor(log_2 q)."""
    z = t+1
    return (24*n*z*(2*n**6+n*z)*(n*n*z+1),
            1 << (t*max(2,n-2)))


def tail_bases():
    for n,t in ((64,1),(4,16),(3,16)):
        a,b = uniform(n,t)
        require(a < b, ("classical tail",n,t))
    require((65**9 < 2*64**9 and 3**3 < 2**62*2**3 and
             5**9 < 2**16*4**9 and 18**3 < 4*17**3), "ratio estimates")
    t = 16
    require(2*t*(5+t)*(3*(t+1)+1) < 2**t, "rank-one tail")
    require(6*(t+1)*(166+t+1)*(248*(t+1)+1) < 2**(2*t), "exceptional tail")
    require(17**3 < 2*16**3, "field tail ratio")


def classical(kind,n,q,p,f):
    N,m,o = parameters(kind,n,q,f)
    if N*o < 2000:
        return 'order below 2000'
    if (kind,n,q) == ('L',4,2):
        return 'alternating A8'
    if n<=12:
        c = TABLE3[kind][n-2]
        require(c>0,(kind,n))
        B = F(c+len(factors(f)),m)
    else:
        z = q.bit_length()
        k = (3*n+1)//2 + 14*(isqrt(n)+1) + 12 + z
        ell = 2*n**6+n*z
        B = F(k,m)+F(ell*q**((6 if kind=='U' else 3)*n),N)
    K = capacity(o)
    if K*B*primorial_bound(N.bit_length()) < 1:
        return 'maximal counts'
    if K*divisor_tail(N,m) < 1:
        return 'divisor tail'
    group = f"{kind}{n}({q})"
    if group in CTBL and K*maximal_order_bound(N, CTBL[group]) < 1:
        return 'maximal indices'
    raise ValueError(("classical gap",group,N,m,o))


# GM Table 5 (arXiv:2509.25118v2): type, C, upper order exponent r,
# and safe lower minimal-index exponent a.
EX = [('Sz',4,6,2), ('G2',11,14,4), ('Ree',5,8,3), ('3D4',12,29,9),
      ('F4',19,52,11), ('2F4',9,28,10), ('E6',27,78,16),
      ('2E6',25,82,18), ('E7',50,133,27), ('E8',166,248,50)]


def exceptional(q,p,f,kind,c,r,a):
    # Groups outside the ranges of the exceptional simple families are
    # omitted, not treated as counterexamples. The Tits group is separate.
    if kind in ('Sz','2F4') and not(p==2 and f%2==1 and f>=3):
        return None
    if kind=='Ree' and not(p==3 and f%2==1 and f>=3):
        return None
    if kind=='G2' and q==2:
        return None
    z = q.bit_length()
    m = q**a
    if kind=='G2' and q in (3,4):
        m = {3:351,4:416}[q]
    # |Out| divides 6f; for the Suzuki and small Ree families it divides f.
    o = f if kind in ('Sz','Ree','2F4') else 6*f
    b = capacity(o)*(c+(z-1).bit_length())*primorial_bound(r*z)
    require(b < m, ("exceptional gap",kind,q,b,m))
    return 'exceptional maximal counts'

def sporadic():
    # GM Table 1: except for M11,M12,M22,M23,M24,J2,HS, all rows
    # (including Tits) satisfy ell/m1 <= 1/16. All have |S| < 2^200.
    require(capacity(2)*primorial_bound(200) < 16, "sporadic generic")
    for name,N,c in (('J2',604800,9),('HS',44352000,10)):
        P = prod(F(p,p-1) for p,_ in factors(N))
        require(capacity(2)*c*P < 100, name)
    for name,N in (('M12',95040),('M22',443520)):
        require(capacity(2)*maximal_order_bound(N, CTBL[name]) < 1, name)
    # Out(M11), Out(M23), Out(M24) are trivial; these were simple already.


def check():
    tail_bases()
    require(capacity(6)*divisor_tail(262080,64)==F(48017,65520), "field example")
    sporadic()
    counts = Counter()
    fields = {t: [] for t in range(1,16)}
    for q in range(2,2**16):
        fac = factors(q)
        if len(fac) == 1:
            p,f = fac[0]
            fields[q.bit_length()-1].append((q,p,f))
    for kind in TABLE3:
        for n in range(2,64):
            if not valid(kind,n):
                continue
            for t,Ft in fields.items():
                if n >= 3:
                    a,b = uniform(n,t)
                    if a < b:
                        counts['uniform classical bins'] += 1
                        continue
                else:
                    if 2*t*(5+t)*(3*(t+1)+1) < (1 << t):
                        counts['uniform classical bins'] += 1
                        continue
                for q,p,f in Ft:
                    if (kind,n,q) in (('L',2,2),('L',2,3),('U',3,2),('S',4,2)):
                        continue
                    if kind=='O' and p==2:
                        continue  # the same simple groups are in the symplectic family
                    counts[classical(kind,n,q,p,f)] += 1
    for t,Ft in fields.items():
        if 6*(t+1)*(166+t+1)*(248*(t+1)+1) < (1 << (2*t)):
            counts['uniform exceptional bins'] += 1
            continue
        for q,p,f in Ft:
            for row in EX:
                result = exceptional(q,p,f,*row)
                if result:
                    counts[result] += 1
    return counts


def negative_control():
    # Contaminate a true maximal-index certificate with a whole-socle part.
    # Even ignoring that it is not proper, the capacity must then fail.
    N, o = 20160, 12
    good = maximal_order_bound(N, CTBL['L3(4)'])
    require(good*capacity(o)<1, "positive control")
    def admit(orders):
        require(F(sum(orders),N)*capacity(o)<1, "capacity exhausted")
    orders = set().union(*(divisors(N//i) for i in CTBL['L3(4)']))
    admit(orders)
    try:
        admit(orders | {N})
    except ValueError as e:
        require(str(e)=="capacity exhausted", "wrong rejection")
        return
    raise ValueError("accepted corrupted certificate")


if __name__ == '__main__':
    counts = check()
    negative_control()
    print("PASS: classical and exceptional tails; sporadics and Tits; finite cases:")
    for method in sorted(counts):
        print(f"  {method}: {counts[method]}")
    print("PASS: corrupted certificate rejected")
