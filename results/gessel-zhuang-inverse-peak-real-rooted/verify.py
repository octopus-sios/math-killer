#!/usr/bin/env python3
"""Exact finite cross-checks, not a numerical proof of the asymptotic theorem.

python3 verify.py [maximum n, default 39]
"""
from fractions import Fraction as Q
from itertools import permutations
from math import comb, gcd
import sys


def zeros(n):
    return [[0] * n for _ in range(n)]


def step(n, prev, older, L, M):
    """Integer form of D_s D_t with peak/left-peak flags L,M."""
    v = zeros(n // 2 + 3)
    for r, row in enumerate(prev):
        for s, x in enumerate(row):
            if not x:
                continue
            a, b = 2*r+L, 2*s+M
            v[r][s] += a*b*x
            v[r+1][s] += (n-a)*b*x
            v[r][s+1] += a*(n-b)*x
            v[r+1][s+1] += (n-a)*(n-b)*x
    for r, row in enumerate(older):
        for s, x in enumerate(row):
            if x:
                q = (n-2+L*M)*x
                v[r][s] += q
                v[r][s+1] -= q
                v[r+1][s] -= q
                v[r+1][s+1] += q
    assert all(x >= 0 and x % n == 0 for row in v for x in row)
    return [[x // n for x in row] for row in v]


def tables(n, W, U, V):
    D = list(map(list, zip(*V)))
    E, F, G = ([[0]*len(W)] for _ in range(3))
    for k in range(1, n+1):
        for X, A, B in ((E, W, V), (F, D, U)):
            X.append([u-v for u, v in zip((B if k % 2 else A)[k//2], X[-1])])
        G.append([(2 if n >= 2 else 1)*u-v for u, v in zip(E[-1], G[-1])])
    return [W, U, V, D, E, F, G]


def stats(p):
    desc = [x > y for x, y in zip(p, p[1:])]
    pk = sum(not a and b for a,b in zip(desc, desc[1:]))
    left = bool(desc and desc[0])
    br = 1 + sum(a != b for a,b in zip(desc, desc[1:]))
    return pk+1, pk+left, br+left, br


def brute(n, T):
    A = [[[0]*len(row) for row in X] for X in T]
    for p in permutations(range(n)):
        s,l,u,b = stats(p)
        i,j,_,_ = stats([p.index(x) for x in range(n)])
        for X,(k,v) in zip(A, [(s,i),(l,j),(l,i),(s,j),(u,i),(u,j),(b,i)]):
            X[k][v] += 1
    assert T == A


def binpow(t,k):
    """Generalized binomial [x^k](1+x)^t for integer t."""
    if k < 0:
        return 0
    if t >= 0:
        return comb(t,k)
    return (-1)**k * comb(k-t-1,k)


def kernel(n,s,left,z):
    """Direct [x^n] in (1); multiply denominator out, no poles or roots."""
    a,h = (s//2, s%2) if left else (0,0)
    # (1+x)^a (1-x)^(s-a-h) / ((1-x)^s - z(1+x)^s)
    den = [comb(s,k)*((-1)**k-z) for k in range(s+1)]
    coeff = []
    for k in range(n+1):
        num = sum(comb(a,i)*(-1)**(k-i)*binpow(s-a-h,k-i)
                  for i in range(min(a,k)+1))
        coeff.append((num - sum(den[i]*coeff[k-i]
                                 for i in range(1,min(s,k)+1))) / den[0])
    return coeff[-1]


def poly(a,x):
    p = 0
    for b in reversed(a):
        p = p*x+b
    return p


def verify_extraction(n,T):
    # Coefficients of u^r in the source identities, before triangular inversion.
    for f,X in enumerate(T):
        left = f in (1,3,5)
        for z in (Q(-1,3), Q(-2,5)):
            t = 4*z/(1+z)**2
            column = (1+z)**(n+(not left))/(1-z)**(n+1)
            factor = [Q(1,4),Q(1),Q(1,2),Q(1,2),Q(1,4),Q(1,2),Q(1,8)][f]
            if f==6 and n==1:
                continue
            vals = [factor*column*poly(row,t) for row in X]
            for r in range(1,n+2):
                if f<=3 and (r%2 != int(f in (1,2))):
                    continue
                total = 0
                for k,row in enumerate(vals):
                    if not row:
                        continue
                    if f<=3:
                        shift = 2*k+int(f in (1,2))
                        A,B,C,D = n+int(f in (0,3))-2*k,-(n+1),0,0
                        base = 4**k
                    else:
                        shift = k
                        A,B,C,D = ((n-k,1-n,0,-2) if f in (4,5)
                                   else (n-1-k,-n,3,-1))
                        base = 2**k
                    m = r-shift
                    c = sum(binpow(A,i)*(-1)**j*binpow(B,j)*binpow(C,l)*
                            (-1)**(m-2*i-2*j-l)*binpow(D,m-2*i-2*j-l)
                            for i in range(m//2+1)
                            for j in range((m-2*i)//2+1)
                            for l in range(m-2*i-2*j+1))
                    total += row*base*c
                assert total == kernel(n,r,left,z), (n,f,r,z)


def primitive(p):
    while p and not p[-1]:
        p.pop()
    if p:
        g = gcd(*p)
        p = [x//g for x in p]
    return p


def real_simple_off_zero(p):
    p = primitive(p[:])
    if not p:
        return True  # empty slice
    while p[0]==0:
        p.pop(0)
    if len(p)==1:
        return True
    chain = [p, primitive([i*x for i,x in enumerate(p) if i])]
    while len(chain[-1])>1:
        a,b = chain[-2][:],chain[-1]
        while len(a)>=len(b):
            scale, mult = abs(b[-1]), a[-1]*(1 if b[-1]>0 else -1)
            q=len(a)-len(b)
            a=primitive([scale*x-(mult*b[i-q] if i>=q else 0)
                         for i,x in enumerate(a)])
        if not a:
            return False
        chain.append([-x for x in a])
    def variations(signs):
        nz=[x>0 for x in signs if x]
        return sum(x!=y for x,y in zip(nz,nz[1:]))
    return (variations([q[-1]*(-1)**(len(q)-1) for q in chain]) -
            variations([q[0] for q in chain]) == len(p)-1)


def int_kernel(n, s, left, m):
    """(m+1)^(n+1) K_s(-1/m); use the integer denominator recurrence."""
    a, h = (s//2, s%2) if left else (0, 0)
    p = []
    for t in range(n+1):
        num = sum(comb(a,j)*binpow(s-a-h,t-j)*(-1)**(t-j)
                  for j in range(min(a,t)+1))
        value = m*(m+1)**t*num
        value -= sum(comb(s,i)*(m*(-1)**i+1)*(m+1)**(i-1)*p[t-i]
                     for i in range(1,min(t,s)+1))
        p.append(value)
    return p[-1]


def certify_first_rows(n,T):
    """Identify each candidate exactly at d+1 distinct rational t-values.

    These direct identities from the source, rather than the recurrence
    used to propose coefficients, certify the finite step of Section 4.
    """
    for f,(X,k,C) in enumerate(zip(T,[2,1,1,2,3,3,3],[4,4,2,8,2,4,1])):
        if k>=len(X) or (n==1 and f==6):
            continue
        left = f in (1,3,5)
        row = X[k]
        p = n+int(not left)
        d = p//2
        assert not any(row[d+1:])
        for m in range(2,d+3):
            def K(s):
                return int_kernel(n,s,left,m)
            if f in (0,3):
                rhs = K(4)-2*n*K(2)
            elif f in (1,2):
                rhs = K(3)-(2*n+1)*K(1)
            elif f in (4,5):
                rhs = K(3)-2*K(2)+(3-2*n)*K(1)
            else:
                rhs = K(3)-4*K(2)+(11-2*n)*K(1)
            lhs = sum(x*(-4*m)**j*(m-1)**(p-2*j)
                      for j,x in enumerate(row) if x)
            assert C*(m if left else 1)*lhs == rhs, (n,f,m)


def main(limit):
    assert limit>=39
    W,U,V = (zeros(3) for _ in range(3))
    W[1][1]=U[0][0]=V[0][1]=1
    A,B,C = [[0]],[[1]],[[0]]
    for n in range(1,limit+1):
        if n>1:
            (A,W),(B,U),(C,V) = ((W,step(n,W,A,0,0)),(U,step(n,U,B,1,1)),
                                  (V,step(n,V,C,1,0)))
        T=tables(n,W,U,V)
        assert all(x>=0 for X in T for row in X for x in row)
        if n<=8:
            brute(n,T)
        if n<=39:
            certify_first_rows(n,T)
        if n<=10:
            verify_extraction(n,T)
        assert all(real_simple_off_zero(row) for X in T for row in X)
        if n==8:
            # Corrupt a coefficient in the mixed up-down-run / inverse-left-peak row.
            T[5][3][2]+=1
            try:
                verify_extraction(n,T)
            except AssertionError:
                pass
            else:
                raise AssertionError("corrupted coefficient accepted")
    assert real_simple_off_zero([2,3,1]) and not real_simple_off_zero([2,2,1])
    print(f"PASS: literal permutations through 8; all seven source transforms through 10"
          f"; first non-elementary rows reconstructed through 39; integer Sturm through {limit}; mutations rejected")


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv)>1 else 39)
