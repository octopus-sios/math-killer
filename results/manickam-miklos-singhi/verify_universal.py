#!/usr/bin/env python3
"""Exact audit of the seven-k theorem in PROOF_UNIVERSAL.md.
Run: python3 verify_universal.py
No numerical optimization, finite-k cutoff, or external dependency.
All rejected certificates raise errors also under python -O.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import comb

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

# (p_lo, p_hi, target r, required complement r_c, beta, Amax, Hmax, h-cells)
# Cell left boundary is the previous right boundary; final boundary must be Hmax.
# Each cell: (1000*h_right, 100*z, 100*u).
S6 = Q(87,100)
S5 = Q(69,100)
ROWS = (
    (Q(0),Q(1,7),S6,S5,Q(588,1000),Q(324,1000),Q(737,1000),((737,69,60),)),
    (Q(1,7),Q(1,6),S6,S5,Q(560,1000),Q(369,1000),Q(748,1000),((540,75,57),(748,70,64))),
    (Q(0),Q(1,8),Q(1),S6,Q(644,1000),Q(271,1000),Q(756,1000),((756,67,63),)),
    (Q(1,8),Q(1,7),Q(1),S6,Q(247,400),Q(306,1000),Q(764,1000),((459,70,54),(604,68,58),(764,64,68))),
)

def floor6(x):
    return (x*10**6).__floor__()

def base():
    # For u <= 69/80 the discriminant expression increases with u,
    # and is convex as a function of w in [0,1/6].
    z=Q(69,80)
    for w in (Q(0),Q(1,6)):
        need((1-6*w+Q(9,4)*w*w)*z*z+Q(9,2)*w*z<Q(3,4),"base discriminant")
    need(z*(1-Q(1,5))==S5 and Q(4,25)<Q(1,6),"base scale")

def dual(z,u):
    need(z>0 and u>0,"invalid contact points")
    d=z+z*(z+u)/(3*z+u)
    c=(3*z+u)/(z*z*(z+u)**3)
    lam=2*u-d
    need(lam>=0,"dual sign")
    need(c*z*(z+u)**2*(d-z)==1,"value at positive contact")
    need(-4*z*z+(3*d-2*u)*z+u*d==0,"stationary positive contact")
    return c,lam,2*u*d-u*u

def row_check(row):
    lo,P,r,rc,b,A,H,cells=row
    need(0<=lo<P<=Q(1,5) and 0<rc<=1 and 0<r<=1,"stage parameters")
    v=1-P; T=P/v; W=P*v; gl=1-2*P; gh=(1-2*lo)/(1-lo)
    y=b+r-1; zeta=y/b
    need(0<=y<rc and y<=b<1 and T*zeta<=4*(1-b),"mixing monotonicity")
    need((rc-y)**2>T*(1-b)*zeta,"bad-star lower bound")
    need(0<=A and P*(1-b)<=A*A*(v*b+P*(1-b)),"positive cap")
    need(0<H<=1 and r<=H*H*v*(1+r),"negative cap")
    need(A*A<=Q(1,2) and W<=Q(1,6) and 0<gl<=gh<=1,"moment parameters")
    left=Q(0); out=[]
    for hr,zi,ui in cells:
        right=Q(hr,1000)
        need(left<right<=H,"cell bounds/order")
        c,lam,I=dual(Q(zi,100),Q(ui,100))
        plus=3*W+(1-6*W)*A*A+lam*gh*A
        need(plus>=3*W,"endpoint proof hypothesis")
        def lb(h):
            minus=max(3*w+(1-6*w)*h*h-lam*gl*h for w in (0,W))
            cap=max(minus, h*h*minus+(1-h*h)*plus)
            return v*c*(I-cap)
        L=min(lb(left),lb(right))
        need(L>=r, "quartic certificate failed: "+str((left,right,zi,ui,L,r)))
        out.append(floor6(L))
        left=right
    need(left==H,"uncovered negative maximum")
    return out

def certificate(rows=ROWS):
    base()
    # Logical dependency/coverage checks: p' = p/(1-p).
    regions=[(Q(1,5),S5)]
    pending=None
    endpoint=Q(0); result=[]
    for row in rows:
        lo,P,r,rc,*_=row
        if pending!=r:
            if pending is not None:
                regions.append((endpoint,pending))
            pending=r
            endpoint=0
        need(lo==endpoint,"gap in density interval")
        need(any(P/(1-P)<=bound and rc<=val for bound,val in regions),
             "unjustified complement input")
        result.append(row_check(row))
        endpoint=P
    need(endpoint==Q(1,7) and pending==1,"theorem not reached")
    return result

def ff(x,j):
    r=1
    for i in range(j):
        r*=x-i
    return r

def polynomial_identities():
    """Exact polynomial identity test, not testing a finite range of the theorem.

    Clearing the common (n)_4 denominator in (1) gives polynomials of
    degree <=4 in EACH of n,k. A polynomial of coordinate degree <=4
    vanishing at a Cartesian 5x5 grid vanishes identically: apply the
    univariate root bound in n at fixed k and then to each coefficient in k.
    """
    for n in range(10,15):
        for k in range(1,6):
            h=[ff(k,j)*ff(n-j,4-j) for j in range(5)] # (n)_4*pi_j
            pv=k*(n-k)*(n-2)*(n-3)
            pvg=k*(n-k)*(n-2*k)*(n-3)
            pvw=k*(n-k)*(k-1)*(n-k-1)
            need(h[1]-h[2]==pv,"second moment identity")
            need(h[1]-3*h[2]+2*h[3]==pvg,"third moment identity")
            need(h[2]-2*h[3]+h[4]==pvw,"paired fourth moment identity")
            need(h[1]-7*h[2]+12*h[3]-6*h[4]==pv-6*pvw,"singleton fourth moment identity")
            # The numerator in w<=p(1-p) is positive at n>=5k
            # because k(n-k)/n^2 <= 4/25 < (n-1)/(5n-6).
            need(k*(n-k)*(n-2)*(n-3)-n*n*(k-1)*(n-k-1)
                 ==n*n*(n-1)-k*(n-k)*(5*n-6),"w estimate identity")
    # Clearing the denominators of the backup 3k^2 comparison at n=3k^2
    # in the Appendix produces polynomials of degree <=4 in k.
    for k in range(1,6):
        n=3*k*k
        need((n-1-(2*k-1)*(k-1))*(n-k)-k*k*(n-1)==2*k*(2*k-1)**2,
             "independent quadratic backup")

def identity_checks():
    # Coefficient identities are proved for all n,k in the text; also test
    # actual consumer (sum over subsets), including vanishing pi_3, pi_4.
    # Inputs are not normalized here.
    tested=0
    for n,k in ((6,2),(8,3),(11,4),(14,2),(12,5)):
        # Outside the certificate range is intentional for algebra checks.
        p=Q(k,n); v=Q(n-k,n-1); g=Q(n-2*k,n-2)
        w=Q((k-1)*(n-k-1),(n-2)*(n-3))
        for seed in (1,2,3,4,5):
            x=[(i**3+7*seed*i*i+seed*seed*i+1)%(7+seed) for i in range(n)]
            x=[n*a-sum(x) for a in x]
            vals=[sum(x[i] for i in S) for S in combinations(range(n),k)]
            m=[Q(sum(y**j for y in vals),len(vals)) for j in (2,3,4)]
            V=sum(y*y for y in x); S3=sum(y**3 for y in x); S4=sum(y**4 for y in x)
            need(m==[p*v*V,p*v*g*S3,p*v*((1-6*w)*S4+3*w*V**2)],"slice moment counts")
            tested+=1
    # Test the disjointness action on every inclusion basis vector on a
    # complete finite slice, including the top degree with zero eigenvalue.
    m,a,b=8,2,3
    for j in range(b+1):
        for U in combinations(range(m),j):
            U=set(U)
            for A in combinations(range(m),a):
                rem=set(range(m))-set(A)
                count=sum(U<=set(B) for B in combinations(rem,b))
                coeff=Q(ff(b,j),ff(m-a,j))
                inc_exc=sum((-1)**len(J) for s in range(j+1)
                            for J in combinations(U,s) if set(J)<=set(A))
                need(Q(count,comb(m-a,b))==coeff*inc_exc,"disjoint operator inclusion basis")
    return tested

if __name__=="__main__":
    polynomial_identities()
    print("Symbolic moment identities and quadratic-backup identity: PASS (root-count certificate)")
    result=certificate()
    for row,res in zip(ROWS,result):
        print(f"p in [{row[0]}, {row[1]}], r={row[2]}: certified lower bounds x10^6 (floored) {res}")
    print("finite cross-checks of exact slice moments:",identity_checks(),
          "; disjoint-operator inclusion basis: PASS")
    for mutation in ("quartic","mixing","coverage"):
        bad=list(ROWS); a=list(bad[-1])
        if mutation=="quartic": a[7]=((459,70,54),(604,50,58),(764,64,68))
        if mutation=="mixing": a[4]=Q(2,3)
        if mutation=="coverage": a[0]=Q(13,100)
        bad[-1]=tuple(a)
        try: certificate(bad)
        except ValueError as exc:
            print("corruption detected:",mutation,str(exc)[:150])
        else:
            raise AssertionError("undetected corrupted "+mutation+" certificate")
    print("PASS: the rational interval certificates cover EVERY k>=2 and n>=7k; k=1 is immediate.")
