"""Exact verifier of the finite inequalities in PROOF_BERNOULLI.md.
Integer/Fraction arithmetic, including the vectorized Bellman updates.
No probability table, external solver, transcendental library, or float input.
Usage: python3 verify_constants.py   (requires NumPy)
"""
from fractions import Fraction as F
from math import isqrt,gcd
from functools import lru_cache
import argparse,sys
import numpy as np

# Q stores probabilities, S stores only scalar analytic enclosures.
Q=10**7
S=10**9
R=10**6 # square-root enclosure scale in branching
H=16 # integration mesh denominator for characteristic functions

def ceildiv(a,b): return -((-a)//b)
def floorf(x): return x.numerator//x.denominator
def ceilf(x): return ceildiv(x.numerator,x.denominator)
def ceilroot(a):
    x=isqrt(a); return x+(x*x<a)
def root_down(x,s):
    return isqrt(floorf(x*s*s))
def root_up(x,s):
    a=root_down(x,s); return a+(a*a!=x*s*s)
def mulup(a,b): return ceildiv(a*b,S)
def muldn(a,b): return (a*b)//S

def expup(x): # exp(-x/S) upper, in units 1/S
    assert x>=0
    y=ceildiv(S*S*4096,4096*S+x)
    for i in range(12): y=mulup(y,y)
    return y

def expdn(x): # lower
    y=max(0,S-ceildiv(x,4096))
    for i in range(12): y=muldn(y,y)
    return y

def baseline():
    # Machin: pi/4=4 atan(1/5)-atan(1/239), from the tangent addition formula.
    def ar(q,n):
        return sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
    pi_lo=16*ar(5,4)-4*ar(239,3); pi_hi=16*ar(5,3)-4*ar(239,2)
    assert F(25,8)<pi_lo<=pi_hi<F(22,7)
    assert 2*pi_hi*F(3988,10000)**2<1<2*pi_lo*F(2,5)**2
    assert pi_hi*F(2,5)<F(44,35)
    assert (3+F(23,50))**2<12
    # Sharp Fourier multiplier and fourth-degree moment tensor bound
    assert F(1,2)<4*F(1,2)*F(7,8)
    for k in range(1000):
        t,u=F(k,1000),F(k+1,1000)
        # pi t A <= 1 - pi^2 t^2(1-t)/3, positive on [0,1].
        assert F(22,7)**2*F(4,27)/3<1
        assert (1-pi_lo**2*t*t*(1-u)/3)**2+pi_hi**2*u*u*(1-t)**2<F(21,20)**2
    assert F(12,35)+F(7,60)<F(23,50)
    assert F(23,50)>F(3,4)*(F(1,8)+F(9,20))
    assert F(1,5)*F(5,3)==F(1,3)
    assert F(3,8)+6*(F(3,8)-F(1,7))**2/F(3,8)>F(55,49)
    assert (F(3,4)-F(3,8))**2>F(1,6)*(1-F(3,8))

@lru_cache(None)
def normal(D,G):
    X=D*G
    a=[0]*(2*X+1); a[X]=Q//2
    pos=neg=0
    for j in range(1,X+1):
        # right integral lower, left integral upper
        neg+=3988*expdn(ceildiv(S*j*j,2*D*D))
        pos+=4000*expup((S*(j-1)*(j-1))//(2*D*D))
        a[X-j]+=Q//2+neg*Q//(10000*S*D)
        a[X+j]=max(0,Q//2-ceildiv(pos*Q,10000*S*D))
    return np.asarray(a,dtype=np.int64)

@lru_cache(None)
def spectralerrors(B,low,high):
    # Cache by a containing 1/40 probability band if possible.
    pq=min(low*(1-low),high*(1-high))
    ma=max(low*low+(1-low)**2,high*high+(1-high)**2)
    out=[0]
    for k in range(1,B+1):
        b=F(k,B); b2u=ceilf(S*b*b); b2l=floorf(S*b*b)
        dd=root_up(b*b/pq,S) # upper delta
        aa=ceilf(ma*dd)
        third=ceilf(max(abs(1-2*low),abs(1-2*high))*dd)
        fourth=ceilf(max(abs(1-6*pq), abs(1-6*min(F(1,4),high*(1-high))) )*F(dd**2,S))
        fifth=ceilf(max(low**4+(1-low)**4,high**4+(1-high)**4)*F(dd**3,S*S))
        sixth=ceilf(b**4*S)
        # cap frequency at 40, and t*delta <=11/2
        steps=min(40*H, (11*H*S)//(2*dd))
        e=S; h1=h2=0
        for j in range(1,steps+1):
            # t in [(j-1)/H,j/H], y_hi=(j/H)*dd/(2*S)
            yu=ceildiv(j*j*dd*dd,4*H*H*S) # y_hi^2 upper
            yl=(j*j*dd*dd)//(4*H*H*S)
            sinc=max(0, S-ceildiv(yu,6)+yl*yl//(120*S)-ceildiv(yu**3,5040*S*S))
            ds=muldn(sinc,sinc)
            xl=ds*(j-1)**2//(2*H*H)
            g=expup(muldn(S-b2u,xl))
            z=expup(xl)+expup(S*(j-1)**2//(2*H*H))
            # m bounds |cf difference| / t in 1/S units.
            m=mulup(g,min(ceildiv(aa*j*j,6*H*H)+ceildiv(b2u*j**3,8*H**3),
                ceildiv(third*j*j,6*H**2)+ceildiv(fourth*j**3,24*H**3)+
                ceildiv(fifth*j**4,120*H**4)+ceildiv(sixth*j**5,48*H**5)))
            h1+=min(m,ceildiv(z*H,j-1)) if j>1 else m
            h2+=min(z,ceildiv(j*m,H))
            if j%H==0: # T=j/H, min of rigorous candidate errors
                val=ceildiv(44*H*S,35*j)+min(ceildiv(h1,3*H)+ceildiv(h2,j),ceildiv(21*8*h1,20*25*H))
                e=min(e,val)
        out.append(ceildiv(e*Q,S))
    return np.array(out,dtype=np.int64)

def bands(lo,hi): # enlarge parameter interval for reusable smoothing bounds only
    return F(floorf(40*lo),40),F(ceilf(40*hi),40)

class Table:
    def __init__(self,lo,hi,B,D,G,K):
        assert F(1,8)<=lo<=hi<=F(1,2)
        assert 0<B<=512 and 0<D<=512 and 1<=G<=16 and 1<=K<=256
        self.B=B;self.D=D;self.G=G;self.X=X=D*G;self.N=N=2*X+1
        self.lo=lo; self.hi=hi
        # Explicit uint-free signed bounds. Scalar operations use Python int.
        # Indices, threshold numerators, probability averages fit signed int64.
        assert max(hi.denominator,lo.denominator)*Q<2**62
        j=np.arange(-X,X+1,dtype=np.int64)
        err=spectralerrors(B,*bands(lo,hi))
        cant=(np.minimum(0,j)**2*Q)//(D*D+j*j)
        sg=np.array([Q-ceildiv(Q*expup(S*i*i//(2*D*D)),S) if i<0 else 0 for i in map(int,j)],dtype=np.int64)
        cant=np.maximum(cant,sg)
        base=np.maximum(cant[None,:],normal(D,G)[None,:]-err[:,None])
        base[0,:]=Q # empty domain for positive norm and cap zero
        f=base.copy()
        self.g=root_up(hi/(1-hi),R); self.d=root_down((1-hi)/hi,R)
        assert self.g<=R and self.d<=3*R
        # lookup indices for all shells and thresholds; sentinel row-end for zero
        n0=np.zeros_like(f);n1=np.zeros_like(f)
        for k in range(1,B+1):
            vl=isqrt((B*B-k*k)*R*R)
            vh=ceilroot((B*B-(k-1)**2)*R*R)
            cap=min(B,ceildiv(k*R*B,vl)) if vl else B
            for a,y in [(j*R*B+D*self.g*k,n0),(j*R*B-D*self.d*(k-1),n1)]:
                jj=np.where(a<0,-((-a)//vh),
                            -((-a)//vl) if vl else X+1)
                y[k]=np.where(jj>X,(B+1)*N,cap*N+X+np.maximum(-X,jj))
        a,b=lo.as_integer_ratio()
        for it in range(K):
            ff=np.append(f.reshape(-1),np.int64(0))
            v=(a*ff[n1]+(b-a)*ff[n0])//b
            # previous row is valid for the whole ball so valid on this shell
            v=np.maximum(f,v)
            f=np.minimum.accumulate(v,axis=0)
        self.f=f
        assert f.min()>=0 and f.max()<=Q and np.all(f[:,:-1]>=f[:,1:])

def mix_threshold(lo,hi,aux):
    # Largest J (units 1/1000) for which all L in [0,J/1000] satisfy
    # B_r(L) < aux/(Q*r). Uses a lower bound for P_r(strict success).
    r=hi/(1-hi); s=lo/(1-lo)
    beta=F(aux,Q)/r
    for j in range(1000):
        a,b=F(j,1000),F(j+1,1000)
        d=beta-(1+(r-r*r)/2)*b
        if d<=0 or 4*d*d<=(1+r)**2*r*(1-a)*(1-s*a):
            if b*r*r>=F(aux,Q)**4:return j
    return 1000

def classify(T,aux,U,depth,mutation=False):
    # sorted prefix boxes, coefficient grid 1/U. Threshold numerators in 1/(U*R).
    lo,hi=T.lo,T.hi
    a,b=lo.as_integer_ratio(); goal=hi*Q
    J=mix_threshold(lo,hi,aux)
    if mutation: J=0; goal=Q # corrupted claimed lower bound (probability one)
    X,N,B,D=T.X,T.N,T.B,T.D
    f=T.f.tolist()
    visits=[0]*(depth+1); leaves=[0,0]; worst=None
    probs=[[1]]
    for h in range(depth): probs.append([c*n for c in probs[-1] for n in (b-a,a)])
    def rec(path,sl,sh,arr):
        nonlocal worst
        h=len(path); visits[h]+=1; mx=path[-1] if path else U
        zl=isqrt(max(0,U*U-sh)*R*R)
        zh=ceilroot((U*U-sl)*R*R)
        cap=min(B,ceildiv(mx*R*B,zl)) if zl else B; row=f[cap]
        vals=[]
        for z in arr:
            y=ceildiv(z*D,zh) if z<0 and zh else (-X if z<0 else (ceildiv(z*D,zl) if zl else X+1))
            vals.append(0 if y>X else row[X+max(-X,y)])
        if h==1 and (Q-vals[1])*1000<=Q*J and J>0:
            leaves[0]+=1; return True
        num=sum(c*v for c,v in zip(probs[h],vals))
        if num*goal.denominator>b**h*goal.numerator:
            leaves[1]+=1;return True
        if h==depth:
            worst=(path,F(num,Q*b**h)); return False
        for k in range(1,mx+1):
            nl=sl+(k-1)**2
            if nl>U*U:break
            bu=k*T.g; su=(k-1)*T.d
            if not rec(path+(k,),nl,sh+k*k,[x+y for x in arr for y in (bu,-su)]):
                return False
        return True
    ok=rec((),0,0,[0])
    return ok,(visits,leaves),worst

def run_interval(lo,hi,B,D,G,K,U,depth,mutation=False):
    T=Table(lo,hi,B,D,G,K)
    rlo=lo/(1-lo);rhi=hi/(1-hi)
    V=Table(rlo,rhi,B,D,G,K)
    return classify(T,int(V.f[B,V.X]),U,depth,mutation)

def main():
    pa=argparse.ArgumentParser()
    pa.add_argument('--lo',type=F,default=F(1,7))
    pa.add_argument('--hi',type=F,default=F(3,10))
    pa.add_argument('--mesh',type=int,default=200)
    pa.add_argument('--B',type=int,default=128)
    pa.add_argument('--D',type=int,default=150)
    pa.add_argument('--G',type=int,default=10)
    pa.add_argument('--K',type=int,default=32)
    pa.add_argument('--U',type=int,default=180)
    pa.add_argument('--depth',type=int,default=5)
    pa.add_argument('--subdivide',type=int,default=6)
    pa.add_argument('--mutation-test',action='store_true')
    args=pa.parse_args()
    if not __debug__: raise RuntimeError("run without python -O")
    baseline()
    def check(lo,hi,lev):
        ok,counts,w=run_interval(lo,hi,args.B,args.D,args.G,args.K,args.U,args.depth,args.mutation_test)
        if not ok and lev and not args.mutation_test:
            mid=(lo+hi)/2
            check(lo,mid,lev-1);check(mid,hi,lev-1);return
        print(f"{lo}..{hi}: {'PASS' if ok else 'FAIL'} {counts} {w or ''}",flush=True)
        if not ok: raise SystemExit(1)
    assert F(1,7)<=args.lo<=args.hi<=F(1,3) and args.mesh>=1
    p=args.lo
    if p==args.hi:check(p,p,0)
    while p<args.hi:
        q=min(args.hi,F(floorf(p*args.mesh)+1,args.mesh))
        check(p,q,args.subdivide);p=q
    print("PASS baseline and all requested interval inequalities")

if __name__=="__main__":main()
