"""Replay sign-profile mixing cuts and integer LP duals. No numerical libraries."""
from math import comb,isqrt
from fractions import Fraction
D=10**6
W=10**10
def check(ok,msg):
    if not ok:raise ValueError(msg)
def amplification(n,k,r,v,lo):
    """Nondisjoint pairs are ignored. Every retained pair sees a product
    of bipartite Kneser couplings under independent relabelings."""
    t=n-r
    check(v and all(j in lo for j in v),'stratum support')
    check(sum(v)>=r and len(v)*k-sum(v)<=t,'not a cover')
    offset=0;sets=[]
    for j in v:
        sets.append({u%r for u in range(offset,offset+j)})
        offset+=j
    def rho2(m,i,j):
        if i*j==0:return Fraction(0)
        check(i+j<=m,'disjoint pair sizes')
        return Fraction(i*j,(m-i)*(m-j))
    edges=[]
    for i in range(len(v)):
        for h in range(i):
            if sets[i]&sets[h]:continue
            a,b=v[i],v[h];x,y=lo[a],lo[b]
            z=max(rho2(r,a,b),rho2(t,k-a,k-b))*x*(D-x)*y*(D-y)
            top=-(-z.numerator//z.denominator)
            sq=isqrt(top);sq+=sq*sq<top
            g=(x*y-sq)//D
            if g>0:edges.append((g,i,h))
    forest=list(range(len(v)))
    def root(i):
        while forest[i]!=i:i=forest[i]
        return i
    gain=D
    for g,i,h in sorted(edges,reverse=True):
        i,h=root(i),root(h)
        if i!=h:
            forest[i]=h
            gain+=g
    return gain
def check_spectral(n,k,t,obj):
    check(type(n)is int and type(k)is int and type(t)is int and 0<k<n and 0<=t<=comb(n,k),'parameters')
    check(obj.get('kind')=='SPEC1' and len(obj['cells'])==n-1,'cells')
    N=comb(n,k)
    for r,cell in enumerate(obj['cells'],1):
        J=range(max(0,k-(n-r)),min(k,r)+1)
        C={j:comb(r,j)*comb(n-r,k-j) for j in J}
        lo={j:D if j==k else 0 for j in J}
        def bound(proof,objvec):
            residual={j:W*objvec[j] for j in J};lhs=0
            for w,key in proof:
                check(type(w)is int and w>=0 and isinstance(key,str),'row format')
                if key=='H':
                    # Under the negation of the target, counts are integral.
                    lhs-=w*D*(t-1)
                    for j in J:residual[j]+=w*C[j]
                elif key.startswith('M'):
                    j=int(key[1:])
                    check(j in J and j+1 in J,'bad monotone swap')
                    residual[j]+=w*N
                    residual[j+1]-=w*N
                elif key.startswith('P'):
                    v=list(map(int,key[1:].split(',')))
                    gain=amplification(n,k,r,v,lo)
                    lhs+=w*N*gain
                    for j in v:residual[j]-=w*N
                else:raise ValueError('unknown row '+key)
            # p_0=0, p_k=1; 0<=p_j<=1 otherwise.
            return lhs+D*sum(z if j==k else 0 if j==0 else min(0,z) for j,z in residual.items())
        for updates in cell['rounds']:
            nxt=lo.copy()
            for s,proof in updates.items():
                j=int(s)
                check(j in J,'updated stratum')
                z=bound(proof,{i:N*int(i==j) for i in J})//(N*W)
                nxt[j]=max(lo[j],z)
                check(nxt[j]<=D,'bound out of probability range')
            lo=nxt
        z=bound(cell['final'],C)
        check(z>D*W*(t-1),f'open spectral cell r={r}, target={t}')
    return True
