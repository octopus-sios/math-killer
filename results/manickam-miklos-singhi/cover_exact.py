"""Integer checker for sign-stratified pseudo-matching certificates (no solver).
Each P-row lists positive counts of k-sets. Cycle positive labels through the
positive slots; use distinct negative labels. Thus positives are covered and
negatives do not repeat. At least one edge is nonnegative. Permute within the
two classes: each edge with j positives is uniform within stratum j.
"""
from math import comb
import json

def require(v, msg):
    if not v: raise ValueError(msg)

def support(n,k,r):
    return range(max(0,k-(n-r)), min(k,r)+1)

def bound(n,k,r,rows,den):
    J=support(n,k,r)
    residual={j:den*comb(r,j)*comb(n-r,k-j) for j in J}
    rhs=0
    for row in rows:
        w,typ,*v=row
        require(type(w) is int and w>=0 and all(type(i) is int for i in v),'multipliers or entries')
        if typ=='P':
            require(v and all(j in J for j in v),'inadmissible stratum')
            require(sum(v)>=r and k*len(v)-sum(v)<=n-r,'not a pseudo-matching')
            for j in v: residual[j]-=w
            rhs+=w
        elif typ=='M':
            require(len(v)==1 and v[0] in J and v[0]+1 in J,'monotone stratum')
            j=v[0];residual[j]+=w;residual[j+1]-=w
        else: raise ValueError('unknown cover rule')
    # 0 <= p_j <= 1, p_0=0 (all-negative), p_k=1 (all-nonnegative)
    rhs+=sum(v if j==k else 0 if j==0 else min(0,v) for j,v in residual.items())
    return -((-rhs)//den)

def check_cover(n,k,t,obj):
    if obj.get('kind')=='SPEC1':
        from spectral_exact import check_spectral
        return check_spectral(n,k,t,obj)
    require(type(n) is int and 1<=k<n and t>=0,'domain')
    den=obj['den'];cells=obj['cells']
    require(type(den) is int and den>0 and len(cells)==n-1,'coverage')
    # r=0 impossible for nonnegative total; r=n trivial.
    require(t<=comb(n,k),'trivial all-positive case')
    for r,rows in enumerate(cells,1):
        lb=bound(n,k,r,rows,den)
        require(lb>=t,f'stratum r={r}: {lb} < {t}')
    return True

if __name__=='__main__':
    import sys
    for file in sys.argv[1:]:
        with open(file) as f:
            code,n,k,t=f.readline().split()
            require(code=='MMSC1','header')
            obj=json.load(f)
            check_cover(int(n),int(k),int(t),obj)
        print('PASS',file,n,k,t)
