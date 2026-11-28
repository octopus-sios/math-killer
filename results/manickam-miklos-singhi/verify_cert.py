#!/usr/bin/env python3
"""Standalone integer certificate checker. No numerical library, solver or
trusted lookup table. See REPORT.md for the counting and Farkas rules."""
import argparse, functools, math, pathlib, sys
from collections import Counter
from dataclasses import dataclass
sys.setrecursionlimit(12000)
class Invalid(ValueError): pass
def check(ok, msg):
    if not ok: raise Invalid(msg)
def choose(a,b):
    return 0 if not 0 <= b <= a else math.comb(a,b)
def depname(n,k,t): return f"m_{n}_{k}_{t}.cert"
def precedes(s,t):
    while s:
        if (s&-s)>(t&-t):return False
        s&=s-1;t&=t-1
    return True
def parse(line):
    try: return list(map(int,line.split()))
    except ValueError as e: raise Invalid("invalid integer") from e

class Geometry:
    """Independent count of an integer union of coordinate-wise downsets."""
    def __init__(self,n,k):
        self.n,self.k=n,k
        self.H=sum(128<<(8*i) for i in range(k))
        @functools.lru_cache(maxsize=150000)
        def left(p):
            # Number of strictly increasing strings with index i at most cap_i;
            # variable-length DP counts allowed positions of the latest index.
            ways=[1]
            for i in range(k):
                cap=p>>(8*i)&255
                accum=0; row=[0]*(cap+1)
                for j in range(1,cap+1):
                    if j-1<len(ways): accum+=ways[j-1]
                    row[j]=accum
                ways=row
            return sum(ways)
        self.left=left
        @functools.lru_cache(maxsize=100000)
        def pack(s):
            check(s>0 and s>>n==0 and s.bit_count()==k,f"invalid {k}-set mask {s}")
            return sum(v<<(8*j) for j,v in enumerate(i+1 for i in range(n) if s>>i&1))
        self.pack=pack
    def intersect(self,a,b):
        high=(((a|self.H)-b)&self.H)>>7
        return a ^ ((a^b)&(255*high))
    def append(self,w,p):
        out=w.copy()
        out[p]=out.get(p,0)+1
        for q,c in w.items():
            j=self.intersect(q,p);out[j]=out.get(j,0)-c
        return {q:c for q,c in out.items() if c}
    def within(self,w,r):
        return sum(c*self.left(self.intersect(q,r)) for q,c in w.items())
    def total(self,w): return sum(c*self.left(q) for q,c in w.items())

class BitGeometry:
    """Integer bitsets indexed by combinatorial-number-system (colex) rank.
    Independent implementation of every closure/overlap count."""
    def __init__(self,n,k):
        self.n,self.k=n,k; self.empty=0
        self.pack=Geometry(n,k).pack
        table={}
        for j in range(k):
            for bound in range(1,n+1):
                @functools.lru_cache(maxsize=None)
                def bits(m,r):
                    if r>m: return 0
                    if bound>=m: return (1<<choose(m,r))-1
                    if j==r-1:return (1<<choose(bound,r))-1
                    return sum(bits(v,r-1)<<choose(v,r) for v in range(r-1,m))
                table[j,bound]=bits(n,k);bits.cache_clear()
        N=choose(n,k)
        @functools.lru_cache(maxsize=max(50,min(4000,100000000*8//N)))
        def ideal(p):
            chunks=[table[i,(p>>(8*i))&255] for i in range(k)]
            chunks.sort(key=int.bit_length);u=chunks[0]
            for v in chunks[1:]:u&=v
            return u
        self.ideal=ideal
    def append(self,w,p): return w|self.ideal(p)
    def total(self,w): return w.bit_count()
    def within(self,w,p): return (w&self.ideal(p)).bit_count()

class Checker:
    def __init__(self):
        self.proved=set();self.count=Counter()
    def verify(self,path,expect=None):
        path=pathlib.Path(path)
        with path.open() as f:
            hdr=f.readline().split()
            check(len(hdr)==5 and hdr[0]=="MMS1","invalid header")
            n,k,t,h=map(int,hdr[1:])
            check(1<=k<=8 and k<n<=38 and 0<t<=choose(n-1,k-1) and 0<=h<=1000,"invalid theorem parameters")
            if expect is not None: check(expect==(n,k,t),"wrong dependency theorem")
            key=(path.resolve(),n,k,t)
            if key in self.proved: return n,k,t
            src=[]
            for i in range(h):
                d=parse(f.readline());check(len(d)==3,"bad dependency line")
                m,j,z=d
                check(0<j<m and 0<z and (m<n or (m==n and j<k)),"dependency not smaller")
                self.verify(path.with_name(depname(m,j,z)),tuple(d));src.append(tuple(d))
            # Divisibility bound via averaging ordered partitions into j-sets.
            for m in range(1,n+1):
                for j in range(1,m+1):
                    if m%j==0: src.append((m,j,choose(m-1,j-1)))
            def lower(m,j):
                check(0<=j<=m,"invalid deletion instance")
                return max([1]+[v for a,b,v in src if
                    (b<=j and a-b<=m-j) or (a-b<=j and b<=m-j)])
            bitmode=path.stat().st_size>4000 and choose(n,k)<=1700000
            g=BitGeometry(n,k) if bitmode else Geometry(n,k)
            allones=lambda j:(1<<j)-1
            # For cuts use the two largest strictly increasing quotas of each
            # kind. Include ALL equally-valued strongest (smallest q) positions.
            quotas=[[],[],[]]
            for typ in range(3):
                jj=k-(typ==2);qmax=n-k if typ==1 else n-1
                prev=0
                for q in range(jj,qmax+1):
                    v=lower(q,jj)
                    if v<=prev: continue
                    prev=v
                    if typ==0:
                        r=allones(k)<<(q-k); sub=0
                    elif typ==1:
                        r=allones(k)<<(q+1-k);sub=1|(allones(k-1)<<(q+2-k))
                    else:
                        r=1|(allones(k-1)<<(q+2-k));sub=0
                    quotas[typ].append((v,g.pack(r),g.pack(sub) if sub else 0))
            # Use all proven quotas: if solver learned a redundant dependency,
            # another proven quota cannot invalidate its bound.
            quotas=[s[::-1] for s in quotas]
            def enough(w):
                base=g.total(w)
                if base>=t:return True
                extra=[]
                for qlist in quotas:
                    deficit=0
                    for v,r,e in qlist:
                        if v<=deficit:break
                        num=g.within(w,r)
                        if e:num-=g.within(w,e)
                        deficit=max(deficit,v-num)
                        if base+deficit>=t:return True
                    extra.append(deficit)
                return base+extra[1]+extra[2]>=t
            pset=set();nset=set();ln=h+1
            def tree(w):
                nonlocal ln
                line=f.readline();ln+=1
                items=line.split()
                check(bool(items),f"missing proof node at {ln}")
                op=items[0];self.count[op]+=1
                if op=="T":
                    check(len(items)==1 and lower(n,k)>=t,"unproved inheritance/divisibility")
                elif op=="G":
                    check(len(items)==2,"invalid block lift")
                    fac=int(items[1]);check(fac>=2 and n%fac==0 and k%fac==0,"invalid block size")
                    nn,jj=n//fac,k//fac
                    z=lower(nn,jj)
                    check((choose(n,k)*z+choose(nn,jj)-1)//choose(nn,jj)>=t,"block lift too weak")
                elif op=="C":
                    check(len(items)==1 and enough(w),"insufficient closure count")
                elif op=="B":
                    check(len(items)==2,"bad branch arity")
                    s=int(items[1]);a=g.pack(s)
                    check(s not in nset and s not in pset,"repeated branch")
                    nset.add(s);tree(w);nset.remove(s)
                    pset.add(s);tree(g.append(w,a));pset.remove(s)
                elif op=="F":
                    check(len(items)>=3 and len(items)%2==1,"malformed Farkas certificate")
                    # Original-coordinates combination. Let c=sum signed rows.
                    # Need c dot x <=0 on the cone of sorted nonnegative-total x.
                    coeff=[0]*n;strict=0
                    for i in range(1,len(items),2):
                        s,z=int(items[i]),int(items[i+1]);a=g.pack(abs(s))
                        check(z>0,"nonpositive multiplier")
                        if s<0:
                            strict+=z
                            if -s not in nset and not any(precedes(a,-s) for a in nset):
                                check(enough(g.append(w,a)),f"unsupported negative row {-s} at {ln}")
                            scale=-z
                        else:
                            check(s in pset or any(precedes(s,a) for a in pset),f"unsupported positive row {s}")
                            scale=z
                        mask=abs(s)
                        while mask:
                            bit=mask&-mask;coeff[bit.bit_length()-1]+=scale;mask-=bit
                    tot=sum(coeff)
                    check(strict>0 and tot<=0,"invalid strict/total multiplier")
                    partial=0
                    for j,c in enumerate(coeff[:-1],1):
                        partial+=c
                        check(n*partial<=j*tot,f"invalid gap multiplier at {ln}, gap {j}")
                else: raise Invalid(f"unknown node {op!r} at {ln}")
            tree(0 if bitmode else {})
            check(not f.read().strip(),"trailing certificate data")
            self.proved.add(key);return n,k,t
def main():
    parser=argparse.ArgumentParser(__doc__);parser.add_argument("files",nargs="+",type=pathlib.Path)
    args=parser.parse_args()
    c=Checker()
    for p in args.files:
        n,k,t=c.verify(p)
        check(p.name==depname(n,k,t),"file/theorem name mismatch")
        print(f"PASS g({n},{k}) >= {t}",flush=True)
    print(f"{len(c.proved)} certificates; proof node counts {dict(c.count)}")
if __name__=="__main__":
    try:main()
    except (ValueError,OSError,RecursionError) as e:
        print("REJECT:",e,file=sys.stderr);sys.exit(1)
