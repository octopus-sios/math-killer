#!/usr/bin/env python3
"""Check finite closure for odd (k+2)-coloring of every k-tree for k=4,5.

python3 verify.py                # both proofs and their negative controls
python3 verify.py --k 5          # just width five
python3 verify.py --k 5 --drop   # damaged table; must fail singleton closure

Integer bitsets only. No external package or SAT solver. Each representative
is a sequence of creation-face IDs: the root face is 0; introducing vertex j
(zero-based) appends faces 1+k*j through k+k*j in slot order.
"""
from functools import cache
from itertools import combinations, permutations
from random import Random
TAB4 = (
  (),
  (0,),
  (0, 4),
  (0, 0, 8),
  (0, 4, 8),
  (0, 4, 7),
  (0, 3, 4),
  (0, 0, 8, 12),
  (0, 3, 4, 10, 13),
  (0, 3, 4, 9, 10),
)
TAB5 = (
  (),
  (0,),
  (0, 5),
  (0, 0, 10),
  (0, 5, 10),
  (0, 5, 9),
  (0, 4, 5),
  (0, 0, 10, 15),
  (0, 5, 5, 14),
  (0, 5, 10, 14),
  (0, 5, 9, 10),
  (0, 5, 9, 15),
  (0, 5, 9, 14),
  (0, 5, 9, 13),
  (0, 5, 8, 9),
  (0, 4, 5, 15),
  (0, 4, 5, 14),
  (0, 4, 5, 13),
  (0, 0, 10, 15, 19),
  (0, 5, 0, 15, 20),
  (0, 5, 5, 15, 20),
  (0, 5, 5, 14, 19),
  (0, 5, 9, 10, 19),
  (0, 4, 5, 5, 20),
  (0, 4, 5, 15, 20),
  (0, 4, 10, 5, 20),
  (0, 4, 10, 5, 18),
  (0, 4, 5, 5, 20, 25),
  (0, 4, 5, 13, 17, 21),
  (0, 4, 5, 13, 16, 17),
  (0, 4, 5, 12, 13, 21),
  (0, 5, 0, 15, 15, 25, 30),
  (0, 4, 5, 15, 5, 25, 30),
  (0, 4, 5, 15, 15, 25, 30),
  (0, 4, 5, 15, 5, 25, 25, 35, 40),
)

import argparse

def decode(k, codes):
    faces=[[]]
    for a in codes:
        assert 0<=a<len(faces)
        children=[[] for _ in range(k)]
        faces[a].append(children)
        faces.extend(children)
    def freeze(face):
        return tuple(sorted(tuple(freeze(c) for c in b) for b in face))
    return freeze(faces[0])

@cache
def permute(f,p):
    new=[]
    for branch in f:
        children=[()] * len(p)
        for i,c in enumerate(branch):
            children[p[i]]=permute(c,p)
        new.append(tuple(children))
    return tuple(sorted(new))
@cache
def size(f):
    return sum(1+sum(map(size,b)) for b in f)

def signatures(f,k,omit=-1):
    """Core is K_k, or K_(k+1) if omit names a face opposite vertex i.
    Core colors equal their indices. Pack each mask in one byte."""
    m=k+(omit>=0)
    base=tuple(k if i==omit else i for i in range(k))
    parents=[]
    def unfold(f,face):
        for b in f:
            u=m+len(parents);parents.append(face)
            for j,c in enumerate(b):
                unfold(c,face[:j]+(u,)+face[j+1:])
    unfold(f,base);n=m+len(parents)
    adj=[[] for _ in range(n)]
    for u,p in enumerate(parents,m):
        for v in p:
            adj[u].append(v);adj[v].append(u)
    colors=list(range(m))+[-1]*len(parents);out=set()
    def go(u):
        if u==n:
            sig=0
            for i,a in enumerate(adj):
                s=0
                for v in a:s ^= 1<<colors[v]
                if i>=m and not s:return
                if i<m:sig|=s<<(8*i)
            out.add(sig)
        else:
            used={colors[j] for j in parents[u-m]}
            for c in range(k+2):
                if c not in used:
                    colors[u]=c;go(u+1)
    go(m)
    return tuple(sorted(out))

def robust(states,m):
    """Is there NO cover by one nonzero slice per coordinate?"""
    if not states:return False
    grouped=[{} for _ in range(m)]
    states=tuple(states)
    for j,s in enumerate(states):
        bit=1<<j
        for d in grouped:
            x=s&255
            if x:d[x]=d.get(x,0)|bit
            s >>= 8
    def visit(rem,avail):
        if not rem:return True
        a=states[(rem&-rem).bit_length()-1];flags=avail
        while flags:
            flag=flags&-flags;i=flag.bit_length()-1;flags^=flag
            x=(a>>(8*i))&255
            if x and visit(rem&~grouped[i][x],avail^flag):return True
        return False
    return not visit((1<<len(states))-1,(1<<m)-1)

def xorprod(cols):
    s={0}
    for col in cols:s={a^b for a in s for b in col}
    return s

class Check:
    def __init__(self,k,reps):
        self.representatives = reps
        self.k=k;self.perms=tuple(permutations(range(k)))
        fs={permute(decode(k,c),p) for c in reps for p in self.perms}
        self.fs=fs=tuple(sorted(fs,key=lambda f:(size(f),f)))
        self.index=idx={f:i for i,f in enumerate(fs)};assert fs[0]==()
        self.act={p:tuple(idx[permute(f,p)] for f in fs) for p in self.perms}
        self.top=tuple(signatures(f,k) for f in fs)
        self.face=tuple(tuple(signatures(f,k,i) for f in fs) for i in range(k))
        self.random=Random(59)
        h=sum(1<<(8*i) for i in range(k))
        self.centerbits=h<<k;self.low=(1<<(8*k))-1

    def terminal(self):
        k=self.k;full=(1<<k)-1
        for rows in self.top:
            if not any(all(((s>>(8*i))&255) != (full^(1<<i)) for i in range(k)) for s in rows):
                raise ValueError("no valid coloring on the bare root clique")
        print("PASS terminal forests:",len(self.fs),flush=True)

    def siblings(self):
        fs=self.fs;n=len(fs);k=self.k;idx=self.index
        enc=lambda f:tuple(sorted(idx[(b,)] for b in f))
        known={enc(f) for f in fs}
        seen=set(known)
        @cache
        def deletable(g):
            return robust(xorprod([self.top[i] for i in g]),k)
        count=0
        for f in known:
            for j in range(1,n):
                if len(fs[j])!=1:continue
                g=tuple(sorted(f+(j,)))
                if g in seen:continue
                if not any(deletable(t) for h in range(1,len(g)+1) for t in combinations(g,h)):
                    raise ValueError(("sibling closure",g))
                seen.update(tuple(sorted(a[i] for i in g)) for a in self.act.values())
                count+=1
        print("PASS unlisted sibling orbits:",count,flush=True)

    def bag_robust(self,ids,with_center):
        k=self.k
        cols=[self.face[i][a] for i,a in enumerate(ids) if a]
        total=1
        for c in cols:total*=len(c)
        def project(states):
            if not with_center:return states
            out=[]
            for s in states:
                if (s>>(8*k))==(1<<k)-1:continue
                a=(s&self.low)^self.centerbits
                d=(a^(a>>1))&self.centerbits
                out.extend((a,a^d^(d<<1)))
            return out
        m=k+int(not with_center)
        # Only early SUCCESS from samples: a non-coverable subfamily certifies all.
        if total>48:
            choice=self.random.choice
            for h in (48,144,480):
                sample=[0]*h
                for c in cols: sample=[a^choice(c) for a in sample]
                if robust(project(sample),m):return True
                if 3*h>=total:break
        return robust(project(xorprod(cols)),m)

    def pairs(self):
        k=self.k;n=len(self.fs);seen=set();weak=set()
        stabilizer=[(self.act[p],p[0]==1) for p in self.perms if {p[0],p[1]}=={0,1}]
        count=0
        for a in range(1,n):
            for b in range(1,n):
                if (a,b) in seen:continue
                orbit={(r[b],r[a]) if rev else (r[a],r[b]) for r,rev in stabilizer}
                seen.update(orbit)
                if not self.bag_robust((a,b),False):weak.update(orbit)
                count+=1
        print("PASS two-face orbit tests:",count,"; retained ordered pairs:",len(weak),flush=True)
        return weak

    def check_single(self, ids, listed):
        if ids not in listed and not self.bag_robust(ids, True):
            raise ValueError(("unlisted irreducible singleton", ids))

    def singles(self,weak,mutation):
        k=self.k;n=len(self.fs)
        # allowed[i,j][a] is the bitset of compatible b labels on face j.
        allowed={}
        for i,j in combinations(range(k),2):
            r=self.act[next(p for p in self.perms if (p[0],p[1])==(i,j))]
            bits=[1]*n;bits[0]=(1<<n)-1
            for a,b in weak:bits[r[a]]|=1<<r[b]
            allowed[i,j]=bits
        known=set()
        for f in self.fs:
            if len(f)==1:known.add(tuple(self.index[g] for g in f[0]))
        if mutation:
            # Remove the last representative and its orbit from the whitelist.
            victim=decode(k,self.representatives[-1])
            deleted={tuple(self.index[c] for c in permute(victim,p)[0]) for p in self.perms}
            t=tuple(self.index[c] for c in victim[0])
            if not all((allowed[i,j][t[i]] >> t[j]) & 1 for i,j in combinations(range(k),2)):
                raise ValueError("mutation did not reach the singleton test")
            try:
                self.check_single(t, known-deleted)
            except ValueError as e:
                if e.args != (("unlisted irreducible singleton",t),): raise
                print("PASS corrupted table rejected by singleton closure",flush=True)
            else:
                raise ValueError("corrupted table was not rejected")
        seen=set(known)
        acts=list(self.act.items())
        ids=[0]*k;nall=ntest=0
        def rec(i,possible):
            nonlocal nall,ntest
            if i==k:
                nall+=1;t=tuple(ids)
                if t in seen:return
                self.check_single(t,known)
                for p,r in acts:
                    u=[0]*k
                    for h in range(k):u[p[h]]=r[t[h]]
                    seen.add(tuple(u))
                ntest+=1
            else:
                flags=possible[0]
                while flags:
                    e=flags&-flags;a=e.bit_length()-1;flags^=e
                    ids[i]=a
                    rec(i+1,[v&allowed[i,j][a] for j,v in enumerate(possible[1:],i+1)])
        rec(0,[(1<<n)-1]*k)
        print("PASS residual tuples:",nall,"; unlisted orbits:",ntest,flush=True)

    def verify(self, mutation):
        k=self.k
        hist=[sum(size(f)==n for f in self.fs) for n in range(max(map(size,self.fs))+1)]
        print("Width",k,"; table by interior order:",hist,flush=True)
        self.terminal()
        self.siblings()
        self.singles(self.pairs(),mutation)
        print(f"PASS: every {k}-tree is odd {k+2}-colorable",flush=True)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k",type=int,choices=(4,5))
    parser.add_argument("--drop",action="store_true",help="negative control: delete the final table orbit")
    args=parser.parse_args()
    for k in (args.k,) if args.k else (4,5):
        reps=TAB4 if k==4 else TAB5
        Check(k,reps[:-1] if args.drop else reps).verify(not args.drop)
