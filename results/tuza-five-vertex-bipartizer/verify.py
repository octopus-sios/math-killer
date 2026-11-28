#!/usr/bin/env python3
"""Exhaustive finite checks supplementary to PROOF.md. Standard library only."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations,combinations_with_replacement

def need(p,msg):
    if not p: raise AssertionError(msg)
def pairs(V):
    return {tuple(sorted(e)) for e in combinations(V,2)}
def triangles(n,E):
    return [pairs(t) for t in combinations(range(n),3) if pairs(t)<=E]
def nu(n,E):
    T=triangles(n,E)
    def rec(i,used):
        if i==len(T): return 0
        v=rec(i+1,used)
        return v if T[i]&used else max(v,1+rec(i+1,used|T[i]))
    return rec(0,set())
def cores():
    es=sorted(pairs(range(5)));hist=Counter()
    for mask in range(1<<len(es)):
        E={e for i,e in enumerate(es) if mask>>i&1}
        u=nu(5,E);h=len(E)-2*u; hist[h]+=1
        need(h<=6,'h>6')
        if h>=5:
            mandatory={e for e in E if nu(5,E-{e})<u}
            need(len(mandatory)<=1,'mandatory edges')
            for B in combinations(range(5),4):need(bool((pairs(B)&E)-mandatory),'four colors')
    return dict(sorted(hist.items()))
def is_wke(n,E):
    for k in range(n//2+1):
        for t in combinations(E,k):
            if len({v for e in t for v in e})!=2*k:continue
            for Q in combinations(range(n),k):
                if all(e in t or set(e)&set(Q) for e in E): return True
    return False
def links():
    count=0
    for n in range(1,6):
        es=sorted(pairs(range(n)))
        for mask in range(1<<len(es)):
            E={e for i,e in enumerate(es) if mask>>i&1};count+=1
            if not is_wke(n,E):
                missing=set(es)-E
                need(n==5 and len({v for e in missing for v in e})==2*len(missing),'small link')
    return count
def hall_boundary():
    # Exhaust the row multisets at q=a, allowing every row to miss 0, 1 or 2
    # colors. For q>a the proof in PROOF.md applies without enumeration.
    total=deficient=0
    for a in (3,4,5):
        rows=[r for r in range(1<<a) if a-r.bit_count()<=2]
        for shape in combinations_with_replacement(rows,a):
            total+=1
            N=[sum(1<<j for j,r in enumerate(shape) if d&r) for d in range(1<<a)]
            D=max(range(1<<a),key=lambda d:d.bit_count()-N[d].bit_count())
            if D.bit_count()<=N[D].bit_count():continue
            deficient+=1
            need(D.bit_count()<=2 and N[D].bit_count()<=1,'large obstruction')
            for B in range(1<<a):
                if not B&D:need((N[B]&~N[D]).bit_count()>=B.bit_count(),'outside Hall')
    return total,deficient
def verify_coloring(E,P):
    used=set()
    for a,b,s in P:
        edges=pairs((a,b,s))
        need(len({a,b,s})==3 and edges<=E and not edges&used,'invalid packing')
        used.update(edges)
def mutations():
    P=[(1,2,0),(1,3,4)]
    E=pairs(P[0])|pairs(P[1])|{(0,3)}
    verify_coloring(E,P)
    for edges,T in [(E,[(1,2,0),(1,3,0)]),(E-{(1,4)},P)]:
        try:verify_coloring(edges,T)
        except AssertionError:continue
        raise AssertionError('accepted corrupted certificate')
    return 2
def constants():
    eta=F(1,10**18);beta=F(1,10**5)
    need(12*eta<beta**3/36 and 2*beta-6*eta>beta,'Case 1')
    need(120**2*3*beta < F(2,3)**2 and 7200*beta < F(1,12),'Case 2')
    for m in range(6,10):need(m-2*(m//4)>=4,'small m')
    for m in range(10,14):need(m-2*(m//4)>=6,'large m')
if __name__=='__main__':
    constants()
    print('h histogram:',cores())
    print('small links:',links())
    print('boundary Hall shapes (all, deficient):',hall_boundary())
    print('rejected mutations:',mutations())
