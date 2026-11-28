#!/usr/bin/env python3
"""Exact certificates for the two rotation bounds; raises on corrupted certificates."""
from fractions import Fraction as F

# Columns of general RHSs: n,a,b,c,h,l,k. RHS minus tau >= 0.
GROWS=(
    (3,-1,0,0,0,0,0),                       # P,A books
    (F(3,2),F(5,2),F(3,2),-1,0,F(1,2),0), # cut; distinct red opposites
    (3,0,0,-2,1,0,0),                       # safe opposite switch
    (3,0,0,-1,0,0,-1),                      # promote rotated residual
    (3,0,-1,F(8,3),-F(2,3),0,0),           # colored S
    (3,0,-1,2,0,-1,F(8,3)),                # colored rotated residual
)
GW=(15,6,4,8,6,3)
# Columns of colored RHSs: p,q,u,l,k.
CROWS=(
    (3,-2,-1,1,0),
    (3,-1,-1,0,-1),
    (2,2,0,-1,F(8,3)),
    (2,F(8,3),0,-F(2,3),0),
)
CW=(7,8,3,6)

def cert(rows,w,den,coeff,x,target):
    assert len(rows)==len(w)>0 and all(len(r)==len(coeff)==len(x) for r in rows)
    assert sum(w)==den and min(w)>=0 and den>0
    beta=tuple(sum(z*r[j] for r,z in zip(rows,w)) for j in range(len(x)))
    assert beta==coeff,beta
    vals=[sum(F(a)*b for a,b in zip(row,x)) for row in rows]
    assert vals==[target]*len(rows),vals
    return beta

def general(rows=GROWS,w=GW,x=(14,3,9,3,3,0,0)):
    n,a,b,c,h,l,k=x;m=n-a
    assert 0<=l<=h<=c<=b<=m and 0<=k<=b-l
    return cert(rows,w,42,(117,0,0,0,0,0,0),x,39)
def colored(rows=CROWS,w=CW,x=(32,9,0,6,3)):
    p,q,u,l,k=x
    assert 0<=l<=q<=p-u and 0<=k<=p-l
    return cert(rows,w,24,(63,0,-15,0,0),x,84)
def main():
    print("general:",general()," =>",F(117,42))
    print("colored:",colored()," =>",F(63,24), "- u coefficient",F(15,24))
    assert F(165,59)-F(39,14)==F(9,826)
    bad=list(GROWS);bad[5]=(*bad[5][:5],0,F(8,3))
    corrupt=(lambda:general(rows=bad),lambda:general(w=(15,6,5,7,6,3)),
             lambda:general(x=(14,3,8,3,3,0,0)),lambda:colored(w=(6,9,3,6)))
    for fn in corrupt:
        try:fn()
        except AssertionError:continue
        raise AssertionError("corrupt certificate accepted")
    print("PASS: 2 exact primal/dual certificates; 4 corrupted witnesses rejected.")
if __name__=='__main__':main()
