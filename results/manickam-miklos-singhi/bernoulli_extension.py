"""Fast integer prefix check for the extended interval (requires a C++17 compiler).
Builds the accompanying prefix.cpp; no external tables or solver. 
Run python3 bernoulli_extension.py --help for optional subinterval replay.
"""
from bernoulli_constants import F,Q,S,Table,baseline,ceildiv,floorf,ceilf,mix_threshold
import numpy as np, argparse,subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

def triple(t):
    # Three real thresholds sum <0. Sort them; raise the largest so sum is 0.
    # If the smallest <= -2, one-sided Chebyshev already guarantees 4/5.
    row=t.f[t.B].tolist()
    def v(i): # threshold i/50
        j=ceildiv(i*t.D,50)
        return row[max(-t.X,j)+t.X] if j<=t.X else 0
    k=4*Q//5
    for i in range(-100,1):
        # smallest x in [i/50,(i+1)/50], second y>=x and <= -x/2
        for j in range(i,(-i)//2+1):
            k=min(k,v(i+1)+v(j+1)+v(-i-j))
    return k

def run(compiler,args,p,h):
    T=Table(p,h,args.B,args.D,args.G,args.K)
    V=Table(p/(1-p),h/(1-h),args.B,args.D,args.G,args.K)
    def test(t,goal,J,C,mode,depth):
        a,b=t.lo.as_integer_ratio();c,d=goal.as_integer_ratio()
        header=[a,b,c,d,t.B,t.D,t.G,args.U,depth,J,C,t.g,t.d,mode,args.coarse]
        data=(' '.join(map(str,header))+'\n'+' '.join(map(str,t.f.reshape(-1).tolist()))+'\n').encode()
        v=subprocess.run([compiler],input=data,stdout=subprocess.PIPE,check=False)
        if v.returncode not in [0,1]:raise RuntimeError('invalid checker invocation')
        return v.returncode==0,v.stdout.decode().strip().replace('\n','; ')
    aux=int(V.f[V.B,V.X]); cert=[]
    if p>=F(31,100) and not args.no_aux:
        # Complement pairs at auxiliary bias s<1/2; same reasoning as triple().
        c2=4*Q//5;row=V.f[V.B].tolist()
        for i in range(-100,1):
            c2=min(c2,row[V.X+ceildiv((i+1)*V.D,50)]+row[V.X+ceildiv(-i*V.D,50)])
        for ratio in (F(3,4),F(7,10)):
            goal=ratio*V.hi
            if aux>=goal*Q:break
            ok,stat=test(V,goal,0,c2,2,min(args.depth,8))
            if ok:
                aux=floorf(goal*Q)
                cert.append('aux='+str(goal)+':'+stat)
                break
    J=mix_threshold(p,h,aux)
    ok,stat=test(T,F(1) if args.mutation_test else h,0 if args.mutation_test else J,
                 triple(T),int(args.no_tie),args.depth)
    return ok,' '.join([stat]+cert)

def main():
    if not __debug__:raise RuntimeError("run without python -O")
    baseline()
    ap=argparse.ArgumentParser()
    ap.add_argument('--lo',type=F,default=F(29,100));ap.add_argument('--hi',type=F,default=F(31,100))
    ap.add_argument('--mesh',type=int,default=300)
    ap.add_argument('--B',type=int,default=192);ap.add_argument('--D',type=int,default=240)
    ap.add_argument('--G',type=int,default=10);ap.add_argument('--K',type=int,default=48)
    ap.add_argument('--coarse',type=int,default=1);ap.add_argument('--depth',type=int,default=8);ap.add_argument('--U',type=int,default=256)
    ap.add_argument('--subdivide',type=int,default=7);ap.add_argument('--no-tie',action='store_true')
    ap.add_argument('--no-aux',action='store_true');ap.add_argument('--mutation-test',action='store_true');args=ap.parse_args()
    assert F(1,7)<=args.lo<=args.hi<=F(1,3)
    src=Path(__file__).with_name('prefix.cpp')
    with TemporaryDirectory(dir=src.parent) as td:
        exe=Path(td).absolute()/'prefix'
        subprocess.run(['g++','-O3','-std=c++17','-o',exe,src],check=True)
        def check(p,h,lev):
            ok,res=run(exe,args,p,h)
            print(f'{p}..{h}: {res}',flush=True)
            if not ok:
                if lev and p<h and not args.mutation_test:
                    m=(p+h)/2;check(p,m,lev-1);check(m,h,lev-1)
                else:raise SystemExit(1)
        p=args.lo
        if p==args.hi:check(p,p,0)
        while p<args.hi:
            h=min(args.hi,F(floorf(p*args.mesh)+1,args.mesh))
            check(p,h,args.subdivide);p=h
        print('PASS covered',args.lo,args.hi)
if __name__=='__main__':main()
