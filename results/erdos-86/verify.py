#!/usr/bin/env python3
"""Exact zero-float verifier for Erdos Problem #86 (C4-free subgraphs of Q_n).

Requires ONLY Python 3 standard library + g++ (-std=c++17 -O3 -fopenmp).
Zero floats, zero NumPy/SciPy/SymPy, zero external SDP/SAT/MIP solvers.

Runs three independent exact suites:
  Suite 1: Coupled H4 + rooted B5 + finite lattice cuts + edge-book inventory
           dual upper bounds for pi_e(C4) and Q_n (n in {8,9,10,11,12,16}),
           with on-the-fly orbit censuses (H4: 3,212,821 / 1,226,436,381;
           B4: 2,144 / 46,553; B5: 170,055 / 19,571,625) and mandatory
           corrupted-certificate mutation rejections (B4 price + Gram factor).
  Suite 2: Pure full-Q4 primal SDP relaxation obstruction laws (floor8/9/10.json)
           verified by exact rational Schur complements, proving pure-Q4 SDP
           cannot improve Q8 below 692, with mandatory mutation rejection.
  Suite 3: Exact period-<=16 translation-invariant extremal theorem for Q_7..Q_10
           (max edges 296, 672, 1472, 3200), importing only ex(Q_5, C_4) = 56,
           with explicit C4-free lift verification and C4-mutation rejection.
"""
import array, ast, collections, functools, gzip, itertools as it, json, os, re, struct, subprocess, sys, tempfile, zipfile
from fractions import Fraction as F
from math import prod
from pathlib import Path
HERE=Path(__file__).resolve().parent
CLAIMS = [
    (0,  'cert_asymptotic.npz', '253730158483485323/429000000000000000'),
    (8,  'cert_q8.npz',         '1346954636130710129/2016000000000000000'),
    (9,  'cert_q9.npz',         '1075255913169191273/1612800000000000000'),
    (10, 'cert_q10.npz',        '7960674831095286151/12096000000000000000'),
    (11, 'cert_q11.npz',        '432415022065590379/660000000000000000'),
    (12, 'cert_q12.npz',        '5179649375710126039/7920000000000000000'),
    (16, 'cert_q16.npz',        '1081058230849675073/1680000000000000000'),
]
def need(cond,msg):
    if not cond: raise ValueError(msg)
def read(z,key):
    b=z.read(key+'.npy')
    need(b[:6]==b'\x93NUMPY' and b[6:8] in (b'\x01\x00',b'\x02\x00'),'NPY header')
    p=10 if b[6]==1 else 12
    hlen=int.from_bytes(b[8:p],'little');h=ast.literal_eval(b[p:p+hlen].decode('ascii'))
    kinds={'|i1':'b','<i2':'h','<i4':'i','<i8':'q'}
    need(h['descr'] in kinds and h['fortran_order'] is False,'signed integer array required')
    sh=h['shape'];need(isinstance(sh,tuple) and all(type(k) is int and k>=0 for k in sh),'invalid shape')
    a=array.array(kinds[h['descr']]);need(a.itemsize==int(h['descr'][2:]),'integer size');a.frombytes(b[p+hlen:])
    need(len(a)==prod(sh),'shape mismatch')
    return sh,a
def vec(z,key,k):
    sh,a=read(z,key);need(sh==(k,),key+' shape');return a
def scalar(z,key):
    sh,a=read(z,key);need(sh==(),key+' not scalar');return a[0]
@functools.lru_cache(None)
def edges(m):
    return [(x,x|(1<<i)) for i in range(m) for x in range(1<<m) if not (x>>i)&1]
def slots(m,sub,axes,base):
    E={e:i for i,e in enumerate(edges(m))}
    def trans(x):return base^sum(1<<j for i,j in enumerate(axes) if (x>>i)&1)
    return [E[tuple(sorted((trans(x),trans(y))))] for x,y in edges(sub)]
def pull(h,inds):
    return sum(((h>>k)&1)<<i for i,k in enumerate(inds))
@functools.lru_cache(None)
def geometry(s,m,t):
    root=slots(m,s,range(s),0)
    sq=[sum(1<<j for j in slots(m,2,(a,b),x)) for a,b in it.combinations(range(m),2)
        for x in range(1<<m) if not (x&((1<<a)|(1<<b)))]
    unused=[slots(m,m,tuple(range(s))+p,0) for p in it.permutations(range(s,m))]
    def canon(h):return min(pull(h,p) for p in unused)
    fs=sorted({canon(h) for h in range(1<<len(edges(m))) if pull(h,root)==t and all(h&q!=q for q in sq)})
    ix={v:i for i,v in enumerate(fs)};perms=[]
    for axes in it.permutations(range(s)):
        for base in range(1<<s):
            if pull(t,slots(s,s,axes,base))!=t:continue
            p=slots(m,m,axes+tuple(range(s,m)),base)
            perm=[ix[canon(pull(h,p))] for h in fs]
            need(sorted(perm)==list(range(len(fs))),'not a root permutation');perms.append(perm)
    return fs,perms
def gram(z,key,d,mutation=0):
    sh,R=read(z,key);need(len(sh)==2 and sh[1]==d and sh[0]<=d,'Gram shape')
    X=[[int(i==j) for j in range(d)] for i in range(d)]
    rows=[R[j:j+d] for j in range(0,len(R),d)]
    if mutation:rows.append([mutation]*d)
    for r in rows:
        nz=[(i,v) for i,v in enumerate(r) if v]
        for k,v in nz:
            a=X[k]
            for j,w in nz:a[j]+=v*w
    return X
def cuts(z,n,t,s,fs,perms,Q):
    tag=str(t);nf=len(fs)
    if 'obs'+tag+'.npy' not in z.namelist():return
    sh,ff=read(z,'obs'+tag);need(n>=5 and len(sh)==2 and sh[1]==nf,'finite lattice shape')
    k=sh[0];hh,cc,tt=[vec(z,u+tag,k) for u in ('hs','coef','typ')]
    # Combine terms with the same integer observable before expensive lifting.
    groups=collections.defaultdict(lambda:[0,0,0])
    for i in range(k):
        c,h,typ=cc[i],hh[i],tt[i];a=tuple(ff[i*nf:(i+1)*nf])
        need(c>=0 and abs(h)<100000 and all(abs(b)<10000 for b in a),'cut coefficient')
        if s==0:
            need(typ==1 and list(a)==[(m&1)+(m>>2&1) for m in fs],'not an incident degree count')
            m2=n
        else:
            need(typ==0 and s in (1,2),'not a single-axis observable');m2=2*(n-s)
        if c:
            u=groups[a];u[0]+=c*m2*m2;u[1]-=c*m2*(2*h+1);u[2]+=c*((2*h+1)**2-1)
    M=[[0]*nf for _ in range(nf)]
    for a,(aa,ab,ac) in groups.items():
        for i,b in enumerate(a):
            A=aa*b+ab;B=ab*b+ac;row=M[i]
            for j,e in enumerate(a):row[j]+=A*e+B
    if groups:
        for p in perms:
            for i,k in enumerate(p):
                row=Q[i];v=M[k]
                for j,l in enumerate(p):row[j]+=v[l]
def dump(f,row):
    need(all(type(x) is int and abs(x)<=10**16 for x in row),'integer table range')
    f.write(struct.pack('<%dq'%len(row),*row))
def tables(z,B,n,path,mutation=False):
    scale=scalar(z,'scale');need(0<scale<=10**9 and scalar(z,'n')==n and (n==0 or 5<=n<=100),'dimension/scale')
    with path.open('wb') as out:
        out.write(struct.pack('<q',scale**2))
        for t,((s,m,tm),(nf,bl)) in enumerate(zip(((0,2,0),(1,2,0),(1,2,1),(2,3,0),(2,3,1),(2,3,3),(2,3,5),(2,3,7)),B)):
            flags,perms=geometry(s,m,tm);need(len(flags)==nf,'raw flag count');Q=[[0]*nf for i in flags]
            for j,(d,Vs) in enumerate(bl):
                X=gram(z,'R%d_%d'%(t,j),d,scale if mutation and t==j==0 else 0)
                for V in Vs:
                    need(all(all(type(v) is int for v in triple) and 0<=triple[0]<nf and 0<=triple[1]<d for triple in V),'invalid integral lift')
                    for r,c,b in V:
                        row=Q[r];v=X[c]
                        for k,l,a in V:row[k]+=a*b*v[l]
            cuts(z,n,t,s,flags,perms,Q)
            for p in perms:
                need(all(all(row[j]==v[l] for j,l in enumerate(p)) for i,k in enumerate(p) for row,v in [(Q[i],Q[k])]),'root invariance')
            for i,row in enumerate(Q):
                need(all(a==Q[j][i] for j,a in enumerate(row)),'matrix symmetry');dump(out,row)
    return scale
def balltables(z,D,n,path,negative=False):
    Q=[[0]*512 for _ in range(512)]
    for t in (0,1):
        sh,u=read(z,'U'+str(t));need(len(sh)==1 and list(u)==sorted(set(u)) and all(0<=x<512 and x%2==t for x in u),'marked-ball indices')
        X=gram(z,'B'+str(t),len(u))
        for i,k in enumerate(u):
            for j,l in enumerate(u):Q[k][l]=X[i][j]
    with path.open('wb') as f:
        e=list(vec(z,'ell',2144))
        if negative:e[0]+=10*D
        dump(f,e)
        for row in Q:dump(f,row)
        if 'book.npy' in z.namelist():
            m=scalar(z,'bookD');need(4<=m<=16 and (not n or m<n),'book length')
            f.write(struct.pack('<i',m));dump(f,list(vec(z,'book',8192)))
def accept(score,claim):
    need(score<=claim,'claimed bound exceeded')
def verify_coupled_upper_bounds():
    need(sys.byteorder=='little','little-endian C++ interchange required')
    manifest=CLAIMS
    need(len(set(n for n,_,_ in manifest))==len(manifest),'duplicate dimension')
    B=json.loads(gzip.decompress((HERE/'data/joint_bases.json.gz').read_bytes()))
    need(len(B)==8,'root family count');cases=[];args=[]
    with tempfile.TemporaryDirectory() as td:
        tmp=Path(td);env=dict(os.environ);env.setdefault('OMP_NUM_THREADS','2')
        def run(c,**kw):return subprocess.run(list(map(str,c)),cwd=tmp,env=env,check=True,**kw)
        for name,source in [('enum4',ENUM),('audit',AUDIT)]:
            cpp=tmp/(name+'.cpp');cpp.write_text(source);run(['g++','-std=c++17','-O3','-fopenmp',cpp,'-o',tmp/name])
        run([tmp/'enum4'])
        def add(n,q,m,t,e,book):
            args.extend([t,str(n),e,str(int(bool(m)))]);cases.append((n,F(q),m,book))
        for k,(n,fn,q) in enumerate(manifest):
            with zipfile.ZipFile(HERE/'data'/fn) as z:
                t=tmp/f't{k}';e=tmp/f'e{k}';d=tables(z,B,n,t)**2;balltables(z,d,n,e)
                book='book.npy' in z.namelist();add(n,q,None,t,e,book)
                em=tmp/f'm{k}';balltables(z,d,n,em,True);add(n,q,'B4 price',t,em,book)
                if k==0:
                    tm=tmp/'mutGram';tables(z,B,n,tm,True);add(n,q,'Gram factor',tm,e,book)
        r=run([tmp/'audit',tmp/'h4_orbits.bin',*args],stdout=subprocess.PIPE,text=True).stdout
        b=collections.defaultdict(list);found=set();cur=None;ns=0
        for l in r.splitlines():
            if l.startswith('CASE '):cur=int(l.split()[1])
            elif l.startswith(('B5 numerator','inventories ')):
                a,h=re.search(r'numerator (-?\d+) denominator (\d+)',l).groups();b[cur].append(F(int(a),int(h)))
            elif l.startswith('H4 '):
                _,i,a,h,m,c=l.split();i=int(i);n,q,mutation,book=cases[i]
                need(i not in found and len(b[i])==1+int(book) and int(c)==(1 if mutation else 3212821),'missing scan')
                found.add(i);score=F(int(a),int(h))+sum(b[i])
                if mutation:
                    # One counterexample row is enough for rejection, NEVER for acceptance.
                    try:accept(score,q)
                    except ValueError:print('n',n,'corrupt',mutation,'rejected:',score,'>',q)
                    else:raise ValueError('mutation not rejected')
                else:
                    accept(score,q);need(score==q,'recomputed maximum does not match manifest')
                    print('n',n,'exact density',score,'H4 mask',m,('edges <= '+str((score*n*2**(n-1)).__floor__())) if n else 'asymptotic')
            elif l.startswith(('B4 orbits','B5 orbits','representatives')):
                print(l);ns+=1
        need(ns==3 and found==set(range(len(cases))),'missing census or bound')
    print('PASS')
ENUM = r'''
#include <iostream>
#include <vector>
#include <cstdint>
#include <algorithm>
#include <fstream>
#include <chrono>
#include <array>
#include <numeric>
#include <omp.h>

// Edge indexing for Q_4 (32 edges):
// We put the 12 edges of bottom Q_3 (vertices 0..7) in bits 20..31 (MSB)
// so that minimizing the 32-bit mask first minimizes the bottom Q_3!
// Specifically:
//   bits 20..31: bottom Q_3 edges (12 edges: 4 along dim 0, 4 along dim 1, 4 along dim 2, vertices 0..7)
//   bits  8..19: top    Q_3 edges (12 edges: vertices 8..15, same order as bottom Q_3)
//   bits  0.. 7: vertical   edges (8 edges: (v, v+8) for v = 0..7, bit v)
//
// Within a Q_3 (12 edges, bits 0..11):
//   for d in {0,1,2}, for u in 0..7 with ((u>>d)&1)==0: edge (u, u^(1<<d))
//   Let's list them explicitly in deterministic order.

struct Edge {
    int u, v, d;
};

static Edge q3_edges[12];
static int q3_edge_idx[8][8];
static Edge q4_edges[32];
static int q4_edge_idx[16][16];

// Squares in Q_3 (6 squares) and Q_4 (24 squares)
static uint16_t q3_sq_masks[6];
static uint32_t q4_sq_masks[24];
static uint32_t q4_vert_sq_masks[12]; // squares involving dim 3

// Aut(Q_3): 48 elements
static uint8_t aut3_vmap[48][8];      // image of vertex v in Q_3
static uint8_t aut3_emap[48][12];     // edge e in input maps to aut3_emap[p][e] in output (or inverse)

// Aut(Q_4): 384 elements, indexed as face_id (0..7) * 48 + q3_aut (0..47)
// Specifically, face_id = 2*fdir + fside (fdir in 0..3, fside in 0..1).
// We construct a bijection phi_{face_id, p} of Q_4 that maps face (fdir, fside)
// onto the bottom Q_3 face (bit 3 == 0), with the Q_3 automorphism p applied inside it!
static uint8_t aut4_emap[384][32];    // bit e of source -> bit aut4_emap[g][e] of dest
static uint8_t face_extract_emap[8][12]; // for each of the 8 Q_3 faces, the 12 Q_4 edge indices in standard Q_3 order

void init_tables() {
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 8; j++)
            q3_edge_idx[i][j] = -1;
    int idx = 0;
    for (int d = 0; d < 3; d++) {
        for (int u = 0; u < 8; u++) {
            if (((u >> d) & 1) == 0) {
                int v = u | (1 << d);
                q3_edges[idx] = {u, v, d};
                q3_edge_idx[u][v] = q3_edge_idx[v][u] = idx;
                idx++;
            }
        }
    }

    for (int i = 0; i < 16; i++)
        for (int j = 0; j < 16; j++)
            q4_edge_idx[i][j] = -1;

    // bits 0..7: vertical edges (v, v+8)
    for (int v = 0; v < 8; v++) {
        q4_edges[v] = {v, v + 8, 3};
        q4_edge_idx[v][v + 8] = q4_edge_idx[v + 8][v] = v;
    }
    // bits 8..19: top Q_3 edges
    for (int e = 0; e < 12; e++) {
        int u = q3_edges[e].u + 8;
        int v = q3_edges[e].v + 8;
        int b = 8 + e;
        q4_edges[b] = {u, v, q3_edges[e].d};
        q4_edge_idx[u][v] = q4_edge_idx[v][u] = b;
    }
    // bits 20..31: bottom Q_3 edges
    for (int e = 0; e < 12; e++) {
        int u = q3_edges[e].u;
        int v = q3_edges[e].v;
        int b = 20 + e;
        q4_edges[b] = {u, v, q3_edges[e].d};
        q4_edge_idx[u][v] = q4_edge_idx[v][u] = b;
    }

    // Q_3 squares (6)
    int sq = 0;
    for (int a = 0; a < 3; a++) {
        for (int b = a + 1; b < 3; b++) {
            for (int u = 0; u < 8; u++) {
                if (((u >> a) & 1) == 0 && ((u >> b) & 1) == 0) {
                    int ua = u | (1 << a);
                    int ub = u | (1 << b);
                    int uab = ua | (1 << b);
                    uint16_t m = 0;
                    m |= (1u << q3_edge_idx[u][ua]);
                    m |= (1u << q3_edge_idx[u][ub]);
                    m |= (1u << q3_edge_idx[ua][uab]);
                    m |= (1u << q3_edge_idx[ub][uab]);
                    q3_sq_masks[sq++] = m;
                }
            }
        }
    }

    // Q_4 squares (24) and vertical squares (12)
    sq = 0;
    int vsq = 0;
    for (int a = 0; a < 4; a++) {
        for (int b = a + 1; b < 4; b++) {
            for (int u = 0; u < 16; u++) {
                if (((u >> a) & 1) == 0 && ((u >> b) & 1) == 0) {
                    int ua = u | (1 << a);
                    int ub = u | (1 << b);
                    int uab = ua | (1 << b);
                    uint32_t m = 0;
                    m |= (1u << q4_edge_idx[u][ua]);
                    m |= (1u << q4_edge_idx[u][ub]);
                    m |= (1u << q4_edge_idx[ua][uab]);
                    m |= (1u << q4_edge_idx[ub][uab]);
                    q4_sq_masks[sq++] = m;
                    if (b == 3) q4_vert_sq_masks[vsq++] = m;
                }
            }
        }
    }

    // Aut(Q_3): 48 elements
    int perms3[6][3] = {
        {0,1,2}, {0,2,1}, {1,0,2}, {1,2,0}, {2,0,1}, {2,1,0}
    };
    int g = 0;
    for (int root = 0; root < 8; root++) {
        for (int p = 0; p < 6; p++) {
            for (int v = 0; v < 8; v++) {
                int img = root;
                for (int d = 0; d < 3; d++) {
                    if ((v >> d) & 1) img ^= (1 << perms3[p][d]);
                }
                aut3_vmap[g][v] = img;
            }
            for (int e = 0; e < 12; e++) {
                int u = aut3_vmap[g][q3_edges[e].u];
                int v = aut3_vmap[g][q3_edges[e].v];
                aut3_emap[g][e] = q3_edge_idx[u][v];
            }
            g++;
        }
    }

    // Aut(Q_4): organized as 8 faces x 48 Q_3 automorphisms
    // For face (fdir, fside): remaining 3 dims in ascending order are rem[0], rem[1], rem[2].
    // Base embedding of Q_3 into face (fdir, fside):
    //   v_3 in 0..7 -> v_4 = (fside << fdir) | sum_{j=0}^2 ((v_3>>j)&1) << rem[j]
    // Then for Q_3 automorphism p (which maps v_3 -> aut3_vmap[p][v_3]),
    // we define Q_4 map phi_{face, p} mapping v_4 in dest (0..15) to src vertex in Q_4:
    //   dest_bit_3 == 0 -> face vertex at src corresponding to aut3_vmap[p][v_3]
    //   dest_bit_3 == 1 -> opposite face vertex (flip fdir) at src
    // Wait: let's verify! If dest_mask has edge (x,y) iff src_mask has edge (src(x), src(y)),
    // then dest_bottom_Q3 (dest_bit_3 == 0) has edge (u,v) iff face_mask has edge (aut3_vmap[p][u], aut3_vmap[p][v]).
    // Let's be 100% consistent: define apply3(p, mask3) as:
    //   dest bit e' = src bit e where e' = aut3_emap[p][e],
    //   i.e., dest has edge (aut3_vmap[p][u], aut3_vmap[p][v]) iff src has edge (u, v)!
    // Then for Q_4: map src vertex s -> dest vertex d as follows:
    //   Given face (fdir, fside) with remaining dims rem[0..2]:
    //   For src vertex s:
    //     local_v3 = bit_rem0 | (bit_rem1 << 1) | (bit_rem2 << 2)
    //     dest_bit3 = ((s >> fdir) & 1) ^ fside   (so face vertices get dest_bit3 = 0!)
    //     dest_v3 = aut3_vmap[p][local_v3]
    //     dest_v4 = dest_v3 | (dest_bit3 << 3)
    // Let's check! If s is on the face (fdir, fside), dest_bit3 = 0, so s maps to dest_v3 in bottom Q_3,
    // and the induced bottom Q_3 of dest is LITERALLY apply3(p, extract_face(src, face))!!
    // And as (fdir, fside, p) ranges over 4 x 2 x 48 = 384, are all 384 maps distinct automorphisms of Q_4?
    // YES! Because fdir chooses which source dim maps to dest dim 3 (4 choices),
    // fside chooses bit-flip of dim 3 (2 choices), and p chooses Aut(Q_3) on remaining 3 dims (48 choices).
    // 4 * 2 * 48 = 384 = |Aut(Q_4)|!
    for (int fdir = 0; fdir < 4; fdir++) {
        int rem[3];
        int r = 0;
        for (int d = 0; d < 4; d++) if (d != fdir) rem[r++] = d;
        for (int fside = 0; fside < 2; fside++) {
            int fid = 2 * fdir + fside;
            // Face extraction table
            for (int e3 = 0; e3 < 12; e3++) {
                int u3 = q3_edges[e3].u;
                int v3 = q3_edges[e3].v;
                int u4 = (fside << fdir);
                int v4 = (fside << fdir);
                for (int j = 0; j < 3; j++) {
                    if ((u3 >> j) & 1) u4 |= (1 << rem[j]);
                    if ((v3 >> j) & 1) v4 |= (1 << rem[j]);
                }
                face_extract_emap[fid][e3] = q4_edge_idx[u4][v4];
            }
            for (int p = 0; p < 48; p++) {
                int gid = fid * 48 + p;
                int vmap4[16];
                for (int s = 0; s < 16; s++) {
                    int local_v3 = (((s >> rem[0]) & 1) << 0)
                                 | (((s >> rem[1]) & 1) << 1)
                                 | (((s >> rem[2]) & 1) << 2);
                    int dbit3 = ((s >> fdir) & 1) ^ fside;
                    int dv3 = aut3_vmap[p][local_v3];
                    vmap4[s] = dv3 | (dbit3 << 3);
                }
                for (int e4 = 0; e4 < 32; e4++) {
                    int du = vmap4[q4_edges[e4].u];
                    int dv = vmap4[q4_edges[e4].v];
                    aut4_emap[gid][e4] = q4_edge_idx[du][dv];
                }
            }
        }
    }
}

static inline uint16_t apply3(int p, uint16_t m) {
    uint16_t out = 0;
    const uint8_t* em = aut3_emap[p];
    while (m) {
        int b = __builtin_ctz(m);
        m &= m - 1;
        out |= (1u << em[b]);
    }
    return out;
}

static inline uint32_t apply4(int gid, uint32_t m) {
    uint32_t out = 0;
    const uint8_t* em = aut4_emap[gid];
    while (m) {
        int b = __builtin_ctz(m);
        m &= m - 1;
        out |= (1u << em[b]);
    }
    return out;
}

static inline uint16_t extract_face(int fid, uint32_t m) {
    uint16_t out = 0;
    const uint8_t* em = face_extract_emap[fid];
    for (int e3 = 0; e3 < 12; e3++) {
        out |= (uint16_t)(((m >> em[e3]) & 1u) << e3);
    }
    return out;
}

int main() {
    auto t0 = std::chrono::steady_clock::now();
    init_tables();

    // Step 1: Enumerate all C4-free Q_3 labeled graphs and canonical orbits
    static uint16_t canon3[4096];
    static uint8_t is_c4free3[4096];
    static std::vector<uint8_t> to_canon3[4096]; // all p in 0..47 such that apply3(p, m) == canon3[m]

    std::vector<uint16_t> c4free_q3_labeled;
    std::vector<uint16_t> h3_orbits;

    for (uint16_t m = 0; m < 4096; m++) {
        bool ok = true;
        for (int s = 0; s < 6; s++) {
            if ((m & q3_sq_masks[s]) == q3_sq_masks[s]) {
                ok = false;
                break;
            }
        }
        is_c4free3[m] = ok ? 1 : 0;
        if (!ok) {
            canon3[m] = 0xFFFF;
            continue;
        }
        c4free_q3_labeled.push_back(m);
        uint16_t best = 0xFFFF;
        for (int p = 0; p < 48; p++) {
            uint16_t img = apply3(p, m);
            if (img < best) best = img;
        }
        canon3[m] = best;
        for (int p = 0; p < 48; p++) {
            if (apply3(p, m) == best) to_canon3[m].push_back(p);
        }
        if (m == best) h3_orbits.push_back(m);
    }

    std::cout << "C4-free labeled Q_3: " << c4free_q3_labeled.size() << "\n";
    std::cout << "C4-free Q_3 orbits |H_3|: " << h3_orbits.size() << " (expected 99)\n";

    // Edge-count histogram for Q_3
    int q3_hist[13] = {0};
    for (uint16_t m : h3_orbits) q3_hist[__builtin_popcount(m)]++;
    std::cout << "Q_3 edge histogram:";
    for (int k = 0; k <= 12; k++) if (q3_hist[k]) std::cout << " " << k << ":" << q3_hist[k];
    std::cout << "\n";

    // Step 2: Enumerate all C4-free Q_4 orbits in parallel over L in h3_orbits
    int nL = (int)h3_orbits.size();
    std::vector<std::vector<uint32_t>> thread_orbits(nL);

    // Precompute vertical square constraints per (L, U):
    // A vertical square has bottom edge e in L, top edge e in U, and two vertical edges u, v.
    // It is all-1 iff (L has e) && (U has e) && (M has u) && (M has v).
    // So for each edge e in 0..11, if ((L & U) >> e) & 1, then (M & ((1<<u)|(1<<v))) != ((1<<u)|(1<<v))!
    uint8_t edge_vert_pair[12];
    for (int e = 0; e < 12; e++) {
        edge_vert_pair[e] = (1u << q3_edges[e].u) | (1u << q3_edges[e].v);
    }

    #pragma omp parallel for schedule(dynamic, 1)
    for (int li = 0; li < nL; li++) {
        uint16_t L = h3_orbits[li];
        auto& out_vec = thread_orbits[li];
        for (uint16_t U : c4free_q3_labeled) {
            if (canon3[U] < L) continue;
            // Collect forbidden vertical pairs
            uint16_t common = L & U;
            uint8_t forb[12];
            int nforb = 0;
            uint16_t tmp = common;
            while (tmp) {
                int e = __builtin_ctz(tmp);
                tmp &= tmp - 1;
                forb[nforb++] = edge_vert_pair[e];
            }
            uint32_t base = ((uint32_t)L << 20) | ((uint32_t)U << 8);
            for (uint32_t M = 0; M < 256; M++) {
                bool ok = true;
                for (int k = 0; k < nforb; k++) {
                    if ((M & forb[k]) == forb[k]) {
                        ok = false;
                        break;
                    }
                }
                if (!ok) continue;
                uint32_t mask = base | M;

                // Canonicality test: check all 8 Q_3 faces
                bool is_min = true;
                uint16_t faces[8];
                for (int fid = 0; fid < 8; fid++) {
                    uint16_t f = extract_face(fid, mask);
                    faces[fid] = f;
                    if (canon3[f] < L) {
                        is_min = false;
                        break;
                    }
                }
                if (!is_min) continue;

                // For every face with canon3[f] == L, check all p in to_canon3[f]
                for (int fid = 0; fid < 8 && is_min; fid++) {
                    uint16_t f = faces[fid];
                    if (canon3[f] != L) continue;
                    for (uint8_t p : to_canon3[f]) {
                        uint32_t img = apply4(fid * 48 + p, mask);
                        if (img < mask) {
                            is_min = false;
                            break;
                        }
                    }
                }
                if (is_min) {
                    out_vec.push_back(mask);
                }
            }
        }
    }

    size_t total = 0;
    for (int li = 0; li < nL; li++) total += thread_orbits[li].size();

    std::vector<uint32_t> h4_orbits;
    h4_orbits.reserve(total);
    uint64_t q4_hist[33] = {0};
    for (int li = 0; li < nL; li++) {
        for (uint32_t m : thread_orbits[li]) {
            h4_orbits.push_back(m);
            q4_hist[__builtin_popcount(m)]++;
        }
    }
    std::sort(h4_orbits.begin(), h4_orbits.end());

    auto t1 = std::chrono::steady_clock::now();
    double secs = std::chrono::duration<double>(t1 - t0).count();

    std::cout << "C4-free Q_4 orbits |H_4|: " << h4_orbits.size()
              << " (expected 3212821) in " << secs << " s\n";
    std::cout << "Q_4 edge histogram:\n";
    int max_e = 0;
    for (int k = 0; k <= 32; k++) {
        if (q4_hist[k]) {
            max_e = k;
            std::cout << "  e=" << k << ": " << q4_hist[k] << "\n";
        }
    }
    std::cout << "Max edges in C4-free Q_4: " << max_e << "\n";

    // Sanity check: verify 1000 random orbits have zero C4 and are true Aut(Q_4) minima!
    uint64_t bad = 0;
    size_t step = std::max<size_t>(1, h4_orbits.size() / 2000);
    for (size_t idx = 0; idx < h4_orbits.size(); idx += step) {
        uint32_t m = h4_orbits[idx];
        for (int s = 0; s < 24; s++) {
            if ((m & q4_sq_masks[s]) == q4_sq_masks[s]) bad++;
        }
        for (int gid = 0; gid < 384; gid++) {
            if (apply4(gid, m) < m) { bad++; break; }
        }
    }
    std::cout << "Random brute-force 384-automorphism sanity check bad=" << bad << "\n";

    // Save binary file
    std::ofstream fout("h4_orbits.bin", std::ios::binary);
    uint64_t cnt = h4_orbits.size();
    fout.write(reinterpret_cast<const char*>(&cnt), sizeof(cnt));
    fout.write(reinterpret_cast<const char*>(h4_orbits.data()), cnt * sizeof(uint32_t));
    fout.close();
    std::cout << "Wrote h4_orbits.bin (" << (cnt * 4 + 8) << " bytes)\n";
    return 0;
}

'''
AUDIT = r'''
#include <unordered_map>
// Independent integer-only Q4 census and flag certificate evaluator. g++ -O3 -fopenmp -std=c++17
// Usage: audit census h4_orbits.bin ; audit score h4_orbits.bin tables.bin n
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
#include <omp.h>
using namespace std;
using u32=uint32_t;using u16=uint16_t;using i64=int64_t;using i128=__int128;
void check(bool ok,const char* msg){if(!ok)throw runtime_error(msg);}
string dec(i128 x){if(x<0)return "-"+dec(-x);if(x<10)return to_string(int(x));return dec(x/10)+char(48+x%10);}
const int types[8]={0,0,1,0,1,3,5,7};
vector<pair<int,int>> edges[5];int indexE[5][16][16];vector<u32> squares[5];vector<u32> H;
void geometry(){
for(int n=1;n<=4;n++){
 auto &e=edges[n];if(n==4){
 for(int x=0;x<8;x++)e.emplace_back(x,x+8);
 for(int s:{8,0})for(auto [x,y]:edges[3])e.emplace_back(x+s,y+s);
 }else for(int d=0;d<n;d++)for(int x=0;x<(1<<n);x++)if(x<(x^(1<<d)))e.emplace_back(x,x^(1<<d));
 for(int j=0;j<(int)e.size();j++){auto [x,y]=e[j];indexE[n][x][y]=indexE[n][y][x]=j;}
 for(int a=0;a<n;a++)for(int b=0;b<a;b++)for(int x=0;x<1<<n;x++)if((x&((1<<a)|(1<<b)))==0){
 int y=x^(1<<a),z=x^(1<<b),w=y^(1<<b);u32 m=0;
 for(auto [k,l]:vector<pair<int,int>>{{x,y},{x,z},{y,w},{z,w}})m|=u32(1)<<indexE[n][k][l];squares[n].push_back(m);}
}}
bool ok(int n,u32 m){for(auto s:squares[n])if((m&s)==s)return false;return true;}
int pc(u32 m){return __builtin_popcount(m);}
using Perm=array<int,4>;
struct Map{
 vector<int> b; // target edges -> source edges
 Map()=default;
 Map(int n,int m,const vector<int>&vert){for(auto [x,y]:edges[m])b.push_back(indexE[n][vert[x]][vert[y]]);}
 u32 read(u32 m)const{u32 o=0;for(int i=0;i<(int)b.size();i++)o|=((m>>b[i])&1)<<i;return o;}
};
vector<int> embed(int r,const vector<int>&ds){vector<int> v(1<<ds.size(),r);for(int x=1;x<(int)v.size();x++)v[x]=v[x&(x-1)]^(1<<ds[__builtin_ctz(x)]);return v;}
struct Lut{u32 a[4][256];Lut(Map m){for(int j=0;j<4;j++)for(u32 k=0;k<256;k++)a[j][k]=m.read(k<<(8*j));}
u32 read(u32 x)const{return a[0][x&255]|a[1][x>>8&255]|a[2][x>>16&255]|a[3][x>>24];}};
void load(const char*file){ifstream f(file,ios::binary);uint64_t n=0;f.read((char*)&n,8);check(n==3212821,"wrong size");H.resize(n);f.read((char*)H.data(),4*n);check(bool(f)&&f.peek()==-1,"bad graph file");
check(adjacent_find(H.begin(),H.end(),greater_equal<u32>())==H.end(),"not strictly increasing");}
void census(){
 vector<Lut> au;vector<int>d={0,1,2,3};do{for(int x=0;x<16;x++)au.emplace_back(Map(4,4,embed(x,d)));}while(next_permutation(d.begin(),d.end()));
 vector<u16> stab(H.size(),0);int bad=0;
 // Verify minimality and stabilizer order for EVERY stored representative.
 #pragma omp parallel for reduction(+:bad)
 for(int chunk=0;chunk<(int)H.size();chunk+=4096){int end=min(int(H.size()),chunk+4096);
 for(auto &g:au)for(int i=chunk;i<end;i++){u32 x=H[i],y=g.read(x);bad+=(y<x);stab[i]+=y==x;}
 for(int i=chunk;i<end;i++)bad+=!ok(4,H[i]);}
 check(bad==0,"nonminimal or forbidden representative");uint64_t sum=0;
 for(auto s:stab){check(s&&384%s==0,"bad stabilizer");sum+=384/s;}
 // Independent labelled count: choose lower and upper square-free Q3 masks; vertical set independent in their intersection.
 int ind[4096]={};vector<int> q3;for(int k=0;k<4096;k++){
 if(ok(3,k))q3.push_back(k);
 for(int v=0;v<256;v++){bool b=true;for(int i=0;i<12&&b;i++)if(k>>i&1){auto [x,y]=edges[3][i];b=!((v>>x&1)&&(v>>y&1));}ind[k]+=b;}}
 uint64_t count=0;for(int a:q3)for(int b:q3)count+=ind[a&b];
 cout<<"representatives "<<H.size()<<" stabilizer_orbit_sum "<<sum<<" independent_labelled_count "<<count<<" >=20_edges "<<count_if(H.begin(),H.end(),[](u32 x){return pc(x)>=20;})<<endl;
 check(count==sum,"coverage failure");
}
struct Flag{int type,idx;};vector<Flag> flag[3];int nf[8]={},off[9]={};
void flags(){
 for(int s=0;s<=2;s++){int m=s==2?3:2;vector<int> id;for(int i=0;i<m;i++)id.push_back(i);
 vector<int> sm;for(int i=0;i<s;i++)sm.push_back(i);Map typ(m,s,embed(0,sm));
 int N=1<<edges[m].size();flag[s].resize(N,{-1,-1});
 // Map to canonical type then quotient unused coordinate permutations fixing the root pointwise.
 map<int,int> look[8];vector<pair<int,int>> canon(N,{-1,-1});
 for(int h=0;h<N;h++)if(ok(m,h)){
 int besttype=17,r0=-1;vector<int> perm0;
 for(int r=0;r<(1<<s);r++){auto p=id;do{Map g(m,m,embed(r,p));int t=typ.read(g.read(h));if(t<besttype){besttype=t;r0=r;perm0=p;}}
 while(next_permutation(p.begin(),p.begin()+s));}
 int t=(s==0?0:s==1?1:3);while(types[t]!=besttype)t++;
 // Label transport (r0,perm0) depends only on the type, not the extension colours.
 int val=N;do{val=min(val,int(Map(m,m,embed(r0,perm0)).read(h)));}while(next_permutation(perm0.begin()+s,perm0.end()));
 canon[h]={t,val};look[t][val]=0;
 }
 for(int t=0;t<8;t++)for(auto &kv:look[t])kv.second=nf[t]++;
 for(int h=0;h<N;h++)if(canon[h].first>=0){auto [t,b]=canon[h];flag[s][h]={t,look[t].at(b)};}
 }
 for(int t=0;t<8;t++)off[t+1]=off[t]+nf[t]*nf[t];}
u32 vs(int r,const vector<int>&d){u32 mask=0;for(int x:embed(r,d))mask|=1<<x;return mask;}
struct Emb{int s;vector<int> vertices;bool operator<(const Emb&o)const{return s!=o.s?s<o.s:vertices<o.vertices;}};
struct FastEmb{int face;array<u16,4096> index;};
struct Event{int cat,a,b;};
vector<Event> events;vector<FastEmb> embeds;vector<Lut> faces;
void schedule(bool finite){ // derive unique pairs by enumerating all labelled cube isometries, NOT the search schedule.
 vector<vector<int>> fv;for(int fixed=0;fixed<4;fixed++)for(int side=0;side<2;side++){
 vector<int> ds;for(int i=0;i<4;i++)if(i!=fixed)ds.push_back(i);fv.push_back(embed(side<<fixed,ds));faces.emplace_back(Map(4,3,fv.back()));}
 map<Emb,int> idx;
 auto number=[&](int s,int r,vector<int>d){
 Emb e{s,embed(r,d)};auto it=idx.find(e);if(it!=idx.end())return it->second;
 int f=0;vector<int> loc;for(;f<8;f++){loc.clear();for(auto v:e.vertices){auto j=find(fv[f].begin(),fv[f].end(),v);if(j!=fv[f].end())loc.push_back(j-fv[f].begin());}if(loc.size()==e.vertices.size())break;}
 check(f<8,"embedding");Map g(3,d.size(),loc);FastEmb a{};a.face=f;
 for(int k=0;k<4096;k++){auto h=flag[s][g.read(k)];a.index[k]=h.type<0?0:u16(256*h.type+h.idx);}
 int id=embeds.size();embeds.push_back(a);idx[e]=id;return id;};
 for(int cat=2;cat==2;cat++){
 int s=cat==3?0:cat;set<array<u32,3>> seen;for(int r=0;r<16;r++){vector<int> p={0,1,2,3};do{
 vector<int> dr(p.begin(),p.begin()+s),u,w;
 if(s==0){u={p[0],p[1]};w=cat==3?vector<int>{p[0],p[2]}:vector<int>{p[2],p[3]};}
 else if(s==1){u={p[0],p[1]};w={p[0],p[2]};}else{u={p[0],p[1],p[2]};w={p[0],p[1],p[3]};}
 auto a=vs(r,u),b=vs(r,w);if(!seen.insert({vs(r,dr),min(a,b),max(a,b)}).second)continue;
 events.push_back({cat,number(s,r,u),number(s,r,w)});
 }while(next_permutation(p.begin(),p.end()));}
 int expect[4]={48,96,24,192};check(int(seen.size())==expect[cat],"event count");
 }}
namespace ball {
// A radius-two ball is encoded by d root-to-singletons in axis order,
// then singleton-to-doubleton edges in lex order (singleton axis,added axis).
using Edge=pair<int,int>;
Edge und(int a,int b){return {min(a,b),max(a,b)};}
vector<Edge> bedges(int d){
 vector<Edge> e;for(int i=0;i<d;i++)e.push_back({0,1<<i});
 for(int i=0;i<d;i++)for(int j=0;j<d;j++)if(i!=j)e.push_back({1<<i,(1<<i)|(1<<j)});return e;
}
struct Pull{
 vector<int> slots;
 Pull(const vector<Edge>&outer,const vector<Edge>&inner,int base,const vector<int>&axes){
  auto vv=embed(base,axes);for(auto [x,y]:inner){auto p=und(vv[x],vv[y]);
  auto it=find(outer.begin(),outer.end(),p);check(it!=outer.end(),"not a coordinate restriction");slots.push_back(it-outer.begin());}}
 u32 operator()(u32 h)const{u32 a=0;for(int j=0;j<(int)slots.size();j++)a|=((h>>slots[j])&1)<<j;return a;}
};
struct LUT{
 array<array<u32,256>,4>a{};
 LUT(Pull g){for(int j=0;j<4;j++)for(u32 k=0;k<256;k++)a[j][k]=g(k<<(8*j));}
 u32 get(u32 h)const{return a[0][h&255]|a[1][h>>8&255]|a[2][h>>16&255]|a[3][h>>24];}
};
struct Census{
 int d;vector<u32>reps;vector<int> id;vector<Edge> e;
 explicit Census(int dimension):d(dimension),e(bedges(d)){
  id.assign(1u<<(d*d),-1);vector<LUT> autos;vector<int>p(d);iota(p.begin(),p.end(),0);do{autos.emplace_back(Pull(e,e,0,p));}while(next_permutation(p.begin(),p.end()));
  vector<u32> squares;for(int a=0;a<d;a++)for(int b=0;b<a;b++){u32 s=0;int cut=(1<<a)|(1<<b);
   for(int i=0;i<(int)e.size();i++)if(((e[i].first|e[i].second)&~cut)==0)s|=u32(1)<<i;check(pc(s)==4,"square");squares.push_back(s);}
  uint64_t sum=0,independent=0;
  for(u32 m=0;m<id.size();m++){
   if(id[m]>=0||any_of(squares.begin(),squares.end(),[=](u32 s){return (m&s)==s;}))continue;
   int stab=0,k=reps.size();reps.push_back(m);
   for(auto &g:autos){auto img=g.get(m);check(img>=m && (id[img]==-1||id[img]==k),"noncanonical");stab+=img==m;id[img]=k;}
   check(stab&&autos.size()%stab==0,"stabilizer");sum+=autos.size()/stab;
  }
  for(int root=0;root<1<<d;root++){uint64_t ways=1;for(int i=0;i<d;i++)for(int j=0;j<i;j++)ways*=((root>>i)&(root>>j)&1)?3:4;independent+=ways;}
  check(sum==independent,"B census");check((d==4 && reps.size()==2144)||(d==5 && reps.size()==170055),"B orbit count");
  cout<<"B"<<d<<" orbits "<<reps.size()<<" stabilizer_orbit_sum "<<sum<<" independent_labelled "<<independent<<endl;
 }
};
// Four-page edge book: color 0..7 records (at first endpoint,at second
// endpoint,parallel spine). For a present central edge color 7 is forbidden.
int bK=0;
vector<i64> bprice;
int pagekey(int t,array<int,4> a){
 sort(a.begin(),a.end());return 4096*t+a[0]+8*a[1]+64*a[2]+512*a[3];
}
int reverse_page(int x){return (x&4)|((x&1)<<1)|((x&2)>>1);}
// Degree elevation of the exact four-page inventory totals. For a color
// multiplicity vector a of weight k, each four-subset survives deletion of
// exactly k-4 of its pages' complement. Therefore
//    (k-4) S_k(a) = sum_j a_j S_{k-1}(a-e_j).
// This is an integer identity, with endpoint reversal included at k=4.
void read_inventory(ifstream& fs,int n,i64 scale2){
 bK=0;bprice.clear();if(fs.peek()==-1)return;
 int32_t p=0;fs.read((char*)&p,4);check(p>=4&&p<=16&&(!n||p<n),"inventory size");
 bK=p;bprice.resize(8192);fs.read((char*)bprice.data(),8*bprice.size());
 check(bool(fs)&&fs.peek()==-1,"inventory table");
 for(i64 q:bprice)check(q>=-10000000000000000LL&&q<=10000000000000000LL,"book overflow");
 i128 best=-((i128)1<<121);uint64_t census=0;
 for(int t=0;t<2;t++){
  unordered_map<uint64_t,i128> prev,cur;
  for(int k=4;k<=p;k++){
   cur.clear();vector<int>x(k,0);while(true){
    array<int,8> mult{};uint64_t key=0;
    for(int c:x){mult[c]++;key+=uint64_t(1)<<(5*c);}
    i128 v=0;
    if(k==4){array<int,4>a{x[0],x[1],x[2],x[3]};v=bprice[pagekey(t,a)];for(int&u:a)u=reverse_page(u);v+=bprice[pagekey(t,a)];}
    else{
     for(int c=0;c<8-t;c++)if(mult[c])v+=i128(mult[c])*prev.at(key-(uint64_t(1)<<(5*c)));
     check(v%(k-4)==0,"integer elevation");v/=k-4;
    }
    if(k<p)cur.emplace(key,v);else{census++;best=max(best,-v);}
    int i=k-1;while(i>=0&&x[i]==7-t)i--;if(i<0)break;int a=x[i]+1;fill(x.begin()+i,x.end(),a);
   }
   cur.swap(prev);
  }
 }
 auto choose=[](int n,int k){i64 a=1;for(int j=1;j<=k;j++)a=a*(n-j+1)/j;return a;};
 check(census==uint64_t(choose(p+7,7)+choose(p+6,6)),"inventory census");
 cout<<"inventories "<<census<<" D "<<p<<" numerator "<<dec(best)<<" denominator "<<dec(i128(scale2)*2*choose(p,4))<<endl;
}
int edgeb[32][32];i64 pagesum(u32 mask){
 if(!bK)return 0;
 auto b=[=](int x,int y){return (int)((mask>>edgeb[x][y])&1);};
 i64 a=0;for(int i=0;i<5;i++){array<int,4>s;int l=0;
  for(int j=0;j<5;j++)if(j!=i){
   int u=1<<i,v=1<<j,w=u|v;s[l++]=b(0,v)+2*b(u,w)+4*b(v,w);
  }a+=bprice[pagekey(b(0,1<<i),s)];
 }
 return a;
}

vector<i64> ell,Gram;
vector<LUT> at_vertex; vector<int> bid4;
Census& c4(){static Census obj(4);return obj;}
Census& c5(){static Census obj(5);return obj;}
void setup(i64 D,int n,const char*fname){
 ifstream f(fname,ios::binary);ell.resize(2144);Gram.resize(512*512);
 f.read((char*)ell.data(),8*ell.size());f.read((char*)Gram.data(),8*Gram.size());
 check(bool(f),"B table size");read_inventory(f,n,D);for(auto &v:{&ell,&Gram})for(auto a:*v)check(-10000000000000000LL<=a&&a<=10000000000000000LL,"B accumulator size");
 auto& c4=ball::c4();auto& c5=ball::c5();for(int j=0;j<(int)c5.e.size();j++){auto [x,y]=c5.e[j];edgeb[x][y]=edgeb[y][x]=j;}if(bid4.empty())bid4=c4.id;
 vector<int>axes{0,1,2,3};vector<Edge>E4=edges[4];for(auto&p:E4)p=und(p.first,p.second);
 if(at_vertex.empty())for(int v=0;v<16;v++)at_vertex.emplace_back(Pull(E4,c4.e,v,axes));
 vector<Edge>e3=bedges(3);vector<LUT>proj;array<vector<pair<LUT,LUT>>,5> f3;
 array<vector<u32>,5>pairmask;
 for(int i=0;i<5;i++){
  vector<int>other;for(int j=0;j<5;j++)if(i!=j)other.push_back(j);
  proj.emplace_back(Pull(c5.e,c4.e,0,other));
  for(auto j:other)for(auto k:other)if(j<k){
    f3[i].emplace_back(Pull(c5.e,e3,0,{i,j,k}),Pull(c5.e,e3,0,{i,k,j}));
    pairmask[i].push_back((1u<<j)|(1u<<k));}
 }
 // Probabilities conditional on uniform ordered pair draws in [n] minus i.
 // With m=n-1 available, denominator m(m-1), probabilities of overlap
 // 0,1,2 are (m-2)(m-3),4(m-2),2 divided by that denominator.
 i64 den=n?(n-1)*(n-2):1,L=60*den,w[3]={n?4LL*(n-3)*(n-4):4LL,n?4LL*(n-3):0LL,n?4LL:0LL};
 i128 best=-((i128)1<<121);u32 witness=0;
 for(auto m:c5.reps){
  i64 price=-pagesum(m);for(auto &p:proj){int id=bid4[p.get(m)];check(id>=0,"B5 face");price+=ell[id];}
  i64 sums[3]={};for(int i=0;i<5;i++){int ff[6];
   for(int j=0;j<6;j++)ff[j]=min(f3[i][j].first.get(m),f3[i][j].second.get(m));
   for(int j=0;j<6;j++)for(int k=j;k<6;k++)sums[pc(pairmask[i][j]&pairmask[i][k])]+=Gram[ff[j]*512+ff[k]];}
  i128 sc=-i128(L/5)*price;for(int i=0;i<3;i++)sc+=i128(sums[i])*w[i];
  if(sc>best){best=sc;witness=m;}
 }
 cout<<"B5 numerator "<<dec(best)<<" denominator "<<dec(i128(D)*L)<<" achieving_mask "<<witness<<endl;
}
i64 sum4(u32 m){
 i64 s=0;for(auto&g:at_vertex){int id=bid4[g.get(m)];if(id<0)abort();s+=ell[id];}return s;
}
} // namespace ball

// Called once per transcript, after the regenerated Q4 representatives have
// been independently checked. A rooted four-ball determines ALL edge-root
// and vertex-root terms. Tabulate those cheaply on its 2,144 orbits. Only
// the 24 square roots need pairs of complete 3-cube flags.
struct Case { int n; i64 D,L; bool negative; vector<i128> atv,sq; };
Case readcase(const char*path,int n,const char*extra,bool neg){
 ifstream f(path,ios::binary);i64 D;f.read((char*)&D,8);
 check(D>0&&D<=1000000000000000000LL,"bad scale");
 vector<i64>T(off[8]);f.read((char*)T.data(),T.size()*8);check(bool(f)&&f.peek()==-1,"H4 matrix size");
 for(i64 v:T)check(v>=-10000000000000000LL&&v<=10000000000000000LL,"H4 accumulator range");
 ball::setup(D,n,extra);
 i64 L=n?192LL*n*(n-1)*(n-2):96;
 i64 wo[4]={2,1,4,0},wd[3]={};
 if(n){wo[0]=L*(n-2)*(n-3)/(n*(n-1)*48);wd[0]=L/(n*(n-1)*48);
 wo[1]=L*(n-2)/((n-1)*96);wd[1]=L/(2*(n-1)*96);
 wo[2]=L*(n-3)/((n-2)*24);wd[2]=L/(2*(n-2)*24);
 wo[3]=L*4*(n-2)/(n*(n-1)*192);}
 auto term=[&](int cat,Flag a,Flag b){
  int t=a.type;check(t>=0&&t==b.type&&a.idx<nf[t]&&b.idx<nf[t],"incompatible flags");
  i64 cross=T[off[t]+a.idx*nf[t]+b.idx];
  i64 diag=T[off[t]+a.idx*(nf[t]+1)]+T[off[t]+b.idx*(nf[t]+1)];
  return i128(wo[cat])*cross+(cat<3?i128(wd[cat])*diag:0);
 };
 Case c{n,D,2*L,neg,vector<i128>(2144),vector<i128>(off[8])};
 auto &C4=ball::c4();vector<ball::Pull> pp;int idx[4][4];
 for(int i=0;i<4;i++)for(int j=0;j<4;j++)if(i!=j){idx[i][j]=pp.size();pp.emplace_back(C4.e,edges[2],0,vector<int>{i,j});}
 for(size_t i=0;i<C4.reps.size();i++){
  u32 m=C4.reps[i];i128 val=i128(2*L/16)*ball::ell[i];int mm[4][4];
  for(int j=0;j<4;j++)for(int k=0;k<4;k++)if(j!=k)mm[j][k]=pp[idx[j][k]](m);
  vector<pair<int,Flag>> v;
  for(int j=0;j<4;j++)for(int k=0;k<j;k++)v.push_back({(1<<j)|(1<<k),flag[0][mm[j][k]]});
  for(int j=0;j<6;j++)for(int k=0;k<j;k++)
   val+=2*term((v[j].first&v[k].first)?3:0,v[j].second,v[k].second);
  // Count each unordered edge-root with both orientations. Its pair term
  // is invariant under reversing the root (checked in Python).
  for(int a=0;a<4;a++)for(int j=0;j<4;j++)if(j!=a)for(int k=0;k<j;k++)if(k!=a)
   val+=term(1,flag[1][mm[a][j]],flag[1][mm[a][k]]);
  c.atv[i]=val;
 }
 for(int t=3;t<8;t++)for(int a=0;a<nf[t];a++)for(int b=0;b<nf[t];b++)
  c.sq[off[t]+a*nf[t]+b]=2*term(2,{t,a},{t,b});
 return c;
}
void replay(const vector<Case>&cc,const vector<int>&which,bool negative){
 const int count=which.size();if(!count)return;
 vector<i128>v(2144*count),sq(off[8]*count);
 for(int j=0;j<count;j++){auto&c=cc[which[j]];for(int i=0;i<2144;i++)v[i*count+j]=c.atv[i];for(int i=off[3];i<off[8];i++)sq[i*count+j]=c.sq[i];}
 vector<vector<i128>> best(omp_get_max_threads(),vector<i128>(count,-(i128(1)<<122)));
 vector<vector<int>> ids(best.size(),vector<int>(count,0));check(H[0]==0,"empty representative");
 #pragma omp parallel
 {int thr=omp_get_thread_num();vector<u16>flags_here(embeds.size());vector<i128>z(count);
 #pragma omp for
 for(int k=0;k<(negative?1:int(H.size()));k++){
  u32 x=H[k];u16 fac[8];for(int i=0;i<8;i++)fac[i]=faces[i].read(x);
  for(unsigned i=0;i<embeds.size();i++)flags_here[i]=embeds[i].index[fac[embeds[i].face]];
  for(int j=0;j<count;j++){auto&c=cc[which[j]];z[j]=i128(c.L/32)*c.D*pc(x);}
  for(auto&g:ball::at_vertex){int i=ball::bid4[g.get(x)];check(i>=0,"bad four-ball");auto*q=&v[i*count];
   for(int j=0;j<count;j++)z[j]+=q[j];}
  for(auto&e:events){int a=flags_here[e.a],b=flags_here[e.b],t=a>>8;
   check(t==(b>>8)&&t>=3&&e.cat==2,"square root");auto*q=&sq[(off[t]+(a%256)*nf[t]+(b%256))*count];
   for(int j=0;j<count;j++)z[j]+=q[j];}
  for(int j=0;j<count;j++)if(z[j]>best[thr][j]){best[thr][j]=z[j];ids[thr][j]=k;}
 }}
 for(int j=0;j<count;j++){int b=0;for(size_t t=1;t<best.size();t++)if(best[t][j]>best[b][j])b=t;
  auto&c=cc[which[j]];cout<<"H4 "<<which[j]<<" "<<dec(best[b][j])<<" "<<dec(i128(c.D)*c.L)<<" "<<H[ids[b][j]]<<" "<<(negative?1:H.size())<<endl;}
}
int main(int argc,char**argv){try{
 check(argc>=6&&(argc-2)%4==0,"usage: audit orbits (table dim extra neg)...");geometry();load(argv[1]);census();flags();schedule(false);
 vector<Case>cc;vector<int>pos,neg;
 for(int i=2;i<argc;i+=4){int n=stoi(argv[i+1]);bool m=stoi(argv[i+3]);check(n==0||(n>=5&&n<=100),"certificate n");
  cout<<"CASE "<<cc.size()<<endl;(m?neg:pos).push_back(cc.size());cc.push_back(readcase(argv[i],n,argv[i+2],m));}
 replay(cc,pos,false);replay(cc,neg,true);return 0;
 }catch(const exception&e){cerr<<"FAIL: "<<e.what()<<endl;return 1;}}

'''


# =============================================================================
# Suite 2: Pure full-Q4 primal SDP relaxation obstruction laws (zero-float)
# =============================================================================
def _primal_cube(m):
    return [(x, x ^ (1 << i)) for i in range(m) for x in range(1 << m) if not (x >> i) & 1]

_PRIMAL_Q3 = _primal_cube(3)
_PRIMAL_Q4 = [(v, v + 8) for v in range(8)] + [(u + a, v + a) for a in (8, 0) for u, v in _PRIMAL_Q3]
_PRIMAL_EDGE = {e: k for k, e in enumerate(_PRIMAL_Q4)}

@functools.lru_cache(None)
def _primal_proj(r, ds):
    v = [r]
    for i in ds:
        v += [x ^ (1 << i) for x in v]
    return tuple(_PRIMAL_EDGE[tuple(sorted((v[a], v[b])))] for a, b in _primal_cube(len(ds)))

def _primal_face(h, r, ds):
    return sum(((h >> j) & 1) << i for i, j in enumerate(_primal_proj(r, ds)))

def _primal_shapes():
    axes = set(range(4))
    S = []
    for r in range(16):
        S.append((0, r, (), list(it.combinations(range(4), 2))))
    for s in (1, 2):
        for root in it.combinations(range(4), s):
            rm = sum(1 << i for i in root)
            for v in range(16):
                if v & rm:
                    continue
                for order in it.permutations(root):
                    for shift in range(16):
                        if shift & ~rm:
                            continue
                        S.append((s, v ^ shift, order, [(d,) for d in sorted(axes - set(root))]))
    return S

def _primal_check_psd(M):
    """Exact rational symmetric Schur complement check (including singular blocks)."""
    R = [[F(x) for x in row] for row in M]
    for k in range(len(R)):
        t = R[k][k]
        need(t >= 0, 'negative diagonal pivot')
        if not t:
            need(not any(R[k][k + 1:]), 'nonzero off-diagonal at zero pivot')
            continue
        for i in range(k + 1, len(R)):
            r = R[k][i] / t
            if r:
                for j in range(i, len(R)):
                    R[i][j] -= r * R[k][j]

def _primal_compute(data):
    n = data['n']
    need(type(n) is int and n >= 4, 'finite dimension')
    L = 192 * n * (n - 1) * (n - 2)
    wo = (
        L * (n - 2) * (n - 3) // (n * (n - 1) * 48),
        L * (n - 2) // ((n - 1) * 96),
        L * (n - 3) // ((n - 2) * 24),
        L * 4 * (n - 2) // (n * (n - 1) * 192),
    )
    wd = (
        L // (n * (n - 1) * 48),
        L // (2 * (n - 1) * 96),
        L // (2 * (n - 2) * 24),
        0,
    )
    Y = collections.defaultdict(lambda: collections.defaultdict(int))
    tot = score = 0
    seen = set()
    sched = _primal_shapes()
    for h, z in data['support']:
        need(type(h) is int and 0 <= h < (1 << 32) and h not in seen and type(z) is int and z > 0, 'invalid law')
        seen.add(h)
        tot += z
        score += z * h.bit_count()
        for ds in it.combinations(range(4), 2):
            mask = sum(1 << i for i in ds)
            for r in range(16):
                if not (r & mask):
                    need(_primal_face(h, r, ds) != 15, 'not square free')
        for s, r, ds, ex in sched:
            t = _primal_face(h, r, ds)
            M = Y[s, t]
            fi = [min(_primal_face(h, r, ds + f), _primal_face(h, r, ds + f[::-1])) if s == 0 else _primal_face(h, r, ds + f) for f in ex]
            for i, j in it.combinations(range(len(ex)), 2):
                a, b = fi[i], fi[j]
                c = 3 if s == 0 and (set(ex[i]) & set(ex[j])) else s
                M[a, b] += z * wo[c]
                M[b, a] += z * wo[c]
                if wd[c]:
                    M[a, a] += 2 * z * wd[c]
                    M[b, b] += 2 * z * wd[c]
    need(tot > 0, 'empty law')
    for M in Y.values():
        fl = sorted(set(i for i, _ in M))
        _primal_check_psd([[M[i, j] for j in fl] for i in fl])
    return F(score, 32 * tot)

PRIMAL_CLAIMS = [
    (8,  'floor8.json',  '235127287245/347826087008'),
    (9,  'floor9.json',  '10666666601287/16000000007312'),
    (10, 'floor10.json', '10515188745587/16000000000144'),
]

def verify_primal_relaxation_floors():
    print("\n=== Suite 2: Pure Full-Q4 Primal Relaxation Floors (Exact Rational Schur) ===")
    for expected_n, fn, expected_q in PRIMAL_CLAIMS:
        data = json.loads((HERE / 'data' / fn).read_text(encoding='utf-8'))
        need(data['n'] == expected_n, f'{fn}: dimension mismatch')
        q = _primal_compute(data)
        need(q == F(data['full_sdp_lower']) == F(expected_q), f'{fn}: density mismatch')
        edge_eq = q * expected_n * (1 << (expected_n - 1))
        print(f"primal floor n={expected_n} support={len(data['support'])} density={q} edge_equiv>{int(edge_eq)} ({edge_eq.numerator // edge_eq.denominator}.{((edge_eq.numerator % edge_eq.denominator) * 10000) // edge_eq.denominator:04d})")
        if expected_n == 8:
            # Proves pure-Q4 SDP cannot prove ex(Q_8, C_4) <= 691 (floor > 692)
            need(edge_eq > 692, 'expected pure-Q4 floor on Q8 > 692')
            # Mutation test 1: injecting a C4-containing Q4 mask must fail
            mut_c4 = {'n': 8, 'support': list(data['support']) + [[(1 << 32) - 1, 1]], 'full_sdp_lower': data['full_sdp_lower']}
            try:
                _primal_compute(mut_c4)
            except ValueError as err:
                print(f"primal mutation (C4 mask) rejected: {err}")
            else:
                raise ValueError('primal C4 mutation not rejected')
            # Mutation test 2: non-positive weight must fail
            mut_neg = {'n': 8, 'support': [[data['support'][0][0], -1]] + list(data['support'][1:]), 'full_sdp_lower': data['full_sdp_lower']}
            try:
                _primal_compute(mut_neg)
            except ValueError as err:
                print(f"primal mutation (negative weight) rejected: {err}")
            else:
                raise ValueError('primal negative-weight mutation not rejected')
    print("SUITE 2 PASS")


# =============================================================================
# Suite 3: Period-<=16 translation-invariant extremal theorem (n = 7,8,9,10)
# =============================================================================
def _p16_perm(a, t):
    return sum(1 << (x ^ t) for x in range(16) if (a >> x) & 1)

@functools.lru_cache(None)
def _p16_domains(t, b):
    cells = sorted({(1 << x) | (1 << (x ^ t)) for x in range(16)})
    return tuple(
        (t, a, tuple(_p16_perm(a, u) & a for u in range(16)))
        for comb in it.combinations(cells, b // (2 if t else 1))
        for a in [sum(comb)]
    )

def _p16_ok(p, q):
    return not (p[2][q[0]] & q[2][p[0]])

def _p16_extend(H, count, goal, best):
    used = {p[0] for p in H}
    rem = {c: [p for p in _p16_domains(c, count) if all(_p16_ok(y, p) for y in H)] for c in range(16) if c not in used}
    rem = {c: z for c, z in rem.items() if z}
    def rec(h, d):
        nonlocal best
        if len(h) > len(best):
            best = h
        while len(h) + len(d) > len(best) and len(best) < goal:
            c = min(d, key=lambda i: (len(d[i]), i))
            row = d.pop(c)
            for p in row:
                nxt = {k: [q for q in r if _p16_ok(p, q)] for k, r in d.items()}
                rec(h + [p], {k: r for k, r in nxt.items() if r})
        return best
    return rec(H, rem)

def _p16_lift(H):
    n = len(H)
    E = []
    s = [0] * (1 << n)
    for x in range(1, 1 << n):
        s[x] = s[x & (x - 1)] ^ H[(x & -x).bit_length() - 1][0]
    for x in range(1 << n):
        for j, p in enumerate(H):
            if not ((x >> j) & 1) and ((p[1] >> s[x]) & 1):
                E.append((x, x ^ (1 << j)))
    return E

def _verify_c4_free_graph(n, edges):
    N = 1 << n
    edge_set = set()
    present_dir = [bytearray(N) for _ in range(n)]
    deg = [0] * N
    for u, v in edges:
        if u > v:
            u, v = v, u
        need(0 <= u < v < N, 'vertex out of range')
        diff = u ^ v
        need(diff != 0 and (diff & (diff - 1)) == 0, 'non-hypercube edge')
        need((u, v) not in edge_set, 'duplicate edge')
        edge_set.add((u, v))
        d = diff.bit_length() - 1
        present_dir[d][u] = 1
        present_dir[d][v] = 1
        deg[u] += 1
        deg[v] += 1
    n0 = n2o = n4 = total = 0
    for i in range(n):
        bi = 1 << i
        pi = present_dir[i]
        for j in range(i + 1, n):
            bj = 1 << j
            pj = present_dir[j]
            mask = bi | bj
            for x in range(N):
                if x & mask:
                    continue
                total += 1
                a, c, b, d = pi[x], pi[x ^ bj], pj[x], pj[x ^ bi]
                s = a + b + c + d
                if s == 4:
                    n4 += 1
                elif s == 0:
                    n0 += 1
                elif s == 2 and a == c and b == d:
                    n2o += 1
    need(total == (n * (n - 1) // 2) * (1 << (n - 2)), 'square count mismatch')
    need(n4 == 0, f'NOT C4-FREE: {n4} four-cycles')
    # Also check square-defect identity sum (2 deg - n)^2 = n * 2^n + 8 * (n0 - n2o)
    sum_h2 = sum((2 * dv - n) ** 2 for dv in deg)
    need(sum_h2 == n * N + 8 * (n0 - n2o), 'square-defect identity mismatch')
    return edge_set

def _p16_signatures(n, T):
    seen = 0
    def rec(A, hi, m, total, z):
        nonlocal seen
        if total + hi * m + max(0, z) <= T:
            return
        if m:
            for k in range(0, hi + 1, 2):
                rec(A + [k], k, m - 1, total + k, z)
            return
        a = sorted(A + ([z] if z >= 0 else []), reverse=True)
        if sum(a[:2]) > 24 or sum(a[:5]) > 56:
            return
        seen += 1
        if z >= 0 and z + A[0] // 2 > 16:
            return
        if z > 8 and A[0] + A[1] == 24:
            return
        high = sum(b >= 12 for b in A)
        large = sum(b >= 10 for b in A)
        if high >= 1 and large > 8:
            return
        if high >= 2 and large > 7:
            return
        if high >= 3 and large > 5:
            return
        if z == 11 and A.count(10) >= 9:
            return
        raise AssertionError(('unexcluded', z, A))
    for z in range(-1, 17):
        rec([], 16, n - int(z >= 0), 0, z)
    return seen

def verify_period16_extremal():
    print("\n=== Suite 3: Exact Period-<=16 Translation-Invariant Extrema (Q7..Q10) ===")
    h1 = _p16_extend([_p16_domains(1, 12)[0]], 10, 18, [])
    h2 = []
    two = three = mx = 0
    for a, b in it.product(_p16_domains(1, 12), _p16_domains(2, 12)):
        if not _p16_ok(a, b):
            continue
        two += 1
        h2 = _p16_extend([a, b], 10, 18, h2)
        for c in _p16_domains(4, 12):
            if not (_p16_ok(c, a) and _p16_ok(c, b)):
                continue
            three += 1
            mx = max(mx, sum(
                any(all(_p16_ok(p, q) for q in (a, b, c)) for p in _p16_domains(d, 10))
                for d in range(1, 16) if d not in (1, 2, 4)
            ))
    need((len(h1), len(h2), 3 + mx) == (8, 7, 5), 'heavy subset bounds mismatch')
    print(f"heavy subset bounds: (8, 7, 5) verified; heavy pairs={two}, triples={three}")

    for n, T in [(7, 74), (8, 84), (9, 92), (10, 100)]:
        cnt = _p16_signatures(n, T)
        for m in range(n - 1):
            bound = (84 if m == 8 else (10 * m + 6 if m >= 5 else min(56, 16 * m)))
            need(bound + 16 <= T, 'multi-zero bound failed')
        print(f"n={n} signatures_excluded={cnt} exact_max={T * (1 << (n - 5))}")

    pm = [
        (1, 16383), (2, 62805), (4, 61030), (8, 59881), (14, 59035),
        (11, 55989), (7, 56154), (13, 54702), (0, 27030), (0, 38505),
    ]
    H = [next(p for p in _p16_domains(c, m.bit_count()) if p[1] == m) for c, m in pm]
    for n, opt in [(7, 296), (8, 672), (9, 1472), (10, 3200)]:
        need(all(_p16_ok(p, q) for j, p in enumerate(H[:n]) for q in H[j + 1:n]), 'extremizer mask conflict')
        E = _p16_lift(H[:n])
        need(len(E) == opt, f'n={n} edge count mismatch')
        edge_set = _verify_c4_free_graph(n, E)
        # Mandatory C4-creating mutation check for every n in {7,8,9,10}
        N = 1 << n
        mutated_ok = False
        for i in range(n):
            bi = 1 << i
            for j in range(i + 1, n):
                bj = 1 << j
                mask = bi | bj
                for x in range(N):
                    if x & mask:
                        continue
                    sq = [
                        (min(x, x ^ bi), max(x, x ^ bi)),
                        (min(x ^ bj, x ^ bi ^ bj), max(x ^ bj, x ^ bi ^ bj)),
                        (min(x, x ^ bj), max(x, x ^ bj)),
                        (min(x ^ bi, x ^ bi ^ bj), max(x ^ bi, x ^ bi ^ bj)),
                    ]
                    missing = [e for e in sq if e not in edge_set]
                    if len(missing) == 1:
                        try:
                            _verify_c4_free_graph(n, E + [missing[0]])
                        except ValueError:
                            mutated_ok = True
                            break
                        raise ValueError(f'n={n}: C4 mutation not rejected')
                if mutated_ok:
                    break
            if mutated_ok:
                break
        need(mutated_ok, f'n={n}: failed to run C4 mutation test')
        print(f"n={n} extremizer verified: {opt} edges, C4-free, square-defect OK, C4 mutation rejected")
    print("SUITE 3 PASS")


def main():
    print("=== Suite 1: Coupled H4 + B5 + Lattice Cuts + Edge-Book Upper Bounds ===")
    verify_coupled_upper_bounds()
    verify_primal_relaxation_floors()
    verify_period16_extremal()
    print("\nALL ERDOS #86 EXACT VERIFICATION SUITES PASSED")


if __name__ == '__main__':
    main()
