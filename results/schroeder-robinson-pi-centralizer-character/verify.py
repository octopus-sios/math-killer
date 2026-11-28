#!/usr/bin/env python3
"""Exact checks of the unitary Weil row formulas. Standard library for the default checks.

Compare log-coefficient recurrences with explicit conjugacy parameters, keeping
character values in Z[X]/Phi_(q+1). For SU(3,2) also use actual matrices. Use --tables GAP for the CTblLib sweep.
"""
import sys
from collections import defaultdict
from functools import cache
from itertools import combinations, permutations, product
from math import gcd, lcm


def divisors(x):
    return [d for d in range(1, x + 1) if x % d == 0]


@cache
def primes(x):
    out = set()
    d = 2
    while d * d <= x:
        if x % d == 0:
            out.add(d)
            while x % d == 0:
                x //= d
        d += 1
    return frozenset(out | ({x} if x > 1 else set()))


def pi_part(x, pi):
    a = 1
    for p in pi:
        while x % p == 0:
            a *= p
            x //= p
    return a


def tot(x):
    return sum(gcd(i, x) == 1 for i in range(1, x + 1))


def exact(x, d):
    a, b = divmod(x, d)
    assert b == 0, (x, d)
    return a


def divide_monic(f, g):
    f = f[:]
    h = [0] * (len(f) - len(g) + 1)
    for i in reversed(range(len(h))):
        h[i] = f[i + len(g) - 1]
        for j, c in enumerate(g):
            f[i + j] -= h[i] * c
    return h, f


@cache
def cyclotomic(m):
    f = [-1] + [0] * (m - 1) + [1]
    for d in divisors(m)[:-1]:
        f, rem = divide_monic(f, cyclotomic(d))
        assert not any(rem)
    return f


def weil_sum(q, n, det_kernels, r, k):
    """Entry (det index i, scalar index j) sums (-q)^dim ker(z^j g-I)."""
    M = q + 1
    f = [0] * M
    for i, weights in det_kernels.items():
        for j, w in enumerate(weights):
            f[(k * i - r * j) % M] += (-1)**n * w
    _, f = divide_monic(f, cyclotomic(M))
    assert not any(f[1:]), f
    return exact(f[0], M)


def exp_series(lognums):
    c = [1]
    for m in range(1, len(lognums)):
        c.append(exact(sum(lognums[i] * c[m-i] for i in range(1, m+1)), m))
    return c


@cache
def series(q, n, pi, k):
    a = pi_part(q+1, pi)
    L = a // gcd(a, k)
    alpha, beta = [0], [0]
    for m in range(1, n+1):
        js = divisors(m) if primes(q) <= pi else [1]
        A = sum(j * pi_part(q**(m//j) - (-1)**(m//j), pi) for j in js if j % L == 0)
        alpha.append(A)
        beta.append((-1)**m * (A + sum(j * ((-q)**(m//j) - 1) for j in js)))
    return exp_series(alpha)[n], exp_series(beta)[n]


@cache
def U(q, n, pi, r, k):
    M = q + 1
    a = pi_part(M, pi)
    if (r + n*k) % a:
        return 0
    A, B = series(q, n, pi, k)
    c = M//a - 1 if r == 0 else (-1 if r % a == 0 else 0)
    return exact(a * (B + (-1)**n * c * A), M)


def special(q, n, pi, r, D):
    M = q + 1
    a = pi_part(D, pi)
    ans = 0
    for e in divisors(a):
        for v in divisors(gcd(M, n//e)):
            if v > 1 and not primes(q) <= pi:
                continue
            m = exact(n, e*v)
            ans += tot(e)*tot(v)*(-1)**(n-m)*sum(
                (-1)**((e-1)*v*m*k) * U(q, m, pi, s, v*k % M)
                for s in range(M) if (e*s-r) % M == 0 for k in range(M))
    return exact(ans, M*a)


class Classes:
    """Enumerate blocks (orbit, length), as multisets of total dimension n."""

    def __init__(self, q, n):
        M = q + 1
        orders = [q**d - (-1)**d for d in range(1, n+1)]
        self.mod = V = lcm(*orders)
        self.step = T = V//M
        left = {k*(V//h) for h in orders for k in range(h)}
        self.root = {}
        blocks = []
        self.data = {}
        while left:
            x = min(left)
            y, orbit = x, []
            while y in left:
                left.remove(y)
                self.root[y] = x
                orbit.append(y)
                y = -q*y % V
            assert y == x
            for j in range(1, n//len(orbit)+1):
                key = (x, j)
                blocks.append((key, j*len(orbit)))
                self.data[key] = (sum(orbit)*j, primes(V//gcd(V, x)) |
                                  (primes(q) if j > 1 else frozenset()))
        types = {}
        def emit(rest, lo, seq):
            if rest:
                for i in range(lo, len(blocks)):
                    key, w = blocks[i]
                    if w <= rest:
                        emit(rest-w, i, seq+(key,))
                return
            det = exact(sum(self.data[key][0] for key in seq) % V, T)
            lens = [0]*M
            for x, j in seq:
                if x % T == 0:
                    lens[-(x//T) % M] += 1
            weights = tuple((-q)**l for l in lens)
            support = frozenset().union(*(self.data[key][1] for key in seq))
            types[seq] = (support, det, gcd(M, *(j for x, j in seq)), weights)
        emit(n, 0, ())
        self.types = types

    def shift(self, seq, i):
        return tuple(sorted((self.root[(x+i*self.step) % self.mod], j) for x, j in seq))


def addweights(a, b, h=1):
    for j in range(len(b)):
        a[j] += h*b[j]


def predicted_zero(q, n, pi, r, k=None):
    """None for a descended special row; a twist index k for a full-unitary row."""
    M = q+1
    a = pi_part(M, pi)
    special_row = k is None
    if (r % gcd(n, a) if special_row else (r+n*k) % a):
        return True
    if r:
        return False
    odd_complete = n % 2 and all(primes(q**d+1) <= pi for d in range(1, n+1, 2))
    small = (n, q) == (3, 2) and 2 in pi and 3 not in pi
    return bool(small or (odd_complete and (gcd(n, M) == 1 if special_row else k % M == 0)))


def check(q, n, short=False):
    C = Classes(q, n)
    M = q+1
    base = defaultdict(lambda: [0]*M)
    for pi, det, _, w in C.types.values():
        addweights(base[pi, det], w)
    ps = sorted(set().union(*(pi for pi, _ in base)))
    subsets = ([frozenset(u) for j in range(len(ps)+1) for u in combinations(ps, j)]
               if not short else list(map(frozenset, [[], ps, [2], [3], [2,3], ps[1:]])))
    GU_cases = SQ_cases = 0
    sample = {}
    for pi in subsets:
        counts = defaultdict(lambda: [0]*M)
        for (support, det), w in base.items():
            if support <= pi:
                addweights(counts[det], w)
        for r, k in product(range(M), repeat=2):
            val = weil_sum(q,n,counts,r,k)
            assert val == U(q,n,pi,r,k) and val >= 0, (q,n,pi,r,k,val)
            assert (val == 0) == predicted_zero(q,n,pi,r,k), (q,n,pi,r,k,val)
            GU_cases += 1
        for D in divisors(gcd(n, M)):
            a = pi_part(D, pi)
            seen = set()
            sums = [0]*M
            for seq, (support, det, h, w) in C.types.items():
                if det or not support <= pi or seq in seen:
                    continue
                for i in range(0, M, M//a):
                    alt = C.shift(seq, i)
                    sp, dt, h2, _ = C.types[alt]
                    assert sp <= pi and dt == 0 and h2 == h
                    seen.add(alt)
                addweights(sums, w, h)
            for r in range(0, M, D):
                val = weil_sum(q,n,{0:sums},r,0)
                assert val == special(q,n,pi,r,D) and val >= 0, (q,n,pi,r,D,val)
                assert (val == 0) == predicted_zero(q,n,pi,r), (q,n,pi,r,D,val)
                SQ_cases += 1
                if r == 0 and n % 2 and gcd(n,M) == 1:
                    zero = all(primes(q**d+1) <= pi for d in range(1,n+1,2))
                    assert (val == 0) == zero
                    if (q,n) == (2,5):
                        sample[tuple(sorted(pi))] = val
    print(f"GU_{n}({q}): {len(C.types)} classes, {GU_cases} twisted rows; "
          f"{SQ_cases} special/central-quotient rows agree")
    if sample:
        print("PSU_5(2), degree 10: pi={} -> %d; {2} -> %d; {3,11} -> %d; full -> %d"
              % (sample[()], sample[2,], sample[3,11], sample[tuple(ps)]))


@cache
def absolute_bound(q, m):
    # T_m = [t^m] product_j (1-t^(2j))/(1-q t^j)^2
    c = [1] + [0]*m
    for j in range(1,m+1):
        for s in range(m,2*j-1,-1):
            c[s] -= c[s-2*j]
        for _ in range(2):
            for s in range(j,m+1):
                c[s] += q*c[s-j]
    return c[m]


def finite_tail():
    assert 3*3**15 > 16*32**3*34 and 3*101**2 > 16*6**3*8
    pending = set()
    pairs = 0
    for n in range(4,32,2):
        for q in range(3,101,2):  # includes all prime powers in range
            M = q + 1
            g = gcd(M,n)
            pairs += 1
            for a0 in divisors(g):
                bad = sum(tot(e)*tot(v)*e*absolute_bound(q, n//(e*v))
                          for e in divisors(a0) for v in divisors(gcd(g,n//e))
                          if (n//(e*v)) % 2)
                if a0*(q**n-2*q**(n//2)-3) <= n*M*bad:
                    pending.add((q,n))
    assert pairs == 686
    assert pending == {(3,4),(3,6),(5,6),(3,10)}
    print(f"even-rank estimate: {pairs} bounded parameter pairs; "
          f"exact remaining (q,n) = {sorted(pending)}")
    for q,n in sorted(pending):
        M = q+1
        ps = sorted(primes(q).union(*(primes(q**i-(-1)**i) for i in range(1,n+1))))
        cases = 0
        smallest = central_min = None
        for j in range(len(ps)+1):
            for u in combinations(ps,j):
                pi = frozenset(u)
                for D in divisors(gcd(n,M)):
                    for r in range(0,M,D):
                        val = special(q,n,pi,r,D)
                        assert val >= 0, (q,n,pi,r,D,val)
                        smallest = val if smallest is None else min(val,smallest)
                        compatible = r % gcd(n,pi_part(M,pi)) == 0
                        assert (val > 0) == compatible
                        if compatible:
                            central_min = val if central_min is None else min(val,central_min)
                        cases += 1
        assert central_min == {(3,4):13, (3,6):115, (5,6):2004, (3,10):9602}[q,n]
        assert cases == {(3,4):112, (3,6):384, (5,6):1536, (3,10):12288}[q,n]
        assert smallest == 0
        print(f"  q={q}, n={n}: {2**len(ps)} prime sets, {cases} quotient/row sums, min={smallest}, central-compatible min={central_min}")


def matrix_check():
    """Independent SU_3(2) and PSU_3(2) conjugacy orbits over F4=F2[t]/(t²+t+1)."""
    mul = ((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))
    conj = (0,1,3,2)
    def dot(x, y):
        return mul[x[0]][y[0]] ^ mul[x[1]][y[1]] ^ mul[x[2]][y[2]]
    def herm(x, y):
        return dot(x, tuple(conj[i] for i in y))
    def mat(A, B):
        return tuple(tuple(dot(x, y) for y in zip(*B)) for x in A)
    def adj(A):
        return tuple(tuple(conj[y] for y in x) for x in zip(*A))
    def scale(A,s):
        return tuple(tuple(mul[s][v] for v in row) for row in A)
    def det(A):
        z = 0
        for i,j,k in permutations(range(3)):
            z ^= mul[A[0][i]][mul[A[1][j]][A[2][k]]]
        return z
    vec = list(product(range(4), repeat=3))
    ones = [x for x in vec if herm(x, x) == 1]
    group = [A for A in product(ones, repeat=3) if det(A) == 1 and
             all(herm(A[i], A[j]) == 0 for i,j in combinations(range(3), 2))]
    I = ((1,0,0),(0,1,0),(0,0,1))
    for D in (1,3):
        def canon(A):
            return A if D == 1 else min(scale(A,s) for s in (1,2,3))
        left = {canon(A) for A in group}
        assert len(left) == 216//D
        rows = []
        while left:
            A = min(left)
            orbit = {canon(mat(mat(g,A),adj(g))) for g in group}
            assert orbit <= left
            left -= orbit
            B, order = A, 1
            while canon(B) != canon(I):
                B = mat(B,A)
                order += 1
                assert order <= 216
            w = []
            for s in (1,2,3):
                f = sum(tuple(mul[s][dot(row,x)] for row in A) == x for x in vec)
                w.append((-2)**{1:0, 4:1, 16:2, 64:3}[f])
            rows.append((primes(order),w))
        for pi in map(frozenset, ([],[2],[3],[2,3])):
            kernels = [0]*3
            for support,w in rows:
                if support <= pi:
                    addweights(kernels,w)
            for r in range(0,3,D):
                assert weil_sum(2,3,{0:kernels},r,0) == special(2,3,pi,r,D)
        print(f"matrix SU_3(2)/C{D}: order {216//D}, {len(rows)} classes; all rows agree")


def rank_one_checks():
    # Sum the two series over inversion orbits of the actual cyclic tori.
    # Trace to Q exactly: sum_{a in units mod t} exp(2pi i a*l/t)
    # is phi(t)*mu(h)/phi(h), h=t/gcd(t,l).
    @cache
    def ram(t, l):
        h = t//gcd(t,l)
        ps = primes(h)
        mu = (-1)**len(ps) if all(h % (p*p) for p in ps) else 0
        return exact(tot(t)*mu, tot(h))
    cases = 0
    for q in (4,5,7,8,9,11,13,16,17,19,23,25,27,32):
        d = gcd(2,q-1)
        ps = sorted(primes(q*(q*q-1)))
        for c in divisors(d):
            Z = d//c
            for sign in (1,-1):  # principal for +1, cuspidal for -1
                t = (q-sign)//c
                for r in range(1,t):
                    for s in range(len(ps)+1):
                        for subset in combinations(ps,s):
                            pi = frozenset(subset)
                            P = pi_part(t,pi)
                            z = pi_part(Z,pi)
                            i = int(primes(q) <= pi)
                            # Contributions weighted by phi(t): central,
                            # central times unipotent, then semisimple pairs.
                            central = sum(ram(t,r*x % t) for x in range(0,t,t//z))
                            tr = central*(q+sign+sign*i*d)
                            correction = 0
                            for x in range(0,t,t//P):
                                if x % (t//z) == 0 or x > (-x) % t:
                                    continue
                                tr += sign*2*ram(t,r*x % t)
                                if x == (-x) % t:
                                    correction = (-1)**r
                            val = exact(tr,tot(t))
                            prediction = (z*(q+sign*i*d)
                                          + sign*((P if r % P == 0 else 0)+correction)
                                          if r % z == 0 else 0)
                            assert val == prediction and val >= 0
                            if c == d:
                                assert val > 0  # full support on simple PSL2
                            if 2*r == t:
                                assert val % 2 == 0  # the two exceptional rows
                            cases += 1
    print(f"rank-one series: {cases} exact torus-orbit sums agree")


def mutation_check():
    # At pi empty the identity is the only class. Change its 1-eigenspace
    # dimension from five to four; the exact comparison must not accept it.
    good = [(-2)**5,1,1]
    expected = U(2,5,frozenset(),0,0)
    assert weil_sum(2,5,{0:good},0,0) == expected == 10
    try:
        assert weil_sum(2,5,{0:[(-2)**4,1,1]},0,0) == expected
    except AssertionError:
        print("PASS: corrupted identity eigenspace rejected")
    else:
        raise AssertionError("corrupted witness accepted")



def alternating_check(n):
    """Trace the actual centralizer-induced modules of §7 on even permutations."""
    V = lcm(*range(1, n+1))
    even = []
    reps = {}
    for x in permutations(range(n)):
        seen = set()
        cycles = []
        for j in range(n):
            if j in seen:
                continue
            c = []
            while j not in seen:
                seen.add(j)
                c.append(j)
                j = x[j]
            cycles.append(c)
        if (n-len(cycles)) % 2:
            continue
        pos = {z: i for c in cycles for i, z in enumerate(c)}
        even.append((x, cycles, pos))
        reps[tuple(sorted(map(len, cycles)))] = x
    ps = sorted(primes(V)-{2})
    count = 0
    for shape, g in reps.items():
        # Contributions to the induced trace come exactly from indices x
        # fixed by g. For each cycle of x read the rotation applied by g.
        shifts = [sum(pos[g[c[0]]] * (V//len(c)) for c in cs)
                  for x, cs, pos in even if all(g[x[j]] == x[g[j]] for j in range(n))]
        for a in range(len(ps)+1):
            for u in combinations(ps, a):
                pi = {2, *u}
                k = pi_part(V, pi)
                poly = [0]*V
                for h in shifts:
                    poly[h*k % V] += 1
                wanted = len(shifts) if primes(lcm(*shape)) <= pi else 0
                poly[0] -= wanted
                assert not any(divide_monic(poly, cyclotomic(V))[1]), (n, shape, pi)
                count += 1
    print(f"A_{n}: induced traces match local centralizers in {count} type/prime-set checks")


TABLE_SWEEP = r"""
if LoadPackage("ctbllib") <> true then Error("need CTblLib"); fi;
CheckTable := function(t, exactOrders)
  local ord, keys, blocks, cols, weights, lo, row, need, choices, d, keep, count;
  ord := OrdersClassRepresentatives(t);
  if exactOrders then keys := ord;
  else keys := List(ord,x->Product(PrimeDivisors(x))); fi;
  blocks := Set(keys);
  cols := List(blocks,d->Positions(keys,d));
  if blocks[1]<>1 or cols[1]<>[1] then Error("identity block"); fi;
  need := []; count := 0;
  for row in Irr(t) do
    weights := List(cols,b->Sum(row{b}));
    if not ForAll(weights,IsInt) then Error("noninteger block"); fi;
    lo := weights[1]+Sum(weights{[2..Length(weights)]},x->Minimum(x,0));
    if exactOrders and lo<1 then Error("order-set strictness failed"); fi;
    if lo<0 then Add(need,weights); fi;
    count := count+1;
  od;
  if count<>Length(ord) then Error("incomplete table"); fi;
  choices := PrimeDivisors(Size(t));
  if Length(need)>0 then
    for d in List(Combinations(choices),Product) do
      keep := Filtered([1..Length(blocks)],j->d mod blocks[j]=0);
      if ForAny(need,w->Sum(w{keep})<0) then
        Error("negative in ",Identifier(t)," for prime product ",d);
      fi;
    od;
  fi;
  return [1,count,count*2^Length(choices)];
end;
spor := ["M11","M12","M22","M23","M24","J1","J2","J3","J4","Co1","Co2","Co3",
  "Fi22","Fi23","F3+","HS","McL","He","Ru","Suz","ON","HN","Ly","Th","B","M"];;
s := Sum(spor,n->CheckTable(CharacterTable(n),true));;
if s<>[26,1396,6941472] then Error("sporadic coverage"); fi;
Print("All order selections strictly positive: 26 sporadic tables, 1396 rows\n");
names := Set(Concatenation(spor, AllCharacterTableNames(IsSimple,true,IsDuplicateTable,false),
  AllCharacterTableNames(IsAlmostSimple,true,IsDuplicateTable,false),
  AllCharacterTableNames(IsQuasisimple,true,IsDuplicateTable,false)));;
s := Sum(names,n->CheckTable(CharacterTable(n),false));;
Print("CTblLib ",PackageInfo("ctbllib")[1].Version,": [tables,rows,row/prime-set pairs] = ",s,"\n");
if PackageInfo("ctbllib")[1].Version="1.3.11" and s<>[444,45450,12142258] then Error("selection changed"); fi;
wr := [["A5",2],["A5",3],["A5",4],["2.A5",2],["U5(2)",2],["L2(7)",3],["A5.2",3]];;
s := Sum(wr,p->CheckTable(CharacterTableWreathSymmetric(CharacterTable(p[1]),p[2]),false));;
if s<>[7,1742,23336] then Error("wreath coverage"); fi;
Print("Wreath products: ",s,"\n");
CycleCheck:=function(H,l)
 local t,w,wr,rows,pr,pi,sel,obs,pred,a,b,r,j,tt,h,allowed;
 t:=CharacterTable(H);
 w:=WreathProduct(H,Group(CycleFromList([1..l])));
 wr:=CharacterTable(w);
 rows:=List(Irr(t),ValuesOfClassFunction); pr:=PrimeDivisors(Size(w));
 for pi in Combinations(pr) do
  allowed:=function(tb)local n;n:=Product(pi);return Filtered([1..NrConjugacyClasses(tb)],
   i->n mod Product(PrimeDivisors(OrdersClassRepresentatives(tb)[i]))=0);end;
  sel:=allowed(t); obs:=SortedList(List(Irr(wr),r->Sum(r{allowed(wr)})));
  pred:=[];
  for tt in Tuples([1..Length(rows)],l) do
   r:=tt[1];
   if Size(Set(tt))=1 then
    a:=Sum(rows[r]{sel}); b:=Sum(sel,i->rows[r][i]^l);
    h:=(a^l+(l-1)*b)/l;
    if l in pi then Append(pred,Concatenation([h+(l-1)*a],List([2..l],i->h-a)));
    else Append(pred,List([1..l],i->h)); fi;
   elif tt=Minimum(List([0..l-1],k->Concatenation(tt{[k+1..l]},tt{[1..k]}))) then
    Add(pred,Product(tt,r->Sum(rows[r]{sel}))+(l-1)*Sum(sel,i->Product(tt,r->rows[r][i])));
   fi;
  od;
  if SortedList(pred)<>obs then Error("formula mismatch");fi;
 od;
 Print("actual group, order ",Size(w)," / ",Length(obs)," rows agrees for all ",2^Length(pr)," sets\n");
end;
CycleCheck(AlternatingGroup(5),2);CycleCheck(SymmetricGroup(3),3);
Print("PASS: GAP tables\n");QUIT;
"""


def table_checks(gap):
    """Optional external data: run exact GAP, require positive completion marker."""
    import subprocess
    p = subprocess.run([gap, "-A", "-q", "--quitonbreak"], input=TABLE_SWEEP,
                       text=True, capture_output=True, check=True)
    print(p.stdout, end="")
    if p.stderr or "PASS: GAP tables" not in p.stdout.splitlines():
        raise RuntimeError("incomplete table run: " + p.stderr)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run without -O")
    if sys.argv[1:]:
        if len(sys.argv) != 3 or sys.argv[1] != "--tables":
            raise SystemExit("usage: verify.py [--tables GAP_EXECUTABLE]")
        table_checks(sys.argv[2])
        raise SystemExit(0)
    for q, n in [(2,3),(2,4),(2,5),(2,6),(2,7),(2,9),(3,3),(3,4),(3,5),(3,6),(4,5),(5,3)]:
        check(q,n,short=(q,n)==(2,9))
    matrix_check()
    finite_tail()
    rank_one_checks()
    alternating_check(6)
    alternating_check(7)
    mutation_check()
    print("PASS: all exact recurrence and direct checks")
