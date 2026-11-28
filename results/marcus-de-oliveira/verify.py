#!/usr/bin/env python3
"""Zero-float exact verification suite for the Marcus-de Oliveira Conjecture campaign.

Pure Python stdlib + exact rational/symbolic SymPy (no floating-point arithmetic,
no numerical optimizers). Replays every exact algebraic, combinatorial, polyhedral,
and sum-of-squares certificate supporting Theorems A-F in PROOF.md, together with
mandatory corrupted-witness rejection checks for every section.

Usage:
    python3 results/marcus-de-oliveira/verify.py
"""

from __future__ import annotations

import json
import math
import random
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache, lru_cache, reduce
from itertools import combinations, combinations_with_replacement as cwr, permutations, product
from math import comb, gcd, lcm, prod
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent


# =============================================================================
# Section 1: Theorem A — n=4 Arrowhead 70-Compound & Direct Cauchy Pencil Proof
# =============================================================================

def verify_section_1_arrowhead() -> None:
    print("[1/7] Theorem A: n=4 arrowhead 70-compound & direct Cauchy-pencil identities...")
    nodes = tuple(range(8))
    Js = list(combinations(nodes, 4))

    def noncrossing_matchings(ns: tuple[int, ...]):
        if not ns:
            yield ()
            return
        for j in range(1, len(ns), 2):
            for a in noncrossing_matchings(ns[1:j]):
                for b in noncrossing_matchings(ns[j + 1:]):
                    yield ((ns[0], ns[j]),) + a + b

    Ms = list(noncrossing_matchings(nodes))
    assert len(Ms) == 14

    def is_split(J: tuple[int, ...], m: tuple[tuple[int, int], ...]) -> int:
        Jset = set(J)
        return int(all((a in Jset) != (b in Jset) for a, b in m))

    def gap_poly_from_edges(edges) -> dict[int, int]:
        p: dict[int, int] = {0: 1}
        for a, b in edges:
            q: Counter[int] = Counter()
            for i in range(a, b):
                step = 1 << (4 * i)
                for e, v in p.items():
                    q[e + step] += v
            p = dict(q)
        return p

    def vandermonde_poly(J: tuple[int, ...]) -> dict[int, int]:
        Jc = tuple(a for a in nodes if a not in J)
        edges = [
            (a, b)
            for s in (J, Jc)
            for a, b in combinations(s, 2)
            if b != 7
        ]
        return gap_poly_from_edges(edges)

    C = [[is_split(s, m) for m in Ms] for s in Js]
    Z = [vandermonde_poly(s) for s in Js]
    E = sorted(set().union(*Z))
    assert len(Js) == 70 and len(E) == 802

    # Exact rational Gauss-Jordan on the 70x14 incidence system
    n = len(Ms)
    M = [
        [Fraction(x) for x in r] + [Fraction(int(i == j)) for j in range(len(Js))]
        for i, r in enumerate(C)
    ]
    for j in range(n):
        k = next(i for i in range(j, len(M)) if M[i][j])
        M[j], M[k] = M[k], M[j]
        piv = M[j][j]
        M[j] = [z / piv for z in M[j]]
        for i in range(len(M)):
            if i != j and M[i][j]:
                fac = M[i][j]
                M[i] = [a - fac * b for a, b in zip(M[i], M[j])]
    assert all(v.denominator == 1 for r in M[:n] for v in r)
    L = [[(j, int(c)) for j, c in enumerate(r[n:]) if c] for r in M[:n]]
    W = [[sum(c * Z[j].get(e, 0) for j, c in r) for e in E] for r in L]

    def check_weights(weights: list[list[int]]) -> None:
        assert all(min(r) >= 0 and any(r) for r in weights)
        for r, p in zip(C, Z):
            ix = [i for i, c in enumerate(r) if c]
            for j, e in enumerate(E):
                assert sum(weights[i][j] for i in ix) == p.get(e, 0)

    check_weights(W)

    # Independent direct check from raw 24-term Leibniz expansion of cleared Cauchy pencil
    raw_terms = []
    for p in permutations(range(4)):
        edges = [(2 * r + 1, 2 * t) for r in range(3) for t in range(4) if p[r] != t]
        parity = (
            1
            + sum(t < v for j, t in enumerate(p) for v in p[:j])
            + sum(b < a for a, b in edges)
        ) % 2
        sgn = -1 if parity else 1
        pol = gap_poly_from_edges(sorted((min(a, b), max(a, b)) for a, b in edges))
        raw_terms.append((p, sgn, pol))

    def check_raw_pencil(terms) -> None:
        for J, z, row in zip(Js, Z, C):
            Jset = set(J)
            lhs: Counter[int] = Counter()
            for p, sgn, pol in terms:
                if all(((2 * i + 1 in Jset) != (2 * p[i] in Jset)) for i in range(4)):
                    for m, v in pol.items():
                        lhs[m] += sgn * v
            want = {m: sum(w[k] for w, c in zip(W, row) if c) for k, m in enumerate(E)}
            for m in set(lhs) | set(want) | set(z):
                assert lhs[m] == want.get(m, 0) == z.get(m, 0)

    check_raw_pencil(raw_terms)

    # Corrupted-witness mutation tests
    W_bad = [row[:] for row in W]
    W_bad[0][0] += 1
    try:
        check_weights(W_bad)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 1 weight mutation escaped!")

    raw_bad = list(raw_terms)
    p0, s0, pol0 = raw_bad[0]
    raw_bad[0] = (p0, -s0, pol0)
    try:
        check_raw_pencil(raw_bad)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 1 Leibniz sign mutation escaped!")

    print("  PASS: 70 compound & cleared Cauchy-pencil identities, 14 positive weights, 802 gap monomials; mutations rejected.")


# =============================================================================
# Section 2: Theorem B — Rank-Excess-2 Branches & 6x6 Nonnormal Lift Witness
# =============================================================================

def verify_section_2_rank_excess() -> None:
    print("[2/7] Theorem B: Rank-excess-2 branch identities & 6x6 nonnormal simultaneous polynomial witness...")
    I = sp.I
    Q = sp.Rational
    E2 = sp.eye(2)
    N2 = sp.zeros(2)
    sz = sp.diag(1, -1)
    sx = sp.Matrix([[0, 1], [1, 0]])
    J2 = sp.Matrix([[0, 1], [-1, 0]])

    def eq(A, B) -> bool:
        Z = A - B
        if isinstance(Z, sp.MatrixBase):
            return all(sp.cancel(e) == 0 for e in Z)
        return sp.cancel(Z) == 0

    def check_branch(mutate_cov: bool = False) -> None:
        def constraint(pts):
            A = sp.Matrix([[1, p, q] for p, q in pts])
            c = A.T.nullspace()[0]
            assert all(c)
            return (c.T * sp.Matrix([[p * p, p * q, q * q] for p, q in pts])).T

        c1 = constraint([(1, 0), (-1, 0), (0, 1), (0, -1)])
        c2 = constraint([
            (Q(3, 5), Q(4, 5)),
            (Q(-3, 5), Q(-4, 5)),
            (Q(-4, 5), Q(3, 5)),
            (Q(4, 5), Q(-3, 5)),
        ])
        u = c1.cross(c2)
        assert u[0] and u[0] == u[2] and u[1] == 0

        S = 2 * sz + I * sx
        Z = S.adjugate()
        assert Z == -S

        def H(t):
            return (t * Z + (t * Z).H) / 2

        d_val, e_val = 13, -7
        ns = (sz, -sz, sx, -sx)
        Ps = [(E2 + n) / 2 for n in ns]
        Xs = []
        groups = []
        for g, p in [(d_val, Q(3, 4)), (e_val, Q(1, 4))]:
            b = [p, p, 1 - p, 1 - p]
            spec = [Q(g, 4), Q(-g, 4), -I * g / 2, I * g / 2]
            Es = [w * A for w, A in zip(b, Ps)]
            L = -g * E2 / 2
            for t, Pmat, E0 in zip(spec, Ps, Es):
                M = H(t) - L
                assert eq(M, g * (E2 - Pmat)) and eq(E0 * M, N2) and eq(E0 * J2 + J2 * E0, sp.trace(E0) * J2)
            assert eq(sum(Es, N2), E2)
            A = sum((t * U for t, U in zip(spec, Es)), N2)
            assert (A * A.H - A.H * A) != N2
            Xs.append(A)
            groups.append((g, b, spec, Es))
        assert eq(sum(Xs, N2), S)

        t_sym = sp.symbols("u", real=True) + I * sp.symbols("v", real=True)
        RHS = 0
        for g, b, spec, _ in groups:
            denom = abs(g) if mutate_cov else g
            RHS += sum(w / denom * sp.re(t_sym * a) ** 2 for w, a in zip(b, spec))
        assert eq(sp.re(t_sym * t_sym), RHS)

        g, b, spec, Es = groups[1]
        h_sym = sp.symbols("h", real=True)
        ts = [1, 1, -Q(1, 3), -Q(1, 3)]
        Es1 = [(E2 + I * h_sym * a * J2).H * V * (E2 + I * h_sym * a * J2) for a, V in zip(ts, Es)]
        assert eq(sum(Es1, N2), (1 + h_sym * h_sym / 3) * E2)
        Y = sum((t * A for t, A in zip(spec, Es1)), N2) / (1 + h_sym * h_sym / 3)
        assert eq(Y.diff(h_sym).subs(h_sym, 0), N2)
        d2 = sp.re(sp.cancel((Xs[0] + Y).det()).diff(h_sym, 2).subs(h_sym, 0))
        assert d2 == 2 * g * sum(w * a * a for w, a in zip(b, ts)) == -Q(28, 3)

        R = sp.Matrix([[1, 2], [3, 4]])
        Sp = R.inv() * S * R.inv().T
        assert eq(R.T * Z * R, R.det() ** 2 * Sp.adjugate())

        g1, g2 = 1 + 2 * I, -1 + 3 * I
        G = sp.diag(g1, g2)
        aa, bb = sp.symbols("a b", real=True)
        uu = aa + I * bb
        assert sp.solve([sp.re(g1 * uu), sp.re(g2 * uu)], [aa, bb]) == {aa: 0, bb: 0}
        D1 = sp.diag(2 * I / g1, I / g2)
        D2 = sp.diag(3 * I / g1, -5 * I / g2)
        D = 3 * D1 - 2 * D2
        assert D.det() == 0 and D != N2 and eq((D * G).applyfunc(sp.re), N2)

    check_branch(False)
    try:
        check_branch(True)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 2 covariance mutation escaped!")

    # Exact 6x6 unitary lift of a nonnormal 4+4 compression pair
    def simp(A):
        return A.applyfunc(sp.cancel)

    def cayley(seed: int):
        r = random.Random(seed)
        T = sp.Matrix(4, 4, lambda i, j: r.choice([-1, 0, 1]) + I * r.choice([-1, 0, 1]))
        K = (T - T.H) / 3
        return simp((sp.eye(4) - K) * (sp.eye(4) + K).inv())

    P = cayley(123)
    Q_ = cayley(50)
    V = P[:, :2]
    W = Q_[:, :2]
    a = [1 + I, -2 + 3 * I, 3 - I, -1 - 2 * I]
    b = [2 - I, -3 + I, 1 + 4 * I, 2 + 2 * I]
    X = simp(V.H * sp.diag(*a) * V)
    Y = simp(W.H * sp.diag(*b) * W)
    for A in (X, Y):
        assert simp(A * A.H - A.H * A) != N2

    def coeff(tr, det):
        return sp.Matrix([1, sp.re(tr), sp.im(tr), sp.re(det), sp.im(det)])

    goal = coeff((X + Y).trace(), sp.cancel((X + Y).det()))
    ids = [(i, k, j, l) for i, k in combinations(range(4), 2) for j, l in permutations(range(4), 2)]
    mat = sp.Matrix.hstack(*[
        coeff(a[i] + a[k] + b[j] + b[l], (a[i] + b[j]) * (a[k] + b[l]))
        for i, k, j, l in ids
    ])

    U6 = sp.zeros(6)
    U6[:2, :4] = Q_.H[:2, :]
    U6[4:, :4] = Q_.H[2:, :]
    U6[2:4, 4:] = sp.eye(2)
    U6[:4, :] = P * U6[:4, :]
    U6 = simp(U6)
    assert simp(U6.H * U6) == sp.eye(6)
    aa = [sp.cancel(1 / t) for t in a] + [0, 0]
    bb = [sp.cancel(1 / t) for t in b] + [0, 0]
    Cprod = sp.prod(aa[:4] + bb[:4])
    D6 = sp.cancel((sp.diag(*aa) + U6 * sp.diag(*bb) * U6.H).det(method="domain-ge") / Cprod)
    assert D6 == sp.cancel((X + Y).det()) and X.det() != 0 and Y.det() != 0

    den = int(sp.ilcm(*[sp.denom(t) for z in aa + bb for t in (sp.re(z), sp.im(z))]))
    grid = [[(int(sp.re((z + w) * den)), int(sp.im((z + w) * den))) for w in bb] for z in aa]
    vals = set()
    for p in permutations(range(6)):
        vx, vy = 1, 0
        for i, j in enumerate(p):
            ux, uy = grid[i][j]
            vx, vy = vx * ux - vy * uy, vx * uy + vy * ux
        vals.add((vx, vy))
    expected = {sp.cancel(den ** 6 * Cprod * (a[i] + b[j]) * (a[k] + b[l])) for i, k, j, l in ids} | {0}
    assert vals == {(int(sp.re(z)), int(sp.im(z))) for z in expected}

    simplex_idx = [11, 29, 41, 54, 61]
    simplex_w = [
        Q(1751608601261, 58103797067670),
        Q(1206854459045, 3873586471178),
        Q(6138212000942, 29051898533835),
        Q(8502446533769, 58103797067670),
        Q(17470501045081, 58103797067670),
    ]

    def check_simplex(weights):
        wv = sp.Matrix(weights)
        assert len(simplex_idx) == len(weights) == 5 and min(weights) > 0
        assert mat[:, simplex_idx] * wv == goal

    check_simplex(simplex_w)
    bad_w = list(simplex_w)
    bad_w[0] += Q(1, 10000)
    try:
        check_simplex(bad_w)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 2 simplex weight mutation escaped!")

    print("  PASS: Rank-excess-2 branch identities, 6x6 unitary lift, all 720 products & 5-vertex simplex verified; mutations rejected.")


# =============================================================================
# Section 3: Theorem C — Universal U(4) -> SO(4) Simultaneous 70-Minor Chord
# =============================================================================

def verify_section_3_real_chord() -> None:
    print("[3/7] Theorem C: Universal U(4) -> SO(4) 70-minor real-chord identities...")
    F = sp.Rational
    i = sp.I
    I4 = range(4)
    P2 = list(combinations(I4, 2))

    def giv(a, b, q):
        z = sp.cancel(q * sp.conjugate(q))
        c = (1 - z) / (1 + z)
        u = 2 * q / (1 + z)
        g = sp.eye(4)
        g[a, a] = g[b, b] = c
        g[a, b] = u
        g[b, a] = -sp.conjugate(u)
        return g

    # Complementary pairing & balanced phase pencil on a generic SU(4) matrix
    U = sp.eye(4)
    for (j, k), q in zip(P2, [F(1, 3) + i / 2, F(2, 7) - i / 3, F(-2, 5) + i / 4,
                              F(1, 7) + i / 6, F(2, 3) - i / 3, F(-3, 7) + i / 7]):
        U = (U * giv(j, k, q)).applyfunc(sp.expand_complex)
    assert (U.H * U - sp.eye(4)).applyfunc(sp.simplify) == sp.zeros(4) and sp.expand_complex(U.det()) == 1

    pm = {(a, b): sp.expand_complex(U.extract(a, b).det()) for a in P2 for b in P2}
    Ks = [q for q in P2 if 0 in q]
    comp = lambda q: tuple(k for k in I4 if k not in q)
    W = []
    for b in Ks:
        assert sp.expand_complex(sum(sp.conjugate(pm[a, b]) * pm[a, comp(b)] for a in Ks)) == 0
        W.append([sp.expand_complex(pm[a, b] * pm[a, comp(b)]) for a in Ks])

    zmap = lambda t: (1 + i * t) / (1 - i * t)
    g = [zmap(F(1, 2)), zmap(F(-1, 4)), zmap(F(1, 3))]
    g.append(1 / prod(g))
    g = [sp.expand_complex(x) for x in g]
    M = (U.T * sp.diag(*g) * U).applyfunc(sp.expand_complex)
    for n_idx, b in enumerate(Ks):
        h = 2 * sp.re(sum(g[0] * g[j + 1] * W[n_idx][j] for j in range(3)))
        assert sp.expand_complex(M.extract(b, comp(b)).det() - h) == 0

    # Rational isolating bracket for balanced phases
    v = [sp.Matrix([[sp.re(W[j][k]), -sp.im(W[j][k])] for j in range(2)]) for k in range(3)]
    t_sym = sp.symbols("t", real=True)
    xx = sp.Matrix([1 - t_sym * t_sym, 2 * t_sym])
    den = 1 + t_sym * t_sym
    found_bracket = None
    for j in range(3):
        A, B, Cmat = v[j:] + v[:j]
        if not B.det():
            continue
        for q in [0, 1, -1, F(1, 2), F(-1, 2), F(1, 3), F(2, 3), F(4, 3)]:
            w = sp.expand_complex(zmap(q))
            uvec = sp.Matrix([sp.re(w), sp.im(w)])
            yvec = -B.inv() * (A * xx + den * Cmat * uvec)
            assert (A * xx + B * yvec + den * Cmat * uvec).applyfunc(sp.expand) == sp.zeros(2, 1)
            p = sp.Poly(sp.expand(yvec.dot(yvec) - den ** 2), t_sym)
            gg = sp.gcd(p, p.diff())
            sq = p.exquo(gg) if gg.degree() else p
            rr = sq.intervals()
            if rr:
                lo, hi = rr[0][0]
                assert (lo == hi and sq.eval(lo) == 0) or (sq.eval(lo) * sq.eval(hi) < 0)
                assert sp.rem(p, sq).is_zero
                found_bracket = (p.degree(), lo, hi)
                break
        if found_bracket:
            break
    assert found_bracket is not None

    # Simultaneous 70-minor chord identity on O1 diag(z, 1, 1, 1) O2
    U1 = sp.eye(4)
    V1 = sp.eye(4)
    for j, (k, l) in enumerate(P2):
        U1 = U1 * giv(k, l, F(j + 1, j + 3))
        V1 = V1 * giv(k, l, F(2 - j, j + 4))
    zval = (3 + 4 * i) / 5
    A = U1 * sp.diag(zval, 1, 1, 1) * V1
    B = U1 * V1
    C = U1 * sp.diag(-1, 1, 1, 1) * V1

    def check_chord(t_w):
        assert (B - C).rank() == 1 and (A.H * A - sp.eye(4)).applyfunc(sp.expand) == sp.zeros(4)
        cnt = 0
        for sz_k in range(5):
            for r in combinations(I4, sz_k):
                for c in combinations(I4, sz_k):
                    f = A.extract(r, c).det()
                    assert sp.expand_complex(
                        f * sp.conjugate(f) - t_w * B.extract(r, c).det() ** 2 - (1 - t_w) * C.extract(r, c).det() ** 2
                    ) == 0
                    cnt += 1
        assert cnt == 70

    check_chord(F(4, 5))
    try:
        check_chord(F(3, 5))
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 3 chord weight mutation escaped!")

    print("  PASS: Complementary pairing, rational phase bracket, and all 70 simultaneous minor-square chord identities verified; mutation rejected.")


# =============================================================================
# Section 4: Theorem D — Two-Tetrahedron SOS, Shor/P(delta) Obstruction, KKT Saddles
# =============================================================================

def verify_section_4_two_tetrahedron_and_obstructions() -> None:
    print("[4/7] Theorem D: Disjoint two-tetrahedron 151-SOS atlas, Shor/P(delta) obstruction, & escaped KKT saddles...")
    N6 = range(6)
    P4 = list(permutations(range(4)))

    def prim(x):
        d = reduce(gcd, x, 0)
        return tuple(t // d for t in x) if d else tuple(x)

    def fracprim(x):
        d = lcm(*(Fraction(v).denominator for v in x))
        return prim(tuple(int(v * d) for v in x))

    def dot(x, y):
        return sum(a * b for a, b in zip(x, y))

    def sign(p):
        return (-1) ** sum(a > b for a, b in combinations(p, 2))

    def col(i, j):
        return 6 * i + j

    def bar0(k):
        i, j = divmod(k, 6)
        return col(i ^ 1, j ^ 1)

    def bar(m):
        return tuple(sorted(bar0(k) for k in m))

    def canon(m):
        return min(m, bar(m))

    def add_m(m, n):
        return tuple(sorted(m + n))

    def ec(k):
        i, j = divmod(k, 6)
        return (-1) ** (i % 2) * 16 ** (i // 2) + (-1) ** (j % 2) * 16 ** (3 + j // 2)

    def wt(m):
        return sum(ec(k) for k in m)

    def minor_dict(I_idx, J_idx):
        return {tuple(sorted(col(i, j) for i, j in zip(I_idx, p))): sign(p) for p in permutations(J_idx)}

    def axpy(r, c, s):
        for k, a in s.items():
            v = r.get(k, 0) + c * a
            if v:
                r[k] = v
            elif k in r:
                del r[k]

    def rowrank(rows):
        piv = {}
        for row in rows:
            r = {i: a for i, a in enumerate(row) if a}
            while r:
                k = max(r)
                v = r[k]
                if k not in piv:
                    piv[k] = {i: Fraction(x, v) for i, x in r.items()}
                    break
                axpy(r, -v, piv[k])
        return len(piv)

    def clip(rays, f, active):
        e = [dot(f, r) for r in rays]
        z = [{i for i, a in enumerate(active) if not dot(a, r)} for r in rays]
        out = {r for r, k in zip(rays, e) if k >= 0}
        for i, k in enumerate(e):
            if k <= 0:
                continue
            for j, h in enumerate(e):
                if h >= 0:
                    continue
                if rowrank([active[s] for s in z[i] & z[j]]) < len(f) - 2:
                    continue
                out.add(prim(tuple(k * b - h * a for a, b in zip(rays[i], rays[j]))))
        return sorted(out)

    class QSO:
        def __init__(self):
            low = defaultdict(list)
            for deg in range(3):
                for m in cwr(range(36), deg):
                    low[wt(m)].append(m)
            eq = []
            for i in N6:
                for j in N6:
                    for tr in (0, 1):
                        d = Counter()
                        for k in N6:
                            u, v = (col(k, i), col(k, j)) if tr else (col(i, k), col(j, k))
                            d[add_m((u,), (bar0(v),))] += 1
                        if i == j:
                            d[()] -= 1
                        eq.append((2, d))
            for deg in (3, 4):
                for A in combinations(N6, deg):
                    Ac = tuple(k for k in N6 if k not in A)
                    for B in combinations(N6, deg):
                        Bc = tuple(k for k in N6 if k not in B)
                        D = minor_dict(A, B)
                        sgn_e = (-1) ** (sum(A) + sum(B))
                        axpy(D, -sgn_e, {bar(m): v for m, v in minor_dict(Ac, Bc).items()})
                        if D:
                            eq.append((deg, D))
            self.piv = {}
            for deg, D in eq:
                w = wt(next(iter(D)))
                assert all(wt(m) == w for m in D)
                for a in low.get(-w, []):
                    if len(a) > 4 - deg:
                        continue
                    row = Counter()
                    for m, v in D.items():
                        t = canon(add_m(m, a))
                        row[(len(t), t)] += v
                    r = {t: v for t, v in row.items() if v}
                    while r:
                        k = max(r)
                        v = r[k]
                        if k not in self.piv:
                            self.piv[k] = {t: Fraction(x, v) for t, x in r.items()}
                            break
                        axpy(r, -v, self.piv[k])

        @cache
        def red(self, m):
            t = (len(m), m)
            if t not in self.piv:
                return {m: 1}
            v = {}
            for k, x in self.piv[t].items():
                if k != t:
                    axpy(v, -x, self.red(k[1]))
            return v

        @cache
        def gram(self, key: str):
            word = []
            for term in key.split(";"):
                x, a = term.split("@")
                m = tuple(map(int, a.split(","))) if a else ()
                assert len(m) <= 2 and all(0 <= k < 36 for k in m)
                word.append((int(x), m))
            assert len({wt(m) for _, m in word}) == 1
            v = {}
            for tr in range(2):
                for shift in range(3):
                    def act(k):
                        i, j = divmod(k, 6)
                        conv = lambda idx: 2 * ((shift + (-1) ** tr * (idx // 2)) % 3) + (idx % 2)
                        return col(conv(j), conv(i)) if tr else col(conv(i), conv(j))

                    w = [(x, tuple(sorted(act(k) for k in m))) for x, m in word]
                    for x, m in w:
                        for y, n in w:
                            axpy(v, x * y, self.red(canon(add_m(bar(m), n))))
            return v

    def spectralrows():
        Y = []
        for p in P4:
            d = [[0, 0] for _ in range(3)]
            slots = [i for i in range(4) if p[i]]
            for mask in range(7):
                s_val = 0
                cnt = mask.bit_count()
                for k, i in enumerate(slots):
                    if mask & (1 << k):
                        s_val += p[i] - 1
                    elif i:
                        s_val += i - 1
                    else:
                        break
                else:
                    x, y = [(2, 0), (-1, 1), (-1, -1)][s_val % 3]
                    d[cnt][0] += (-1) ** cnt * x
                    d[cnt][1] += (-1) ** cnt * y
            assert d[0][1] == 0
            Y.append((1, d[0][0], *d[1], *d[2]))
        return Y

    def vk(p):
        Iset = [{0, a} for a in range(1, 4)]
        d = [[sum(p[k] in b for k in a) - 1 for b in Iset] for a in Iset]
        return (1, d[0][0] ** 2, d[0][1] ** 2, d[1][0] ** 2, d[1][1] ** 2, *sum(d, []))

    qso = QSO()
    Xrows = spectralrows()
    Ypts = sorted(set(Xrows))
    assert len(Ypts) == 10
    Vmat = sp.Matrix([vk(p) for p in P4])
    Xmat = sp.Matrix(Xrows)
    ix = list(Vmat.T.rref()[1])
    assert len(ix) == 14
    Mmat = Vmat[ix, :].inv() * Xmat[ix, :]
    assert Vmat * Mmat == Xmat

    vlist = [qso.red(())]
    for i, j in [(0, 0), (0, 1), (1, 0), (1, 1)] + [(i, j) for i in range(3) for j in range(3)]:
        d = {}
        for t in (0, 1):
            k = col(2 * i, 2 * j + t)
            axpy(d, (-1) ** (t * int(len(vlist) >= 5)), qso.red(canon(add_m((k,), (bar0(k),)))))
        vlist.append(d)
    bases = []
    for k in range(6):
        v0 = {}
        for h, x in zip(vlist, Mmat[:, k]):
            axpy(v0, 6 * Fraction(int(x.p), int(x.q)), h)
        bases.append(v0)

    @cache
    def target(r):
        z = {}
        for x, b in zip(r, bases):
            axpy(z, x, b)
        return z

    def check_gram(r, cert_entry):
        a = {}
        for key, w in cert_entry:
            z = Fraction(w)
            assert z > 0
            axpy(a, z, qso.gram(key))
        assert a == target(r)

    cert_data = json.loads((HERE / "two_tetrahedron_sos.json").read_text(encoding="utf-8"))
    certs = {tuple(map(int, s.split(","))): v for s, v in cert_data["squares"].items()}
    for t_vec, c_entry in certs.items():
        check_gram(t_vec, c_entry)

    # Bernstein / de Casteljau leaf-cone coverage over all real lambda^3
    lam = sp.symbols("l", real=True)

    def controls(p_row, q_row, pol):
        def coeff_pair(v):
            _, a, x, y, u, w = v
            return a + x * lam + u * lam * lam, y * lam + w * lam * lam

        x, y = coeff_pair(p_row)
        u, v = coeff_pair(q_row)
        d_poly = u - x
        e_poly = v - y
        c_list = [e_poly * x - d_poly * y, -e_poly, -e_poly * lam, d_poly * lam, -e_poly * lam * lam, d_poly * lam * lam]
        g_poly = sp.gcd_list(c_list)
        m_polys = [sp.Poly(sp.cancel(k / g_poly), lam) for k in c_list]
        deg_n = max(int(k.degree()) for k in m_polys if k)
        return [tuple(Fraction(int(k.nth(idx)) * pol ** idx, comb(deg_n, idx)) for k in m_polys) for idx in range(deg_n + 1)]

    def split_bernstein(c_pts):
        left, right = [], []
        cur = list(c_pts)
        while cur:
            left.append(cur[0])
            right.append(cur[-1])
            cur = [tuple((x + y) / 2 for x, y in zip(s, t)) for s, t in zip(cur, cur[1:])]
        return left, right[::-1]

    used_certs = set()
    leaf_count = 0

    def walk_tree(node, cone):
        nonlocal leaf_count
        if node != 0:
            assert isinstance(node, list) and len(node) == 2
            for child, sub_c in zip(node, split_bernstein(cone)):
                walk_tree(child, sub_c)
            return
        leaf_count += 1
        B = [fracprim(z) for z in cone]
        d = len(B)
        A = [tuple(int(i == j) for j in range(d)) for i in range(d)]
        R = A.copy()
        for y in Ypts:
            a_vec = tuple(dot(k, y) for k in B)
            R = clip(R, a_vec, A)
            A.append(a_vec)
            if not R:
                return
        for w in R:
            t_vec = prim(tuple(dot(w, z) for z in zip(*B)))
            if any(t_vec):
                assert t_vec in certs
                used_certs.add(t_vec)

    for i, j in combinations(range(10), 2):
        for pol in (1, -1):
            c_pts = controls(Ypts[i], Ypts[j], pol)
            for sgn in (1, -1):
                key = ",".join(map(str, [i, j, pol, sgn]))
                walk_tree(cert_data["leaves"][key], [tuple(sgn * v for v in r) for r in c_pts])

    assert len(used_certs) == 151 and leaf_count == 216

    # Corrupted Gram mutation test
    t_sample = next(t for t in sorted(used_certs) if any(target(t).values()))
    c_bad = list(certs[t_sample])
    nm, ww = c_bad[0]
    c_bad[0] = (nm, str(Fraction(ww) + 1))
    try:
        check_gram(t_sample, c_bad)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 4 Gram weight mutation escaped!")

    # 4b. Shor / P_outer / P(delta) exact obstructions
    def cross_ratio(vals):
        return (vals[0] - vals[1]) * (vals[2] - vals[3]) / ((vals[0] - vals[2]) * (vals[1] - vals[3]))

    a_shor = [0, 1, sp.I, 2 + 2 * sp.I]
    b_shor = [2, 1 + sp.I, 3 + sp.I, 2 * sp.I]
    assert sp.im(cross_ratio(a_shor)) != 0 and sp.im(cross_ratio(b_shor)) != 0
    assert all(x + y != 0 for x in a_shor for y in b_shor)
    v_shor = {p: sp.expand(prod(a_shor[i] + b_shor[p[i]] for i in range(4))) for p in P4}
    fake_shor = {p: sum(v_shor[tuple(k ^ j for k in p)] for j in range(4)) / 2 - v_shor[p] for p in P4}
    assert max(map(sp.re, v_shor.values())) == -40 and max(map(sp.re, fake_shor.values())) == -34

    # P(delta) obstruction witness for EVERY delta > 0
    pairs4 = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    W4 = [[1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1]]

    def cmul(u, v):
        return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])

    def cadd(u, v):
        return (u[0] + v[0], u[1] + v[1])

    def cprod(lst):
        r = (Fraction(1), Fraction(0))
        for x in lst:
            r = cmul(r, x)
        return r

    a_pd = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(0), Fraction(-4)), (Fraction(-1), Fraction(4))]
    b_pd = [(Fraction(-6), Fraction(4)), (Fraction(4), Fraction(0)), (Fraction(-1), Fraction(-1)), (Fraction(0), Fraction(1))]
    pvals = {p: cprod([cadd(a_pd[i], b_pd[p[i]]) for i in range(4)]) for p in P4}
    M_pd = max(v[0] for v in pvals.values())
    assert M_pd == 120
    p_max = next(p for p, v in pvals.items() if v[0] == M_pd)

    def det_SQ(S, Q):
        S_hat = [[Fraction(0)] * 3 for _ in range(3)]
        for p_idx in range(3):
            for q_idx in range(3):
                S_hat[p_idx][q_idx] = sum(
                    W4[p_idx + 1][i] * S[i][j] * W4[q_idx + 1][j]
                    for i in range(4) for j in range(4)
                ) / 4
        for i in range(4):
            assert sum(S[i]) == 1 and sum(S[r][i] for r in range(4)) == 1
            assert all(S[i][j] >= 0 for j in range(4))
        for p_idx in range(3):
            assert sum(Q[p_idx]) == 1 and sum(Q[r][p_idx] for r in range(3)) == 1
            for q_idx in range(3):
                assert Q[p_idx][q_idx] >= 0
                assert Q[p_idx][q_idx] + S_hat[p_idx][q_idx] >= 0
                assert Q[p_idx][q_idx] - S_hat[p_idx][q_idx] >= 0
        val = cadd(cprod(a_pd), cprod(b_pd))
        for i in range(4):
            pa = cprod([a_pd[r] for r in range(4) if r != i])
            for j in range(4):
                pb = cprod([b_pd[s] for s in range(4) if s != j])
                t = cadd(cmul(pa, b_pd[j]), cmul(a_pd[i], pb))
                val = cadd(val, (t[0] * S[i][j], t[1] * S[i][j]))
        for p_idx, (R1, R2) in enumerate(pairs4):
            aR1 = cmul(a_pd[R1[0]], a_pd[R1[1]])
            aR2 = cmul(a_pd[R2[0]], a_pd[R2[1]])
            for q_idx, (C1, C2) in enumerate(pairs4):
                bC1 = cmul(b_pd[C1[0]], b_pd[C1[1]])
                bC2 = cmul(b_pd[C2[0]], b_pd[C2[1]])
                ms = (Q[p_idx][q_idx] + S_hat[p_idx][q_idx]) / 2
                mo = (Q[p_idx][q_idx] - S_hat[p_idx][q_idx]) / 2
                t1 = cadd(cmul(aR1, bC2), cmul(aR2, bC1))
                t2 = cadd(cmul(aR1, bC1), cmul(aR2, bC2))
                val = cadd(val, (t1[0] * ms + t2[0] * mo, t1[1] * ms + t2[1] * mo))
        return val

    S_opt = [[Fraction(0) if i == j else Fraction(1, 3) for j in range(4)] for i in range(4)]
    C3 = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]
    Q_opt = [[(Fraction(1, 3) if p_idx == q_idx else Fraction(0)) + Fraction(2, 3) * C3[p_idx][q_idx] for q_idx in range(3)] for p_idx in range(3)]
    assert det_SQ(S_opt, Q_opt)[0] == 142

    def mperm(p):
        mp = []
        for R1, _ in pairs4:
            img = tuple(sorted((p[R1[0]], p[R1[1]])))
            for idx, (C1, C2) in enumerate(pairs4):
                if img == C1 or img == C2:
                    mp.append(idx)
                    break
        return mp

    mperms = [mperm(p) for p in P4]

    def min_all_orb2(S, Q):
        mval = Fraction(10 ** 9)
        for pr, mpr in zip(P4, mperms):
            for pc, mpc in zip(P4, mperms):
                val = sum(S[pr[i]][pc[i]] for i in range(4)) + Q[mpr[0]][mpc[1]] - Q[mpr[1]][mpc[0]]
                if val < mval:
                    mval = val
        return mval

    assert min_all_orb2(S_opt, Q_opt) == Fraction(-2, 3)
    S0 = [[Fraction(1) if p_max[i] == j else Fraction(0) for j in range(4)] for i in range(4)]
    Q0 = [[Fraction(0)] * 3 for _ in range(3)]
    for ri, (R1, _) in enumerate(pairs4):
        img = tuple(sorted((p_max[R1[0]], p_max[R1[1]])))
        for ci, (C1, C2) in enumerate(pairs4):
            if img == C1 or img == C2:
                Q0[ri][ci] = Fraction(1)
    assert det_SQ(S0, Q0) == pvals[p_max]
    t_mix = Fraction(1, 5)
    St = [[(1 - t_mix) * S0[i][j] + t_mix * S_opt[i][j] for j in range(4)] for i in range(4)]
    Qt = [[(1 - t_mix) * Q0[p_idx][q_idx] + t_mix * Q_opt[p_idx][q_idx] for q_idx in range(3)] for p_idx in range(3)]
    assert det_SQ(St, Qt)[0] == Fraction(120) + t_mix * Fraction(22)
    assert min_all_orb2(St, Qt) >= Fraction(-2, 15)

    # 4c. Exact rational Pi_4-escaped irreducible KKT saddle (U = (I+4K)/7)
    def inertia(H):
        H = sp.Matrix(H)
        d = [0, 0, 0]
        while H.rows:
            k = next((j for j in range(H.rows) if H[j, j]), None)
            if k is None:
                k = next(((i, j) for i in range(H.rows) for j in range(i) if H[i, j]), None)
                if k is None:
                    d[1] += H.rows
                    break
                i, j = k
                t = sp.eye(H.rows)
                t[i, j] = 1
                H = t.T * H * t
                continue
            d[0 if H[k, k] < 0 else 2] += 1
            J = [i for i in range(H.rows) if i != k]
            H = H.extract(J, J) - H.extract(J, [k]) * H.extract([k], J) / H[k, k]
        return tuple(d)

    K4 = sp.Matrix([[0, 1, 1, 1], [-1, 0, 1, -1], [-1, -1, 0, 1], [-1, 1, -1, 0]])
    E4 = sp.eye(4)
    I4 = list(range(4))
    Cmat = sp.sqrt(3) * E4 + sp.I * K4
    assert Cmat.rank() == 2 and all(Cmat[i, j] != 0 for i in I4 for j in I4)
    zv = [prod(Cmat[i, p[i]] for i in I4) for p in P4]
    t_s = sp.symbols("t", real=True)
    D_t = (sp.sqrt(3) * t_s + 3 * sp.I) * (sp.sqrt(3) * t_s - sp.I) ** 3 / (t_s * t_s + 3) ** 2
    phase = sp.I * sp.conjugate(sp.diff(D_t, t_s).subs(t_s, sp.Rational(1, 4)))
    assert phase != 0
    normalized = [sp.simplify(sp.re(phase * z)) for z in zv]
    f_vec = fracprim([Fraction(int(sp.simplify(a / normalized[0]).p), int(sp.simplify(a / normalized[0]).q)) for a in normalized])
    M4 = E4 + 4 * K4
    assert M4.T * M4 == 49 * E4 and M4.det() == 7 ** 4

    def Q_M(i, j):
        A_idx = [0, i]
        B_idx = [0, j]
        bc = [k for k in I4 if k not in B_idx]
        return sum(M4.extract(A_idx, b).det() ** 2 for b in (B_idx, bc))

    assert 49 * sum(M4[i, i] ** 2 for i in I4) - abs(Q_M(1, 2) - Q_M(2, 1)) == -316
    R0, S0_b = [], []
    for i, j in combinations(I4, 2):
        a = sp.zeros(4)
        a[i, j] = 1
        R0.append(a - a.T)
        S0_b.append(a + a.T)

    def path_eval(A, img=False):
        d = A * M4
        h = A * d
        x = y = 0
        for p, w in zip(P4, f_vec):
            ps = sign(p) * w
            for i in I4:
                rest = prod(M4[k, p[k]] for k in I4 if k != i)
                x += ps * d[i, p[i]] * rest
                y += ps * h[i, p[i]] * rest
                for j in range(i):
                    y += 2 * ps * d[i, p[i]] * d[j, p[j]] * prod(M4[k, p[k]] for k in I4 if k != i and k != j)
        return (0, -y) if img else (x, y)

    ds = []
    for gs, img in [(R0, False), (S0_b, True)]:
        H = sp.zeros(6)
        h0 = []
        for i, G in enumerate(gs):
            x_v, q_v = path_eval(G, img)
            assert x_v == 0
            h0.append(q_v)
            H[i, i] = q_v
            for j in range(i):
                H[j, i] = H[i, j] = (path_eval(G + gs[j], img)[1] - q_v - h0[j]) / 2
        ds.append(inertia(H))
    sig = tuple(map(sum, zip(*ds)))
    assert sorted([sig[0], sig[2]]) == [3, 6] and sig[1] == 3

    # 4d. Open family of genuinely complex Pi_4-escaped irreducible KKT eigenbases
    a_s, b_s, h_s = sp.symbols("a b h", real=True)

    def c3_unit(aa, bb, hh):
        c = (1 - 3 * aa * aa) / (1 + 3 * aa * aa)
        ss = 2 * aa / (1 + 3 * aa * aa)
        d = (1 - 3 * bb * bb) / (1 + 3 * bb * bb)
        t = 2 * bb / (1 + 3 * bb * bb)
        v = (1 + sp.I * hh) / (1 - sp.I * hh)
        U = sp.zeros(4)
        U[0, 0] = c
        for j in range(3):
            U[0, j + 1] = -ss
            U[j + 1, 0] = ss
        for j in range(3):
            for k in range(3):
                sg = [0, 1, -1][(k - j) % 3]
                U[j + 1, k + 1] = c / 3 + v * (d * (int(j == k) - sp.Rational(1, 3)) + sg * t)
        return U, v * v

    U_c3, det_c3 = c3_unit(a_s, b_s, h_s)
    sub = {a_s: sp.Rational(-1, 2), b_s: sp.Rational(2, 5), h_s: sp.Rational(1, 13)}
    Mc3 = U_c3.subs(sub).applyfunc(sp.cancel)
    Dc3 = sp.cancel(det_c3.subs(sub))
    assert (Mc3.H * Mc3 - sp.eye(4)).applyfunc(sp.simplify) == sp.zeros(4)
    assert sp.simplify(Mc3.det() - Dc3) == 0 and all(x for x in Mc3)
    plaquette = sp.simplify(sp.im(Mc3[0, 0] * Mc3[1, 1] * sp.conjugate(Mc3[1, 0] * Mc3[0, 1])))
    assert plaquette != 0
    abs2 = lambda z: sp.simplify(z * sp.conjugate(z))
    Qc3 = lambda i, j: sum(abs2(Mc3.extract([0, i], C_idx).det()) for C_idx in ([0, j], [k for k in range(4) if k not in (0, j)]))
    esc_c3 = sum(abs2(Mc3[i, i]) for i in range(4)) - abs(Qc3(1, 2) - Qc3(2, 1))
    assert esc_c3 < 0
    Jmat = []
    for sym in (a_s, b_s, h_s):
        DM = U_c3.diff(sym).subs(sub).applyfunc(sp.cancel)
        dD = det_c3.diff(sym).subs(sub)
        row = []
        for p in P4:
            base = prod(Mc3[k, p[k]] for k in range(4))
            row.append(sign(p) * sp.re(sp.cancel(sum(DM[j, p[j]] * base / Mc3[j, p[j]] for j in range(4)) / Dc3 - dD * base / Dc3 ** 2)))
        Jmat.append(list(sp.Matrix([row]) * Xmat[:, 1:]))
    Znull = sp.Matrix(Jmat).nullspace()
    assert len(Znull) == 2

    print("  PASS: 151 quartic SO(6) SOS certs (216 leaf cones), Shor/P(delta) gaps, & rational/complex KKT saddles verified; mutation rejected.")


# =============================================================================
# Section 5: Theorem E — Collision-Free Singular-Boundary Curvature (n=4..8)
# =============================================================================

def verify_section_5_singular_boundary() -> None:
    print("[5/7] Theorem E: Collision-free singular-boundary transverse Hessian (n=4..8)...")
    I = sp.I
    F = sp.Rational
    R2 = sp.Matrix([[4, -3], [3, 4]]) / 5

    def check_spectra(a, c):
        n = len(a)
        den = int(sp.ilcm(*[sp.denom(z) for t in a + c for z in (sp.re(t), sp.im(t))]))
        grid = [[(int(sp.re((z - w) * den)), int(sp.im((z - w) * den))) for w in c] for z in a]
        vals = []
        active = []
        for p in permutations(range(n)):
            x, y = 1, 0
            for i, j in enumerate(p):
                u, v = grid[i][j]
                x, y = x * u - y * v, x * v + y * u
            assert x or y
            vals.append(-y)
            active.append(x if y == 0 else 0)
        assert min(vals) == 0 and min(active) < 0 < max(active)
        return vals.count(0), F(min(v for v in vals if v > 0), den ** n)

    def second_deriv(H, K, C):
        assert K.H == -K
        d = C * K - K * C
        dd = K * d - d * K
        D = lambda mat: mat.det(method="domain-ge")
        n = len(H.diagonal())
        first = 0
        sec = 0
        for j in range(n):
            H1 = H.copy()
            H1[:, j] = d[:, j]
            first += D(H1)
            for k in range(j):
                H2 = H1.copy()
                H2[:, k] = d[:, k]
                sec += 2 * D(H2)
            H1[:, j] = dd[:, j]
            sec += D(H1)
        return first.expand(), sec.expand()

    def run_case(n: int, mutate: bool = False):
        m = n - 2
        a0 = sp.diag(-2, 2)
        a = [-2 * I, 2 * I] + [2 + F(j + 1, 100) for j in range(m)]
        c = [I, I * F(38, 13)] + [-2 - F(2 * j + 1, 100) for j in range(m)]
        if mutate:
            c[0] = c[0] + I / 13
        cnt, _ = check_spectra(a, c)
        c0 = R2 * sp.diag(*[sp.im(v) for v in c[:2]]) * R2.T
        P = sp.diag(*a[2:])
        V = sp.eye(m)
        V[:2, :2] = R2
        Q = V * sp.diag(*[-v for v in c[2:]]) * V.T
        G = P + Q
        A = sp.diag(I * a0, P)
        C = sp.diag(I * c0, -Q)
        H = A - C
        assert (a0 - c0).rank() == 1 and (P * Q - Q * P) != sp.zeros(m)
        assert H.rank() == n - 1 and cnt == 2 * math.factorial(m)
        T = sp.Matrix(2, m, lambda i, j: (i + 1) * (j + 1) + I * (i - 2 * j - 1))
        K = sp.zeros(n)
        K[:2, 2:] = T
        K[2:, :2] = -T.H
        first, d2 = second_deriv(H, K, C)
        v = (a0 - c0).nullspace()[0]
        z = T.H * c0 * v
        u = T.H * v
        bracket = ((z.H * G.inv() * z + u.H * (Q - Q * G.inv() * Q) * u)[0] / (v.H * v)[0]).expand()
        assert bracket > 0 and first == 0
        pred = -2 * (a0 - c0).trace() * G.det() * bracket
        assert pred > 0 and -sp.im(d2) == pred
        K[0, 1] = 1
        K[1, 0] = -1
        f2, s2 = second_deriv(H, K, C)
        assert f2 != 0 and sp.im(f2) == 0 and -sp.im(s2) == pred

        aa = [0] + [1] * (n - 1)
        cc = [0, 1] + [0] * (n - 2)
        assert {prod(aa[i] - cc[j] for i, j in enumerate(p)) for p in permutations(range(n))} == {0, -1}
        C2 = sp.diag(*cc)
        H2 = sp.diag(*aa) - C2
        K[0, 1] = 2 + 3 * I
        K[1, 0] = -2 + 3 * I
        f22, d22 = second_deriv(H2, K, C2)
        assert f22 == 0 and -d22 == 26

    for n in range(4, 9):
        run_case(n, False)
    try:
        run_case(4, True)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 5 spectral mutation escaped!")

    print("  PASS: Exact collision-free corank-1 inward transverse Hessian & corank-2 collision fixtures for n=4..8 verified; mutation rejected.")


# =============================================================================
# Section 6: Theorem F (Part 1) — 82-Facet Pi_4 DD & 23-Square Q(rho) U(4) SOS
# =============================================================================

def verify_section_6_pi4_and_orbit2_sos() -> None:
    print("[6/7] Theorem F (part 1): Exact 82-facet Pi_4 double description & 23-square Q(rho) U(4) Orbit-2 SOS...")
    IDX = range(4)
    PAIRS = list(combinations(IDX, 2))
    PERMS = list(permutations(IDX))
    A2 = [(0, 1), (0, 2)]
    comp4 = lambda C: tuple(i for i in IDX if i not in C)

    def pc(s):
        return (1,) + tuple(int(s[i] == j) for i, j in product(range(3), repeat=2)) + tuple(
            int(set(s[i] for i in r) in (set(c), set(IDX) - set(c))) for r, c in product(A2, repeat=2)
        )

    V = [pc(s) for s in PERMS]
    CF = (2, -2, -1, -1, -1, 0, 1, -1, 1, 0, 0, 1, -1, 0)

    def dot(a, b):
        return sum(x * y for x, y in zip(a, b))

    def prim(r):
        d = reduce(lcm, (Fraction(x).denominator for x in r), 1)
        rr = [int(x * d) for x in r]
        g = reduce(gcd, rr)
        return tuple(x // g for x in rr)

    # Exact double-description enumeration of Pi_4
    mV = sp.Matrix(V)
    ix = list(mV.T.rref()[1])
    m0 = mV[ix, :]
    assert m0.cols == m0.rows == 14
    mi = m0.inv()
    rays = [prim([Fraction(int(mi[r, c].p), int(mi[r, c].q)) for r in range(14)]) for c in range(14)]
    desc = {r: sum(1 << i for i in ix if dot(r, V[i]) == 0) for r in rays}
    for n_idx in range(24):
        if n_idx in ix:
            continue
        h = {r: dot(V[n_idx], r) for r in desc}
        nxt = {r: (z | (1 << n_idx) if h[r] == 0 else z) for r, z in desc.items() if h[r] >= 0}
        for rp, zp in desc.items():
            if h[rp] <= 0:
                continue
            for rm, zm in desc.items():
                if h[rm] >= 0:
                    continue
                z = zp & zm
                if z.bit_count() < 12:
                    continue
                if any((z & zt) == z for t, zt in desc.items() if t != rp and t != rm):
                    continue
                r_new = prim([h[rp] * m - h[rm] * p for m, p in zip(rm, rp)])
                nxt[r_new] = z | (1 << n_idx)
        desc = nxt

    idx_map = {p: i for i, p in enumerate(PERMS)}
    mul_tbl = [[idx_map[tuple(q[p[j]] for j in IDX)] for p in PERMS] for q in PERMS]

    def orb(v):
        return {tuple(v[mul_tbl[q][mul_tbl[i][p]]] for i in range(24)) for p, q in product(range(24), repeat=2)}

    eval_r = lambda r: prim([dot(x, r) for x in V])
    sq_v = tuple(int(p[0] == 0) for p in PERMS)
    minor_v = tuple(int({p[0], p[1]} == {0, 1}) for p in PERMS)
    kinds = [orb(sq_v), orb(minor_v), orb(eval_r(CF))]
    assert list(map(len, kinds)) == [16, 18, 48] and len(desc) == 82
    assert {eval_r(r) for r in desc} == set().union(*kinds)
    assert all(min(dot(r, p) for p in V) == 0 for r in desc)

    # Exact degree-6 U(4) moment quotient & 23-square Q(rho) SOS verification
    add_m = lambda m, n: tuple(sorted(m + n))

    def echelon(rows):
        piv = {}
        for row in rows:
            r = {i: v for i, v in row.items() if v}
            while r:
                k = max(r)
                v = r[k]
                if k not in piv:
                    if v != 1:
                        r = {
                            i: (w // v if type(w) is int and type(v) is int and w % v == 0 else Fraction(w) / v)
                            for i, w in r.items()
                        }
                    piv[k] = r
                    break
                for i, x in piv[k].items():
                    w = r.get(i, 0) - v * x
                    if w:
                        r[i] = w
                    else:
                        r.pop(i, None)
        return piv

    nv = 32
    d_deg = 3

    @lru_cache(None)
    def bar_u(m):
        return tuple(sorted(t ^ 16 for t in m))

    wt_table = [(16 ** (t % 16 // 4) + 16 ** (t % 4 + 4)) * (-1 if t >= 16 else 1) for t in range(nv)]
    weight_u = lambda m: sum(wt_table[t] for t in m)
    allm = defaultdict(list)
    for deg in range(2 * d_deg - 1):
        for m in cwr(range(nv), deg):
            allm[weight_u(m)].append(m)
    G_blocks = defaultdict(list)
    for w, lst in allm.items():
        G_blocks[w].extend(m for m in lst if len(m) <= d_deg)

    eq = []
    for transpose in (False, True):
        for i in IDX:
            for j in IDX:
                r = Counter()
                for k in IDX:
                    a_idx = 4 * i + k if not transpose else 4 * k + i
                    b_idx = 4 * j + k if not transpose else 4 * k + j
                    r[tuple(sorted((a_idx, b_idx + 16)))] += 1
                if i == j:
                    r[()] = -1
                eq.append((weight_u(next(iter(r))), r))

    def reduce_block(w, g):
        ix_b = {m: i for i, m in enumerate(g)}
        rows = []
        for ew, r in eq:
            dw = w - ew
            for m in allm.get(dw, ()):
                if len(m) > d_deg - 2:
                    break
                rows.append({ix_b[add_m(m, n)]: c for n, c in r.items()})
        piv = echelon(rows)
        return [m for i, m in enumerate(g) if i not in piv]

    canon_u = lambda m: min(m, bar_u(m))
    var = {}

    def get_var(m):
        m = canon_u(m)
        if m not in var:
            var[m] = len(var)
        return var[m]

    get_var(())
    blocks = []
    for w, g in G_blocks.items():
        if not g or w < 0:
            continue
        blocks.append(reduce_block(w, g))

    ker = []
    for w, r in eq:
        for m in allm[-w]:
            s_c = Counter()
            for n, c in r.items():
                s_c[get_var(add_m(m, n))] += c
            ker.append(s_c)

    n_var = len(var)
    invvar = [None] * n_var
    for m, i in var.items():
        invvar[i] = m
    perm_ord = sorted(range(n_var), key=lambda i: (len(invvar[i]), invvar[i]))
    order = {i: j for j, i in enumerate(perm_ord)}
    piv_k = echelon(({order[i]: v for i, v in r.items()} for r in ker))
    expansion_ord = {}
    free = []
    for k in range(n_var):
        if k not in piv_k:
            expansion_ord[k] = {len(free): 1}
            free.append(perm_ord[k])
            continue
        a_c = Counter()
        for l_idx, c in piv_k[k].items():
            if l_idx == k:
                continue
            for j, v in expansion_ord[l_idx].items():
                a_c[j] -= c * v
        expansion_ord[k] = {j: v for j, v in a_c.items() if v}
    expansion = [expansion_ord[order[i]] for i in range(n_var)]
    n_free = len(free)
    assert n_free == 261

    inner_u = lambda v, w: canon_u(add_m(bar_u(v), w))

    def facet_obj_u():
        r = Counter({(): CF[0]})
        for i, j in product(range(3), repeat=2):
            a_t = (4 * i + j,)
            r[inner_u(a_t, a_t)] += CF[1 + 3 * i + j]
        for i, j in product(range(2), repeat=2):
            R_p = PAIRS[i]
            C_p = PAIRS[j]
            for c_sub in (C_p, comp4(C_p)):
                ri, rk = R_p
                cj, cl = c_sub
                a_t = (4 * ri + cj, 4 * rk + cl)
                b_t = (4 * ri + cl, 4 * rk + cj)
                for x, vx in ((a_t, 1), (b_t, -1)):
                    for y, vy in ((a_t, 1), (b_t, -1)):
                        r[inner_u(x, y)] += CF[10 + 2 * i + j] * vx * vy
        return r

    # Stabilizer of the Orbit-2 facet
    W_vals = [dot(row, CF) for row in V]
    mats = [frozenset((i, p[i]) for i in range(4)) for p in PERMS]
    m_index = {s: i for i, s in enumerate(mats)}
    stab = []
    for p, q, tr in product(PERMS, PERMS, (0, 1)):
        lut = [(q[j], p[i]) if tr else (p[i], q[j]) for i in range(4) for j in range(4)]
        if all(W_vals[m_index[frozenset(lut[4 * i + j] for i, j in s)]] == W_vals[k] for k, s in enumerate(mats)):
            v_perm = [4 * i + j for i, j in lut]
            stab.append(v_perm + [x + 16 for x in v_perm])
    assert len(stab) == 24

    # Cubic number field Q(rho), rho^3 + rho^2 + 3*rho - 1 = 0, 0 < rho < 1
    r_sym = sp.symbols("r")
    poly_r = sp.Poly(r_sym ** 3 + r_sym ** 2 + 3 * r_sym - 1, r_sym)
    R_field = sp.QQ.alg_field_from_poly(poly_r, root_index=0)
    rr = R_field.unit
    assert rr ** 3 + rr ** 2 + 3 * rr - 1 == R_field.zero

    def alg_coeffs(x):
        return [Fraction(int(a.numerator), int(a.denominator)) for a in R_field.convert(x).to_list()]

    def alg_read(s_str: str):
        return R_field.new([R_field.dom.convert(Fraction(i)) for i in s_str.split(",")]) if s_str else R_field.zero

    # Exact rational bisection isolating rho in (0, 1) to 110 bits
    lo, hi = Fraction(0), Fraction(1)
    for _ in range(110):
        mid = (lo + hi) / 2
        if mid ** 3 + mid ** 2 + 3 * mid < 1:
            lo = mid
        else:
            hi = mid

    def alg_interval(x):
        l_b = h_b = Fraction(0)
        for c in alg_coeffs(x):
            ll = min(l_b * lo, l_b * hi) + c
            hh = max(h_b * lo, h_b * hi) + c
            l_b, h_b = ll, hh
        return l_b, h_b

    K_conf = [[0, -1, -1, -1], [1, 0, -1, 1], [1, 1, 0, -1], [1, -1, 1, 0]]
    assert all(
        K_conf[i][j] == -K_conf[j][i] and sum(K_conf[i][l] * K_conf[j][l] for l in range(4)) == 3 * int(i == j)
        for i in range(4) for j in range(4)
    )
    sign_conf = [int(K_conf[i][3 - j]) if i != 3 - j else 1 for i in range(4) for j in range(4)]
    diag_conf = [int(i == 3 - j) for i in range(4) for j in range(4)]
    gamma = 4 * rr ** 2 / (3 + rr ** 2) - 8 * rr / (3 + rr ** 2) ** 2

    @lru_cache(None)
    def sm_u(m):
        ret = Counter()
        for P_s in stab:
            v = canon_u(tuple(sorted(P_s[t] for t in m)))
            for j, x in expansion[var[v]].items():
                ret[j] += x
        return {j: R_field.convert(Fraction(x, len(stab))) for j, x in ret.items() if x}

    f_obj = facet_obj_u()
    target_c = Counter()
    for m, v in f_obj.items():
        for j, x in sm_u(m).items():
            target_c[j] += x * int(v)
    for j, x in sm_u(()).items():
        target_c[j] -= x * gamma
    target_u = {j: x for j, x in target_c.items() if x}

    # Exact attainment on (rho I + K) J / sqrt(3 + rho^2) & stabilizer invariance in quotient
    cf_q = Counter()
    val_att = R_field.zero
    for m, cc in f_obj.items():
        for j, w in expansion[var[canon_u(m)]].items():
            cf_q[j] += int(cc) * w
        val_att += R_field.convert(int(cc)) * prod(
            sign_conf[k % 16] * (rr if diag_conf[k % 16] else R_field.one) for k in m
        ) / (3 + rr ** 2) ** (len(m) // 2)
    assert val_att == gamma
    cf_q[0] = R_field.convert(cf_q[0]) - gamma
    assert all(target_u.get(i, R_field.zero) == R_field.convert(cf_q[i]) for i in range(n_free))

    basis_cache = {}

    def get_basis(k):
        if k in basis_cache:
            return basis_cache[k]
        ms = blocks[k]
        d_max = max(map(len, ms))
        w_list = []
        wk = []
        for m in ms:
            a_cnt = sum(diag_conf[j % 16] for j in m)
            b_cnt = (d_max - len(m)) // 2
            sg = prod(sign_conf[j % 16] for j in m)
            w_list.append(sg * rr ** a_cnt * (3 + rr ** 2) ** b_cnt)
            wk.append((b_cnt, -a_cnt))
        piv_i = max(range(len(ms)), key=lambda i: wk[i])
        rest = [i for i in range(len(ms)) if i != piv_i]
        ratios = [w_list[i] / w_list[piv_i] for i in rest]
        basis_cache[k] = (ms, piv_i, rest, ratios)
        return basis_cache[k]

    def square_col(k, vec):
        ms, piv_i, rest, ratios = get_basis(k)
        assert len(rest) == len(vec)
        terms = {rest[i]: int(v) for i, v in enumerate(vec) if v}
        terms[piv_i] = -sum(w * int(v) for v, w in zip(vec, ratios))
        ix_t = list(terms)
        c_out = Counter()
        for j, v in enumerate(ix_t):
            for u in ix_t[: j + 1]:
                coeff = (1 if u == v else 2) * terms[u] * terms[v]
                if not coeff:
                    continue
                for h_idx, x in sm_u(inner_u(ms[u], ms[v])).items():
                    c_out[h_idx] += x * coeff
        return c_out

    sos_data = json.loads((HERE / "orbit2_u4_sos.json").read_text(encoding="utf-8"))
    squares = sos_data["squares"]
    cols = [square_col(k, v) for k, v in squares]
    weights = [alg_read(x) for x in sos_data["weights"]]
    assert len(squares) == len(weights) == 23

    def check_sos(w_list):
        for w in w_list:
            assert alg_interval(w)[0] > 0
        for i in range(n_free):
            lhs = sum((c.get(i, R_field.zero) * w for c, w in zip(cols, w_list)), R_field.zero)
            assert lhs == target_u.get(i, R_field.zero)

    check_sos(weights)

    # Corrupted SOS weight mutation test
    w_mut = [w if i else w + R_field.one for i, w in enumerate(weights)]
    try:
        check_sos(w_mut)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 6 Q(rho) SOS mutation escaped!")

    print("  PASS: 82 facets (16/18/48), exact conference attainment, & 23-square Q(rho) U(4) SOS (261 free moments); mutation rejected.")


# =============================================================================
# Section 7: Theorem F (Part 2) — Tao 6x6 Hadamard Escape & Positive Slices
# =============================================================================

def verify_section_7_tao_hadamard() -> None:
    print("[7/7] Theorem F (part 2): Tao 6x6 Hadamard 45-zero mask, signed distance 1/40, & positive slice laws...")
    E = [
        [0, 0, 0, 0, 0, 0],
        [0, 0, 1, 1, 2, 2],
        [0, 1, 0, 2, 2, 1],
        [0, 1, 2, 0, 1, 2],
        [0, 2, 2, 1, 0, 1],
        [0, 2, 1, 2, 1, 0],
    ]

    def mask(e_mat):
        return [
            (i, k, j, l)
            for i, k in combinations(range(6), 2)
            for j, l in combinations(range(6), 2)
            if (e_mat[i][j] + e_mat[k][l] - e_mat[i][l] - e_mat[k][j]) % 3 == 0
        ]

    def verify_mask(e_mat):
        for i, k in combinations(range(6), 2):
            assert Counter((e_mat[i][j] - e_mat[k][j]) % 3 for j in range(6)) == {0: 2, 1: 2, 2: 2}
        Z = mask(e_mat)
        assert len(Z) == 45
        counts = Counter(sum({p[i], p[k]} == {j, l} for i, k, j, l in Z) for p in permutations(range(6)))
        assert counts == {1: 360, 5: 360}
        return Z

    Z = verify_mask(E)
    bad_E = [r[:] for r in E]
    bad_E[1][1] += 1
    try:
        verify_mask(bad_E)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 7 Tao matrix mutation escaped!")

    def phases(I_sub, J_sub) -> int:
        k = len(I_sub)
        coeff = [0, 0, 0]
        for p in permutations(range(k)):
            parity = sum(p[i] > p[j] for i in range(k) for j in range(i + 1, k)) % 2
            coeff[sum(E[i][J_sub[p[r]]] for r, i in enumerate(I_sub)) % 3] += 1 - 2 * parity
        a, b, c = coeff
        return a * a + b * b + c * c - a * b - a * c - b * c

    ps = list(permutations(range(6)))
    ss = {k: list(combinations(range(6), k)) for k in (1, 2, 3)}
    hits = [sum({p[i], p[j]} == {k, l} for i, j, k, l in Z) for p in ps]

    def check_signed(mutate: bool = False):
        w = [5 if f == 1 else -1 for f in hits]
        assert sum(w) == 1440 and w.count(-1) == 360
        if mutate:
            j = w.index(5)
            w[0], w[j] = w[j], w[0]
        upper = Fraction(0)
        heavy = [0] * len(ps)
        nheavy = 0
        for k, subs in ss.items():
            for I_sub in subs:
                byJ = {J_sub: [] for J_sub in subs}
                for t, p in enumerate(ps):
                    byJ[tuple(sorted(p[i] for i in I_sub))].append(t)
                for J_sub, L_idx in byJ.items():
                    d = Fraction(phases(I_sub, J_sub), 6 ** k)
                    assert Fraction(sum(w[t] for t in L_idx), 1440) == d
                    h1 = Fraction(sum(hits[t] == 1 for t in L_idx), 360)
                    upper = max(upper, abs(h1 - d))
                    if k == 3 and d == Fraction(1, 8):
                        nheavy += 1
                        for t in L_idx:
                            heavy[t] += 1
        assert nheavy == 40 and Counter(zip(hits, heavy)) == {(1, 4): 360, (5, 0): 360}
        assert upper == (nheavy * Fraction(1, 8) - max(heavy)) / nheavy == Fraction(1, 40)

    check_signed(False)
    try:
        check_signed(True)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 7 signed-weight mutation escaped!")

    # Positive slice laws (repeated-eigenvalue 192-uniform & cross-collision 41/96)
    rep = (1, 0, 2, 3, 4, 5)
    GEN = [(rep, (1, 0, 3, 2, 5, 4)), ((1, 2, 3, 4, 5, 0), (3, 1, 4, 0, 5, 2))]
    spair = lambda i, j: (i, j) if i < j else (j, i)

    def check_slices(mutate: bool = False):
        Zset = set(Z)
        for r, s in GEN:
            assert {(*spair(r[i], r[k]), *spair(s[j], s[l])) for i, k, j, l in Z} == Zset
        Orb = {(0, 0)}
        prev = set()
        while prev != Orb:
            prev = set(Orb)
            for r, s in GEN:
                Orb.update((r[i], s[j]) for i, j in prev)
        assert len(Orb) == 36
        pairs_orb = {(0, 1)}
        prev = set()
        while prev != pairs_orb:
            prev = set(pairs_orb)
            for r, _ in GEN:
                pairs_orb.update(spair(r[i], r[k]) for i, k in prev)
        assert len(pairs_orb) == 15

        safe = [p for p in ps if all(((i < 2) != (k < 2)) or spair(p[i], p[k]) != (j, l) for i, k, j, l in Z)]
        assert len(safe) == 192
        M_col = [
            (16, [0]),
            (4, [120, 264, 390, 512, 633]),
            (3, [121, 126, 266, 339, 403, 444, 514, 536, 647, 687]),
            (2, [127, 341, 450, 538, 693]),
            (1, [148, 181, 208, 237, 243, 325, 333, 356, 378, 443, 458, 466, 500, 547, 557, 561, 617, 662, 666, 676]),
        ]
        ws = {i: v for v, L_idx in M_col for i in L_idx}
        assert sum(ws.values()) == 96 and len(ws) == 41
        if mutate:
            ws[120] -= 1
            ws[121] += 1
        for k in (1, 2, 3):
            subs = ss[k]
            ro = defaultdict(list)
            for I_sub in subs:
                ro[tuple(sorted(0 if i < 2 else i for i in I_sub))].append(I_sub)
            image = lambda p, I_sub: tuple(sorted(p[i] for i in I_sub))
            for O_grp in ro.values():
                cnt = defaultdict(int)
                for I_sub in O_grp:
                    for p in safe:
                        cnt[image(p, I_sub)] += 1
                for J_sub in subs:
                    assert cnt[J_sub] * 6 ** k == 192 * sum(phases(I_sub, J_sub) for I_sub in O_grp)
            for I_sub in subs:
                cnt = defaultdict(int)
                for t, w_val in ws.items():
                    cnt[image(ps[t], I_sub)] += w_val
                for J_sub in subs:
                    if (0 in I_sub) != (0 in J_sub):
                        assert cnt[J_sub] * 6 ** k == 96 * phases(I_sub, J_sub)

    check_slices(False)
    try:
        check_slices(True)
    except AssertionError:
        pass
    else:
        raise RuntimeError("Section 7 collision-weight mutation escaped!")

    print("  PASS: Tao_6 45-zero mask, optimal signed weights (neg mass 1/4, l_inf 1/40), & positive slice laws (192 & 41/96); mutations rejected.")


def main() -> None:
    verify_section_1_arrowhead()
    verify_section_2_rank_excess()
    verify_section_3_real_chord()
    verify_section_4_two_tetrahedron_and_obstructions()
    verify_section_5_singular_boundary()
    verify_section_6_pi4_and_orbit2_sos()
    verify_section_7_tao_hadamard()
    print("ALL 7 EXACT ZERO-FLOAT VERIFICATION SECTIONS PASSED.")


if __name__ == "__main__":
    main()
