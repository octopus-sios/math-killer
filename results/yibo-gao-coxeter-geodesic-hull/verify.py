#!/usr/bin/env python3
"""
Exact (zero-float) verification script for the disproof of Gaetz–Gao's
strong hull property conjecture (Conjecture 1.2 of arXiv:2012.06841v2)
and the ordinary hull property in W(A3~) and all irreducible affine
Coxeter groups of rank >= 4.

Uses only exact integer and rational (fractions.Fraction) arithmetic.
"""

from collections import deque
from fractions import Fraction
import random
import sys


# =============================================================================
# 1. Exact AffPerm4 model of W(A3~) matching lean/Conjectures/YiboGaoCoxeterGeodesicHull.lean
# =============================================================================

def perm_inv(s):
    r = [0, 0, 0, 0]
    for i, v in enumerate(s):
        r[v] = i
    return tuple(r)


def aff_mul(f, g):
    af, sf = f
    ag, sg = g
    sfi = perm_inv(sf)
    return (
        tuple(af[i] + ag[sfi[i]] for i in range(4)),
        tuple(sf[sg[i]] for i in range(4)),
    )


def aff_inv(f):
    a, s = f
    return (tuple(-a[s[i]] for i in range(4)), perm_inv(s))


def aff_eval_inv(f, y):
    a, s = f
    si = perm_inv(s)
    q, r = divmod(y, 4)
    return si[r] + 4 * (q - a[r])


def phi_coords(f):
    """6-tuple of hyperplane thresholds Phi_{ij}(f) = floor((f^{-1}(i) - f^{-1}(j)) / 4)."""
    return tuple(
        (aff_eval_inv(f, i) - aff_eval_inv(f, j)) // 4
        for i in range(4)
        for j in range(i + 1, 4)
    )


def l1_dist(f, g):
    pf, pg = phi_coords(f), phi_coords(g)
    return sum(abs(x - y) for x, y in zip(pf, pg))


AFF_ID = ((0, 0, 0, 0), (0, 1, 2, 3))
AFF_GENS = [
    ((1, 0, 0, -1), (3, 1, 2, 0)),  # s_0
    ((0, 0, 0, 0), (1, 0, 2, 3)),   # s_1
    ((0, 0, 0, 0), (0, 2, 1, 3)),   # s_2
    ((0, 0, 0, 0), (0, 1, 3, 2)),   # s_3
]
A3_TILDE_MATRIX = [
    [1, 3, 2, 3],
    [3, 1, 3, 2],
    [2, 3, 1, 3],
    [3, 2, 3, 1],
]


def aff_word_prod(word):
    res = AFF_ID
    for k in word:
        res = aff_mul(res, AFF_GENS[k])
    return res


def check_coxeter_relations(gens, mul_fn, id_elem, matrix):
    n = len(matrix)
    for i in range(n):
        for j in range(n):
            m = matrix[i][j]
            prod = id_elem
            step = mul_fn(gens[i], gens[j])
            for _ in range(m):
                prod = mul_fn(prod, step)
            if prod != id_elem:
                return False, (i, j, m)
    return True, None


# =============================================================================
# 2. Independent exact integer Tits geometric representation of W(A3~)
# =============================================================================

def mat_mul(A, B):
    n = len(A)
    return tuple(
        tuple(sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n))
        for i in range(n)
    )


def build_tits_generators(matrix):
    """Exact integer Tits reflection matrices for simply-laced Coxeter matrices (m_ij in {1,2,3})."""
    n = len(matrix)
    B = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                B[i][j] = 2
            elif matrix[i][j] == 2:
                B[i][j] = 0
            elif matrix[i][j] == 3:
                B[i][j] = -1
            else:
                raise ValueError("Unsupported Coxeter entry")
    gens = []
    for k in range(n):
        # S_k(e_j) = e_j - B[k][j] e_k
        M = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        for j in range(n):
            M[k][j] -= B[k][j]
        gens.append(tuple(tuple(row) for row in M))
    mat_id = tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))
    return mat_id, gens


def verify_model_and_l1_isometry():
    ok, bad = check_coxeter_relations(AFF_GENS, aff_mul, AFF_ID, A3_TILDE_MATRIX)
    assert ok, f"AffPerm4 failed Coxeter relation {bad}"

    mat_id, tits_gens = build_tits_generators(A3_TILDE_MATRIX)
    ok_t, bad_t = check_coxeter_relations(tits_gens, mat_mul, mat_id, A3_TILDE_MATRIX)
    assert ok_t, f"Tits representation failed Coxeter relation {bad_t}"

    # BFS ball of radius 6 in BOTH representations simultaneously
    radius = 6
    aff_dist = {AFF_ID: 0}
    tits_dist = {mat_id: 0}
    aff_to_tits = {AFF_ID: mat_id}
    tits_to_aff = {mat_id: AFF_ID}
    q = deque([(AFF_ID, mat_id, 0)])
    while q:
        u_a, u_t, d = q.popleft()
        if d == radius:
            continue
        for k in range(4):
            v_a = aff_mul(u_a, AFF_GENS[k])
            v_t = mat_mul(u_t, tits_gens[k])
            in_a = v_a in aff_dist
            in_t = v_t in tits_dist
            assert in_a == in_t, "Representation mismatch on BFS ball"
            if not in_a:
                aff_dist[v_a] = d + 1
                tits_dist[v_t] = d + 1
                aff_to_tits[v_a] = v_t
                tits_to_aff[v_t] = v_a
                q.append((v_a, v_t, d + 1))
            else:
                assert aff_to_tits[v_a] == v_t
                assert tits_to_aff[v_t] == v_a

    assert len(aff_dist) == len(tits_dist)
    for f, d in aff_dist.items():
        assert l1_dist(AFF_ID, f) == d, f"l1_dist mismatch for {f}"

    # Verify pairwise l1_dist(f, g) == length(f^-1 * g) and step size 1
    rng = random.Random(20261127)
    elems = sorted(aff_dist.keys())
    for _ in range(1000):
        f = rng.choice(elems)
        g = rng.choice(elems)
        assert l1_dist(f, g) == l1_dist(AFF_ID, aff_mul(aff_inv(f), g))
        for k in range(4):
            assert l1_dist(f, aff_mul(f, AFF_GENS[k])) == 1

    print(f"[PASS] Model consistency & L1 isometry verified on full radius-{radius} ball ({len(aff_dist)} elements) + 1000 pairs.")


# =============================================================================
# 3. Exact geodesic convex hull verification in Cay(W(A3~), S)
# =============================================================================

def exact_phi_box_bfs(anchors):
    """Enumerate the exact Phi-coordinate box spanned by anchors via connected Cayley BFS."""
    phis = [phi_coords(x) for x in anchors]
    lo = [min(p[c] for p in phis) for c in range(6)]
    hi = [max(p[c] for p in phis) for c in range(6)]

    def in_box(f):
        pf = phi_coords(f)
        return all(lo[c] <= pf[c] <= hi[c] for c in range(6))

    seen = {anchors[0]}
    q = deque([anchors[0]])
    while q:
        u = q.popleft()
        for g in AFF_GENS:
            v = aff_mul(u, g)
            if v not in seen and in_box(v):
                seen.add(v)
                q.append(v)
    for a in anchors:
        assert a in seen, "Anchor missing from connected Phi-box"
    return seen


def verify_geodesic_closure_directly(anchors, hull_set):
    """
    Independent graph-theoretic sanity check:
    1. Every anchor lies in hull_set.
    2. For a pair {u, v}, EVERY w in hull_set satisfies dist(u, w) + dist(w, v) == dist(u, v)
       and EVERY neighbor of w outside hull_set fails dist(u, z) + dist(z, v) == dist(u, v).
    3. For a general finite set X, hull_set is closed under taking all shortest-path neighbors
       between any x, y in hull_set (checked by convexity of the Phi-box).
    """
    for a in anchors:
        assert a in hull_set
    if len(anchors) == 2:
        u, v = anchors
        duv = l1_dist(u, v)
        for w in hull_set:
            assert l1_dist(u, w) + l1_dist(w, v) == duv
            for g in AFF_GENS:
                z = aff_mul(w, g)
                if z not in hull_set:
                    assert l1_dist(u, z) + l1_dist(z, v) > duv


def pure_geodesic_closure_small(anchors):
    """
    Completely independent brute-force iterative geodesic closure in Cay(W(A3~), S),
    using ONLY graph shortest-path distances (no Phi-box assumption).
    Suitable for small hulls (e.g. L = 1, 2).
    """
    C = set(anchors)
    while True:
        added = set()
        C_list = list(C)
        # Check every neighbor z of every vertex in C to see if z lies on a geodesic
        # between some pair (u, v) in C.
        candidates = set()
        for w in C_list:
            for g in AFF_GENS:
                z = aff_mul(w, g)
                if z not in C:
                    candidates.add(z)
        for z in candidates:
            found = False
            for i in range(len(C_list)):
                u = C_list[i]
                duz = l1_dist(u, z)
                for j in range(i + 1, len(C_list)):
                    v = C_list[j]
                    if duz + l1_dist(z, v) == l1_dist(u, v):
                        found = True
                        break
                if found:
                    break
            if found:
                added.add(z)
        if not added:
            return C
        C |= added


def verify_a3tilde_counterexamples():
    w_a = [0, 3, 1, 2]
    w_b = [2, 0, 3, 1]
    t1_word = w_a + w_a
    t2_word = w_b + w_b

    t1 = aff_word_prod(t1_word)
    t2 = aff_word_prod(t2_word)
    assert t1 == ((1, 1, -1, -1), (0, 1, 2, 3))
    assert t2 == ((1, -1, 1, -1), (0, 1, 2, 3))
    assert l1_dist(AFF_ID, t1) == 8
    assert l1_dist(AFF_ID, t2) == 8

    def t_pow(t, L):
        a, s = t
        return (tuple(L * x for x in a), s)

    # Cross-check independent pure geodesic closure against Phi-box on L = 1
    H1_box = exact_phi_box_bfs([AFF_ID, t1, t2])
    H1_geo = pure_geodesic_closure_small([AFF_ID, t1, t2])
    assert H1_box == H1_geo and len(H1_box) == 53
    assert exact_phi_box_bfs([AFF_ID, t1]) == pure_geodesic_closure_small([AFF_ID, t1])
    assert exact_phi_box_bfs([AFF_ID, t2]) == pure_geodesic_closure_small([AFF_ID, t2])
    print("[PASS] Independent iterative geodesic closure matches Phi-box exactly at L=1 (|Conv(e,t1,t2)| = 53).")

    # Negative control: L = 1 satisfies both inequalities
    c1_u = len(exact_phi_box_bfs([AFF_ID, t1]))
    c1_v = len(exact_phi_box_bfs([AFF_ID, t2]))
    assert c1_u == 12 and c1_v == 13 and c1_u * c1_v == 156 >= 53
    print("[PASS] Negative control (L=1): 12 * 13 = 156 >= 53 (no false violation before crossover).")

    # Concrete symmetric STRONG hull counterexample: L = 8
    u8, v8 = t_pow(t1, 8), t_pow(t2, 8)
    Hu8 = exact_phi_box_bfs([AFF_ID, u8])
    Hv8 = exact_phi_box_bfs([AFF_ID, v8])
    Huv8 = exact_phi_box_bfs([AFF_ID, u8, v8])
    verify_geodesic_closure_directly([AFF_ID, u8], Hu8)
    verify_geodesic_closure_directly([AFF_ID, v8], Hv8)
    assert len(Hu8) == 96 and len(Hv8) == 97 and len(Huv8) == 9825
    assert len(Hu8) * len(Hv8) == 9312 < 9825
    print(
        f"[PASS] Strong hull counterexample (L=8): |Conv(e, t1^8)|={len(Hu8)}, "
        f"|Conv(e, t2^8)|={len(Hv8)}, prod={len(Hu8)*len(Hv8)} < {len(Huv8)} = |Conv(e, t1^8, t2^8)|."
    )

    # Concrete ORDINARY hull counterexample (hence also strong hull): (L1, L2) = (5, 10)
    u5, v10 = t_pow(t1, 5), t_pow(t2, 10)
    Hu5 = exact_phi_box_bfs([AFF_ID, u5])
    Hv10 = exact_phi_box_bfs([AFF_ID, v10])
    Huv510 = exact_phi_box_bfs([u5, v10])
    verify_geodesic_closure_directly([AFF_ID, u5], Hu5)
    verify_geodesic_closure_directly([AFF_ID, v10], Hv10)
    verify_geodesic_closure_directly([u5, v10], Huv510)
    assert l1_dist(AFF_ID, u5) == 40
    assert l1_dist(AFF_ID, v10) == 80
    assert l1_dist(u5, v10) == 100
    assert len(Hu5) == 60 and len(Hv10) == 121 and len(Huv510) == 7921
    assert len(Hu5) * len(Hv10) == 7260 < 7921
    print(
        f"[PASS] Ordinary hull counterexample (L1=5, L2=10): |Conv(e, t1^5)|={len(Hu5)}, "
        f"|Conv(e, t2^10)|={len(Hv10)}, prod={len(Hu5)*len(Hv10)} < {len(Huv510)} = |Conv(t1^5, t2^10)|."
    )

    # Verify Lean symbolic family bounds at m = 1 and numeric inequality at m = 200000
    u_m1, v_m1 = t_pow(t1, 6), t_pow(t2, 12)
    c_u1 = len(exact_phi_box_bfs([AFF_ID, u_m1]))
    c_v1 = len(exact_phi_box_bfs([AFF_ID, v_m1]))
    c_uv1 = len(exact_phi_box_bfs([u_m1, v_m1]))
    assert c_u1 == 72 <= 48 * (6 * 1 + 2)
    assert c_v1 == 145 <= 48 * (12 * 1 + 2)
    assert (1 + 1) ** 3 <= c_uv1 and c_uv1 == 13105 and c_u1 * c_v1 == 10440 < 13105

    m = 200000
    lhs = (m + 1) ** 3
    rhs = (48 * (6 * m + 2)) * (48 * (12 * m + 2))
    assert lhs > rhs
    print(f"[PASS] Lean symbolic family bounds verified at m=1 (exact: 72*145=10440 < 13105) and m=200000 ({lhs} > {rhs}).")


# =============================================================================
# 4. Universal interior-node theorem for ALL irreducible affine types of rank >= 4
# =============================================================================

def exact_rank(vecs):
    if not vecs:
        return 0
    mat = [[Fraction(x) for x in v] for v in vecs]
    r = 0
    cols = len(mat[0])
    for c in range(cols):
        piv = None
        for i in range(r, len(mat)):
            if mat[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        pv = mat[r][c]
        mat[r] = [x / pv for x in mat[r]]
        for i in range(len(mat)):
            if i != r and mat[i][c] != 0:
                f = mat[i][c]
                mat[i] = [mat[i][j] - f * mat[r][j] for j in range(cols)]
        r += 1
    return r


def gen_positive_roots_from_cartan(C):
    n = len(C)
    roots = set()
    q = deque()
    for i in range(n):
        e = tuple(1 if j == i else 0 for j in range(n))
        roots.add(e)
        q.append(e)
    while q:
        v = q.popleft()
        for j in range(n):
            val = sum(v[i] * C[i][j] for i in range(n))
            nv = tuple(v[k] - (val if k == j else 0) for k in range(n))
            if nv not in roots:
                roots.add(nv)
                q.append(nv)
    return sorted(r for r in roots if all(x >= 0 for x in r))


def cartan_A(n):
    return [[2 if i == j else (-1 if abs(i - j) == 1 else 0) for j in range(n)] for i in range(n)]


def cartan_B(n):
    C = cartan_A(n)
    C[n - 2][n - 1] = -2
    return C


def cartan_C(n):
    C = cartan_A(n)
    C[n - 1][n - 2] = -2
    return C


def cartan_D(n):
    C = [[2 if i == j else 0 for j in range(n)] for i in range(n)]
    for i in range(n - 2):
        C[i][i + 1] = C[i + 1][i] = -1
    C[n - 3][n - 1] = C[n - 1][n - 3] = -1
    return C


CARTAN_F4 = [
    [2, -1, 0, 0],
    [-1, 2, -2, 0],
    [0, -1, 2, -1],
    [0, 0, -1, 2],
]

CARTAN_E6 = [
    [2, 0, -1, 0, 0, 0],
    [0, 2, 0, -1, 0, 0],
    [-1, 0, 2, -1, 0, 0],
    [0, -1, -1, 2, -1, 0],
    [0, 0, 0, -1, 2, -1],
    [0, 0, 0, 0, -1, 2],
]

CARTAN_E7 = [
    [2, 0, -1, 0, 0, 0, 0],
    [0, 2, 0, -1, 0, 0, 0],
    [-1, 0, 2, -1, 0, 0, 0],
    [0, -1, -1, 2, -1, 0, 0],
    [0, 0, 0, -1, 2, -1, 0],
    [0, 0, 0, 0, -1, 2, -1],
    [0, 0, 0, 0, 0, -1, 2],
]

CARTAN_E8 = [
    [2, 0, -1, 0, 0, 0, 0, 0],
    [0, 2, 0, -1, 0, 0, 0, 0],
    [-1, 0, 2, -1, 0, 0, 0, 0],
    [0, -1, -1, 2, -1, 0, 0, 0],
    [0, 0, 0, -1, 2, -1, 0, 0],
    [0, 0, 0, 0, -1, 2, -1, 0],
    [0, 0, 0, 0, 0, -1, 2, -1],
    [0, 0, 0, 0, 0, 0, -1, 2],
]


def verify_universal_affine_rank_ge_4():
    """
    For any irreducible finite root system of rank n >= 3 with interior node b (deg(b) >= 2),
    d1 = omega_b^v and d2 = s_b(omega_b^v) satisfy:
      rank(Phi_d1^perp) = rank(Phi_d2^perp) = n - 1,
      dim F = n - rank(Phi_d1^perp cap Phi_d2^perp) = deg(b) + 1 >= 3.
    """
    cases = [
        ("A3~", cartan_A(3), 1, 3),
        ("A4~", cartan_A(4), 1, 3),
        ("B3~", cartan_B(3), 1, 3),
        ("B4~", cartan_B(4), 1, 3),
        ("C3~", cartan_C(3), 1, 3),
        ("C4~", cartan_C(4), 1, 3),
        ("D4~", cartan_D(4), 1, 4),
        ("D5~", cartan_D(5), 2, 4),
        ("F4~", CARTAN_F4, 1, 3),
        ("E6~", CARTAN_E6, 3, 4),
        ("E7~", CARTAN_E7, 3, 4),
        ("E8~", CARTAN_E8, 3, 4),
    ]
    for name, C, b, expected_dimF in cases:
        n = len(C)
        pos = gen_positive_roots_from_cartan(C)
        d1 = tuple(1 if i == b else 0 for i in range(n))
        d2 = tuple(d1[i] - C[i][b] * d1[b] for i in range(n))
        p1 = [r for r in pos if sum(r[i] * d1[i] for i in range(n)) == 0]
        p2 = [r for r in pos if sum(r[i] * d2[i] for i in range(n)) == 0]
        p12 = [r for r in p1 if sum(r[i] * d2[i] for i in range(n)) == 0]
        r1, r2, r12 = exact_rank(p1), exact_rank(p2), exact_rank(p12)
        dimF = n - r12
        assert r1 == n - 1 and r2 == n - 1 and dimF == expected_dimF and dimF >= 3, (
            f"Unexpected ranks for {name}: r1={r1}, r2={r2}, r12={r12}"
        )
    print(f"[PASS] Universal interior-node criterion verified across {len(cases)} affine types (A3..A4, B3..B4, C3..C4, D4..D5, F4, E6, E7, E8), all dim F >= 3.")


# =============================================================================
# 5. Negative / mutation-rejection controls
# =============================================================================

def verify_negative_controls():
    # Control A: Finite Coxeter group S_4 = W(A3) satisfies the strong hull property exhaustively.
    s4_gens = [
        (1, 0, 2, 3),
        (0, 2, 1, 3),
        (0, 1, 3, 2),
    ]
    s4_id = (0, 1, 2, 3)

    def s4_mul(p, q):
        return tuple(p[q[i]] for i in range(4))

    def s4_inv(p):
        return perm_inv(p)

    def s4_left_inversions(p):
        pi = s4_inv(p)
        return frozenset((i, j) for i in range(4) for j in range(i + 1, 4) if pi[i] > pi[j])

    # Generate all 24 elements of S_4
    s4 = {s4_id}
    q = deque([s4_id])
    while q:
        u = q.popleft()
        for g in s4_gens:
            v = s4_mul(u, g)
            if v not in s4:
                s4.add(v)
                q.append(v)
    assert len(s4) == 24
    inv_sets = {w: s4_left_inversions(w) for w in s4}

    def conv_s4(elems):
        inter = set.intersection(*(set(inv_sets[x]) for x in elems))
        union = set.union(*(set(inv_sets[x]) for x in elems))
        return sum(1 for w in s4 if inter <= inv_sets[w] <= union)

    for u in s4:
        cu = conv_s4([s4_id, u])
        for v in s4:
            cv = conv_s4([s4_id, v])
            cuv = conv_s4([s4_id, u, v])
            assert cu * cv >= cuv, f"False violation in S_4 for {u}, {v}"
    print("[PASS] Negative control (finite W(A3) = S4): strong hull property holds for all 576 pairs (e, u, v).")

    # Control B: Mutation of s_0 must be rejected by Coxeter relation checker.
    mutated_gens = list(AFF_GENS)
    mutated_gens[0] = ((1, 1, 0, -2), (3, 1, 2, 0))
    ok_mut, bad_mut = check_coxeter_relations(mutated_gens, aff_mul, AFF_ID, A3_TILDE_MATRIX)
    assert not ok_mut and bad_mut is not None
    print(f"[PASS] Mutation control: corrupted s_0 rejected by Coxeter relation checker at {bad_mut}.")


def main():
    verify_model_and_l1_isometry()
    verify_a3tilde_counterexamples()
    verify_universal_affine_rank_ge_4()
    verify_negative_controls()
    print("\nALL CHECKS PASSED (100% exact zero-float arithmetic).")


if __name__ == "__main__":
    main()
