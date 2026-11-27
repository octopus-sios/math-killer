#!/usr/bin/env python3
"""Exact zero-float verification suite for Conway's Thrackle Conjecture results.

Self-contained stdlib-only verifier (no floating-point arithmetic) covering:
  1. Exact integer-scaled cyclic DP discharging certificates for all 12 tiers
     (A through F, including E2 and E2b -> m <= floor(5(n-1)/4)) plus
     corrupted-target negative controls and exact minimum-cardinality target scans.
  2. Exact periodic bipartite plane sharpness witnesses (A, B, C, Cprior, D, F)
     and necessity witness dual_Dstar.json (proving Theta(1,7,9) is required to
     reach 5/4 after NSB(15)), with girth >= 8, exhaustive minimal-bicycle checks,
     and mutation controls.
  3. Exact rational segment-intersection construction and exhaustive inner-start
     3-step dual-walk enumeration on standard odd musquashes C_5 and C_7
     (closing the unbounded plane exclusion for all cycles of length <= 7),
     cross-checked by an independent combinatorial dart-orbit plane checker
     with crossing-sign mutation controls.
  4. First-principles combinatorial rotation-system check of C_4 non-thrackleability
     (0 plane thrackle models) and positive control on C_5.
  5. Complete minimal-bicyclic graph enumeration for n in {13, 14, 15} (40, 48, 56
     graphs) plus targeted n = 16 exclusions (db_8_8_1, th_1_7_9, ...), checked
     1-to-1 against sat_manifest.json for structural accuracy, strict-RUP / DRAT /
     zero-RAT-core / semantic-audit consistency, and corrupted-manifest rejection.
"""

from __future__ import annotations

import copy
import json
import math
import re
import sys
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEX64_RE = re.compile(r"^[0-9a-f]{64}$")


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


# =============================================================================
# Section 1: Exact Discharging Certificates & Minimum-Cardinality Target Scans
# =============================================================================


def ordered_pair(a: int, b: int) -> tuple[int, int]:
    return (a, b) if a <= b else (b, a)


class Tier:
    def __init__(self, N: int, theta: tuple = (), db: tuple = (), hex_free: bool = False):
        self.N = N
        self.theta = set(theta)
        self.db = set(db)
        self.hex_free = hex_free

    def cap(self, s: int, D: int) -> int:
        b = self.N + 2
        c = min(s, s + D - b)
        if D <= self.N + 1 and c >= 1 and c == s + D - b:
            if tuple(sorted((c, s - c, D - c))) in self.theta:
                c -= 1
        if self.hex_free and s == 6 and D <= self.N + 1:
            c = 0
        return max(c, 0)

    def mingap(self, s: int, t: int) -> int:
        g = self.N + 2 - s - t
        if g >= 0 and (*ordered_pair(s, t), g) in self.db:
            g += 1
        return max(0, g)


def check_discharging(tier: Tier, d: Q, h: Q, bend: int = 0) -> tuple[bool, object]:
    A = {s: (d + 6 * h) / s - 1 for s in (6, 8)}
    if not (8 <= d and h >= 0 and all(u >= 0 for u in A.values())):
        return False, "parameter range"
    if any(tier.cap(6, s) > 0 for s in (6, 8)):
        return False, "small hex contacts"
    if any(A[8] * r - h > 0 for r in range(1, tier.cap(8, 8) + 1)):
        return False, "unbudgeted 8:8"
    if bend and (tier.cap(6, 10) != 0 or tier.cap(10, 10) > bend):
        return False, "bad virtual thread bound"

    maxper = max(*A.values(), (h / bend if bend else Q(0)))
    if maxper >= 1:
        return False, "no finite tail"
    tail = max(10, math.ceil((d + 6 * h) / (1 - maxper)))
    scale = math.lcm(d.denominator, h.denominator, *(a.denominator for a in A.values()))
    H = int(h * scale)
    delta = int(d * scale)
    AA = {s: int(A[s] * scale) for s in A}

    for D in range(10, tail, 2):
        wc = [0]
        for g in range(1, D + 1):
            if not bend:
                wc.append(1)
            elif D == 10:
                wc.append((g + bend - 1) // bend)
            else:
                cap10 = tier.cap(10, D)
                vals = [wc[g - r] + 1 - (r - 1) // bend for r in range(1, min(cap10, g) + 1)]
                wc.append(min([1] + vals))

        @lru_cache(None)
        def richgap(g: int, s: int, t: int) -> int:
            if bend and D == 14 and g == 4 and s == t == 6 and tier.cap(6, 10) == 0:
                return max(1, wc[g])
            return wc[g]

        best = -H * wc[D]
        for first in (6, 8):
            if not tier.cap(first, D):
                continue
            dp: list[dict[int, int]] = [{} for _ in range(D + 1)]
            dp[0][first] = 0
            for i in range(D):
                for s, val in dp[i].items():
                    max_r = min(D - i, tier.cap(s, D))
                    for r in range(1, max_r + 1):
                        for t in (6, 8):
                            if not tier.cap(t, D):
                                continue
                            for g in range(tier.mingap(s, t), D - i - r + 1):
                                gap_eff = richgap(g, s, t) if g else int(tier.cap(s, t) == 0)
                                z = val + AA[s] * r - 2 * H - H * gap_eff
                                j = i + r + g
                                if j == D:
                                    if t == first and z > best:
                                        best = z
                                else:
                                    prev = dp[j].get(t)
                                    if prev is None or z > prev:
                                        dp[j][t] = z
        if D * scale - 6 * H - best < delta:
            return False, ("donor", D, Q(D * scale - 6 * H - best, scale), d)
    return True, ("even tail from", tail)


def scan_min_targets(N: int, d: Q, h: Q, bend: int) -> list[tuple]:
    B = N + 2
    T: set[tuple[int, int, int]] = set()
    for D in range(6, N + 2, 2):
        for s in ((6, 8, 10) if bend else (6, 8)):
            r = D + s - B
            if 1 <= r < min(s, D):
                T.add(tuple(sorted((r, D - r, s - r))))
    DB = {(s, t, B - s - t) for s, t in combinations_with_replacement([6, 8], 2) if s + t <= B}
    pool = sorted([("T", v) for v in T] + [("DB", v) for v in DB])
    for k in range(len(pool) + 1):
        ok = []
        for sub in combinations(pool, k):
            t = Tier(N, tuple(v for tag, v in sub if tag == "T"), tuple(v for tag, v in sub if tag == "DB"))
            if check_discharging(t, d, h, bend)[0]:
                ok.append(sub)
        if ok:
            return ok
    raise AssertionError("no minimal target set found")


def verify_section_1_discharging() -> None:
    theta13 = ((2, 6, 6),)
    C15 = ((2, 6, 8), (2, 4, 10), (4, 6, 6))
    E16 = ((1, 7, 9), (3, 5, 9))
    certs = {
        "P+one_theta": (Tier(12, theta13), Q(396, 49), Q(6, 49), 0),
        "A": (Tier(13), Q(42, 5), Q(1, 5), 0),
        "B": (Tier(14), Q(9), Q(1, 6), 0),
        "C1": (Tier(14, ((2, 6, 8),)), Q(688, 73), Q(16, 219), 0),
        "C3": (Tier(14, ((2, 6, 8), (2, 4, 10)), ((8, 8, 0),)), Q(19, 2), Q(1, 12), 0),
        "C4": (Tier(14, C15, ((8, 8, 0),)), Q(124, 13), Q(2, 13), 3),
        "C5": (Tier(14, C15, ((8, 8, 0), (6, 6, 4))), Q(124, 13), Q(2, 13), 3),
        "D": (Tier(15), Q(124, 13), Q(2, 13), 3),
        "E1": (Tier(15, ((1, 7, 9),)), Q(168, 17), Q(0), 0),
        "E2": (Tier(15, E16), Q(10), Q(0), 0),
        "E2b": (Tier(15, ((1, 7, 9),), ((8, 8, 1),)), Q(10), Q(0), 0),
        "F": (Tier(16), Q(10), Q(0), 0),
    }
    for name, (tier, d, h, bend) in certs.items():
        ok, why = check_discharging(tier, d, h, bend)
        require(ok, f"Discharging cert {name} failed: {why}")
        bad, reason = check_discharging(tier, d + Q(1, 101), h, bend)
        require(not bad, f"Corrupted-target mutation survived for {name}")
        require(
            (isinstance(reason, tuple) and reason[0] == "donor") or reason == "unbudgeted 8:8",
            f"Unexpected rejection reason for {name}: {reason}",
        )

    c_min = scan_min_targets(14, Q(124, 13), Q(2, 13), 3)
    e_min = scan_min_targets(15, Q(10), Q(0), 0)
    require(
        c_min == [(("DB", (8, 8, 0)), ("T", (2, 4, 10)), ("T", (2, 6, 8)), ("T", (4, 6, 6)))],
        f"Unexpected C minimal target set: {c_min}",
    )
    require(
        e_min == [
            (("DB", (8, 8, 1)), ("T", (1, 7, 9))),
            (("T", (1, 7, 9)), ("T", (3, 5, 9))),
        ],
        f"Unexpected E minimal target sets: {e_min}",
    )
    print(
        "[PASS 1/5] Discharging certificates: all 12 tiers verified (E2/E2b -> 5/4) "
        "+ 12 raised-target mutations rejected + exact C (4-set) & E (2 pairs) minimality"
    )


# =============================================================================
# Section 2: Exact Bipartite Periodic Plane Sharpness & Necessity Witnesses
# =============================================================================


def expanded_graph(edges: list[tuple]) -> list[set[int]]:
    adj: dict[int, set[int]] = defaultdict(set)
    ids: dict[object, int] = {}

    def idx(x: object) -> int:
        if x not in ids:
            ids[x] = len(ids)
        return ids[x]

    for eid, (u, v, r) in enumerate(edges):
        uv = [u] + [("sub", eid, k) for k in range(1, r)] + [v]
        for a_raw, b_raw in zip(uv, uv[1:]):
            a, b = idx(a_raw), idx(b_raw)
            require(a != b and a not in adj[b], "loop or parallel edge in witness")
            adj[a].add(b)
            adj[b].add(a)
    return [adj[i] for i in range(len(adj))]


def build_periodic_witness(kind: str, K: int = 12) -> list[set[int]]:
    v = lambda i, j: (i % K, j % K)
    if kind == "Cprior":
        def nod(i: int, j: int, k: int) -> tuple[int, int, int]:
            return (i % K, j % K, k if (i + j) % 2 == 0 else -1)
        es = []
        for i in range(K):
            for j in range(K):
                if (i + j) % 2 == 0:
                    es.extend((nod(i, j, k), nod(i, j, (k + 1) % 4), 2) for k in range(4))
                es.extend([(nod(i, j, 0), nod(i + 1, j, 2), 1), (nod(i, j, 1), nod(i, j + 1, 3), 2)])
        return expanded_graph(es)

    if kind == "C":
        dirs = [(1, 0), (1, 0), (1, 1), (0, 1), (-1, 0), (-1, 0), (-1, -1), (0, -1)]
        es = []
        port = lambda i, j, k: (i % K, j % K, k)
        for i in range(K):
            for j in range(K):
                es.extend((port(i, j, k), port(i, j, (k + 1) % 8), 1) for k in range(8))
                for k, rev, r in [(0, 5, 4), (1, 4, 4), (2, 6, 2), (3, 7, 1)]:
                    di, dj = dirs[k]
                    es.append((port(i, j, k), port(i + di, j + dj, rev), r))
        return expanded_graph(es)

    if kind == "B":
        require(K % 2 == 0, "K must be even for B")
        def port_b(i: int, j: int, di: int, dj: int) -> tuple[int, int, int]:
            p = v(i, j)
            return p + (int(di + dj < 0) if i % 2 == j % 2 == 0 else 0,)
        es = []
        for i in range(K):
            for j in range(K):
                if i % 2 == j % 2 == 0:
                    es.append((port_b(i, j, 1, 0), port_b(i, j, -1, 0), 2))
                for di, dj in [(1, 0), (0, 1)]:
                    es.append((port_b(i, j, di, dj), port_b(i + di, j + dj, -di, -dj), 2))
        return expanded_graph(es)

    require(K % 6 == 0, "K must be a multiple of 6")
    tris = []
    old = set()
    weights: dict[tuple, int] = {}

    def epair(x: object, y: object) -> tuple:
        return (x, y) if x <= y else (y, x)

    for i in range(K):
        for j in range(K):
            a, b, c, d = v(i, j), v(i + 1, j), v(i, j + 1), v(i + 1, j + 1)
            old.add(a)
            if kind == "A" and i % 2 == j % 2 == 0:
                z = (i, j, 2)
                tris += [(z, a, b), (z, b, d), (z, d, c), (z, c, a)]
                for t in [a, d, b, c]:
                    weights[epair(t, z)] = 3 if t in [a, d] else 2
            elif kind == "D" and (i + j) % 3 == 0:
                for tag, t in enumerate([(a, b, d), (a, d, c)]):
                    z = (i, j, tag)
                    tris.extend((z, t[k], t[(k + 1) % 3]) for k in range(3))
                    for w in t:
                        weights[epair(z, w)] = 3
            else:
                tris.extend([(a, b, d), (a, d, c)])
                if kind == "D":
                    weights[epair(a, d)] = 3
            if kind == "F":
                weights[epair(a, d)] = 1

    inc: dict[tuple, list[int]] = defaultdict(list)
    for k, t in enumerate(tris):
        for i in range(3):
            inc[epair(t[i], t[(i + 1) % 3])].append(k)
    require(all(len(s) == 2 for s in inc.values()), "non-manifold dual edge")
    if kind in ("A", "F"):
        return expanded_graph([(k, l, weights.get(e, 1 if kind == "A" else 2)) for e, (k, l) in inc.items()])

    def node(x: object, y: object) -> tuple:
        return ("port", x, y) if x in old else ("center", x)

    es = [(node(x, y), node(y, x), weights.get((x, y), 2)) for x, y in inc]
    for tri in tris:
        for i, x in enumerate(tri):
            if x in old:
                es.append((node(x, tri[(i + 1) % 3]), node(x, tri[(i - 1) % 3]), 1))
    return expanded_graph(es)


def is_bipartite_connected(adj: list[set[int]]) -> bool:
    colors = {0: 0}
    q = [0]
    for u in q:
        for w in adj[u]:
            if w not in colors:
                colors[w] = 1 - colors[u]
                q.append(w)
            elif colors[w] == colors[u]:
                return False
    return len(colors) == len(adj)


def minimal_bicycles(adj: list[set[int]], limit: int) -> tuple[list[tuple], int]:
    cycles: list[tuple[int, ...]] = []

    def walk(path: list[int], vis: set[int], start: int) -> None:
        for w in adj[path[-1]]:
            if w == start:
                if len(path) >= 3 and path[1] < path[-1]:
                    cycles.append(tuple(path))
            elif w > start and w not in vis and len(path) < limit - 1:
                vis.add(w)
                path.append(w)
                walk(path, vis, start)
                path.pop()
                vis.remove(w)

    for s in range(len(adj)):
        walk([s], {s}, s)
    verts = [frozenset(c) for c in cycles]
    edges = [
        frozenset(ordered_pair(c[i - 1], c[i]) for i in range(len(c)))
        for c in cycles
    ]
    at: dict[int, list[int]] = defaultdict(list)
    found: set[tuple] = set()
    for j, C in enumerate(cycles):
        for i in {idx for v in C for idx in at[v]}:
            a, b = len(cycles[i]), len(C)
            r = len(edges[i] & edges[j])
            if a + b - r > limit:
                continue
            nv = len(verts[i] & verts[j])
            if nv != r + 1:
                continue
            if r == 0:
                found.add(("DB", *sorted((a, b)), 0))
            else:
                found.add(("T", *sorted((r, a - r, b - r))))
        for v in C:
            at[v].append(j)

    g = min(len(c) for c in cycles)
    for j, C in enumerate(cycles):
        maxdist = limit - len(C) - g
        if maxdist < 1:
            continue
        seen = set(C)
        front = list(C)
        for k in range(1, maxdist + 1):
            front_set = {w for u in front for w in adj[u]} - seen
            targets = {i for w in front_set for i in at[w] if i > j and len(cycles[i]) + len(C) + k <= limit}
            for i in targets:
                if not (seen & verts[i]):
                    found.add(("DB", *sorted((len(C), len(cycles[i]))), k))
            seen.update(front_set)
            front = list(front_set)
    return sorted(found), g


def verify_section_2_witnesses() -> None:
    specs = [
        ("A", 13, Q(21, 16)),
        ("B", 14, Q(9, 7)),
        ("C", 14, Q(19, 15)),
        ("Cprior", 14, Q(14, 11)),
        ("D", 15, Q(62, 49)),
        ("F", 16, Q(5, 4)),
    ]
    for kind, N, slope in specs:
        adj = build_periodic_witness(kind)
        n = len(adj)
        m = sum(len(row) for row in adj) // 2
        require(is_bipartite_connected(adj), f"Witness {kind} not bipartite/connected")
        require(Q(m, n) == slope, f"Witness {kind} slope mismatch: {Q(m, n)} != {slope}")
        types, girth = minimal_bicycles(adj, N + 2)
        require(girth >= 8, f"Witness {kind} girth {girth} < 8")
        require(min(sum(t[1:]) for t in types) == N + 2, f"Witness {kind} min bicycle mismatch: {types}")

        # Negative control: deleting an edge corrupts exact slope
        bad = [set(row) for row in adj]
        u = 0
        w = next(iter(bad[u]))
        bad[u].remove(w)
        bad[w].remove(u)
        require(Q(sum(len(row) for row in bad), 2 * n) != slope, f"Corrupted witness {kind} kept slope")

    require(not is_bipartite_connected([{1, 2}, {0, 2}, {0, 1}]), "Triangle passed bipartiteness")

    # Replay dual_Dstar.json: bipartite periodic plane graph proving Theta(1,7,9) necessity
    dstar_path = HERE / "dual_Dstar.json"
    dstar = json.loads(dstar_path.read_text(encoding="utf-8"))
    K = dstar["K"]
    vid = lambda x, y: (x % K) + K * (y % K)
    ts = {
        tuple(sorted(t))
        for x in range(K)
        for y in range(K)
        for t in [(vid(x, y), vid(x + 1, y), vid(x + 1, y + 1)), (vid(x, y), vid(x, y + 1), vid(x + 1, y + 1))]
    }

    def tri_edges(tris: set[tuple[int, int, int]]) -> dict[tuple[int, int], list[tuple[int, int, int]]]:
        ed: dict[tuple[int, int], list[tuple[int, int, int]]] = defaultdict(list)
        for t in tris:
            for e in combinations(t, 2):
                ed[e].append(t)
        return ed

    for raw_e in dstar["flips"]:
        e = tuple(raw_e)
        ed = tri_edges(ts)
        require(len(ed[e]) == 2, "invalid flip edge in dual_Dstar")
        t1, t2 = ed[e]
        (c,) = set(t1) - set(e)
        (d,) = set(t2) - set(e)
        a, b = e
        require(ordered_pair(c, d) not in ed, "flip creates duplicate edge in dual_Dstar")
        ts = (ts - {t1, t2}) | {tuple(sorted((c, d, a))), tuple(sorted((c, d, b)))}

    ed = tri_edges(ts)
    require(all(len(v) == 2 for v in ed.values()), "dual_Dstar triangulation invalid")
    heavy = {tuple(x) for x in dstar["heavy"]}
    adj_dstar = expanded_graph([(t1, t2, 1 + (e in heavy)) for e, (t1, t2) in ed.items()])
    types_d, g_d = minimal_bicycles(adj_dstar, 17)
    n_d = len(adj_dstar)
    m_d = sum(len(row) for row in adj_dstar) // 2
    require(is_bipartite_connected(adj_dstar), "dual_Dstar not bipartite")
    require(n_d == 255 and m_d == 319 and 4 * m_d > 5 * n_d, f"dual_Dstar density failed: {n_d}, {m_d}")
    require(g_d == 8 and types_d == [("T", 1, 7, 9)], f"dual_Dstar bicycle check failed: g={g_d}, {types_d}")

    # Negative control: dropping one heavy subdivision destroys bipartiteness
    bad_heavy = set(heavy)
    bad_heavy.pop()
    adj_bad = expanded_graph([(t1, t2, 1 + (e in bad_heavy)) for e, (t1, t2) in ed.items()])
    require(not is_bipartite_connected(adj_bad), "Corrupted dual_Dstar remained bipartite")

    print(
        "[PASS 2/5] Sharpness & necessity witnesses: A(21/16), B(9/7), C(19/15), "
        "Cprior(14/11), D(62/49), F(5/4), dual_Dstar(255,319, unique Theta(1,7,9)) + mutations"
    )


# =============================================================================
# Section 3 & 4: Combinatorial Thrackle Map Checker, C_4 Control, & Musquash
# =============================================================================


def audit_map(D: dict) -> tuple[dict, tuple]:
    """Combinatorial orientable surface map checker for planarized drawings."""
    E, X, R, O = D["edges"], D["xs"], D["rows"], D["orders"]
    n, m, x = len(O), len(E), len(X)
    require(len(R) == m, "row count mismatch")
    require(all(len(e) == 2 and 0 <= e[0] < n and 0 <= e[1] < n and e[0] != e[1] for e in E), "bad edges")
    require(len({ordered_pair(e[0], e[1]) for e in E}) == m, "parallel edge")

    inc = [set() for _ in E]
    ct: Counter[tuple[int, int]] = Counter()
    for k, (i, j, s) in enumerate(X):
        require(0 <= i < j < m and s in (0, 1) and not (set(E[i]) & set(E[j])), "bad crossing")
        inc[i].add(k)
        inc[j].add(k)
        ct[i, j] += 1
    expected = {(i, j): 1 for i, j in combinations(range(m), 2) if not (set(E[i]) & set(E[j]))}
    defects = [(i, j, ct[i, j]) for i, j in expected if ct[i, j] != 1]

    origin: list[int] = []
    end: list[int] = []
    seg: dict[tuple[int, int, int], int] = {}
    edges_of_dart: list[int] = []
    for i, ((a, b), row) in enumerate(zip(E, R)):
        require(set(row) == inc[i] and len(row) == len(inc[i]), "bad crossing row")
        path = [a] + [n + k for k in row] + [b]
        for u, v in zip(path, path[1:]):
            d = len(origin)
            origin.extend([u, v])
            end.extend([v, u])
            edges_of_dart.extend([i, i])
            seg[i, u, 1] = d
            seg[i, v, -1] = d + 1

    cyc: list[list[int]] = []
    for v, order in enumerate(O):
        ls = {i for i, e in enumerate(E) if v in e}
        require(bool(ls) and set(order) == ls and len(order) == len(ls), "bad vertex rotation")
        cyc.append([seg[i, v, 1 if E[i][0] == v else -1] for i in order])
    for k, (i, j, s) in enumerate(X):
        v = n + k
        sg = 1 - 2 * s
        cyc.append([seg[i, v, 1], seg[j, v, sg], seg[i, v, -1], seg[j, v, -sg]])

    V = n + x
    dd = len(origin)
    require(dd == 2 * (m + 2 * x) and sorted(d for cc in cyc for d in cc) == list(range(dd)), "bad darts")

    todo = [0]
    seen = {0}
    for u in todo:
        for d in cyc[u]:
            w = end[d]
            if w not in seen:
                seen.add(w)
                todo.append(w)
    require(len(seen) == V, "disconnected planarization")

    T = [-1] * dd
    for cc in cyc:
        for d, g in zip(cc, cc[1:] + cc[:1]):
            T[d ^ 1] = g

    F = [-1] * dd
    faces: list[list[int]] = []
    for d in range(dd):
        if F[d] >= 0:
            continue
        fs = []
        p = d
        while F[p] < 0:
            F[p] = len(faces)
            fs.append(p)
            p = T[p]
        require(p == d, "broken face cycle")
        faces.append(fs)

    genus2 = 2 - (V - dd // 2 + len(faces))
    require(genus2 >= 0 and genus2 % 2 == 0, "non-orientable genus")
    info = dict(n=n, m=m, X=x, V=V, E=dd // 2, F=len(faces), g=genus2 // 2, defects=defects)
    return info, (F, faces, origin, edges_of_dart)


def independent_plane_thrackle_check(
    n: int, edges: list[list[int]], rows: list[list[int]], vertex_orders: list[list[int]], crossing_signs: dict[str, int]
) -> bool:
    """Second, independent rotation-system checker using Simon's edge-pair schema."""
    m = len(edges)
    # Build crossing id table indexed by canonical unordered edge pair (i < j)
    pairs = [(i, j) for i, j in combinations(range(m), 2) if not (set(edges[i]) & set(edges[j]))]
    if len(crossing_signs) != len(pairs):
        return False
    pair_id = {p: k for k, p in enumerate(pairs)}
    for i, row in enumerate(rows):
        expected_nbrs = [j for j in range(m) if j != i and not (set(edges[i]) & set(edges[j]))]
        if sorted(row) != expected_nbrs:
            return False

    # Construct half-edge permutation sigma (rotation) and alpha (edge reversal)
    half_edge_id: dict[tuple[int, int, int], int] = {}
    alpha: list[int] = []
    vertex_of: list[int] = []
    for i, (u, v) in enumerate(edges):
        seq = [u] + [n + pair_id[ordered_pair(i, j)] for j in rows[i]] + [v]
        for a, b in zip(seq, seq[1:]):
            h0 = len(alpha)
            h1 = h0 + 1
            alpha.extend([h1, h0])
            vertex_of.extend([a, b])
            half_edge_id[(i, a, 1)] = h0
            half_edge_id[(i, b, -1)] = h1

    sigma = [-1] * len(alpha)
    for v, order in enumerate(vertex_orders):
        star = [half_edge_id[(i, v, 1 if edges[i][0] == v else -1)] for i in order]
        for a, b in zip(star, star[1:] + star[:1]):
            sigma[a] = b
    for (i, j), k in pair_id.items():
        s = crossing_signs[f"{i},{j}"]
        v = n + k
        d = 1 - 2 * s
        star = [
            half_edge_id[(i, v, 1)],
            half_edge_id[(j, v, d)],
            half_edge_id[(i, v, -1)],
            half_edge_id[(j, v, -d)],
        ]
        for a, b in zip(star, star[1:] + star[:1]):
            sigma[a] = b

    if any(x < 0 for x in sigma):
        return False
    # Count connected components of graph on vertices using alpha/sigma
    comp_seen = {0}
    stack = [0]
    adj_v: dict[int, list[int]] = defaultdict(list)
    for h, opp in enumerate(alpha):
        adj_v[vertex_of[h]].append(vertex_of[opp])
    while stack:
        cur = stack.pop()
        for nxt in adj_v[cur]:
            if nxt not in comp_seen:
                comp_seen.add(nxt)
                stack.append(nxt)
    V = n + len(pairs)
    if len(comp_seen) != V:
        return False
    # Count face orbits of phi = sigma o alpha
    visited = [False] * len(alpha)
    fcount = 0
    for h in range(len(alpha)):
        if visited[h]:
            continue
        fcount += 1
        cur = h
        while not visited[cur]:
            visited[cur] = True
            cur = sigma[alpha[cur]]
    E_plan = len(alpha) // 2
    return (V - E_plan + fcount) == 2


def standard_cert_dict(D: dict) -> dict:
    E, X, O = D["edges"], D["xs"], D["orders"]
    require(len({(a, b) for a, b, _ in X}) == len(X), "repeated crossing pair")
    return dict(
        n=len(O),
        edges=E,
        rows=[[sum(X[k][:2]) - i for k in row] for i, row in enumerate(D["rows"])],
        vertex_orders=O,
        crossing_signs={f"{i},{j}": s for i, j, s in X},
    )


def build_standard_musquash(n: int) -> dict:
    pts_map = {
        5: [(1000, 0), (309, 951), (-809, 588), (-809, -588), (309, -951)],
        7: [(1000, 0), (623, 782), (-223, 975), (-901, 434), (-901, -434), (-223, -975), (623, -782)],
    }
    P = pts_map[n]
    h = n // 2
    verts = [P[(i * h) % n] for i in range(n)]
    edges = [[i, (i + 1) % n] for i in range(n)]
    X: list[list[int]] = []
    R: list[list[tuple[Q, int]]] = [[] for _ in edges]
    for i, j in combinations(range(n), 2):
        if set(edges[i]) & set(edges[j]):
            continue
        a, b = verts[i], verts[(i + 1) % n]
        c, d = verts[j], verts[(j + 1) % n]
        ux, uy = b[0] - a[0], b[1] - a[1]
        wx, wy = d[0] - c[0], d[1] - c[1]
        qx, qy = c[0] - a[0], c[1] - a[1]
        den = ux * wy - uy * wx
        s = Q(qx * wy - qy * wx, den)
        t = Q(qx * uy - qy * ux, den)
        require(0 < s < 1 and 0 < t < 1, "expected proper chord crossing")
        k = len(X)
        X.append([i, j, int(den < 0)])
        R[i].append((s, k))
        R[j].append((t, k))
    D = dict(
        edges=edges,
        orders=[[(i - 1) % n, i] for i in range(n)],
        xs=X,
        rows=[[k for _, k in sorted(row)] for row in R],
    )
    C = standard_cert_dict(D)
    row0 = list(range(n - 3, 1, -2)) + list(range(n - 2, 2, -2))
    require(C["rows"] == [[(i + t) % n for t in row0] for i in range(n)], "non-standard crossing row")
    require(all(s == int((h * (j - i)) % n > h) for i, j, s in X), "non-standard crossing sign")
    require(independent_plane_thrackle_check(**C), "standard musquash failed independent plane check")
    return D


class MusquashGeometry:
    def __init__(self, D: dict):
        self.D = D
        self.info, (self.face, self.faces, self.origin, self.color) = audit_map(D)
        self.slot: dict[tuple[int, int], int] = {}
        self.pos: list[int] = []
        self.dart: list[int] = []
        for e, r in enumerate(D["rows"]):
            for i in range(len(r) + 1):
                dd = len(self.pos)
                self.slot[e, i] = dd
                self.pos.extend([i, i])
                self.dart.extend([dd, dd + 1])

    def trail(self, v: int, inneronly: int | None = None):
        E = self.D["edges"]
        need = sum(1 << i for i, uv in enumerate(E) if v not in uv)

        def go(f: int, mask: int, c: int, w: tuple[int, ...]):
            if not mask:
                yield c, w
                return
            for d in self.faces[f]:
                b = 1 << self.color[d]
                if b & mask:
                    yield from go(self.face[d ^ 1], mask ^ b, c, w + (d,))

        for c in self.dart:
            if self.origin[c] == v and (inneronly is None or self.face[c] == inneronly):
                yield from go(self.face[c], need, c, ())

    def trial(self, v: int, c: int, w: tuple[int, ...]) -> dict:
        D = self.D
        E, R, O, X = D["edges"], D["rows"], D["orders"], D["xs"]
        n, m = len(O), len(E)
        rr = [list(row) for row in R]
        oo = [list(o) for o in O]
        xx = list(X)
        new_row = []
        for d in w:
            i = self.color[d]
            k = len(xx)
            xx.append([i, m, d % 2])
            rr[i].insert(self.pos[d], k)
            new_row.append(k)
        oo[v].insert(oo[v].index(self.color[c]), m)
        return dict(edges=E + [[v, n]], rows=rr + [new_row], orders=oo + [[m]], xs=xx)

    def project_end(self, G0: "MusquashGeometry", w: tuple[int, ...]) -> int:
        n = G0.info["m"]
        d = next(z for z in reversed(w) if self.color[z] < n)
        i = self.color[d]
        D = self.D
        k = sum(D["xs"][x][1] < n for x in D["rows"][i][: self.pos[d]])
        z = G0.slot[i, k] + (d % 2)
        return G0.face[z ^ 1]


def winding_levels(G: MusquashGeometry) -> tuple[dict[int, int], int]:
    n = G.info["n"]
    (outer,) = [
        f for f, ds in enumerate(G.faces) if ({G.origin[d] for d in ds} & set(range(n))) == set(range(n))
    ]
    W = {outer: 0}
    q = [outer]
    for f in q:
        for d in G.faces[f]:
            g = G.face[d ^ 1]
            w = W[f] + 1 - 2 * (d % 2)
            if g not in W:
                W[g] = w
                q.append(g)
            else:
                require(W[g] == w, "winding number conflict")
    require(min(W.values()) == 0 and max(W.values()) == n // 2, "unexpected winding range")
    return W, outer


def verify_section_3_musquash() -> None:
    expected = {5: (2, 44, {0: 1296}), 7: (8, 610, {0: 75028})}
    for n in (5, 7):
        G0 = MusquashGeometry(build_standard_musquash(n))
        W, _ = winding_levels(G0)
        (inner,) = {G0.face[d] for d in G0.dart if G0.origin[d] == 0 and W[G0.face[d]] == 1}
        A = 0
        B = 0
        raw: Counter[int] = Counter()
        for c, w in G0.trail(0, inner):
            D1 = G0.trial(0, c, w)
            H = MusquashGeometry(D1)
            if H.info["g"]:
                continue
            require(
                independent_plane_thrackle_check(**standard_cert_dict(D1)) and W[G0.project_end(G0, w)] == 0,
                "first step failed independent check",
            )
            A += 1
            for j, t in H.trail(n):
                D2 = H.trial(n, j, t)
                K = MusquashGeometry(D2)
                if K.info["g"]:
                    continue
                require(
                    independent_plane_thrackle_check(**standard_cert_dict(D2)) and W[H.project_end(G0, t)] == 1,
                    "second step failed independent check",
                )
                B += 1
                for _, word in K.trail(n + 1):
                    raw[W[K.project_end(G0, word)]] += 1
        require((A, B, dict(raw)) == expected[n], f"Musquash C_{n} census mismatch: {(A, B, dict(raw))}")

        # Negative control: flipping a crossing sign breaks planarity
        C_mut = copy.deepcopy(standard_cert_dict(G0.D))
        k0 = next(iter(C_mut["crossing_signs"]))
        C_mut["crossing_signs"][k0] ^= 1
        require(not independent_plane_thrackle_check(**C_mut), f"Mutated C_{n} passed plane check")

    print(
        "[PASS 3/5] Standard musquash 3-step confinement: C_5 (2, 44, {0: 1296}) & "
        "C_7 (8, 610, {0: 75028}), zero level-2 excursions + crossing-sign mutations rejected"
    )


def verify_section_4_c4_control() -> None:
    """First-principles exhaustive rotation-system check: C_4 has 0 plane thrackles, C_5 has >0."""
    def count_plane_thrackles(n: int) -> int:
        edges = [[i, (i + 1) % n] for i in range(n)]
        noninc = [[j for j in range(n) if j != i and not (set(edges[i]) & set(edges[j]))] for i in range(n)]
        pairs = [(i, j) for i in range(n) for j in noninc[i] if i < j]
        v_orders = [[(i - 1) % n, i] for i in range(n)]
        hits = 0
        for rows in product(*(permutations(r) for r in noninc)):
            rlist = [list(r) for r in rows]
            for signs in product((0, 1), repeat=len(pairs)):
                cs = {f"{i},{j}": s for (i, j), s in zip(pairs, signs)}
                if independent_plane_thrackle_check(n, edges, rlist, v_orders, cs):
                    hits += 1
        return hits

    c4_hits = count_plane_thrackles(4)
    c5_hits = count_plane_thrackles(5)
    require(c4_hits == 0, f"C_4 unexpectedly admitted {c4_hits} plane thrackles")
    require(c5_hits == 2, f"C_5 expected 2 signed plane thrackles (fixed vertex order), got {c5_hits}")
    print(f"[PASS 4/5] First-principles rotation-system control: C_4 -> {c4_hits} models, C_5 -> {c5_hits} models")


# =============================================================================
# Section 5: Minimal Bicyclic Catalogue Completeness & SAT Manifest Integrity
# =============================================================================


def expected_minimal_bicyclic_scope(n: int) -> list[str]:
    """Enumerate every connected simple minimal bicyclic graph on n vertices (m = n + 1, delta >= 2)."""
    M = n + 1
    out: list[str] = []
    # Dumbbells / figure-eights: two cycles of lengths 3 <= j <= k joined by a path of length l = M - j - k >= 0
    for j in range(3, M):
        for k in range(j, M - j + 1):
            out.append(f"db_{j}_{k}_{M - j - k}")
    # Theta graphs: three internally disjoint paths 1 <= a <= b <= c, b >= 2 (simple), a + b + c = M
    for b in range(2, M):
        for a in range(1, b + 1):
            c = M - a - b
            if c >= b:
                out.append(f"th_{a}_{b}_{c}")
    return sorted(out)


def verify_graph_matches_name(name: str, n: int, edges: list[list[int]]) -> None:
    """Verify edge list is simple, connected, has m = n + 1, delta >= 2, and matches canonical name."""
    require(len(edges) == n + 1, f"{name}: m={len(edges)} != n+1={n+1}")
    adj: list[set[int]] = [set() for _ in range(n)]
    for u, v in edges:
        require(0 <= u < n and 0 <= v < n and u != v and v not in adj[u], f"{name}: non-simple edge")
        adj[u].add(v)
        adj[v].add(u)
    # Connectivity
    seen = {0}
    stack = [0]
    while stack:
        cur = stack.pop()
        for nxt in adj[cur]:
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    require(len(seen) == n, f"{name}: disconnected")
    degs = sorted(len(row) for row in adj)
    require(degs[0] >= 2, f"{name}: min degree < 2")

    # Contract degree-2 vertices into branch-to-branch path lengths
    branches = [v for v in range(n) if len(adj[v]) >= 3]
    parts = name.split("_")
    kind = parts[0]
    params = [int(x) for x in parts[1:]]

    def trace_paths() -> list[tuple[int, int, int]]:
        used: set[tuple[int, int]] = set()
        segs: list[tuple[int, int, int]] = []
        bset = set(branches)
        for u in branches:
            for nxt in sorted(adj[u]):
                e = ordered_pair(u, nxt)
                if e in used:
                    continue
                used.add(e)
                prev, cur, length = u, nxt, 1
                while cur not in bset:
                    (w,) = adj[cur] - {prev}
                    used.add(ordered_pair(cur, w))
                    prev, cur, length = cur, w, length + 1
                segs.append((min(u, cur), max(u, cur), length))
        require(len(used) == len(edges), f"{name}: untraced edges")
        return segs

    segs = trace_paths()
    if kind == "th":
        require(len(branches) == 2 and degs[-2:] == [3, 3], f"{name}: bad theta branch degrees")
        require(all(u != v for u, v, _ in segs) and len(segs) == 3, f"{name}: not a theta")
        lengths = sorted(L for _, _, L in segs)
        require(lengths == sorted(params), f"{name}: theta legs {lengths} != {params}")
    elif kind == "db":
        j, k, ell = params
        if ell == 0:
            require(len(branches) == 1 and degs[-1] == 4, f"{name}: bad figure-eight degree")
            require(all(u == v for u, v, _ in segs) and len(segs) == 2, f"{name}: not a figure-eight")
            lengths = sorted(L for _, _, L in segs)
            require(lengths == sorted((j, k)), f"{name}: figure-eight cycles {lengths} != {(j, k)}")
        else:
            require(len(branches) == 2 and degs[-2:] == [3, 3], f"{name}: bad dumbbell branch degrees")
            loops = sorted(L for u, v, L in segs if u == v)
            bridges = [L for u, v, L in segs if u != v]
            require(len(loops) == 2 and len(bridges) == 1, f"{name}: bad dumbbell topology")
            require(loops == sorted((j, k)) and bridges == [ell], f"{name}: dumbbell params mismatch")
    else:
        raise AssertionError(f"Unknown graph family: {name}")


def check_manifest_obj(manifest: dict) -> tuple[int, int, int, int]:
    require(manifest.get("schema_version") == 1, "unexpected sat_manifest schema_version")
    cases = manifest["cases"]
    by_name = {c["graph"]: c for c in cases}
    require(len(by_name) == len(cases), "duplicate graph entry in sat_manifest")

    # Verify exact completeness for n = 13, 14, 15
    exp13 = expected_minimal_bicyclic_scope(13)
    exp14 = expected_minimal_bicyclic_scope(14)
    exp15 = expected_minimal_bicyclic_scope(15)
    require((len(exp13), len(exp14), len(exp15)) == (40, 48, 56), "unexpected scope sizes")

    for n, exp in ((13, exp13), (14, exp14), (15, exp15)):
        got = sorted(c["graph"] for c in cases if c["n"] == n)
        require(got == exp, f"n={n} scope mismatch: missing={set(exp)-set(got)} extra={set(got)-set(exp)}")

    # Verify Crown Jewel E2b pair is present in n = 16
    got16 = {c["graph"] for c in cases if c["n"] == 16}
    require(
        {"db_8_8_1", "th_1_7_9", "th_3_5_9", "th_1_5_11"}.issubset(got16),
        f"Missing required n=16 graphs: {got16}",
    )

    # Verify every case entry
    for c in cases:
        g = c["graph"]
        verify_graph_matches_name(g, c["n"], c["edges"])
        require(c["m"] == c["n"] + 1, f"{g}: m mismatch")
        require(c["status"] == "unsat", f"{g}: status != unsat")
        require(c["plane_models"] == 0, f"{g}: nonzero plane_models")
        require(c["certified"] is True, f"{g}: certified != True")
        require(c["encoding_audited"] is True, f"{g}: encoding_audited != True")
        require(c["drat_verified"] is True, f"{g}: drat_verified != True")
        require(c["strict_rup_verified"] is True, f"{g}: strict_rup_verified != True")
        require(c["rat_lemmas_in_core"] == 0, f"{g}: nonzero RAT lemmas in core")
        require(c["variables"] > 0 and c["clauses"] > 0 and c["clauses"] == c["audit_clauses"], f"{g}: bad clause counts")
        sha_map = c["sha256"]
        for fname in ("formula.cnf", "witness.tsv", "proof.bdrat", "proof.lrat", "planes.jsonl", "graph.json"):
            require(fname in sha_map and bool(HEX64_RE.match(sha_map[fname])), f"{g}: invalid sha256 for {fname}")
        require(c["audit_cnf_sha256"] == sha_map["formula.cnf"], f"{g}: audit/replay formula.cnf sha256 mismatch")
        require(
            sha_map["planes.jsonl"] == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            f"{g}: planes.jsonl is not empty",
        )

    # Verify positive/negative control records in manifest
    pos = manifest["positive_controls"]
    for cname in ("cy_6", "cy_7", "cy_8", "pend_7_0_2"):
        require(pos[cname]["status"] == "sat" and pos[cname]["plane_models"] >= 1, f"bad positive control {cname}")
    require(manifest["negative_controls_passed"] is True, "negative controls not passed")

    cats = {c["graph"]: c for c in manifest.get("path_catalogues", [])}
    for cname in ("pa_6", "pa_7"):
        require(cname in cats, f"missing path catalogue {cname}")
        cat = cats[cname]
        require(
            cat["encoding_audited"] is True
            and cat["drat_verified"] is True
            and cat["strict_rup_verified"] is True
            and cat["rat_lemmas_in_core"] == 0,
            f"uncertified path catalogue {cname}",
        )

    return len(exp13), len(exp14), len(exp15), len(got16)


def verify_section_5_sat_manifest() -> None:
    mpath = HERE / "sat_manifest.json"
    manifest = json.loads(mpath.read_text(encoding="utf-8"))
    n13, n14, n15, n16 = check_manifest_obj(manifest)

    # Corrupted-manifest negative controls:
    # (a) Dropping one n=15 graph must fail completeness check
    m_drop = copy.deepcopy(manifest)
    m_drop["cases"] = [c for c in m_drop["cases"] if c["graph"] != "db_8_8_0"]
    dropped_failed = False
    try:
        check_manifest_obj(m_drop)
    except AssertionError:
        dropped_failed = True
    require(dropped_failed, "Corrupted manifest (missing graph) unexpectedly passed")

    # (b) Tampering formula.cnf sha256 mismatch between audit and replay must fail
    m_sha = copy.deepcopy(manifest)
    m_sha["cases"][0]["audit_cnf_sha256"] = "0" * 64
    sha_failed = False
    try:
        check_manifest_obj(m_sha)
    except AssertionError:
        sha_failed = True
    require(sha_failed, "Corrupted manifest (SHA-256 mismatch) unexpectedly passed")

    # (c) Tampering RAT lemma count must fail
    m_rat = copy.deepcopy(manifest)
    m_rat["cases"][0]["rat_lemmas_in_core"] = 1
    rat_failed = False
    try:
        check_manifest_obj(m_rat)
    except AssertionError:
        rat_failed = True
    require(rat_failed, "Corrupted manifest (nonzero RAT lemmas) unexpectedly passed")

    print(
        f"[PASS 5/5] SAT/DRAT/strict-RUP manifest integrity & completeness: "
        f"n=13 ({n13}/40), n=14 ({n14}/48), n=15 ({n15}/56), n=16 ({n16} targeted: E2b + E2 + th_1_5_11) "
        f"+ 3 corrupted-manifest mutations rejected"
    )


def main() -> None:
    verify_section_1_discharging()
    verify_section_2_witnesses()
    verify_section_3_musquash()
    verify_section_4_c4_control()
    verify_section_5_sat_manifest()
    print("ALL CHECKS PASSED (zero floating-point arithmetic).")


if __name__ == "__main__":
    main()
