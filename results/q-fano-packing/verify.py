#!/usr/bin/env python3
"""Finite lemmas in the proof that every binary hyperplane section has b <= 19.

Standalone. No SAT solving, floating point, external tables, or third-party
packages. Run: python3 verify.py [--all-flags]. A deliberately corrupt
trade is tested on each normal run. Use --mutate to make the check fail.
For definitions, normalization and the non-computational steps see PROOF.md.
"""
from collections import Counter
from itertools import combinations
import argparse


def require(test, message):
    if not test:
        raise ValueError(message)


def points(n):
    return range(1, 1 << n)


def lines(n):
    return tuple((a, b, a ^ b) for a in points(n) for b in points(n)
                 if a < b < a ^ b)


# On F, bit 16 is the radical coordinate. Same function on F/<16>.
def f(a, b):
    return (((((a & 5) << 1) | ((a & 10) >> 1)) & b).bit_count() & 1)


def mask(row):
    return sum(1 << p for p in row)


def pi(L):
    return tuple(sorted(p & 15 for p in L))


def output(S, m, s):
    return (tuple(sorted(S)), m, s)


def flags():
    iso = [L for L in lines(4) if not f(L[0], L[1])]
    spreads = [S for S in combinations(iso, 5)
               if len({p for L in S for p in L}) == 15]
    ff = {output(S, m, s) for S in spreads for m in S for s in m}
    require(len(iso) == 15 and len(spreads) == 6 and len(ff) == 90, "W(2)")
    require(all(len(set(S) & set(T)) == 1 for S, T in combinations(spreads, 2)),
            "disjoint isotropic spreads")
    # Symplectic transvections cover the entire set of flags, by BFS.
    start = min(ff)
    todo = [start]
    reached = {start}
    while todo:
        S, m, s = todo.pop()
        for v in points(4):
            def t(p):
                return p ^ (v if f(p, v) else 0)

            def tl(L):
                return tuple(sorted(t(p) for p in L))

            nxt = output([tl(L) for L in S], tl(m), t(s))
            if nxt not in reached:
                require(nxt in ff, "transvection failed")
                reached.add(nxt)
                todo.append(nxt)
    require(reached == ff, "incomplete flag orbit")
    print("W(2): 15 isotropic lines; 6 spreads; all 90 marked flags in one orbit")
    return sorted(ff)


def blocks_of(S):
    return tuple(frozenset([16, *L, *(p ^ 16 for p in L)]) for L in S)


def pools(S):
    available = [L for L in lines(5) if 16 not in L and pi(L) not in S]
    good = [L for L in available if not f(L[0], L[1])]
    bad = [L for L in available if f(L[0], L[1])]
    require(len(good) == 40 and len(bad) == 80, "trace pool size")
    return good, bad


def check_trade(U, W, good, bad):
    require(len(U) > 0 and len(U) == len(W), "trade size")
    require(len(set(U)) == len(U) and set(U) <= set(good), "U eligibility")
    require(len(set(W)) == len(W) and set(W) <= set(bad), "W eligibility")
    require(Counter(p for L in U for p in L) == Counter(p for L in W for p in L),
            "unbalanced trace trade")


def trades(S):
    """Enumerate all nonempty (U,W) with common support <=11.
    Each point has degree <=2 in U: d pairs of lines through p cover 1+4d
    points. Two masks store the sets of points of degree >=1 and >=2.
    """
    good, bad = pools(S)
    gm = list(map(mask, good))
    bm = list(map(mask, bad))
    hist = Counter()
    visited = 0
    fixture = None

    def search(i, uus, supp, twice):
        nonlocal visited, fixture
        visited += 1
        # |W|=|U|. Each point of one U-line needs a distinct W-line.
        if len(uus) >= 3:
            candidates = [j for j, z in enumerate(bm) if not (z & ~supp)]
            for wws in combinations(candidates, len(uus)):
                used = double = 0
                for j in wws:
                    z = bm[j]
                    if z & double or z & used & ~twice:
                        break
                    double |= used & z
                    used |= z
                else:
                    if used == supp and double == twice:
                        U, W = [good[k] for k in uus], [bad[k] for k in wws]
                        check_trade(U, W, good, bad)
                        nr = (supp.bit_count(), ((supp & 65535) | (supp >> 16)).bit_count(), len(U))
                        hist[nr] += 1
                        if fixture is None:
                            fixture = U, W
        for j in range(i, len(gm)):
            z = gm[j]
            if not (z & twice) and (supp | z).bit_count() <= 11:
                search(j + 1, uus + [j], supp | z, twice | (supp & z))

    search(0, [], 0, 0)
    require(hist == {(10, 10, 4): 240}, "unexpected small trade profile")
    # A nonempty trade has t>=10. At t<=11 it leaves at most one
    # entire radical pair in X (the support occupies ten distinct fibers).
    # A spread shadow uses >=2 non-TI incidences. Each non-TI trace
    # lifts to one block with 4 affine points. Every nonspread has e>=2.
    for (support, fibers, w) in hist:
        doubleX = (support - fibers) + (11 - support)
        lb = 2 * (32 - ((4 * w) // 2))
        ub = 16 * doubleX + 2 * 3 * w
        require(lb > ub, "nonempty-trade shadow inequality")
    # Zero-trade shadow comparison, valid simultaneously up to t=11.
    require(2 * 32 > 8 * (11 // 2), "zero-trade shadow inequality")
    print("beta-flat: nonempty trade histogram (support, fibers, volume):",
          dict(hist), "; visited U subsets including empty:", visited)
    return fixture, good, bad


def trace_completions(inner, Foc):
    # Complete the forced traces using only lines disjoint from Foc.
    j = [sum(p in B for B in inner) for p in range(32)]
    pool = [L for L in lines(5) if not any(set(L) <= B for B in inner)]
    Foc = set(Foc)
    forced = [L for L in pool
              if any(q in Foc and all(not f(q, x) for x in L) for q in L)]
    optional = [L for L in pool if Foc.isdisjoint(L)]
    need = 40 - len(forced)
    if not 0 <= need <= len(optional):
        return
    for c in combinations(optional, need):
        T = forced + list(c)
        a = Counter(p for L in T for p in L)
        if all(a[p] + j[p] == 5 for p in points(5)):
            yield T


def shadow_bounds(S, A, T):
    # Ignore the <=4 affine points per exceptional trace: the other
    # shadows use nonspread TI lines only, hence have e>=2.
    exceptional = [L for L in T if 16 in L or pi(L) in S or f(L[0], L[1])]
    low = 2 * max(0, 32 - 4 * len(exceptional))
    upper = 0
    for p in points(4):
        q = p ^ 16
        if p in A or q in A:
            if q in A:
                p, q = q, p
            # O(p)=G(p) outside F. Each block through its mate q
            # contributes 4 if it also contains p; 0 for an isotropic
            # trace through q not containing p; otherwise at most 2.
            for L in T:
                if q in L:
                    upper += (4 if p in L else 2 if any(f(p, x) for x in L) else 0)
        else:
            Lp, Lq = [L for L in T if p in L], [L for L in T if q in L]
            for L in Lp:
                for M in Lq:
                    if L == M:
                        upper += 4
                    elif set(L).isdisjoint(M):
                        upper += 1
                    # Distinct traces meeting in F cannot have a common
                    # point outside F: this would duplicate a line.
    return len(exceptional), low, upper


def nonbeta(S, m, s):
    rest = [L for L in S if L != m]
    M = frozenset(p for p in points(4) if not f(s, p))
    inner = blocks_of(rest) + (M,)
    require(len(M) == 7 and all(len(B & C) == 1 for B, C in combinations(inner, 2)),
            "t2 normalization")
    elig = [p for p in points(5) if sum(p in B for B in inner) == 1
            and (p not in M or p == s)]
    require(len(elig) == 21, "t2 eligible points")
    hist = Counter()
    for d in elig:
        A = set(elig) - {d}
        count = 0
        for T in trace_completions(inner, A):
            count += 1
            exc, low, up = shadow_bounds(S, A, T)
            require(low > up, "t2 upper fails to contradict lower")
            hist[exc, low, up] += 1
        require(count == 1, "t2 trace completion count")
    require(hist == {(2, 48, 28): 16, (2, 48, 34): 4, (2, 48, 36): 1},
            "t2 shadow histogram")
    return hist


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--all-flags", action="store_true", help="repeat for all 6 spreads / 90 flags")
    ap.add_argument("--mutate", action="store_true", help="feed in a false trade; must exit nonzero")
    args = ap.parse_args()
    ff = flags()
    work = ff if args.all_flags else ff[:1]
    for S in sorted({S for S, m, s in work}):
        (U, W), good, bad = trades(S)
        # Keep the same volume, four distinct eligible W-lines and valid U,
        # but change one W-line: the point degrees are no longer balanced.
        broken = W[1:] + [next(L for L in bad if L not in W)]
        if args.mutate:
            check_trade(U, broken, good, bad)
            raise SystemExit("mutation erroneously accepted")
        try:
            check_trade(U, broken, good, bad)
        except ValueError as e:
            require(str(e) == "unbalanced trace trade", "wrong mutation failure")
        else:
            raise RuntimeError("mutation erroneously accepted")
    print("Corrupted eligible-line trade rejected (point degrees).")
    summary = Counter()
    for S, m, s in work:
        summary.update(nonbeta(S, m, s))
    print("non-beta t2, (exceptional traces, sum e lower, sum e upper):", dict(summary))
    print("PASS: beta trade and non-beta t2 boundary lemmas. With PROOF.md: b(K) <= 19.")


if __name__ == "__main__":
    main()
