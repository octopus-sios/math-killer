#!/usr/bin/env python3
"""Exact stress tests for the interval-growth proof, not a census of all DFAs.

Checks the bound on the number of growing placements against actual indegrees
and constructs words for every nonempty subset in each test automaton.
No dependencies outside the Python standard library.
"""
from collections import deque
from itertools import combinations_with_replacement
from math import gcd


def bound(n, m):
    h = -(-n // m)
    return (n - 1)**2 - (h - 1) * (2*n - m*h - 1)


def arc(n, i, length):
    return sum(1 << ((i+j) % n) for j in range(length))


def apply(w, letters, x):
    for t in w:
        x = letters[t][x]
    return x


def action(row, mask):
    out = 0
    for i, v in enumerate(row):
        if mask >> i & 1:
            out |= 1 << v
    return out


def formulas():
    for n in range(1, 161):
        prev = -1
        for m in range(1, n+1):
            g = (n-1)//m
            eps = n-m*g
            d = n-g-2
            B = bound(n, m)
            # The concave quadratic j*(2*n-1-m*(j+1)) is maximized at g.
            assert B == (n-1)**2 - sum(max(0, 2*n-1-2*m*j) for j in range(1,n))
            assert B > prev
            prev = B
            if n >= 8 and m >= 3:
                assert d >= n//2
                assert B-(2+(n-1)*d+m*g) == g*(m-eps)+eps-3 >= m-3
        assert bound(n, 1) == 0 and bound(n,n) == (n-1)**2
        if n >= 2:
            assert bound(n,2) == n*(n-1)//2


def profile_check(n):
    # All ordered weak compositions of n into n bins are indegree vectors.
    # Cyclic rotation does not change any count below; check one per orbit.
    checked = 0
    for outputs in combinations_with_replacement(range(n), n):
        c = tuple(outputs.count(i) for i in range(n))
        if c.count(0) < 2 or any(c[i:]+c[:i] < c for i in range(1,n)):
            continue
        F = [0]
        for w in c:
            F.append(F[-1] + w-1)
        assert F.pop() == 0
        e = [0]*n
        for l in range(1,n):
            # Two independent computations of the number for the chosen b.
            ups = sum(F[(i+l)%n] > F[i] for i in range(n))
            assert ups == sum(sum((c+c)[i:i+l]) > l for i in range(n))
            e[l] = max(1, ups)  # otherwise the sync hypothesis supplies a different letter
        for m in range(3,n+1):
            g = (n-1)//m
            d = n-g-2
            assert sum(e[2:n-g]) >= 2*d-2
        checked += 1
    return checked


def all_distances(A):
    n = len(A[0])
    pred = [[] for _ in range(1 << n)]
    for x in range(1, 1<<n):
        for row in A:
            pred[action(row, x)].append(x)
    D = [-1]*(1<<n)
    queue = deque(1<<i for i in range(n))
    for x in queue:
        D[x] = 0
    while queue:
        y = queue.popleft()
        for x in pred[y]:
            if D[x] < 0:
                D[x] = D[y]+1
                queue.append(x)
    return D


def proof_words(A, jump):
    n = len(A[0])
    assert n >= 8 and gcd(jump, n) == 1
    assert tuple((i+jump)%n for i in range(n)) == A[0]
    assert len(set(A[1])) <= n-2
    intervals = {arc(n,i,l) for i in range(n) for l in range(n+1)}

    def pre(row, I):
        return sum(1 << i for i,j in enumerate(row) if I >> j & 1)

    assert all(pre(row, I) in intervals for row in A for I in intervals)
    D = all_distances(A)
    assert D[-1] >= 0
    # Stage candidates are (start index, word constant on the arc).
    nodes = [(i, (1,)) for i in range(n) if
             action(A[1], arc(n,i,2)).bit_count() == 1]
    assert len(nodes) >= 2
    chosen = {}
    switches = 0
    for l in range(2,n):
        for j in range(1,len(A)):
            good = {i for i in range(n)
                    if pre(A[j], arc(n,i,l)).bit_count() > l}
            if good:
                switches += j != 1
                break
        else:
            raise ValueError("synchronizing interval action has no enlarging letter")
        t, i, w = min((t,i,w) for i,w in nodes for t in range(n)
                      if (i-t*jump)%n in good)
        assert t <= n-len(good)-(l==2)
        I = pre(A[j], arc(n, i-t*jump, l))
        i = next(i for i in range(n) if arc(n,i,l+1) & ~I == 0)
        w = (j,) + (0,)*t + w
        assert len({apply(w,A,q) for q in range(n) if arc(n,i,l+1)>>q & 1}) == 1
        nodes = [(i,w)]
        chosen[l+1] = (i,w)

    for m in range(3,n+1):
        g = (n-1)//m
        i,w = chosen[n-g]
        # Independently evaluate the whole word once on each state.
        end = [apply(w, A, q) for q in range(n)]
        for s in range(1,1<<n):
            if s.bit_count() != m:
                continue
            t = next(t for t in range(n) if not s & ~arc(n,i-t*jump,n-g))
            assert t <= m*g
            assert len({end[(q+t*jump)%n] for q in range(n) if s >> q & 1}) == 1
            assert D[s] <= t+len(w) <= bound(n,m)-(m-3)
    return switches, D


def fixture(n, jump, folds, reverse=False):
    rows = [tuple((i+jump)%n for i in range(n))]
    for sources in folds:
        row = tuple((i+(i in sources))%n for i in range(n))
        if reverse:
            row = tuple(-x % n for x in row)
        rows.append(row)
    return tuple(rows)


def certificate_accepts(A, s, w, length):
    # Check the semantic witness, not just a stored checksum.
    return (len(w) == length and
            len({apply(w,A,i) for i in range(len(A[0])) if s>>i & 1}) == 1)


def main():
    formulas()
    print("PASS: ceiling, overlap-budget arithmetic, and monotonicity tests")
    counts = [profile_check(n) for n in (8,9,10)]
    print("PASS: all corank >= 2 indegree profiles up to rotation at n=8,9,10:", *counts)
    tests = [(8,3,[(0,3)],False), (9,2,[(0,4)],True),
             (10,3,[(0,3,7)],False), (11,3,[(0,5)],False),
             (12,5,[(0,6),(1,4)],False), (13,5,[(0,2,7)],True)]
    switches = 0
    for n,j,folds,rev in tests:
        A = fixture(n,j,folds,rev)
        count,D = proof_words(A,j)
        switches += count
    assert switches > 0
    print(f"PASS: constructed words and exact subset BFS in {len(tests)} automata; "
          f"{switches} stages required a fallback letter")

    # Independently check the sharp profiles in the known extremal family.
    for n in range(3,13):
        C = (tuple((i+1)%n for i in range(n)), (1,)+tuple(range(1,n)))
        D = all_distances(C)
        for m in range(1,n+1):
            assert max(D[s] for s in range(1,1<<n) if s.bit_count()==m) == bound(n,m)
    print("PASS: Cerny profile from exact BFS at n=3..12")

    # Recover a shortest word for a hardest proper triple of the last C_n.
    s = max((s for s in range(1,1<<n) if s.bit_count()==3), key=D.__getitem__)
    x, w = s, []
    while D[x]:
        j,y = next((j,y) for j,row in enumerate(C) if D[y:=action(row,x)] == D[x]-1)
        w.append(j)
        x = y
    assert certificate_accepts(C,s,w,D[s])
    # Even allowing the shortened length, deleting the last letter must fail.
    assert not certificate_accepts(C,s,w[:-1],len(w)-1)
    print(f"PASS: mutation rejected (n={n}, triple mask={s}, distance={D[s]})")


if __name__ == "__main__":
    main()
