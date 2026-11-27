#!/usr/bin/env python3
"""Exact checks for Thompson 16.95: binary GL(5), GL(6), and rank-one constructions."""
from itertools import combinations, permutations
from random import Random


def independent(words):
    pivots = {}
    for x in words:
        while x and x.bit_length() in pivots:
            x ^= pivots[x.bit_length()]
        if not x:
            return False
        pivots[x.bit_length()] = x
    return True


def binary_cyclic(cols):
    """Try a cyclic e_0, then test powers as n*n-bit vectors."""
    n = len(cols)
    def times(v):
        w = 0
        while v:
            bit = v & -v
            w ^= cols[bit.bit_length() - 1]
            v -= bit
        return w

    def krylov():
        v = 1
        for _ in range(n):
            yield v
            v = times(v)
    if independent(krylov()):
        return True
    action = [0] * (1 << n)
    for j, c in enumerate(cols):
        for i in range(1 << j):
            action[i + (1 << j)] = action[i] ^ c

    def powers():
        a = tuple(1 << i for i in range(n))
        for _ in range(n):
            yield sum(c << (n*i) for i, c in enumerate(a))
            a = tuple(action[c] for c in a)
    return independent(powers())


def binary_reps(n):
    """Visit every row/column orbit at least once; see proof of coverage."""
    cols = sorted(range(1, 1 << n), key=lambda x: (x.bit_count(), x), reverse=True)

    def rec(prefix, start, equal, span):
        if len(prefix) == n:
            yield prefix
            return
        end = len(cols) - (n - len(prefix)) + 1
        for j in range(start, end):
            c = cols[j]
            if c in span or equal & c & ~(c >> 1):
                continue
            if len(prefix) + 1 == n:
                yield prefix + (c,)
            else:
                yield from rec(prefix + (c,), j+1, equal & ~(c ^ (c >> 1)),
                               span | {c ^ x for x in span})
    yield from rec((), 0, (1 << (n-1))-1, {0})


def binary_sweep(n, count_all):
    ps = list(permutations(range(n)))
    Random(1695).shuffle(ps)
    reps, least = 0, len(ps)
    for cols in binary_reps(n):
        reps += 1
        hits = (binary_cyclic(tuple(cols[j] for j in p)) for p in ps)
        if count_all:
            least = min(least, sum(hits))
        elif not any(hits):
            raise AssertionError(("counterexample", cols))
    assert reps > 0
    if count_all:
        assert least == 24
        print(f"GL({n},2): {reps} orbit-cover representatives; minimum {least} orders")
    else:
        assert (n, reps) in {(6, 139629), (7, 28892664)}
        print(f"GL({n},2): {reps} orbit-cover representatives; all have a cyclic order")


class Field:
    """Prime fields and the binary extensions of sizes 4 and 8."""
    def __init__(self, q):
        self.q = q
        self.p = 2 if q in (2, 4, 8) else q
        self.add = [[a ^ b if self.p == 2 else (a+b) % q
                     for b in range(q)] for a in range(q)]
        def multiply(a, b):
            if self.p != 2:
                return a*b % q
            x = 0
            while b:
                if b & 1:
                    x ^= a
                b >>= 1
                a <<= 1
                if a & q:
                    a ^= {2: 0b11, 4: 0b111, 8: 0b1011}[q]
            return x
        self.mul = [[multiply(a, b) for b in range(q)] for a in range(q)]
        self.neg = [row.index(0) for row in self.add]
        self.inv = [None] + [self.mul[a].index(1) for a in range(1, q)]

    def total(self, seq):
        x = 0
        for y in seq:
            x = self.add[x][y]
        return x


def make_perm(n, *cycles):
    p = [-1] * n
    for c in cycles:
        if c:
            for i, j in zip(c, list(c[1:]) + [c[0]]):
                p[i] = j
    assert sorted(p) == list(range(n))
    return p


def inverse(p):
    return [p.index(i) for i in range(len(p))]


def long_order(f, u, B, h):
    assert f.total(u[i] for i in B)
    if len(B) == h:  # one p-power cycle
        return list(B)
    # Choose zero-sum h-blocks directly. The partition lemma ensures existence.
    rem, blocks = list(B), []
    while len(rem) > h:
        block = next(c for c in combinations(rem, h) if not f.total(u[i] for i in c))
        blocks.append(block)
        rem = [i for i in rem if i not in block]
    blocks.append(rem)
    return [b[i] for i in range(h) for b in blocks]


def witness(f, u, v, k, h):
    n = len(u)
    all_i = list(range(n))
    if not any(u) or not any(v):
        return make_perm(n, all_i)
    if not any(a and b for a, b in zip(u, v)):
        return make_perm(n, sorted(all_i, key=lambda i: not u[i]))
    if len(set(u)) == 1:
        r = f.add[1][f.mul[u[0]][f.total(v)]]
        z = 1
        for _ in range(n):
            z = f.mul[z][r]
        if r != 1 and z != 1:
            return make_perm(n, all_i)
        i = next(i for i in all_i if v[i])
        return make_perm(n, [i], [j for j in all_i if j != i])
    if len(set(v)) == 1 or (not f.total(v) and f.total(u)):
        return inverse(witness(f, v, u, k, h))
    for S in combinations(all_i, k):
        B = [i for i in all_i if i not in S]
        if f.total(u[i] for i in B) and (f.total(v) or f.total(v[i] for i in S)):
            return make_perm(n, S, long_order(f, u, B, h))
    raise AssertionError(("no partition", f.q, u, v))


def cyclic_product(f, u, v, p):
    """Independent checker: exact Gaussian elimination on flattened powers of AP."""
    n = len(u)
    if sorted(p) != list(range(n)):
        return False
    mul, add = f.mul, f.add
    a = [[add[int(i == j)][mul[u[i]][v[j]]] for j in p] for i in range(n)]
    power = [[int(i == j) for j in range(n)] for i in range(n)]
    piv = {}
    for k in range(n):
        row = [x for r in power for x in r]
        for j, x in enumerate(row):
            if not x:
                continue
            if j not in piv:
                piv[j] = [mul[t][f.inv[x]] for t in row]
                break
            w = f.neg[x]
            row[j:] = [add[t][mul[w][s]] for t, s in zip(row[j:], piv[j][j:])]
        else:
            return False
        if k+1 < n:
            power = [[f.total(mul[x][y] for x, y in zip(r, c))
                      for c in zip(*power)] for r in a]
    return True


def ternary_checks():
    """Two exceptional orderings used when n is 2 modulo 3."""
    f = Field(3)
    for counts in [(3, 1, 1, 3), (6, 1, 1, 3), (2, 2, 2, 2)]:
        coords = [t for t, c in zip([(1, 1), (1, 2), (2, 1), (2, 2)], counts)
                  for _ in range(c)]
        u, v = map(list, zip(*coords))
        n = len(u)
        if counts == (2, 2, 2, 2):
            p = make_perm(n, [0], list(range(1, n)))
        else:
            short = [0, 1, 2, n-2, n-1]
            B = [i for i in range(n) if i not in short]
            p = make_perm(n, short, long_order(f, u, B, 3))
        assert cyclic_product(f, u, v, p)
        assert not cyclic_product(f, u, v, list(range(n)))
    print("Ternary exceptional five-cycle and seven-cycle constructions: PASS")


def construction_checks():
    rng = Random(1695)
    passed = 0
    # (q, short length, long length, block size). h=m is always a p-power here.
    for q, k, m, h in [(2, 1, 8, 2), (2, 2, 6, 2), (4, 1, 10, 2), (4, 2, 8, 2),
                       (8, 4, 8, 8), (8, 2, 12, 4), (3, 1, 6, 3), (3, 3, 6, 3),
                       (5, 1, 10, 5), (5, 5, 10, 5)]:
        n = k + m
        f = Field(q)
        for zero_sum in (False, True):
            good = 0
            while good < 8:
                u, v = ([rng.randrange(q) for _ in range(n)] for _ in range(2))
                if zero_sum:
                    for col in [u, v]:
                        col[-1] = f.neg[f.total(col[:-1])]
                if not f.add[1][f.total(f.mul[a][b] for a, b in zip(u, v))]:
                    continue
                p = witness(f, u, v, k, h)
                assert cyclic_product(f, u, v, p)
                good += 1
                passed += 1
    f = Field(2)
    for u, v in [([1]*8, [1, 1]+[0]*6), ([1, 1]+[0]*6, [1]*8),
                 ([1]*4+[0]*4, [0]*4+[1]*4)]:
        p = witness(f, u, v, 2, 2)
        assert cyclic_product(f, u, v, p)
        # Valid permutation, wrong witness: minimal polynomial of I+uv^T has degree <=2.
        if cyclic_product(f, u, v, list(range(8))):
            raise AssertionError("corrupted witness accepted")
    print(f"{passed} seeded two-cycle inputs plus three exceptional shapes; corrupted orders rejected")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run without -O")
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seven", action="store_true", help="also run the long GL(7,2) sweep")
    args = parser.parse_args()
    ternary_checks()
    construction_checks()
    binary_sweep(5, True)
    binary_sweep(6, False)
    if args.seven:
        binary_sweep(7, False)
