#!/usr/bin/env python3
"""Exact checks for the stable second hypersimplices. Standard library only."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from math import comb


_rows = [[1]]


def C(n, k):
    if not 0 <= k <= n:
        return 0
    while len(_rows) <= n:
        row = _rows[-1]
        _rows.append([1] + [a+b for a,b in zip(row, row[1:])] + [1])
    return _rows[n][k]


def numerator(n, r):
    """Binomial image formula in the appendix, including the lower-dimensional even endpoint."""
    assert n >= 3 and 1 <= r <= n // 2
    d = n - 2 * r
    if d == 0:
        return [1]
    h = [C(n, 2*i) for i in range(n//2 + 1)]
    for j in range(1, n // (d+2) + 1, 2):
        a, rem = divmod(n - j*(d+2), 2)
        assert rem == 0
        A, B = a+2*j-1, a+j*d-1
        for i in range(j, a+j+1):
            t = C(A, i+j-1)*C(B, i-j) - C(A, i+j)*C(B, i-j-1)
            loss, rem = divmod(n*t, j)
            assert rem == 0 and loss >= 0
            h[i] -= loss
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def from_vertices(n, r):
    """Independent Ehrhart counts by all distinct sums of t allowed vertices.

    Pairing opposite tokens proves degree-by-degree equality with lattice
    points (proof of the coefficient identity). In full dimension, Ehrhart reciprocity and the
    need for n positive coordinates at an interior point give deg(h*)<=n//2.
    Check one extra coefficient whenever it lies within the dimension.
    """
    dim = n//2-1 if n == 2*r else n-1
    top = min(dim, n//2+1)
    radix = top+1  # no carries in any coordinate, even for repeated vertices
    powers = [radix**i for i in range(n)]
    edges = [powers[i]+powers[j] for j in range(n) for i in range(j)
             if min(j-i, n-j+i) >= r]
    layer, counts = {0}, [1]
    for _ in range(top):
        layer = {a+b for a in layer for b in edges}
        counts.append(len(layer))
    h = [sum((-1)**k * comb(dim+1, k) * counts[i-k] for k in range(i+1))
         for i in range(top+1)]
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def check_vector(expected, witness):
    if expected != witness:
        raise ValueError(f"expected {expected}, got {witness}")


def independent_checks():
    for n in range(3, 11):
        for r in range(1, n//2+1):
            check_vector(from_vertices(n, r), numerator(n, r))
    expected = from_vertices(9, 3)
    check_vector(expected, [1, 9, 27, 30, 9])
    corrupted = list(expected)
    corrupted[2] += 1
    try:
        check_vector(expected, corrupted)
    except ValueError:
        pass
    else:
        raise AssertionError("changed coefficient accepted")

    # Width-five formula via power sums of the two roots. Degree <= m, so m+1
    # integer evaluations compare the polynomials identically at each m.
    for m in range(3, 41):
        h = numerator(2*m, m-2)
        for x in range(m+1):
            p, q = 2, 1+2*x
            for _ in range(2, m+1):
                p, q = q, (1+2*x)*q - x*(x-1)*p
            assert q-x**m == sum(v*x**i for i,v in enumerate(h))


def sweep(top):
    total = 0
    for n in range(3, top+1):
        for r in range(1, n//2+1):
            h = numerator(n, r)
            assert h[0] == 1 and min(h) > 0, (n,r)
            assert all(b*b >= a*c for a,b,c in zip(h, h[1:], h[2:])), (n,r)
            total += 1
    return total


def subset_layers(n, r):
    """The new coefficient identity, checked directly with labeled windows."""
    mask = (1 << n) - 1
    first = (1 << (r+1)) - 1
    windows = [((first << j) | (first >> (n-j))) & mask for j in range(n)]
    h = [0]*(n//2+1)
    for s in range(1 << n):
        size = s.bit_count()
        if size % 2 == 0 and all((w & s).bit_count() <= size//2 for w in windows):
            h[size//2] += 1
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def band_row(n):
    """Use log(n) <= 7 for n <= 1024; a slight superset, with exact endpoints."""
    assert 3 <= n <= 1024
    total = 0
    for r in range(1, n//2+1):
        d = n-2*r
        if d > 2 and (d-2)**2 > 448*n:
            continue
        h = numerator(n, r)
        assert h[0] == 1 and min(h) > 0, (n,r)
        assert all(b*b >= a*c for a,b,c in zip(h, h[1:], h[2:])), (n,r)
        total += 1
    return total


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--band", type=int, nargs=2, metavar=("FIRST", "LAST"),
                        help="extended boundary check, 3 <= FIRST <= LAST <= 1024")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.band:
        start, stop = args.band
        if not (3 <= start <= stop <= 1024 and args.jobs >= 1):
            parser.error("invalid band range or job count")
        if args.jobs == 1:
            total = sum(map(band_row, range(start, stop+1)))
        else:
            with ProcessPoolExecutor(max_workers=args.jobs) as pool:
                total = sum(pool.map(band_row, range(start, stop+1)))
        print(f"PASS: {total} band pairs, n={start}..{stop}, d<=2+8*sqrt(7*n)")
    else:
        independent_checks()
        for n in range(3,17):
            for r in range(1,n//2+1):
                check_vector(subset_layers(n,r), numerator(n,r))
        print("Vertex sums through n=10, direct window subsets through n=16,")
        print("mutation rejection, and width-five recurrence agree.")
        print(f"Exact log-concavity for all {sweep(320)} pairs through n=320.")
