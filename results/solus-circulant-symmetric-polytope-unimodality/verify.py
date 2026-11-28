#!/usr/bin/env python3
"""Exact checks for the stable second hypersimplices. Standard library only."""
from functools import lru_cache
from itertools import product
from math import comb


@lru_cache(maxsize=None)
def C(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def numerator(n, r):
    """Formula (2), including the lower-dimensional even endpoint."""
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


def one_image(n, r, i):
    """Equation (3), regarded as an integer-valued polynomial at fixed i."""
    return C(n, 2*i) - n*(C(r, i)*C(n-r-2, i-1) - C(r, i+1)*C(n-r-2, i-2))


def turan(n, r, i):
    return one_image(n, r, i)**2 - one_image(n, r, i-1)*one_image(n, r, i+1)


def nd(n, r, k):
    c = n-2*r-2
    num = 2*(k+1)*(2*k+1)*(r-k)*(n-r-k)*(n+(k+1)*c)
    den = k*(k+2)*(n-2*k)*(n-2*k-1)*(n+k*c)
    return num, den


def tail(z, v, u):
    i = 10+z
    r = i+1+v
    n = 3*r-2+u
    a, b = nd(n, r, i)
    c, d = nd(n, r, i+1)
    return b*d-2*a*d+a*c


def orthant(f, deg, dims):
    """Every coefficient in the product Newton (binomial) basis must be >=0."""
    axis = range(deg+1)
    table = {p: f(*p) for p in product(axis, repeat=dims)}
    for h in range(dims):
        for fixed in product(axis, repeat=dims-1):
            line = [fixed[:h] + (k,) + fixed[h:] for k in axis]
            values = [table[p] for p in line]
            for p in line:
                table[p] = values[0]
                values = [y-x for x, y in zip(values, values[1:])]
    assert min(table.values()) >= 0, min(table.items(), key=lambda p: p[1])


def cone_certificate():
    # Each one_image at index k has degree <= 2k; the Turan difference <= 4i.
    # When tops are nonnegative, out-of-range binomials at k>=0 agree with
    # their falling-factorial polynomial; a fixed negative lower index means 0.
    for i in range(1, 11):
        orthant(lambda v,u: turan(3*(11+v)-2+u, 11+v, i), 4*i, 2)
        for r in range(1, 11):
            base = max(3*r-2, 2*r+1, 2*i+2)
            orthant(lambda u: turan(base+u, r, i), 4*i, 1)
    # Each numerator or denominator in nd has degree <= 6.
    orthant(tail, 12, 3)


def from_vertices(n, r):
    """Independent Ehrhart counts by all distinct sums of t allowed vertices.

    Pairing opposite tokens proves degree-by-degree equality with lattice
    points (PROOF, Sec. 1). In full dimension, Ehrhart reciprocity and the
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

    # Sec. 7 via power sums of the two roots. Degree <= m, so m+1
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


if __name__ == "__main__":
    cone_certificate()
    print("Nonnegative Newton certificates: 110 prefix orthants/rays and one tail orthant.")
    independent_checks()
    print("Vertex sums through n=10, mutation rejection, and width-five recurrence agree.")
    print(f"Log-concavity holds for all {sweep(320)} admissible pairs through n=320.")
