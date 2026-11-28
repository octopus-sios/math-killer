"""Exact universal polynomial certificate. Run: python3 -I verify.py
No packages; no enumeration bound on the partitions or on the hook size.
"""
from fractions import Fraction
from itertools import combinations
from math import factorial, prod

# Sparse polynomials over Z. A monomial key has one base-32 digit per
# exponent. The straight-line calculation below has degree at most 17.
ONE = {0: 1}
BITS = 5
MASK = (1 << BITS) - 1


def var(k):
    return {1 << (BITS * k): 1}


def add(f, g, sign=1):
    r = f.copy()
    for k, v in g.items():
        n = r.get(k, 0) + sign*v
        if n:
            r[k] = n
        else:
            r.pop(k, None)
    return r


def sub(f, g):
    return add(f, g, -1)


def times(f, factors):
    """Only multiply by affine-linear forms."""
    for g in factors:
        r = {}
        for e, c in g.items():
            for k, v in f.items():
                n = e+k
                r[n] = r.get(n, 0) + c*v
        f = {k: v for k, v in r.items() if v}
    return f


def exact_div(f, g):
    """Synthetic division in the last variable of g, which is monic."""
    unit = max(g)
    assert unit and unit & (unit-1) == 0 and g[unit] == 1
    shift = unit.bit_length()-1
    rest = g.copy()
    del rest[unit]
    slices = {}
    for k, v in f.items():
        j = (k >> shift) & MASK
        slices.setdefault(j, {})[k-j*unit] = v
    q = {}
    carry = {}
    for j in range(max(slices, default=0), -1, -1):
        carry = sub(slices.pop(j, {}), times(carry, [rest]))
        if j:
            q.update((k+(j-1)*unit, v) for k, v in carry.items())
    if carry:
        raise ArithmeticError("nonzero polynomial remainder")
    return q


def psum(polys):
    r = {}
    for p in polys:
        r = add(r, p)
    return r


def universal_kernel(t):
    assert 1 <= t <= 4
    a = var(0)
    h = [add(ONE, var(1+i)) for i in range(t)]
    w = [var(1+t+i) for i in range(t-1)]
    theta = sub(a, ONE)
    v = [add(theta, z) for z in h]
    m = psum(h)
    gap = [psum((v[i+1], ONE, w[i])) for i in range(t-1)]
    p = [psum(gap[i:]) for i in range(t)]
    d, partial = [], []
    for k in range(t):
        # d[k] represents the positive row product prod_j |p_k-q_j|,
        # q_j=p_j+v_j, as a list of linear factors.
        row, numerator = [v[k]], [h[k]]
        for j in range(t):
            if j == k:
                continue
            if j < k:
                x = sub(p[j], p[k])
                row.append(add(x, v[j]))
                numerator.extend((add(x, h[j]), add(x, theta)))
            else:
                x = sub(p[k], p[j])
                row.append(sub(x, v[j]))
                numerator.extend((sub(x, h[j]), sub(x, theta)))
        d.append(row)
        partial.append(times(ONE, numerator))

    # Build unsigned consecutive divided differences with their row
    # products already cleared. See the recurrence in PROOF.md.
    for span in range(1, t):
        partial = [
            exact_div(add(times(partial[i], d[i+span]),
                          times(partial[i+1], d[i])),
                      sub(p[i], p[i+span]))
            for i in range(t-span)
        ]
    return sub(times(partial[0], [add(theta, m)]),
               times(m, [lin for row in d for lin in row]))


def evaluate(f, values):
    # Used for independent normalization and mutation checks, not for proving
    # the signs. Here the selected diagrams give integer gap coordinates.
    tab = [[v**j for j in range(18)] for v in values]
    def term(k, c):
        for powers in tab:
            c *= powers[k & MASK]
            k >>= BITS
        assert not k
        return c
    return sum(term(k, c) for k, c in f.items())


# Independent cell-by-cell evaluation of the two original Pieri paths.
def hooks(shape, a):
    return {(r, c): (a*(width-c)+leg+1, a*(width-c+1)+leg)
            for r, width in enumerate(shape)
            for c in range(1, width+1)
            for leg in [sum(length >= c for length in shape[r+1:])]}


def pieri(inner, outer, a):
    mu, lam = hooks(inner, a), hooks(outer, a)
    added = lam.keys() - mu.keys()
    rows = {r for r, _ in added}
    cols = {c for _, c in added}
    assert len(rows) == len(added) and mu.keys() <= lam.keys()
    return prod((Fraction(lam[s][0]*mu[s][1], lam[s][1]*mu[s][0])
                 for s in mu if s[0] not in rows and s[1] in cols),
                start=Fraction(1))


def check_diagram(f, inner, outer, a):
    mu, lam = hooks(inner, a), hooks(outer, a)
    cells = sorted(lam.keys() - mu.keys())
    cols = sorted({c for r, c in cells}, reverse=True)
    groups = [[r for r, c in cells if c == col] for col in cols]
    h = [len(rs) for rs in groups]
    p = [a*c-max(rs) for c, rs in zip(cols, groups)]
    t, m = len(h), sum(h)
    v = [a-1+hi for hi in h]
    w = [p[i]-p[i+1]-1-v[i+1] for i in range(t-1)]
    D = prod(v) * prod((p[i]-p[j]+v[i])*(p[i]-p[j]-v[j])
                       for i, j in combinations(range(t), 2))
    both = 0
    for rs in groups:
        mid = list(outer)
        mid[max(rs)] -= 1
        both += pieri(inner, mid, a)*pieri(mid, outer, a)
    one = pieri(inner, outer, a)
    scalar = prod(z[0] for z in mu.values())*prod(z[1] for z in lam.values())
    g = factorial(m-2)*scalar*((a+m-1)*both-m*a*one)
    bulk = scalar*one / D
    assert bulk.denominator == 1
    K = evaluate(f, [a] + [hi-1 for hi in h] + w)
    if g != a*factorial(m-2)*bulk*K:
        raise ValueError("cell Pieri and reduced kernel disagree")
    return g


def check_window(f):
    """Mickler, arXiv:2401.01582v3, Conj. 3.3, diagrams in printed order.
    A word reads the three arrays consecutively, line by line from the top.
    """
    groups = [
        (7, "UUUUUUUULUUL"),
        (-2, "UUUUUUUUUUUL"),
        (1, "ULUUUUUUUUUL UUUULUUUUUUL UUUUUUUUULUL"),
        (-2, "LUUUUUUULUUL UULUUUUULUUL UUULUUUULUUL UUUUULLULUUU UUUUUUULLUUL UUUUUUUULULL"),
        (-2, "ULUUUUUULUUL UUUULUUULUUL UUUUUUUULLUL"),
        (1, "LLUUUUUULUUL ULLUUUUULUUL UUULLUUULUUL UUUULLLULUUU UUUUUUULLLUL UUUUUUUULLLL"),
        (1, "LUUUULLULUUU UULLUUUULUUL LUUUUUUULULL UULUUUULLUUL UUULUUUULULL UUUUULLLLUUU"),
    ]
    a = var(0)
    x, y = [psum((a, ONE, var(i))) for i in (4, 5)]
    z = add(x, y)
    mu = [(sub(d, a), sub(d, ONE)) for d in (y, z, x)]
    corner = (ONE, a)
    nu = [corner, (psum((a, ONE, ONE)), psum((a, a, ONE))), corner]
    inter = lambda d: (add(d, ONE), add(d, a))
    lam = [corner, inter(y), corner, inter(z), inter(x), corner]
    hooks = mu + nu + [pair[::-1] for pair in lam]  # clear the window norm
    result, weight = {}, 0
    for coeff, words in groups:
        for word in words.split():
            assert len(word) == 12 and set(word) <= {"U", "L"}
            weight += coeff*(word[:6].count("L")-word[6:].count("L"))
            result = add(result, times(ONE, [h[c == "U"]
                         for h, c in zip(hooks, word)]), coeff)
    assert weight == 0
    rook = {k: c for k, c in f.items()
            if not any((k >> (BITS*i)) & MASK for i in (1, 2, 3))}
    assert result == times(rook, [a])
    print("Mickler's 26 diagrams: universal identity and weight verified.")


def main():
    # Height repetitions, idle rows, nonconsecutive columns, and two
    # distinct rank-three diagrams (one is Stanley's p.114 example).
    examples = {
        1: [((1, 1), (2, 2))],
        2: [((3, 3, 2, 1, 1), (4, 4, 2, 2, 2))],
        3: [((3, 1), (4, 2, 1)),
            ((5, 5, 4, 2, 2, 1), (6, 6, 4, 3, 3, 1, 1))],
        4: [((6, 6, 4, 3, 2, 2, 1), (7, 7, 5, 3, 3, 3, 1, 1))],
    }
    for t in range(1, 5):
        f = universal_kernel(t)
        if any(c <= 0 for c in f.values()):
            raise AssertionError("negative coefficient or unpruned zero")
        print(f"t={t}: {len(f)} monomials; sum={sum(f.values())}; "
              f"minimum nonzero={min(f.values(), default=None)}", flush=True)
        for inner, outer in examples[t]:
            for a in (1, 2, 5):
                check_diagram(f, inner, outer, a)
        if t == 3:
            check_window(f)
            # Stanley, p.114, gives Hanlon's scalar product in this example.
            for a in (1, 2, 5):
                hanlon = 8*a**5*(9+97*a+294*a**2+321*a**3+131*a**4+12*a**5)
                assert check_diagram(f, (3, 1), (4, 2, 1), a) == hanlon
            try:
                check_diagram(add(f, ONE), (3, 1), (4, 2, 1), 2)
            except ValueError:
                pass
            else:
                raise AssertionError("corrupted constant passed")
    print("All symbolic and cellwise checks passed; corrupted kernel rejected.")


if __name__ == "__main__":
    main()
