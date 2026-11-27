"""Exact finite checks for the centred Gaussian difference; the general proof is in PROOF.md."""
from functools import lru_cache


@lru_cache(None)
def gaussian(k, a):
    """Product formula for a rectangle of height k, width a (increasing degree)."""
    if min(k, a) < 0:
        raise ValueError("negative box dimension")
    p = [1] + [0] * (k * a)
    for j in range(1, k + 1):
        # Multiply by 1-q^(a+j), then divide by 1-q^j in truncated power series.
        for n in range(k * a, a + j - 1, -1):
            p[n] -= p[n - a - j]
        for n in range(j, k * a + 1):
            p[n] += p[n - j]
    return tuple(p)


def coeff(p, n):
    return p[n] if 0 <= n < len(p) else 0


def difference(k, m, b):
    a, h, u = m - k, k - 2, b - k + 2
    twice = k * a - h * u
    if twice < 0 or twice % 2 or min(a, u) < 0:
        raise ValueError("inadmissible parameters")
    s = twice // 2
    return tuple(v - coeff(gaussian(h, u), n - s)
                 for n, v in enumerate(gaussian(k, a)))


def check_box(k, a, p):
    # Independent q-Pascal identity, including the boundary and BOTH ends.
    if k == 0 or a == 0:
        ok = p == (1,)
    else:
        x, y = gaussian(k - 1, a), gaussian(k, a - 1)
        ok = (len(p) == 1 + k * a and
              all(v == coeff(x, n) + coeff(y, n - k) for n, v in enumerate(p)))
    if not ok:
        raise AssertionError(f"q-Pascal check failed at {k=}, {a=}")


def good(p):
    if p != p[::-1]:
        raise AssertionError("not symmetric about the common centre")
    return p[0] >= 0 and all(p[n] >= p[n - 1] for n in range(1, (len(p) + 1) // 2))


def predicted(k, m, b):
    if k == 3:
        return b != 3 * m - 10 and not (
            (m % 2 == 0 and b == 2) or (m % 4 == 1 and b in (1, 5))
            or (m % 4 == 3 and b == 3))
    if k == 4:
        return m != 5 and b % 2 == 0
    return (k - 2) * b != k * m - 4 * k + 2


def sweep(max_m=120):
    # Published thresholds in the source m-parameter, not widths.
    known = {3: 3, 4: 4, 5: 20, 6: 32, 7: 18}
    boxes = set()
    print("k  triples  shift=1  discrepancies-from-classification  last-discrepancy-m")
    for k in range(3, 11):
        cases = ones = diffs = 0
        last = None
        for m in range(k, max_m + 1):
            for b in range(k - 2, (k * m - 4 * k + 4) // (k - 2) + 1):
                if k * (m - b) % 2:
                    continue
                boxes.update(((k, m - k), (k - 2, b - k + 2)))
                p = difference(k, m, b)
                s1 = (k - 2) * b == k * m - 4 * k + 2
                cases += 1
                ones += int(s1)
                if k >= 5 and s1 and m >= k + 2 and p[:3] != (1, 0, 1):
                    raise AssertionError(("shift-one prefix", k, m, b, p[:3]))
                if good(p) != predicted(k, m, b):
                    diffs += 1
                    last = m
                    if k in known and m >= known[k]:
                        raise AssertionError(("published classification", k, m, b))
        print(k, cases, ones, diffs, last)
    for k, a in boxes:
        check_box(k, a, gaussian(k, a))
    print(f"verified {len(boxes)} distinct Gaussian coefficient arrays by q-Pascal")


def mutation_tests():
    # Symmetric perturbation that preserves nonnegativity, degree and both endpoints.
    k, a = 8, 10
    q = list(gaussian(k, a))
    q[2] += 1
    q[-3] += 1
    try:
        check_box(k, a, tuple(q))
    except AssertionError:
        pass
    else:
        raise AssertionError("q-Pascal accepted symmetric corruption")
    # Moving an admissible difference across the exceptional shift must change the answer.
    if good(difference(8, 18, 19)) or not good(difference(8, 18, 18)):
        raise AssertionError("shift-one/shift-four control did not discriminate")


if __name__ == "__main__":
    sweep()
    mutation_tests()
    print("mutation controls passed")
