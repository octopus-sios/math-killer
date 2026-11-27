"""Exact checks for the cycle identity and rational constant comparison in PROOF.md."""
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import factorial


def permutation_terms():
    # Opposite edges carry (a,A), (b,B), (c,C); 1 on the diagonal.
    M = ("1abc", "a1CB", "bC1A", "cBA1")
    return Counter("".join(sorted(M[i][p[i]] for i in range(4) if i != p[i]))
                   for p in permutations(range(4)))


def cycle_terms():
    E = Counter({"": 1})
    for x in "aAbBcC":
        E[x * 2] += 1
    for tri in ("abC", "aBc", "Abc", "ABC"):
        E["".join(sorted(tri))] += 2
    for pair in ("aA", "bB", "cC"):
        for other in ("aA", "bB", "cC"):
            E["".join(sorted(pair + other))] += 1
    return E


def check_expansion(claimed):
    if permutation_terms() != claimed:
        raise ValueError("cycle expansion disagrees with the permutation definition")


def main():
    E = cycle_terms()
    check_expansion(E)
    print("PASS: cycle polynomial agrees coefficientwise on all 24 permutations")
    corrupted = E.copy()
    corrupted["".join(sorted("abC"))] -= 1
    try:
        check_expansion(corrupted)
    except ValueError:
        print("PASS: corrupted triangle coefficient rejected")
    else:
        raise AssertionError("corrupted expansion accepted")
    t = Fraction(95, 96)
    q = sum(t**i / factorial(i) for i in range(7))
    if (3*q)**8 <= 45*5**8:
        raise AssertionError("Taylor certificate for c > 5/6 failed")
    print("PASS: (3 * Taylor_6(95/96))^8 > 45 * 5^8 exactly")


if __name__ == "__main__":
    main()
