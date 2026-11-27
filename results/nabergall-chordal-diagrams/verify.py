#!/usr/bin/env python3
"""Exact checks for the clique-boundary decomposition.

With no flags: exhaustive object-level check on small fragments, then the
integer recurrence. With --brute 10: additionally count complete diagrams
directly (optional C++17 kernel). No third-party Python packages.
"""
import argparse
from collections import Counter
from itertools import combinations
from math import comb
from pathlib import Path
import subprocess
import tempfile


def catalan(n):
    return comb(2 * n, n) // (n + 1)


def fragments(n):
    """All partial matchings; -1 denotes a singleton."""
    mate = [-1] * n

    def gen(i):
        while i < n and mate[i] >= 0:
            i += 1
        if i == n:
            yield tuple(mate)
            return
        yield from gen(i + 1)
        for j in range(i + 1, n):
            if mate[j] == -1:
                mate[i], mate[j] = j, i
                yield from gen(i + 1)
                mate[i] = mate[j] = -1

    yield from gen(0)


def valid(word):
    """Check the published graph condition directly, not via the grammar."""
    n = len(word)
    chords = [(i, j) for i, j in enumerate(word) if i < j]
    chords += [(i, n + t) for t, i in enumerate(i for i in range(n) if word[i] < 0)]
    d = len(chords)
    adj = [0] * d
    for i, (a, b) in enumerate(chords):
        for j, (c, e) in enumerate(chords[:i]):
            if a < c < b < e or c < a < e < b:
                adj[i] |= 1 << j
                adj[j] |= 1 << i

    def connected(mask):
        seen = mask & -mask
        queue = seen
        while queue:
            bit = queue & -queue
            new = adj[bit.bit_length() - 1] & mask & ~seen
            seen |= new
            queue = (queue ^ bit) | new
        return seen == mask

    if not connected((1 << d) - 1):
        return False
    for k in range(4, d + 1):
        for vertices in combinations(range(d), k):
            mask = sum(1 << i for i in vertices)
            if all((adj[i] & mask).bit_count() == 2 for i in vertices) and connected(mask):
                return False
    return True


def irreducible(word):
    return all(any(word[i] >= cut for i in range(cut)) for cut in range(1, len(word)))


def glue(left, right, t):
    n = len(left)
    word = list(left) + [(j + n if j >= 0 else -1) for j in right]
    a = [i for i in range(n) if word[i] < 0]
    b = [j for j in range(n, len(word)) if word[j] < 0]
    for i, j in zip(a[:t], b[len(b)-t:]):
        word[i], word[j] = j, i
    return tuple(word)


def parses(length, irreducibles, all_valid, *, corrupt=False):
    """Multiset of glued words proposed as canonical irreducibles."""
    ans = Counter()
    if length == 1:
        ans[(-1,)] = 1
    for ell in range(1, length):
        for left in irreducibles[ell]:
            i = left.count(-1)
            for right in all_valid[length - ell]:
                j = right.count(-1)
                limit = min(i, j if corrupt else j - 1)
                for t in range(1, limit + 1):
                    if i + j > 2 * t:
                        ans[glue(left, right, t)] += 1
    return ans


def require_unique(actual, witness):
    if Counter(actual) != witness:
        raise ValueError("the parse multiset does not cover precisely the target set once")


def check_fragments(bound=9):
    all_valid = [set()]
    irr = [set()]
    for n in range(1, bound + 1):
        good = {w for w in fragments(n) if -1 in w and valid(w)}
        indec = {w for w in good if irreducible(w)}
        require_unique(indec, parses(n, irr, all_valid))
        # Check all words, not just multiplicities by weight.
        decompositions = Counter(indec)
        for ell in range(1, n):
            for left in irr[ell]:
                for right in all_valid[n - ell]:
                    decompositions[glue(left, right, 0)] += 1
        require_unique(good, decompositions)
        all_valid.append(good)
        irr.append(indec)
    print(f"PASS: exact one-to-one decomposition of all valid positive-weight fragments through {bound} positions")

    # Allow a forbidden earliest-cut witness (exhaust the right boundary).
    # Already at length 5 this makes a positive-weight diagram parse twice.
    bad = parses(5, irr, all_valid, corrupt=True)
    try:
        require_unique(irr[5], bad)
    except ValueError:
        if not any(bad[w] > 1 for w in irr[5]):
            raise AssertionError("expected a duplicate parse")
        print("PASS: corrupted split rule rejected (duplicate parse at length 5)")
    else:
        raise AssertionError("accepted a noncanonical parse witness")
    return [Counter(w.count(-1) for w in good) for good in all_valid]


def check_counts(small, through=25):
    all_valid, irr = [Counter()], [Counter()]
    for n in range(1, 2 * through):
        ind = Counter({1: 1}) if n == 1 else Counter()
        dec = Counter()
        for ell in range(1, n):
            for i, a in irr[ell].items():
                for j, b in all_valid[n - ell].items():
                    dec[i+j] += a * b
                    for t in range(1, min(i, j - 1) + 1):
                        ind[i+j-2*t] += a * b
        irr.append(ind)
        all_valid.append(ind + dec)
        if n < len(small) and small[n] != all_valid[n]:
            raise ValueError(f"wrong weight distribution at length {n}")
        if n % 2 and all_valid[n][1] != catalan(n // 2) ** 2:
            raise ValueError(f"wrong diagram count at {(n + 1) // 2} chords")
    print(f"PASS: integer fragment recurrence = shifted Catalan square for n=1..{through}")


# Independent enumeration requested for larger n. Open chords are indexed by
# their source order. Closing chord i adds exactly the edges from i to the
# still-open chords with larger indices. A premature return to zero open
# chords, or closing an isolated chord, cannot yield a connected matching.
BRUTE = r"""
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
using Mask = unsigned;
using Count = std::uint64_t;
int n;
std::array<Mask, 16> adj{};
std::array<Count, 16> degree{}, terminal{};
static Mask bit(int i) { return Mask(1) << i; }
static int idx(Mask a) { return __builtin_ctz(a); }
static int card(Mask a) { return __builtin_popcount(a); }
static bool clique(Mask a) {
    while (a) { int i=idx(a); a &= a-1; if (a & ~adj[i]) return false; }
    return true;
}
// Remove simplicial vertices. Such deletion preserves connectivity, and
// every nonempty induced subgraph of a chordal graph has one.
static bool good(Mask all) {
    while (all & (all-1)) {
        Mask t = all;
        while (t) {
            int i=idx(t); Mask a=adj[i] & all;
            if (!a) return false;
            if (clique(a)) { all ^= bit(i); break; }
            t &= t-1;
        }
        if (!t) return false;
    }
    return true;
}
static void gen(int opened, Mask live, int terminals) {
    if (!live && opened) {
        if (opened == n && good(bit(n)-1)) {
            ++degree[card(adj[0])]; ++terminal[terminals];
        }
        return;
    }
    if (opened<n) gen(opened+1,live | bit(opened),terminals);
    for (Mask t=live; t; t &= t-1) {
        int i=idx(t); Mask a=live & ~((bit(i)<<1)-1);
        if (n>1 && !a && !adj[i]) continue;
        adj[i] |= a;
        for (Mask u=a; u; u &= u-1) adj[idx(u)] |= bit(i);
        gen(opened,live ^ bit(i),terminals+!a);
        adj[i] ^= a;
        for (Mask u=a; u; u &= u-1) adj[idx(u)] ^= bit(i);
    }
}
int main(int argc, char** argv) {
    if (argc!=2) return 2;
    int limit=std::atoi(argv[1]); if (limit<1 || limit>12) return 2;
    for (n=1; n<=limit; ++n) {
        degree.fill(0); terminal.fill(0); gen(0,0,0);
        Count total=0; for (Count c : degree) total+=c;
        std::printf("%d %llu degree:",n,(unsigned long long)total);
        for (int i=0;i<n;++i) std::printf(" %llu",(unsigned long long)degree[i]);
        std::printf(" terminals:");
        for (int i=1;i<=n;++i) std::printf(" %llu",(unsigned long long)terminal[i]);
        std::puts(""); std::fflush(stdout);
    }
}
"""


def brute(limit):
    with tempfile.TemporaryDirectory() as tmp:
        cpp, exe = Path(tmp, "direct.cpp"), Path(tmp, "direct")
        cpp.write_text(BRUTE)
        subprocess.run(["c++", "-O3", "-std=c++17", str(cpp), "-o", str(exe)], check=True)
        out = subprocess.check_output([str(exe), str(limit)], text=True)
    for n, line in enumerate(out.splitlines(), 1):
        if tuple(map(int, line.split()[:2])) != (n, catalan(n-1)**2):
            raise ValueError(f"direct enumeration disagrees: {line}")
        print(line)
    if len(out.splitlines()) != limit:
        raise ValueError("incomplete enumeration")
    print(f"PASS: direct perfect-matching enumeration through {limit} chords")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--brute", type=int, choices=range(1, 13), metavar="N")
    args = ap.parse_args()
    check_counts(check_fragments())
    if args.brute:
        brute(args.brute)
