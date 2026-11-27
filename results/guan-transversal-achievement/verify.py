"""Replay O's defense for n=4,5; --mutate deliberately declines a required block."""
import argparse
from itertools import permutations


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


class XWin(Exception):
    """A legal history in which the defense failed to prevent a fast X win."""


class Board:
    def __init__(self, n):
        self.n = n
        self.full = (1 << (n * n)) - 1
        self.rows = [sum(1 << (n*r+c) for c in range(n)) for r in range(n)]
        self.cols = [sum(1 << (n*r+c) for r in range(n)) for c in range(n)]
        # Enumerate precisely the winning sets of size at most n+1, independently
        # of both the defensive rule and the order in which the stones were played.
        self.wins = set()
        for perm in permutations(range(n)):
            p = sum(1 << (n*r+c) for r, c in enumerate(perm))
            self.wins.add(p)
            self.wins.update(p | e for e in bits(self.full ^ p))

    def reply(self, x, o, last, mutate):
        n = self.n
        k = x.bit_count()
        free = self.full ^ (x | o)
        if k < n-1:
            rows = [r for r in self.rows if not r & o]
            r = next((r for r in rows if r & last), rows[0])
            c = next(c for c in self.cols if not c & (o | last))
            return r & c

        if k == n-1:
            rows = [r for r in self.rows if not r & x]
            cols = [c for c in self.cols if not c & x]
            if len(rows) == len(cols) == 1:
                corner = rows[0] & cols[0]
                if free & corner:
                    return next(bits(free ^ corner)) if mutate else corner
                return next(bits(free))

            protected = cols[0] if len(rows) > 1 else rows[0]
            r, s = (r for r in self.rows if not r & o)
            c, d = (c for c in self.cols if not c & o)
            for u, t in [(r & c, s & d), (r & d, s & c)]:
                if u & free and t & free:
                    return t if t & protected else u
            raise ValueError("no free diagonal")

        # O's n-th move: win, block X's threat, or play any free stone.
        return next((p for p in bits(free) if (o | p) in self.wins),
                    next((p for p in bits(free) if (x | p) in self.wins),
                         free & -free))

    def replay(self, mutate=False):
        checked = [0] * (self.n + 1)
        o_wins = 0

        def visit(x, o, depth, history):
            nonlocal o_wins
            # All opening cells are equivalent by renumbering rows and columns.
            for p in bits(self.full ^ (x | o) if depth else 1):
                new_x = x | p
                checked[depth] += 1
                if new_x in self.wins:
                    raise XWin(history + (p,))
                if depth == self.n:
                    continue
                q = self.reply(new_x, o, p, mutate)
                if q <= 0 or q & (q-1) or q & (new_x | o) or not (q & self.full):
                    raise ValueError("illegal O reply")
                new_o = o | q
                if new_o in self.wins:
                    o_wins += 1
                else:
                    visit(new_x, new_o, depth + 1, history + (p, q))

        visit(0, 0, 0, ())
        return checked, o_wins


def format_line(n, history):
    return " ".join(f"{'XO'[i % 2]}({r+1},{c+1})" for i, p in enumerate(history)
                    for r, c in [divmod(p.bit_length() - 1, n)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutate", action="store_true", help="test the corrupted strategy alone")
    mutate = parser.parse_args().mutate
    for n in (4, 5):
        board = Board(n)
        try:
            checked, o_wins = board.replay(mutate)
        except XWin as exc:
            print(f"FAIL n={n}: {format_line(n, exc.args[0])}")
            return 1
        print(f"PASS n={n}: X prefixes by move={checked}, O wins={o_wins}, fast X wins=0")

    try:
        Board(4).replay(mutate=True)
    except XWin as exc:
        print(f"PASS mutation rejected: {format_line(4, exc.args[0])}")
        return 0
    raise RuntimeError("corrupted strategy was not rejected")


if __name__ == "__main__":
    raise SystemExit(main())
