#!/usr/bin/env python3
"""Independent verification of the Z17 starter results.

Shares no code with starters17.py:
  (a) recount starters of Z_p by a DIFFERENT search order (choose one pair per
      gap class g = 1..half in order, points as sets);
  (b) verify the claimed 15-row partition: each row is a starter, rows pairwise
      edge-disjoint, union is all C(16,2) = 120 edges of K16 on {1..16}.
"""
import json
import sys
from itertools import combinations

P = 17
HALF = (P - 1) // 2

PARTITION = [
    [(1, 2), (3, 5), (4, 9), (6, 12), (7, 14), (8, 16), (10, 13), (11, 15)],
    [(1, 3), (2, 6), (4, 12), (5, 10), (7, 13), (8, 11), (9, 16), (14, 15)],
    [(1, 4), (2, 7), (3, 9), (5, 14), (6, 16), (8, 12), (10, 11), (13, 15)],
    [(1, 6), (2, 9), (3, 11), (4, 8), (5, 7), (10, 16), (12, 15), (13, 14)],
    [(1, 8), (2, 4), (3, 14), (5, 9), (6, 15), (7, 10), (11, 16), (12, 13)],
    [(1, 13), (2, 5), (3, 10), (4, 15), (6, 14), (7, 8), (9, 11), (12, 16)],
    [(1, 14), (2, 11), (3, 6), (4, 10), (5, 12), (7, 9), (8, 13), (15, 16)],
    [(1, 12), (2, 16), (3, 15), (4, 14), (5, 13), (6, 8), (7, 11), (9, 10)],
    [(1, 5), (2, 12), (3, 4), (6, 9), (7, 16), (8, 14), (10, 15), (11, 13)],
    [(1, 7), (2, 15), (3, 12), (4, 11), (5, 6), (8, 10), (9, 14), (13, 16)],
    [(1, 9), (2, 13), (3, 8), (4, 7), (5, 15), (6, 10), (11, 12), (14, 16)],
    [(1, 10), (2, 3), (4, 6), (5, 16), (7, 12), (8, 15), (9, 13), (11, 14)],
    [(1, 11), (2, 14), (3, 16), (4, 13), (5, 8), (6, 7), (9, 15), (10, 12)],
    [(1, 15), (2, 10), (3, 7), (4, 16), (5, 11), (6, 13), (8, 9), (12, 14)],
    [(1, 16), (2, 8), (3, 13), (4, 5), (6, 11), (7, 15), (9, 12), (10, 14)],
]


def gap(a: int, b: int) -> int:
    d = (a - b) % P
    return min(d, P - d)


def count_starters_by_gap_order(p: int) -> int:
    """Different algorithm: place one pair per gap class in gap order."""
    half = (p - 1) // 2
    count = 0

    # a pair of gap g is {a, (a+g) mod p}; enumerate unordered pairs via a
    # 'seen' set since a -> a+g wraps
    def rec2(g: int, used: frozenset):
        nonlocal count
        if g > half:
            count += 1
            return
        seen = set()
        for a in range(1, p):
            b = (a + g) % p
            if b == 0 or a in used or b in used:
                continue
            key = frozenset((a, b))
            if key in seen:
                continue
            seen.add(key)
            rec2(g + 1, used | key)

    count = 0
    rec2(1, frozenset())
    return count


def main() -> int:
    # (a) independent recount
    for p, expected in ((11, 25), (13, 133)):
        c = count_starters_by_gap_order(p)
        assert c == expected, (p, c, expected)
        print(f"independent recount p={p}: {c} starters (matches known)")
    c17 = count_starters_by_gap_order(17)
    print(f"independent recount p=17: {c17} starters")

    # (b) partition verification
    assert len(PARTITION) == P - 2 == 15
    all_edges = set(frozenset(e) for e in combinations(range(1, P), 2))
    assert len(all_edges) == 120
    seen_edges = set()
    for r, row in enumerate(PARTITION):
        pts = set()
        gaps = set()
        assert len(row) == HALF == 8
        for a, b in row:
            assert 1 <= a < b <= 16, (r, a, b)
            pts.update((a, b))
            gaps.add(gap(a, b))
            e = frozenset((a, b))
            assert e not in seen_edges, f"edge {sorted(e)} repeated (row {r})"
            seen_edges.add(e)
        assert pts == set(range(1, P)), f"row {r} not a perfect matching"
        assert gaps == set(range(1, HALF + 1)), f"row {r} gaps {sorted(gaps)}"
    assert seen_edges == all_edges, "union is not all of K16"
    print("partition VERIFIED: 15 rows, each a Z17-starter (perfect matching "
          "of {1..16}, one pair per gap 1..8), pairwise edge-disjoint, "
          "union = all 120 edges of K16")
    return 0


if __name__ == "__main__":
    sys.exit(main())
