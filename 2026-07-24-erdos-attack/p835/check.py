#!/usr/bin/env python3
"""INDEPENDENT verifier for a claimed proper (k+1)-coloring of J(2k,k).

Usage: check.py <coloring.json>

Uses NOTHING from the generation pipeline (no orbits, no sigma, no CNF):
  - checks the coloring assigns a color in {0..k} to every k-subset of [2k]
    (exactly C(2k,k) distinct valid bitmasks),
  - iterates ALL (k+1)-subsets S of [2k]; the k+1 k-subsets S minus one element form a
    (k+1)-clique in J(2k,k) and must be RAINBOW (k+1 distinct colors).
Every edge {A,B} (|A cap B| = k-1) lies in exactly one such clique (S = A u B),
and conversely, so "all cliques rainbow" <=> "coloring is proper".
"""
from __future__ import annotations

import json
import sys
from itertools import combinations
from math import comb


def main() -> None:
    with open(sys.argv[1]) as f:
        data = json.load(f)
    n: int = data["n"]
    k: int = data["k"]
    coloring = {int(m): int(c) for m, c in data["coloring"].items()}

    assert len(coloring) == comb(n, k), "wrong number of vertices"
    for m, c in coloring.items():
        assert 0 <= m < (1 << n) and bin(m).count("1") == k, f"bad mask {m}"
        assert 0 <= c <= k, f"color out of range: {c}"

    total = comb(n, k + 1)
    bad = 0
    done = 0
    for S in combinations(range(n), k + 1):
        sm = 0
        for e in S:
            sm |= 1 << e
        seen = 0
        for e in S:
            seen |= 1 << coloring[sm ^ (1 << e)]
        if bin(seen).count("1") != k + 1:
            bad += 1
        done += 1
        if done % 50000 == 0:
            print(f"  ... {done}/{total} cliques, bad so far: {bad}")

    print(f"checked all {total} ({k+1})-cliques of J({n},{k}): non-rainbow = {bad}")
    if bad == 0:
        print(f"VERIFIED: proper {k+1}-coloring of J({n},{k}).")
    else:
        print("FAILED verification.")
        sys.exit(1)


if __name__ == "__main__":
    main()
