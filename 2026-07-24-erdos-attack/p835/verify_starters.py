#!/usr/bin/env python3
"""Independent verification of the starter facts behind PROOF.md (see there)."""
from itertools import combinations

def starters(p):
    pts, out = list(range(1, p)), []
    def gap(a, b):
        d = (a - b) % p
        return min(d, p - d)
    def rec(rem, pairs, used):
        if not rem:
            out.append(frozenset(pairs)); return
        a = min(rem)
        for b in rem:
            if b != a and gap(a, b) not in used:
                rec(rem - {a, b}, pairs + [frozenset((a, b))], used | {gap(a, b)})
    rec(frozenset(pts), [], set())
    return out

if __name__ == "__main__":
    p = 11
    S = starters(p)
    assert len(S) == 25
    R59 = {frozenset((a, a * r % p)) for a in range(1, p) for r in (5, 9)}
    assert len(R59) == 10
    from collections import Counter
    assert Counter(len(s & R59) for s in S) == Counter({0: 15, 3: 10})
    print("p=11 starter facts verified: 25 starters, 10 ratio-{5,9} edges, counts in {0,3}")
    print("=> 9 disjoint starters cover 0 mod 3 of them; 10 required; contradiction.")
