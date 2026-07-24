#!/usr/bin/env python3
"""Generator sanity check: the AG(2,5)-merge balanced colouring of K25 must
satisfy every clause of k25_r5.cnf (produced by gen_sat.py 25)."""
from itertools import combinations, product

n, C = 25, 5
edges = list(combinations(range(n), 2))
eidx = {e: k for k, e in enumerate(edges)}

F = range(5)
pts = list(product(F, F))
def colour(i, j):
    p, q = pts[i], pts[j]
    dx, dy = (q[0] - p[0]) % 5, (q[1] - p[1]) % 5
    c = 5 if dx == 0 else (dy * pow(dx, 3, 5)) % 5
    return 0 if c in (0, 5) else c

assign = {}
for (i, j) in edges:
    col = colour(i, j)
    for c in range(C):
        assign[1 + eidx[(i, j)] * C + c] = (c == col)

nclauses = sat = 0
with open("k25_r5.cnf") as f:
    for line in f:
        if line.startswith("p"):
            continue
        lits = [int(x) for x in line.split()[:-1]]
        if not lits:
            continue
        nclauses += 1
        if any(assign[abs(l)] == (l > 0) for l in lits):
            sat += 1
        else:
            print("VIOLATED:", lits[:20])
print(f"{sat}/{nclauses} clauses satisfied by AG-merge model")
