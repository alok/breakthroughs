#!/usr/bin/env python3
"""#617 disproof attempt via pair-disjoint partitions.

Search: 5 partitions of [26] into <=5 blocks each, such that no pair {u,v}
is co-blocked in two different partitions.  If found: colour pair {u,v} by the
partition co-blocking it (leftover pairs arbitrarily) => each colour class
contains a spanning union of <=5 cliques => independence <= 5 => every 6-set
sees all 5 colours => counterexample to Erdos-Gyarfas #617 (r=5, K_26).

Vars x[i][v][b] : point v in block b of partition i  (i,b in 0..4, v in 0..25).
Symmetry: partition 0 fixed to blocks {0..5},{6..10},{11..15},{16..20},{21..25}.
"""
from itertools import combinations
import sys

N, P, B = 26, 5, 5
def var(i, v, b):
    return 1 + (i * N + v) * B + b

clauses = []
for i in range(P):
    for v in range(N):
        clauses.append([var(i, v, b) for b in range(B)])
        for b1, b2 in combinations(range(B), 2):
            clauses.append([-var(i, v, b1), -var(i, v, b2)])

# fix partition 0
blocks0 = [list(range(0, 6)), list(range(6, 11)), list(range(11, 16)),
           list(range(16, 21)), list(range(21, 26))]
for b, blk in enumerate(blocks0):
    for v in blk:
        clauses.append([var(0, v, b)])

# pair-disjointness: for each pair, partitions i<j, blocks a,b:
# not(both u,v in block a of i AND both in block b of j)
for u, v in combinations(range(N), 2):
    for i, j in combinations(range(P), 2):
        for a in range(B):
            for b in range(B):
                clauses.append([-var(i, u, a), -var(i, v, a),
                                -var(j, u, b), -var(j, v, b)])

# mild symmetry: point 0's block index in each partition = 0 (relabel blocks)
for i in range(1, P):
    clauses.append([var(i, 0, 0)])

out = sys.argv[1] if len(sys.argv) > 1 else "partitions.cnf"
with open(out, "w") as f:
    f.write(f"p cnf {P*N*B} {len(clauses)}\n")
    f.write("".join(" ".join(map(str, cl)) + " 0\n" for cl in clauses))
print(f"wrote {out}: {P*N*B} vars {len(clauses)} clauses", file=sys.stderr)
