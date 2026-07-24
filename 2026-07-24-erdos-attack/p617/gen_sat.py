#!/usr/bin/env python3
"""Erdős problem #617 (Erdős–Gyárfás), first open case r=5.

Conjecture: every 5-colouring of E(K_26) contains a K_6 whose 15 edges miss
at least one colour.

SAT instance: does a 5-colouring of E(K_n) exist such that EVERY 6-subset of
vertices sees all 5 colours on its 15 edges?  SAT => conjecture disproved
(counterexample colouring); UNSAT => the r=5 case is settled affirmatively.

Encoding: var(e,c) for each edge e (i<j) and colour c in 0..4.
  - each edge has >=1 colour and <=1 colour (exactly-one => model is a function)
  - for each 6-subset S, each colour c: OR_{e in S} var(e,c)
Optional mild symmetry breaking: fix colour of edge (0,1) to 0.
"""
import sys
from itertools import combinations

n = int(sys.argv[1]) if len(sys.argv) > 1 else 26
out = sys.argv[2] if len(sys.argv) > 2 else f"k{n}_r5.cnf"
C = 5

edges = list(combinations(range(n), 2))
eidx = {e: k for k, e in enumerate(edges)}
def var(e, c):
    return 1 + eidx[e] * C + c

clauses = []
for e in edges:
    clauses.append([var(e, c) for c in range(C)])            # ALO
    for c1, c2 in combinations(range(C), 2):                  # AMO
        clauses.append([-var(e, c1), -var(e, c2)])
for S in combinations(range(n), 6):
    es = [var(tuple(sorted(p)), 0) for p in combinations(S, 2)]  # base vars
    for c in range(C):
        clauses.append([v + c for v in es])
clauses.append([var((0, 1), 0)])                              # symmetry: edge(0,1)=colour 0

with open(out, "w") as f:
    f.write(f"p cnf {len(edges)*C} {len(clauses)}\n")
    f.write("".join(" ".join(map(str, cl)) + " 0\n" for cl in clauses))
print(f"wrote {out}: {len(edges)*C} vars, {len(clauses)} clauses", file=sys.stderr)
