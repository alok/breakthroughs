#!/usr/bin/env python3
"""#617 K26 instance with canonical-form symmetry breaking / cube splitting.

Canonical form (every balanced colouring is isomorphic to one such):
  - colours sorted by multiplicity at vertex 0: n1>=n2>=...>=n5, sum 25
  - vertices 1..25 relabelled so vertex-0 edge colours are contiguous
    nondecreasing blocks: colour(0, j) = 0 for j in 1..n1, = 1 for next n2, etc.

Modes:
  gen_sat2.py contig OUT          -- contiguity clauses only (single instance)
  gen_sat2.py profile n1,...,n5 OUT -- vertex-0 edge colours fully fixed (cube)
"""
import sys
from itertools import combinations

n, C = 26, 5
edges = list(combinations(range(n), 2))
eidx = {e: k for k, e in enumerate(edges)}
def var(e, c):
    return 1 + eidx[e] * C + c

clauses = []
for e in edges:
    clauses.append([var(e, c) for c in range(C)])
    for c1, c2 in combinations(range(C), 2):
        clauses.append([-var(e, c1), -var(e, c2)])
for S in combinations(range(n), 6):
    es = [var(tuple(sorted(p)), 0) for p in combinations(S, 2)]
    for c in range(C):
        clauses.append([v + c for v in es])

mode = sys.argv[1]
if mode == "contig":
    out = sys.argv[2]
    clauses.append([var((0, 1), 0)])
    for j in range(1, 25):
        e1, e2 = (0, j), (0, j + 1)
        # colour(e2)=k -> colour(e1) in {k-1,k}
        clauses.append([-var(e2, 0), var(e1, 0)])
        for k in range(1, C):
            clauses.append([-var(e2, k), var(e1, k), var(e1, k - 1)])
elif mode == "profile":
    prof = [int(x) for x in sys.argv[2].split(",")]
    out = sys.argv[3]
    assert sum(prof) == 25 and len(prof) == 5 and sorted(prof, reverse=True) == prof
    j = 1
    for c, nc in enumerate(prof):
        for _ in range(nc):
            clauses.append([var((0, j), c)])
            j += 1
else:
    raise SystemExit("mode?")

with open(out, "w") as f:
    f.write(f"p cnf {len(edges)*C} {len(clauses)}\n")
    f.write("".join(" ".join(map(str, cl)) + " 0\n" for cl in clauses))
print(f"wrote {out} ({len(clauses)} clauses)", file=sys.stderr)
