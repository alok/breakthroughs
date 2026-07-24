#!/usr/bin/env python3
"""#617: try to extend the AG(2,5)-based balanced 5-colouring of K_25 to K_26.

K_25 colouring: points F_5^2; colour of pair {p,q} = direction class of q-p
(6 classes: slopes 0,1,2,3,4,inf), with classes for slope 0 and slope inf
merged into one colour => 5 colours. Every 6-set contains a pair of every
parallel class (pigeonhole: 6 points, 5 lines per class), so this is balanced.

Extension: add vertex * with free edge colours y[x] in 0..4 for the 25 edges.
A 6-set {*} u T (|T|=5) sees colours(T) u {y[x] : x in T}; need all 5.
So for each 5-set T missing colour set M: clause 'some x in T has y[x]=c' per c in M.
"""
from itertools import combinations, product
import sys

F = range(5)
pts = list(product(F, F))
pidx = {p: i for i, p in enumerate(pts)}

def cls(p, q):
    dx, dy = (q[0] - p[0]) % 5, (q[1] - p[1]) % 5
    if dx == 0:
        return 5  # 'inf'
    return (dy * pow(dx, 3, 5)) % 5  # slope dy/dx in F5 (dx^-1 = dx^3 mod 5)

def colour(p, q):
    c = cls(p, q)
    return 0 if c in (0, 5) else c  # merge slope-0 and slope-inf -> colour 0; slopes 1..4 -> 1..4

# sanity: K25 colouring is balanced (every 6-set sees all 5 colours)
bad = 0
for S in combinations(pts, 6):
    seen = set(colour(p, q) for p, q in combinations(S, 2))
    if len(seen) < 5:
        bad += 1
print(f"K25 check: {bad} unbalanced 6-sets (want 0)", file=sys.stderr)
assert bad == 0

# extension CNF
def var(x, c):
    return 1 + pidx[x] * 5 + c

clauses = []
for x in pts:
    clauses.append([var(x, c) for c in range(5)])
    for c1, c2 in combinations(range(5), 2):
        clauses.append([-var(x, c1), -var(x, c2)])
nconstr = 0
for T in combinations(pts, 5):
    seen = set(colour(p, q) for p, q in combinations(T, 2))
    for c in set(range(5)) - seen:
        clauses.append([var(x, c) for x in T])
        nconstr += 1
print(f"5-set colour constraints: {nconstr}", file=sys.stderr)

with open("ag_extend.cnf", "w") as f:
    f.write(f"p cnf 125 {len(clauses)}\n")
    f.write("".join(" ".join(map(str, cl)) + " 0\n" for cl in clauses))
print("wrote ag_extend.cnf", file=sys.stderr)
