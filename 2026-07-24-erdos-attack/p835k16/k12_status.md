# k=12 work status at kill time (redirect: k=12 closed negatively, chi(J(24,12)) >= 14)

Completed before kill (artifacts in ../p835k12/):
1. Encoding pipeline built & calibrated (gen12.py): plain C13-twist orbit encoding
   (mirrors validated k=10 gen.py) + NEW AGL(1,13)-equivariant encoding
   (tau = x->2x multiplier, color(tau A) = 2 color(A), affine decomposition
   color(A) = a*x_O + b per orbit, stabilizer-forced colors).
   Calibration: k=2 exhaustive encoder equivalence (CNF-sat == proper AND
   equivariant) + unique AGL witness [2,0] verified proper; k=4, k=6 sampled
   equivalence + DFS count 0 (matches known chi > k+1). Burnside cross-checks.
2. Independent rainbow-clique checker (check12.py) validated on J(4,2)
   good + corrupted colorings.
3. STAGE A RESULT (stands on its own, though now subsumed by chi >= 14):
   The AGL(1,13)-equivariant ansatz for a proper 13-coloring of J(24,12) is
   UNSAT: kissat 0.99s (x2 configs) AND independent arithmetic refutation --
   148,159 constraints violated by stabilizer-forced colors alone.
   Human-readable certificate (stageA_refutation.json):
   A = {0,2,3,4,5,7} u {13,14,16,19,20,23}, B = {0,2,3,4,5,7} u {13,14,19,20,21,23};
   both stabilized by x -> -x+7 (=(a,b)=(12,7)) on the 13-cycle; equivariance
   forces color 10 on both; |A cap B| = 11 so they are adjacent. Monochromatic
   edge => no AGL(1,13)-equivariant proper 13-coloring exists.
4. Stage B instances generated (plain + starter-seeded, 2,704,156 vars,
   210,972,437/503 clauses, 4.1GB each; triples=14,964,576 with exact
   double-counting accounting 208012*144 = 24576 + 2*14964576).
   Starter partition of K12 into 11 disjoint Z13-starters recomputed & verified.
   3 kissat runs launched (~7 min wall, no verdict) -- KILLED on redirect,
   as chi(J(24,12)) >= 14 (S(11,12,24) -> ... -> S(4,5,17) nonexistence,
   Ostergard-Pottonen) makes Stage B necessarily UNSAT.
   Layers t=3..6 generation launched -- KILLED mid-generation.

Nothing about the k=12 kill invalidates the k=10 mod-3 starter theorem or the
p=13/p=17 starter-partition computations (pure Z_p combinatorics).
