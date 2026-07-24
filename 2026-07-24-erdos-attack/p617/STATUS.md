# #617 (Erdős–Gyárfás balanced colourings) — attack aborted after novelty check

## What we built (2026-07-24, ~1 hour)
- Correct SAT encoding of "balanced 5-colouring of K_n exists" (validated: the
  AG(2,5) merged-parallel-class colouring satisfies all 888,801 clauses of the
  K25 instance — [check_model.py](check_model.py)).
- **Lemma 1** (DRAT-verified, [ag_extend.drat](ag_extend.drat)): the AG(2,5)-based balanced
  colouring of K25 does not extend to any balanced colouring of K26.
  Balancedness is hereditary, so any balanced K26 contains a balanced K25 on
  every 25 vertices; this kills the most natural construction route.
- **Lemma 2** (DRAT-verified, [partitions.drat](partitions.drat)): there do NOT exist 5
  partitions of a 26-point set into ≤5 blocks each with no pair co-blocked
  twice. Hence no balanced colouring of K26 in which every colour class
  contains a spanning union of ≤5 cliques ("clique-partition-structured"
  counterexamples are impossible). Cute standalone design-theoretic fact.
- Cube-and-conquer decomposition of the full K26 decision (230 cubes over
  sorted vertex-0 colour profiles, canonical-form symmetry breaking).

## Why aborted
Literature check (2026-07-24) found the r=5 case resolved during the preceding
11 days by four overlapping AI/SAT efforts (nwinter Jul 13; Sneiderman Jul 18,
also r=6..9; Silverstein Jul 21; Kara kernel-pure Lean verification Jul 24),
none yet refereed but collectively decisive: no balanced 5-colouring of K26.
Consistent with the direction our Lemmas 1–2 pointed. A fifth confirmation is
not a breakthrough; cores reallocated to live targets.

Lesson recorded: on erdosproblems.com, the "claimed proofs" counter is a
leading indicator of gold-rush activity — check it during triage, not after.
