# Breakthrough session 2026-07-24: Erdős problem attack

## Mission
Make an original math discovery: resolve (or make citable progress on) an open
Erdős problem from erdosproblems.com / Tao's database.

## Why this target class
- July 2026 news: original AI math discoveries are happening via the Erdős database
  (OpenAI's unit-distance disproof #90, DeepMind's 9 solutions, Fable 5's Jacobian
  counterexample). This is the proven playbook.
- Tao's database flags problems that are *open but reducible to finite computation*:
  - `decidable` (9): resolved by a finite computation (mostly infeasible — asymptotic
    results with astronomical thresholds; ruled out after reading all 9).
  - `falsifiable` (27): a found counterexample would fully resolve.
  - `verifiable` (7): a found construction would fully resolve.
- Selection criteria: feasibility of the finite search on this Mac, P(right answer is
  findable), no prior AI resolution (cross-checked against Tao's AI-contributions wiki),
  instant independent verifiability of any find.

## Method
1. Triage all 34 flagged problems (3 parallel agents reading erdosproblems.com).
2. Pick 1–3 targets; design searches with correct-by-construction checkers.
3. Any hit gets: independent re-verification (separate code path), literature/novelty
   check, and where feasible a Lean 4 kernel-checked certificate.
4. Writeup with provenance; report to erdosproblems.com only after user review.

## Deliverables
- `2026-07-24-erdos-attack/`: search code, certificates, writeup.
- Honest negative results if no hit: documented search bounds are still citable
  ("no counterexample below N") and OEIS-linkable data (Tao's repo requests this).

## Non-goals
- No claim without independent verification + novelty check (the GPT-5 "solutions
  already in the literature" failure mode is the thing to avoid).
