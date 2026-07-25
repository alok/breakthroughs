# Erdős problem attack — 2026-07-24

Autonomous session ("do a breakthrough"): portfolio attack on open Erdős
problems flagged in [Tao's database](https://github.com/teorth/erdosproblems) as
resolvable-in-principle by finite computation, plus structured mathematical
analysis. Six problems attacked in parallel; every claim below was verified by
at least one independent implementation, and novelty was checked against the
literature the same day.

## New results (believed novel as of 2026-07-24)

### 1. Erdős #835 — symmetry obstruction for the first open case  `p835/`
**Theorem (computer-proved, DRAT-certified).** No proper 11-colouring of the
Johnson graph J(20,10) admits a symmetry of order 11 — i.e. for every order-11
element g of Aut(J(20,10)) and every colour-permutation π with π∘colour =
colour∘g, no proper 11-colouring exists. Consequently, if χ(J(20,10)) = 11
(the first open case k = 10 = 11−1 of Erdős–Rosenfeld #835, the only k ≤ 10
not excluded by Ma–Tang), every witness colouring is 11-asymmetric — ruling
out the natural algebraic/equivariant constructions suggested by the
Ma–Tang "k = p−1" pattern.
Method: C₁₁ regular-twist equivariant SAT (184,756 vertices → 16,796 orbits;
10.2M clauses; UNSAT replicated by 4 solver configurations; pipeline validated
in both directions on J(4,2) (SAT, χ=3 reproduced) and J(8,4) (UNSAT, matches
known χ>5)). Weak positive signal recorded: random 40k-vertex induced
subgraphs of J(20,10) are 11-colourable in seconds.

### 2. Erdős #993 — first n = 29 non-log-concavity census  `p993/`
Unimodality of tree independence polynomials (Alavi–Malde–Schwenk–Erdős 1987)
verified exhaustively for **all 8,691,747,673 trees on ≤ 29 vertices** — an
independent replication (different generator, DP, language) of Reynolds' 2026
record. New on top of the literature:
- **Complete census of non-log-concave trees at n = 29: exactly 7** (witnesses
  with exact coefficients; Reynolds explicitly left this audit incomplete).
  Hence **the smallest odd order with non-log-concave trees is exactly 29**.
- The census sequence (NLC trees by order) **0,…,0, 2, 0, 19, 7** (n = 26…29)
  is in no OEIS entry — new sequence candidate.
- **Margin law (empirical)**: min over n-vertex trees of the unimodality
  margin equals ⌊2n/3⌋ for every 8 ≤ n ≤ 29 — the safety gap grows linearly.
- A tree with **9 log-concavity breaks** (more than any published example).
- Literature correction: arXiv:2510.18826's claim of NLC trees "from 27 to 101
  vertices" contradicts two independent exhaustive computations at n = 27 (0).
All 28 NLC witnesses verified by **four** independent implementations
(including [my own](p993/independent_verify_4th.py), distinct from the agent's three).

### 3. Erdős #488 — quantitative structure  `p488/`
No counterexample (conjecture supported). New quantitative findings:
- **Empirical sharp form**: ratio ≤ 2 − 1/max(A) across every family tested
  (equality iff |A| singleton) — a strengthened conjecture worth recording.
- Interpolating family: A = primes in (x, cx] gives ratio → 2·log(c)/(c−1) → 2
  as c → 1⁺, matching measurement to 3–4 digits.
- In Tao's asymptotic regime (his comment: 1.0311, "tweaking permits slightly
  larger"): optimum single window is much wider — primes in (n^0.18, n^0.6]
  gives **ratio 1.0883** (sieve-verified at X = 5·10⁸, exact rational
  re-verification).

### 4. Erdős #97 — structural reduction + evidence  `p97/`
No counterexample to the k=4 version. New: deficit-counting over symmetry
types; exactly-square D_m schemes all fail convexity by an order-one margin;
reduction of the counterexample question to realizing an (m₄)-type point–line
incidence configuration inside a thin parabolic band; an exact algebraic
18-point unit-4-regular (non-convex) configuration; a verified 120-point
configuration with every vertex having exactly 4 unit-distance neighbours,
non-convex at 40/120 vertices. First quantitative evidence toward YES.

## Negative/aborted, with artifacts

### #617 (Erdős–Gyárfás balanced colourings, r = 5)  `p617/`
Aborted after novelty check: resolved during July 13–24, 2026 by four parallel
unrefereed AI/SAT efforts (see [STATUS.md](p617/STATUS.md)). Salvage: two
DRAT-verified lemmas (AG(2,5)-based K₂₅ colouring does not extend to K₂₆;
no 5 pair-disjoint ≤5-block partitions of a 26-set), encoding validated
against the explicit AG(2,5) construction.

### #106 (Erdős–Soifer square packing, k = 3)  `p106/`
Best certified-feasible 10-square packing: side-sum 2.9999861 (< 3); every
tilted start converged back to axis-parallel at machine precision
("tilt-repulsion") — evidence the conjecture is true.

### #647 (m + τ(m) ≤ n + 2 witness hunt)  `p647/` — see final report in this dir.

## Verification discipline
- Every SAT result: solver-independent replication and/or DRAT certificate
  checked with drat-trim.
- Every census/witness: ≥ 2 (usually 3–4) independent implementations.
- Every "new" claim: same-day literature search (which is how #617 was caught
  as already-resolved — the check exists to be failed).

## Provenance
All searches ran locally (M-series, 16 cores) on 2026-07-24. Code, witnesses,
certificates, and logs in the per-problem subdirectories. Nothing has been
posted, submitted, or claimed externally; OEIS submission drafts and
problem-page comment drafts await user review.
