# Erdős problem attack — 2026-07-24

Autonomous session ("do a breakthrough"): portfolio attack on open Erdős
problems flagged in [Tao's database](https://github.com/teorth/erdosproblems) as
resolvable-in-principle by finite computation, plus structured mathematical
analysis. Six problems attacked in parallel; every claim below was verified by
at least one independent implementation, and novelty was checked against the
literature the same day.

## New results (believed novel as of 2026-07-24)

### 1. Erdős #835 → a new design-theory theorem  `p835/`
**Update (same night):** a March 2026 forum comment closes k = 10 and k = 12
outright (Steiner large-set argument: χ(J(20,10)) ≥ 12, χ(J(24,12)) ≥ 14), so
for #835 itself the theorem below is subsumed; the problem's real frontier is
k = 16 (tied to the open S(4,5,21)). What survives as new mathematics
([PROOF.md](p835/PROOF.md)): **Z₁₁ admits at most 7 pairwise disjoint starters — no
golf design of order 11 is cyclic** (refines Colbourn–Nonay 1997; human
mod-3 proof extracted from the SAT core, Lean formalization in progress),
plus the starter ↔ Johnson-colouring technique now aimed at k = 16 / Z₁₇.
Original result as found:
**Theorem (computer-proved, DRAT-certified).** No proper 11-colouring of the
Johnson graph J(20,10) admits a symmetry of order 11 — i.e. for every order-11
element g of Aut(J(20,10)) and every colour-permutation π with π∘colour =
colour∘g, no proper 11-colouring exists. Consequently, if χ(J(20,10)) = 11
(the first open case k = 10 = 11−1 of Erdős–Rosenfeld #835, the only k ≤ 10
not excluded by Ma–Tang), every witness colouring is 11-asymmetric — ruling
out the natural algebraic/equivariant constructions suggested by the
Ma–Tang "k = p−1" pattern.
Method: C₁₁ regular-twist equivariant SAT (184,756 vertices → 16,796 orbits;
10.2M clauses; UNSAT replicated by 5 solver runs; pipeline validated in both
directions on J(4,2) (SAT, χ=3 reproduced) and J(8,4) (UNSAT, matches known
χ>5)). **DRAT certificate formally verified** (drat-trim `s VERIFIED`, 659 MB
proof, 85-min check; core only 51,283/10,150,217 clauses — a compact
human-readable mod-11 obstruction likely exists; see [p835/LEMMA.md](p835/LEMMA.md)).
Weak positive signal recorded: random 40k-vertex induced subgraphs of
J(20,10) are 11-colourable in seconds.

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

**Lean-certified** (`lean/`, `leanm/`): for every census tree it is a
kernel-checked theorem — sorry-free, standard axioms only, no `native_decide`
— that the tree has exactly N_k independent vertex subsets of each size k
(subset-counting semantics via the verified DP correctness theorem
`indepPolyRT_correct`), and that this sequence is non-log-concave yet
unimodal. Apparently the first formally verified independence polynomials
of trees.

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

### #647 (m + τ(m) ≤ n + 2 witness hunt)  `p647/`
No witness: **no n in (24, 3.5×10¹²] satisfies the condition** (direct,
assumption-free segmented τ-sieve at ~0.7×10⁹ values/s; rigorous warm-start
argument via τ(m) ≤ 2√m; 7 independent cross-checks). Extends the OEIS-recorded
direct-sieve frontier (10¹², Idén 2026) by 3.5×. Also independently audited
Hughes's unpublished reduction certificate (erdos647-proof-chain): its
dependency-free verifier passes 30/30 here, pushing corroborated non-existence
to ~6.16×10¹⁷ (with stated trust gaps). Witness hunters should expect nothing
below that.

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
