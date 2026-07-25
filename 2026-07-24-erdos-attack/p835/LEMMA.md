# Lemma: no proper 11-coloring of J(20,10) has a symmetry of order 11

*Context: Erdős problem #835 (Erdős–Rosenfeld) — is χ(J(2k,k)) = k+1 for some k > 2?
First open case k = 10 (Ma–Tang rules out all k > 2 with k+1 not prime). 2026-07-24.*

**Theorem.** There is no pair (c, φ, π) where c is a proper 11-coloring of the Johnson
graph J(20,10), φ ∈ Aut(J(20,10)) has order 11, π is any permutation of the 11 colors,
and c(φA) = π(c(A)) for all vertices A. In particular no proper 11-coloring is
equivariant under any order-11 subgroup of S₂₀, and every AGL(1,11)-equivariant
ansatz is void a fortiori. (The k = 10 case itself remains open in both directions.)

**Computational core.** The C11-twisted system — colorings with
c(σA) = c(A) + 1 (mod 11), σ = (1 2 … 11) fixing 12…20 — is UNSATISFIABLE
(kissat 4.0.4; four independent configurations, 321–487 s each; DRAT certificate
`j20_10.drat` checked by drat-trim).

**Reduction of the theorem to the computation (three steps).**

1. *Conjugacy.* Aut(J(20,10)) ≅ S₂₀ × Z₂ (Z₂ = complementation). An order-11
   element has trivial Z₂-part, hence is g ∈ S₂₀ of order 11, i.e. a single 11-cycle
   with 9 fixed points (two 11-cycles need 22 > 20 points). All such g are conjugate
   to σ; replacing c by c∘h⁻¹ (h g h⁻¹ = σ) we may take φ = σ.
2. *Color action.* σ¹¹ = id gives π¹¹(c(A)) = c(A) for all A; since c uses all 11
   colors (J(20,10) contains 11-cliques, e.g. the one in step 3), π¹¹ = id in S₁₁,
   so π is either the identity or an 11-cycle on the colors.
3. *Two cases.* (a) π = id makes c constant on σ-orbits; but the σ-orbit
   {Aᵢ = {12,…,20} ∪ {i} : i = 1,…,11} is itself an 11-clique
   (any two Aᵢ, Aⱼ intersect in {12,…,20}, size 9), which would be monochromatic —
   contradiction. (b) π an 11-cycle: pick a bijection ψ from the colors to Z/11 with
   ψπψ⁻¹ = (+1); then ψ∘c is a proper coloring with (ψ∘c)(σA) = (ψ∘c)(A) + 1 —
   exactly the C11-twisted system, which is UNSAT. ∎

**Instance.** No 10-subset of [20] is σ-invariant, and 11 is prime, so all 184,756
vertices fall into 16,796 σ-orbits of size exactly 11. One base color x_O ∈ Z/11 per
orbit (c(σᵗ rep_O) = x_O + t). Each of the 9,237,800 edges reduces to a constraint
x_{O₁} − x_{O₂} ≠ δ (mod 11); same-orbit edges are automatically proper. Deduplication
leaves 837,240 triples (O₁, O₂, δ) → CNF with 184,756 one-hot variables and
10,150,217 clauses (plus unit x₀ = 0, sound by global color-shift symmetry).
Encoding validated: exhaustively on J(4,2)/C₃ (SAT, χ = 3 reproduced and
independently rainbow-verified), on J(8,4)/C₅ (UNSAT, matching independent
exhaustive DFS), and at k = 10 by exact identity #monochromatic-edges = 11 ×
#violated-triples for random assignments over all 9,237,800 edges.

**Reproduce.** In this directory:
`python3 gen.py calibrate && python3 gen.py 10 --symbreak` (≈3 s) →
`kissat j20_10.cnf j20_10.drat` (≈6 min, exit 20, `s UNSATISFIABLE`) →
`drat-trim j20_10.cnf j20_10.drat` (prints `s VERIFIED`).
