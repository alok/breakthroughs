# A human proof: no proper 11-colouring of J(20,10) admits an order-11 symmetry

**Theorem.** Let J(20,10) be the Johnson graph (vertices: 10-subsets of a
20-set; edges: pairs meeting in 9 points). No proper 11-colouring of J(20,10)
commutes with any order-11 symmetry of the natural S₂₀×Z₂ action, under any
permutation of the colours.

This rules out all algebraic/equivariant constructions for the first open case
(k = 10) of Erdős problem #835 (Erdős–Rosenfeld: is χ(J(2k,k)) = k+1 for some
k > 2?). Discovered via SAT (5× UNSAT + DRAT `s VERIFIED`), then extracted
into the argument below by UNSAT-core minimization; every finite enumeration
was verified by two independent implementations.

## Proof

**Reduction (Lean-formalized in `leanm/ErdosattackM/Johnson835/`).** An
order-11 element of S₂₀×Z₂ has trivial complement part (11 is odd) and is a
single 11-cycle σ on the ground set (cycle type in S₂₀: parts ∈ {1,11},
lcm 11, sum ≤ 20). The colour permutation π satisfies π¹¹ = id on the image
of the colouring, which is all 11 colours: the σ-orbit of A₀ = F ∪ {0} —
where C = supp σ = {0,…,10} (renaming) and F = the 9 fixed points — is an
11-clique {Aᵢ = F ∪ {i}}. If π = id the clique orbit is monochromatic,
contradiction; otherwise π is an 11-cycle and, after relabelling colours,
the colouring c satisfies the *twist* c(σA) = c(A) + 1 (mod 11).

**Normalization.** Colours shift so that c(F ∪ {i}) = i (consistent with the
twist along the clique orbit).

**The starter system.** Work in Z₁₁ = the cycle coordinates of C. For each
f ∈ F and gap g ∈ {1,…,5}, the σ-orbit of (F∖{f}) ∪ {0,g} has exactly one
member of each colour (twist); let its colour-0 member be (F∖{f}) ∪ D_{f,g},
where D_{f,g} ⊂ Z₁₁ is a pair of cyclic gap g. Properness forces:

1. **0 ∉ D_{f,g}**: the vertex (F∖{f}) ∪ D is adjacent to F ∪ {d} for each
   d ∈ D (they share 9 points), and c(F ∪ {d}) = d, so d ≠ 0.
2. **Rows are matchings**: for fixed f, the pairs D_{f,1},…,D_{f,5} are
   pairwise disjoint (two colour-0 vertices sharing F∖{f} and one cycle point
   meet in 9 points — adjacent, same colour: impossible). Five disjoint
   pairs in Z₁₁∖{0} (10 points), one of each gap: each row is a **starter**
   of Z₁₁ in the classical design-theory sense.
3. **Rows are edge-disjoint**: for f ≠ f′, D_{f,g} ≠ D_{f′,g}
   ((F∖{f}) ∪ D and (F∖{f′}) ∪ D meet in 9 points). Since a pair determines
   its gap, the 9 rows are pairwise edge-disjoint matchings.

For each gap g there are exactly 9 pairs avoiding 0, and the 9 rows use 9
distinct ones — so the rows use *every* pair exactly once: **a twisted proper
colouring yields a partition of the 45 edges of K₁₀ (on Z₁₁∖{0}) into 9
starters.**

**The mod-3 count.** Classify edges {a,b} of K₁₀ by the ratio b·a⁻¹ mod 11 up
to inversion: classes {2,6}, {3,4}, {5,9}, {7,8}, {10} of sizes
10, 10, 10, 10, 5. Z₁₁ has exactly **25 starters**; each contains either 0 or
exactly **3** edges of ratio-class {5,9} (exhaustive check over the 25).
Nine disjoint starters therefore cover ≡ 0 (mod 3) edges of that class — but
they must cover all **10**. Since 10 ≢ 0 (mod 3), no such partition exists. ∎

## Verification record

- 25 starters, class sizes (10,10,10,10,5), per-starter {5,9}-counts
  ∈ {0,3} with distribution 15×0 + 10×3, and failure of the direct
  exact-cover search: verified by two independent implementations
  ([verify_starters.py](verify_starters.py) here, plus the discovery agent's).
- The 41-orbit kernel (clique orbit + 8 rows) is minimal: 7 rows + clique is
  SAT; dropping any gap column or the clique orbit is SAT.
- Sanity at other primes: p = 5 has 1 starter (< 3 rows needed) and p = 7 has
  3 starters with no K₆ partition — consistent with the *known* falsity of
  k = 4, 6. **At p = 13 the obstruction vanishes: K₁₂ does partition into 11
  Z₁₃-starters** — see the k = 12 attack.

## Consequences

- Any proper 11-colouring of J(20,10), if one exists, is 11-asymmetric.
- The analogous C₁₃-symmetric route to χ(J(24,12)) = 13 (the *next* open case
  k = 12) is **not** blocked at the starter level — an explicit starter
  partition of K₁₂ exists and can seed a construction.
