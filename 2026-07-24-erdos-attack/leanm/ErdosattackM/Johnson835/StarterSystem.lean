import Mathlib
/-!
# Starter systems of `Z₁₁` do not tile `K₁₀` nine times (Erdős #835, Stage 2)

The finite combinatorial heart of the Stage-2 proof that the `C₁₁`-twisted
coloring system for `J(20,10)` is unsatisfiable (`TwistedUnsat`).

A *row* is a choice, for each cyclic gap `γ ∈ {1, …, 5}`, of a pair
`{a, a + γ} ⊆ Z₁₁ ∖ {0}`; we record only the *start* `a` (a pair of gap
`γ ≤ 5` has a unique representative `(a, a + γ)`, since `γ ≠ -γ` in `Z₁₁`).
A row whose five pairs are pairwise disjoint is a **starter** of `Z₁₁` in the
classical design-theory sense (it perfectly matches the 10 points of
`Z₁₁ ∖ {0}`, one pair of each gap).

`starter_system_impossible` states that there is no `9 × 5` array
`s : Fin 9 → Fin 5 → Fin 11` of starts such that

* every pair avoids `0`  (`s k g ≠ 0` and `s k g + (g+1) ≠ 0`),
* every row is a starter (row pairs pairwise disjoint), and
* rows are pairwise edge-disjoint (same-gap starts differ across rows,
  which for equal gaps is the same as the pairs differing).

**Proof (mod-3 count).** Weight a pair `(a, a + γ)` by `1` if it lies in the
ratio-`{5,9}` class (`a + γ = 5·a` or `a = 5·(a + γ)` in `Z₁₁`), else `0`.

1. `starter_row_count`: every starter has total weight `0` or `3`
   (exhaustive check — `decide` over the pruned `11⁵` search tree; only
   25 starters survive the constraints).
2. For each gap `g` there are exactly `9` valid starts, and the `9` rows use
   `9` distinct ones — so column `g` uses *every* valid start exactly once
   (injective into a finite set of the same cardinality).  Hence the total
   weight of the array is the total weight of *all* valid `(a, g)`, which is
   `10` (`total_weight`, by `decide`).
3. `3 ∣ (sum of row weights) = 10` — contradiction.
-/

namespace ErdosattackM
namespace Johnson835

/-- The gap value `g + 1 ∈ {1, …, 5}` of a gap index `g : Fin 5`, as an
element of `Z₁₁ = Fin 11`. -/
def gapv (g : Fin 5) : Fin 11 := ⟨g.1 + 1, by omega⟩

/-- The pair started at `a` with gap `g` is disjoint from the pair started
at `b` with gap `g'`: all four endpoint comparisons fail. -/
def PairDisj (a : Fin 11) (g : Fin 5) (b : Fin 11) (g' : Fin 5) : Prop :=
  a ≠ b ∧ a ≠ b + gapv g' ∧ a + gapv g ≠ b ∧ a + gapv g ≠ b + gapv g'

instance (a : Fin 11) (g : Fin 5) (b : Fin 11) (g' : Fin 5) :
    Decidable (PairDisj a g b g') := by unfold PairDisj; infer_instance

/-- Weight of the pair `(a, a + gapv g)`: `1` if it is a ratio-`{5,9}` pair
of `Z₁₁` (i.e. one endpoint is `5` times the other; note `9 = 5⁻¹`), else
`0`. -/
def rWeight (a : Fin 11) (g : Fin 5) : ℕ :=
  if a + gapv g = 5 * a ∨ a = 5 * (a + gapv g) then 1 else 0

/-! ### Small facts about gap values, by `decide` -/

lemma gapv_ne_zero (g : Fin 5) : gapv g ≠ 0 := by decide +kernel +revert

lemma zero_ne_gapv (g : Fin 5) : (0 : Fin 11) ≠ gapv g := by decide +kernel +revert

lemma gapv_injective : ∀ g g' : Fin 5, gapv g = gapv g' → g = g' := by decide +kernel

lemma gapv_add_gapv_ne_zero (g g' : Fin 5) : gapv g + gapv g' ≠ 0 := by
  decide +kernel +revert

/-- Adding a gap value moves every point of `Z₁₁`. -/
lemma add_gapv_ne (a : Fin 11) (g : Fin 5) : a + gapv g ≠ a := by
  intro h
  have h0 : a + gapv g = a + 0 := by rwa [add_zero]
  exact gapv_ne_zero g (add_left_cancel h0)

/-! ### The two exhaustive checks -/

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
/-- **Starter lemma** (exhaustive check): a starter — five pairwise disjoint
pairs `(aᵢ, aᵢ + i)` in `Z₁₁ ∖ {0}`, one of each gap `1, …, 5` — contains
either `0` or exactly `3` ratio-`{5,9}` pairs.  (There are exactly 25
starters; the hypotheses prune the `11⁵` search tree.) -/
private lemma starter_row_count :
    ∀ a₀ : Fin 11, a₀ ≠ 0 → a₀ + gapv 0 ≠ 0 →
    ∀ a₁ : Fin 11, a₁ ≠ 0 → a₁ + gapv 1 ≠ 0 → PairDisj a₀ 0 a₁ 1 →
    ∀ a₂ : Fin 11, a₂ ≠ 0 → a₂ + gapv 2 ≠ 0 → PairDisj a₀ 0 a₂ 2 →
      PairDisj a₁ 1 a₂ 2 →
    ∀ a₃ : Fin 11, a₃ ≠ 0 → a₃ + gapv 3 ≠ 0 → PairDisj a₀ 0 a₃ 3 →
      PairDisj a₁ 1 a₃ 3 → PairDisj a₂ 2 a₃ 3 →
    ∀ a₄ : Fin 11, a₄ ≠ 0 → a₄ + gapv 4 ≠ 0 → PairDisj a₀ 0 a₄ 4 →
      PairDisj a₁ 1 a₄ 4 → PairDisj a₂ 2 a₄ 4 → PairDisj a₃ 3 a₄ 4 →
    rWeight a₀ 0 + rWeight a₁ 1 + rWeight a₂ 2 + rWeight a₃ 3 + rWeight a₄ 4
        = 0 ∨
    rWeight a₀ 0 + rWeight a₁ 1 + rWeight a₂ 2 + rWeight a₃ 3 + rWeight a₄ 4
        = 3 := by
  decide +kernel

/-- The valid starts for gap `g`: starts of `0`-avoiding pairs. -/
private def validStarts (g : Fin 5) : Finset (Fin 11) :=
  Finset.univ.filter fun a => a ≠ 0 ∧ a + gapv g ≠ 0

/-- For each gap there are exactly `9` valid starts (`0`-avoiding pairs). -/
private lemma card_validStarts (g : Fin 5) : (validStarts g).card = 9 := by
  revert g; decide +kernel

set_option maxHeartbeats 1000000 in
/-- Total ratio-`{5,9}` weight of all valid `(start, gap)` positions: the 45
`0`-avoiding pairs of `Z₁₁` contain exactly `10` ratio-`{5,9}` pairs. -/
private lemma total_weight :
    ∑ g : Fin 5, ∑ a ∈ validStarts g, rWeight a g = 10 := by
  decide +kernel

/-! ### The impossibility theorem -/

set_option maxHeartbeats 1000000 in
/-- **No 9-row starter system in `Z₁₁`** (the finite heart of `TwistedUnsat`):
there is no array `s : Fin 9 → Fin 5 → Fin 11` of pair-starts such that all
pairs avoid `0`, each row is a starter (pairwise disjoint pairs, one per
gap), and rows are pairwise edge-disjoint (same-gap starts differ).

Mod-3 count: each row contributes `0` or `3` ratio-`{5,9}` pairs
(`starter_row_count`), while edge-disjointness forces the 9 rows to cover
each of the 45 `0`-avoiding pairs exactly once — total `10 ≢ 0 (mod 3)`. -/
theorem starter_system_impossible :
    ¬ ∃ s : Fin 9 → Fin 5 → Fin 11,
      (∀ k g, s k g ≠ 0) ∧
      (∀ k g, s k g + gapv g ≠ 0) ∧
      (∀ k g g', g ≠ g' → PairDisj (s k g) g (s k g') g') ∧
      (∀ k k' g, k ≠ k' → s k g ≠ s k' g) := by
  rintro ⟨s, h1, h2, h3, h4⟩
  -- Row counts: every row is a starter, so its weight is 0 or 3.
  have hrow : ∀ k, (∑ g : Fin 5, rWeight (s k g) g) = 0 ∨
      (∑ g : Fin 5, rWeight (s k g) g) = 3 := by
    intro k
    have h := starter_row_count
      (s k 0) (h1 k 0) (h2 k 0)
      (s k 1) (h1 k 1) (h2 k 1) (h3 k 0 1 (by decide))
      (s k 2) (h1 k 2) (h2 k 2) (h3 k 0 2 (by decide)) (h3 k 1 2 (by decide))
      (s k 3) (h1 k 3) (h2 k 3) (h3 k 0 3 (by decide)) (h3 k 1 3 (by decide))
        (h3 k 2 3 (by decide))
      (s k 4) (h1 k 4) (h2 k 4) (h3 k 0 4 (by decide)) (h3 k 1 4 (by decide))
        (h3 k 2 4 (by decide)) (h3 k 3 4 (by decide))
    rwa [Fin.sum_univ_five]
  -- Column sums: for each gap, the 9 rows use each of the 9 valid starts
  -- exactly once.
  have hcol : ∀ g : Fin 5, (∑ k : Fin 9, rWeight (s k g) g) =
      ∑ a ∈ validStarts g, rWeight a g := by
    intro g
    have hinj : Function.Injective fun k => s k g :=
      fun k k' h => by_contra fun hne => h4 k k' g hne h
    have himg : (Finset.univ.image fun k => s k g) = validStarts g := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
        simp only [validStarts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h1 k g, h2 k g⟩
      · rw [Finset.card_image_of_injective _ hinj, card_validStarts,
          Finset.card_univ, Fintype.card_fin]
    rw [← himg, Finset.sum_image fun k _ k' _ h => hinj h]
  -- Total weight is 10 …
  have hsum : (∑ k : Fin 9, ∑ g : Fin 5, rWeight (s k g) g) = 10 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun g _ => hcol g]
    exact total_weight
  -- … but it is divisible by 3.
  have hdvd : (3 : ℕ) ∣ ∑ k : Fin 9, ∑ g : Fin 5, rWeight (s k g) g :=
    Finset.dvd_sum fun k _ => by rcases hrow k with h | h <;> simp [h]
  rw [hsum] at hdvd
  omega

end Johnson835
end ErdosattackM
