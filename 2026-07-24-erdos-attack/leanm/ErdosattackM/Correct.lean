import ErdosattackM.Basic
/-!
# Semantic correctness of the rose-tree independence DP

Main theorem: `indepPolyRT_correct` — coefficient `k` of `indepPolyRT t` is
the number of independent `k`-subsets of the vertex set of `t`
(`RT.indepCount t k`).

Strategy: strengthen to the pair statement `dpA_getD` / `dpB_getD` —
`dpA` counts independent sets containing the root, `dpB` those avoiding it —
and induct on the rose-tree structure. The two workhorses are:

* `mulPoly_getD` — `mulPoly` is convolution on coefficients;
* `card_split` — a subset of `range (m + s)` decomposes uniquely as a
  subset of `range m` (`low`) plus a shifted subset of `range s` (`high`),
  turning a filtered `powersetCard` count into a convolution of two counts.

The contiguous-interval labelling of `RT.edges` was designed so that for a
forest `c :: F` the block of `c` is exactly `[m, m + size c)` with
`m = sizeF F + 1`, which makes `card_split` apply verbatim.
-/

namespace ErdosattackM

open Finset
open Finset.HasAntidiagonal (antidiagonal)

/-! ### Coefficient extraction for the polynomial operations -/

theorem addPoly_getD (p q : List Nat) (k : Nat) :
    (addPoly p q).getD k 0 = p.getD k 0 + q.getD k 0 := by
  induction p generalizing q k with
  | nil => simp [addPoly]
  | cons a p ih =>
    cases q with
    | nil => simp [addPoly]
    | cons b q =>
      cases k with
      | zero => simp [addPoly]
      | succ k => simpa [addPoly] using ih q k

theorem getD_map_mul (a : Nat) (q : List Nat) (k : Nat) :
    (q.map (a * ·)).getD k 0 = a * q.getD k 0 := by
  induction q generalizing k with
  | nil => simp
  | cons b q ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih k

/-- `mulPoly` is convolution on coefficients. -/
theorem mulPoly_getD (p q : List Nat) (k : Nat) :
    (mulPoly p q).getD k 0 =
      ∑ ij ∈ antidiagonal k, p.getD ij.1 0 * q.getD ij.2 0 := by
  induction p generalizing k with
  | nil => simp [mulPoly]
  | cons a p ih =>
    rw [show mulPoly (a :: p) q = addPoly (q.map (a * ·)) (0 :: mulPoly p q) from rfl]
    rw [addPoly_getD, getD_map_mul]
    cases k with
    | zero => simp
    | succ k =>
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih k]

/-! ### Independence over edge lists -/

theorem indepIn_nil (S : Finset ℕ) : IndepIn [] S := by
  intro e he
  simp at he

theorem indepIn_append {E₁ E₂ : List (Nat × Nat)} {S : Finset ℕ} :
    IndepIn (E₁ ++ E₂) S ↔ IndepIn E₁ S ∧ IndepIn E₂ S := by
  unfold IndepIn
  exact List.forall_mem_append

/-- Cons form with an explicit pair, so the endpoints appear reduced. -/
theorem indepIn_cons {a b : Nat} {E : List (Nat × Nat)} {S : Finset ℕ} :
    IndepIn ((a, b) :: E) S ↔ ¬(a ∈ S ∧ b ∈ S) ∧ IndepIn E S := by
  unfold IndepIn
  exact List.forall_mem_cons

/-! ### The `low`/`high` decomposition of subsets of `range (m + s)` -/

/-- The part of `S` below the cut `m`. -/
def low (m : Nat) (S : Finset ℕ) : Finset ℕ := S.filter (· < m)

/-- The part of `S` at or above the cut `m`, shifted down by `m`. -/
def high (m : Nat) (S : Finset ℕ) : Finset ℕ :=
  (S.filter fun x => m ≤ x).image (· - m)

theorem mem_low {S : Finset ℕ} {m v : Nat} (hv : v < m) :
    v ∈ low m S ↔ v ∈ S := by
  simp [low, hv]

theorem mem_high {S : Finset ℕ} {m v : Nat} :
    v ∈ high m S ↔ v + m ∈ S := by
  simp only [high, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨hyS, hmy⟩, rfl⟩
    rwa [Nat.sub_add_cancel hmy]
  · intro h
    exact ⟨v + m, ⟨h, Nat.le_add_left m v⟩, by omega⟩

theorem mem_high_zero {S : Finset ℕ} {m : Nat} : 0 ∈ high m S ↔ m ∈ S := by
  simpa using mem_high (S := S) (m := m) (v := 0)

theorem indepIn_low {E : List (Nat × Nat)} {S : Finset ℕ} {m : Nat}
    (hE : ∀ e ∈ E, e.1 < m ∧ e.2 < m) :
    IndepIn E (low m S) ↔ IndepIn E S := by
  unfold IndepIn
  refine forall_congr' fun e => imp_congr_right fun he => not_congr (and_congr ?_ ?_)
  · exact mem_low (hE e he).1
  · exact mem_low (hE e he).2

theorem indepIn_shift {E : List (Nat × Nat)} {S : Finset ℕ} {m : Nat} :
    IndepIn (shiftEdges m E) S ↔ IndepIn E (high m S) := by
  unfold IndepIn shiftEdges
  rw [List.forall_mem_map]
  refine forall_congr' fun e => imp_congr_right fun he => not_congr (and_congr ?_ ?_)
  · exact mem_high.symm
  · exact mem_high.symm

theorem low_subset_range (m : Nat) (S : Finset ℕ) : low m S ⊆ Finset.range m :=
  fun _ hx => Finset.mem_range.2 (Finset.mem_filter.1 hx).2

theorem high_subset_range {m s : Nat} {S : Finset ℕ}
    (hS : S ⊆ Finset.range (m + s)) : high m S ⊆ Finset.range s := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨hyS, hmy⟩ := Finset.mem_filter.1 hy
  have := Finset.mem_range.1 (hS hyS)
  exact Finset.mem_range.2 (by omega)

theorem card_high (m : Nat) (S : Finset ℕ) :
    (high m S).card = (S.filter fun x => m ≤ x).card := by
  refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
  have hx' := (Finset.mem_filter.1 hx).2
  have hy' := (Finset.mem_filter.1 hy).2
  omega

theorem card_low_add_card_high (m : Nat) (S : Finset ℕ) :
    (low m S).card + (high m S).card = S.card := by
  rw [card_high]
  have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => x < m)
  simp only [Nat.not_lt] at h
  exact h

theorem union_low_high (m : Nat) (S : Finset ℕ) :
    low m S ∪ (high m S).image (· + m) = S := by
  have himg : (high m S).image (· + m) = S.filter fun x => m ≤ x := by
    rw [high, Finset.image_image]
    have : ∀ x ∈ S.filter fun x => m ≤ x, ((· + m) ∘ (· - m)) x = id x := by
      intro x hx
      have := (Finset.mem_filter.1 hx).2
      simp [Function.comp, Nat.sub_add_cancel this]
    rw [Finset.image_congr this, Finset.image_id]
  rw [himg]
  have h := Finset.filter_union_filter_not_eq (fun x => x < m) S
  simp only [Nat.not_lt] at h
  exact h

theorem low_union_shift {m : Nat} {S₁ S₂ : Finset ℕ} (h₁ : S₁ ⊆ Finset.range m) :
    low m (S₁ ∪ S₂.image (· + m)) = S₁ := by
  rw [low, Finset.filter_union]
  have hl : S₁.filter (· < m) = S₁ :=
    Finset.filter_true_of_mem fun x hx => Finset.mem_range.1 (h₁ hx)
  have hr : (S₂.image (· + m)).filter (· < m) = ∅ := by
    refine Finset.filter_false_of_mem fun x hx => ?_
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx
    omega
  rw [hl, hr, Finset.union_empty]

theorem high_union_shift {m : Nat} {S₁ S₂ : Finset ℕ} (h₁ : S₁ ⊆ Finset.range m) :
    high m (S₁ ∪ S₂.image (· + m)) = S₂ := by
  rw [high, Finset.filter_union]
  have hl : S₁.filter (fun x => m ≤ x) = ∅ := by
    refine Finset.filter_false_of_mem fun x hx => ?_
    have := Finset.mem_range.1 (h₁ hx)
    omega
  have hr : (S₂.image (· + m)).filter (fun x => m ≤ x) = S₂.image (· + m) := by
    refine Finset.filter_true_of_mem fun x hx => ?_
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx
    omega
  rw [hl, hr, Finset.empty_union, Finset.image_image]
  have : ∀ x ∈ S₂, ((· - m) ∘ (· + m)) x = id x := by
    intro x _
    simp
  rw [Finset.image_congr this, Finset.image_id]

theorem union_shift_subset {m s : Nat} {S₁ S₂ : Finset ℕ}
    (h₁ : S₁ ⊆ Finset.range m) (h₂ : S₂ ⊆ Finset.range s) :
    S₁ ∪ S₂.image (· + m) ⊆ Finset.range (m + s) := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · have := Finset.mem_range.1 (h₁ h)
    exact Finset.mem_range.2 (by omega)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
    have := Finset.mem_range.1 (h₂ hy)
    exact Finset.mem_range.2 (by omega)

theorem card_union_shift {m : Nat} {S₁ S₂ : Finset ℕ} (h₁ : S₁ ⊆ Finset.range m) :
    (S₁ ∪ S₂.image (· + m)).card = S₁.card + S₂.card := by
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (add_left_injective m)]
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx'
  have := Finset.mem_range.1 (h₁ hx)
  omega

/-! ### The splitting identity -/

/-- **Splitting a filtered `powersetCard` count at a cut `m`.**
If, on `k`-subsets of `range (m + s)`, the predicate `R` is equivalent to
`P` on the part below `m` and `Q` on the (shifted) part above, then the
number of `k`-subsets satisfying `R` is the convolution of the `P`- and
`Q`-counts. -/
theorem card_split (m s k : Nat) (P Q R : Finset ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hR : ∀ S ∈ (Finset.range (m + s)).powersetCard k,
      (R S ↔ P (low m S) ∧ Q (high m S))) :
    (((Finset.range (m + s)).powersetCard k).filter R).card
      = ∑ ij ∈ antidiagonal k,
          (((Finset.range m).powersetCard ij.1).filter P).card
            * (((Finset.range s).powersetCard ij.2).filter Q).card := by
  classical
  have hfib : Set.MapsTo (fun S => ((low m S).card, (high m S).card))
      ↑(((Finset.range (m + s)).powersetCard k).filter R) ↑(antidiagonal k) := by
    intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hS
    obtain ⟨hSp, _⟩ := hS
    obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.1 hSp
    simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal]
    rw [card_low_add_card_high, hcard]
  rw [Finset.card_eq_sum_card_fiberwise hfib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun S _ => (low m S, high m S))
      (fun T _ => T.1 ∪ T.2.image (· + m)) ?_ ?_ ?_ ?_
  · -- forward map lands in the product
    intro S hS
    simp only [Finset.mem_filter] at hS
    obtain ⟨⟨hSp, hRS⟩, hfz⟩ := hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 hSp
    rw [Prod.mk.injEq] at hfz
    obtain ⟨hPQ₁, hPQ₂⟩ := (hR S hSp).1 hRS
    rw [Finset.mem_product]
    constructor
    · exact Finset.mem_filter.2
        ⟨Finset.mem_powersetCard.2 ⟨low_subset_range m S, hfz.1⟩, hPQ₁⟩
    · exact Finset.mem_filter.2
        ⟨Finset.mem_powersetCard.2 ⟨high_subset_range hsub, hfz.2⟩, hPQ₂⟩
  · -- backward map lands in the fiber
    intro T hT
    rw [Finset.mem_product] at hT
    obtain ⟨hT₁, hT₂⟩ := hT
    obtain ⟨hp₁, hP⟩ := Finset.mem_filter.1 hT₁
    obtain ⟨hp₂, hQ⟩ := Finset.mem_filter.1 hT₂
    obtain ⟨hsub₁, hcard₁⟩ := Finset.mem_powersetCard.1 hp₁
    obtain ⟨hsub₂, hcard₂⟩ := Finset.mem_powersetCard.1 hp₂
    have hlow := low_union_shift (S₂ := T.2) hsub₁
    have hhigh := high_union_shift (S₂ := T.2) hsub₁
    have hpow : T.1 ∪ T.2.image (· + m) ∈ (Finset.range (m + s)).powersetCard k := by
      refine Finset.mem_powersetCard.2 ⟨union_shift_subset hsub₁ hsub₂, ?_⟩
      rw [card_union_shift hsub₁, hcard₁, hcard₂, hij]
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hpow, ?_⟩, ?_⟩
    · exact (hR _ hpow).2 (by rw [hlow, hhigh]; exact ⟨hP, hQ⟩)
    · rw [hlow, hhigh, hcard₁, hcard₂]
  · -- left inverse
    intro S _
    exact union_low_high m S
  · -- right inverse
    intro T hT
    rw [Finset.mem_product] at hT
    obtain ⟨hT₁, _⟩ := hT
    obtain ⟨hp₁, _⟩ := Finset.mem_filter.1 hT₁
    obtain ⟨hsub₁, _⟩ := Finset.mem_powersetCard.1 hp₁
    rw [low_union_shift (S₂ := T.2) hsub₁, high_union_shift (S₂ := T.2) hsub₁]

/-! ### Count decompositions -/

theorem icount_eq_root_add_noRoot (n k : Nat) (E : List (Nat × Nat)) :
    icount n k E = icountRoot n k E + icountNoRoot n k E := by
  unfold icount icountRoot icountNoRoot
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact (Finset.card_filter_add_card_filter_not (fun S => (0 : ℕ) ∈ S)).symm

/-- The root-containing count of a graph `root ∪ block(E₁) ∪ shifted block(E₂)`
with the extra edge `(m, 0)`: the root forbids the head of the high block. -/
theorem icountRoot_step (m s : Nat) (hm : 0 < m) (E₁ E₂ : List (Nat × Nat))
    (hE₁ : ∀ e ∈ E₁, e.1 < m ∧ e.2 < m) (k : Nat) :
    icountRoot (m + s) k (E₁ ++ ((m, 0) :: shiftEdges m E₂))
      = ∑ ij ∈ antidiagonal k, icountRoot m ij.1 E₁ * icountNoRoot s ij.2 E₂ := by
  unfold icountRoot icountNoRoot
  refine card_split m s k (fun X => IndepIn E₁ X ∧ 0 ∈ X)
      (fun Y => IndepIn E₂ Y ∧ 0 ∉ Y) _ ?_
  intro S _
  rw [indepIn_append, indepIn_cons, indepIn_shift,
    indepIn_low hE₁ (S := S), mem_low (S := S) hm, mem_high_zero]
  tauto

/-- The root-avoiding count: the extra edge `(m, 0)` is vacuous, so the high
block contributes all of its independent sets. -/
theorem icountNoRoot_step (m s : Nat) (hm : 0 < m) (E₁ E₂ : List (Nat × Nat))
    (hE₁ : ∀ e ∈ E₁, e.1 < m ∧ e.2 < m) (k : Nat) :
    icountNoRoot (m + s) k (E₁ ++ ((m, 0) :: shiftEdges m E₂))
      = ∑ ij ∈ antidiagonal k, icountNoRoot m ij.1 E₁ * icount s ij.2 E₂ := by
  unfold icount icountNoRoot
  refine card_split m s k (fun X => IndepIn E₁ X ∧ 0 ∉ X)
      (fun Y => IndepIn E₂ Y) _ ?_
  intro S _
  rw [indepIn_append, indepIn_cons, indepIn_shift,
    indepIn_low hE₁ (S := S), mem_low (S := S) hm]
  tauto

/-! ### Base cases: the single-vertex tree -/

theorem icountRoot_one (k : Nat) : icountRoot 1 k [] = [0, 1].getD k 0 := by
  match k with
  | 0 =>
    unfold icountRoot
    rw [Finset.powersetCard_zero, Finset.filter_singleton]
    simp
  | 1 =>
    unfold icountRoot
    rw [Finset.range_one,
      show ({0} : Finset ℕ).powersetCard 1 = {{0}} from by
        simpa using Finset.powersetCard_self ({0} : Finset ℕ),
      Finset.filter_singleton]
    simp [indepIn_nil]
  | (k + 2) =>
    unfold icountRoot
    rw [Finset.powersetCard_eq_empty.2 (by simp)]
    simp

theorem icountNoRoot_one (k : Nat) : icountNoRoot 1 k [] = [1].getD k 0 := by
  match k with
  | 0 =>
    unfold icountNoRoot
    rw [Finset.powersetCard_zero, Finset.filter_singleton]
    simp [indepIn_nil]
  | (k + 1) =>
    unfold icountNoRoot
    have : ((Finset.range 1).powersetCard (k + 1)).filter
        (fun S => IndepIn [] S ∧ 0 ∉ S) = ∅ := by
      cases k with
      | zero =>
        rw [Finset.range_one,
          show ({0} : Finset ℕ).powersetCard (0 + 1) = {{0}} from by
            simpa using Finset.powersetCard_self ({0} : Finset ℕ),
          Finset.filter_singleton]
        simp
      | succ k =>
        rw [Finset.powersetCard_eq_empty.2 (by simp)]
        exact Finset.filter_empty _
    rw [this]
    simp

/-! ### Edge-endpoint bounds -/

theorem RT.size_pos (t : RT) : 0 < t.size := by
  cases t with
  | node cs => rw [RT.size]; omega

mutual
theorem RT.edges_lt : ∀ (t : RT), ∀ e ∈ t.edges, e.1 < t.size ∧ e.2 < t.size
  | .node cs => by
    rw [RT.edges, RT.size]
    exact RT.edgesF_lt cs
theorem RT.edgesF_lt : ∀ (F : List RT),
    ∀ e ∈ RT.edgesF F, e.1 < RT.sizeF F + 1 ∧ e.2 < RT.sizeF F + 1
  | [] => by
    rw [RT.edgesF]
    intro e he
    simp at he
  | c :: F => by
    intro e he
    rw [RT.edgesF] at he
    rw [RT.sizeF]
    have hc := RT.size_pos c
    rcases List.mem_append.1 he with h | h
    · have := RT.edgesF_lt F e h
      omega
    · rcases List.mem_cons.1 h with h' | h'
      · subst h'
        constructor <;> simp
        omega
      · obtain ⟨e', he', rfl⟩ := List.mem_map.1 h'
        have := RT.edges_lt c e' he'
        constructor <;> simp <;> omega
end

/-! ### The main induction -/

mutual
/-- `dpA` counts independent sets **containing** the root. -/
theorem dpA_getD : ∀ (t : RT) (k : Nat),
    t.dpA.getD k 0 = icountRoot t.size k t.edges
  | .node cs, k => by
    rw [RT.dpA, RT.size, RT.edges]
    exact dpAF_getD cs k

/-- `dpB` counts independent sets **avoiding** the root. -/
theorem dpB_getD : ∀ (t : RT) (k : Nat),
    t.dpB.getD k 0 = icountNoRoot t.size k t.edges
  | .node cs, k => by
    rw [RT.dpB, RT.size, RT.edges]
    exact dpBF_getD cs k

theorem dpAF_getD : ∀ (F : List RT) (k : Nat),
    (RT.dpAF F).getD k 0 = icountRoot (RT.sizeF F + 1) k (RT.edgesF F)
  | [], k => by
    rw [RT.dpAF, RT.sizeF, RT.edgesF]
    exact (icountRoot_one k).symm
  | c :: F, k => by
    rw [RT.dpAF, RT.edgesF, mulPoly_getD]
    have hn : RT.sizeF (c :: F) + 1 = (RT.sizeF F + 1) + c.size := by
      rw [RT.sizeF]; omega
    rw [hn, icountRoot_step (RT.sizeF F + 1) c.size (Nat.succ_pos _)
      (RT.edgesF F) c.edges (RT.edgesF_lt F) k]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [dpAF_getD F ij.1, dpB_getD c ij.2]

theorem dpBF_getD : ∀ (F : List RT) (k : Nat),
    (RT.dpBF F).getD k 0 = icountNoRoot (RT.sizeF F + 1) k (RT.edgesF F)
  | [], k => by
    rw [RT.dpBF, RT.sizeF, RT.edgesF]
    exact (icountNoRoot_one k).symm
  | c :: F, k => by
    rw [RT.dpBF, RT.edgesF, mulPoly_getD]
    have hn : RT.sizeF (c :: F) + 1 = (RT.sizeF F + 1) + c.size := by
      rw [RT.sizeF]; omega
    rw [hn, icountNoRoot_step (RT.sizeF F + 1) c.size (Nat.succ_pos _)
      (RT.edgesF F) c.edges (RT.edgesF_lt F) k]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [dpBF_getD F ij.1, addPoly_getD, dpA_getD c ij.2, dpB_getD c ij.2,
      icount_eq_root_add_noRoot]
end

/-- **Main theorem.** Coefficient `k` of the DP polynomial `indepPolyRT t`
is exactly the number of independent `k`-subsets of the vertex set
`range t.size` of `t` (with respect to the edge list `t.edges`). -/
theorem indepPolyRT_correct (t : RT) (k : Nat) :
    (indepPolyRT t).getD k 0 = t.indepCount k := by
  rw [indepPolyRT, RT.indepCount, addPoly_getD, dpA_getD, dpB_getD,
    icount_eq_root_add_noRoot]

/-! ### From list checks to semantic unimodality -/

/-- Semantic unimodality of `k ↦ L.getD k 0` from two finite checks:
the tail beyond the list is constantly `0`. -/
theorem unimodalAt_getD (L : List Nat) (m : Nat)
    (h₁ : ∀ i, i < m → L.getD i 0 ≤ L.getD (i + 1) 0)
    (h₂ : ∀ i, i < L.length → m ≤ i → L.getD (i + 1) 0 ≤ L.getD i 0) :
    UnimodalAt (fun k => L.getD k 0) m := by
  refine ⟨h₁, fun i him => ?_⟩
  by_cases hi : i < L.length
  · exact h₂ i hi him
  · have hz : L.getD (i + 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
    simp only [hz]
    exact Nat.zero_le _

end ErdosattackM
