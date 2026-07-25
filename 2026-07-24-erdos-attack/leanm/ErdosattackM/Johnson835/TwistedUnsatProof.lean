import ErdosattackM.Johnson835.CliqueOrbit
import ErdosattackM.Johnson835.StarterSystem
/-!
# The twisted system is unsatisfiable (Erdős #835, Stage 2)

`twistedUnsat : TwistedUnsat` — there is no proper 11-coloring `c` of the
Johnson graph `J(20,10)` with `c (σ • A) = c A + 1` for all `A` — proved
**without SAT/LRAT**, by reducing to the finite starter-system obstruction of
`StarterSystem.lean`.

Proof outline (see `p835/PROOF.md`):

* **Normalize** (`twistedUnsat`): replace `c` by `A ↦ c A - c A₀`, still
  proper and twisted, so the clique orbit gets colors `c (F ∪ {i}) = i`
  (`F = {11, …, 19}` the fixed 9-set, `i` a cycle point).
* **Rows** (`no_twisted_normalized`): for each fixed point `f = fixedPt k`
  and gap `g`, the σ-orbit of `baseVertex k g = (F ∖ {f}) ∪ {0, g+1}` has
  exactly one member of each color; shifting by `startOf c k g = -c(base)`
  lands on its color-`0` member
  `zeroVertex c k g = (F ∖ {f}) ∪ {s, s + (g+1)}` (`s = startOf c k g`).
* **Constraints**: properness plus the known colors of the clique orbit force
  (a) `s ≠ 0` and `s + (g+1) ≠ 0` (adjacency with `F ∪ {d}`, colored `d`);
  (b) for fixed `k`, the five pairs `{s, s+(g+1)}` are pairwise disjoint
  (two color-`0` vertices sharing `F ∖ {f}` and one cycle point are
  adjacent); (c) for `k ≠ k'`, same-gap starts differ (else the two
  color-`0` vertices are adjacent).  These are exactly the hypotheses of
  `starter_system_impossible` — contradiction.

All Johnson-adjacency facts are proved symbolically (`Finset.ext` + `omega`
on `Fin.val` coordinates); the only exhaustive checks live in
`StarterSystem.lean`.
-/

namespace ErdosattackM
namespace Johnson835

/-! ### `Fin.ofNat` helpers (`Fin 11` no longer has a `ℕ`-cast) -/

private lemma ofNat_zero : Fin.ofNat 11 0 = 0 := rfl

private lemma ofNat_succ (n : ℕ) : Fin.ofNat 11 (n + 1) = Fin.ofNat 11 n + 1 := by
  apply Fin.ext
  simp [Fin.val_add]

private lemma ofNat_val (j : Fin 11) : Fin.ofNat 11 j.val = j := by
  apply Fin.ext
  simp

/-! ### Indexing the nine fixed points -/

/-- The `k`-th fixed point `k + 11 ∈ {11, …, 19}` of `σ`. -/
def fixedPt (k : Fin 9) : Fin 20 := ⟨(k : ℕ) + 11, by omega⟩

lemma fixedPt_mem_tail9 (k : Fin 9) : fixedPt k ∈ tail9 :=
  mem_tail9.mpr (by simp [fixedPt])

lemma fixedPt_injective : Function.Injective fixedPt := by
  intro k k' h
  have hval : (k : ℕ) + 11 = (k' : ℕ) + 11 := congrArg Fin.val h
  exact Fin.ext (by omega)

/-! ### Row sets `(F ∖ {f}) ∪ {a, b}` -/

/-- The 10-set `(tail9 ∖ {f}) ∪ {emb a, emb b}`: the fixed 9-set with `f`
removed, plus two cycle points. -/
def rowSet (f : Fin 20) (a b : Fin 11) : Finset (Fin 20) :=
  insert (emb a) (insert (emb b) (tail9.erase f))

lemma rowSet_comm (f : Fin 20) (a b : Fin 11) : rowSet f a b = rowSet f b a := by
  unfold rowSet
  rw [Finset.insert_comm]

/-- `emb` is injective. -/
lemma emb_injective : Function.Injective emb := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

lemma rowSet_card {f : Fin 20} (hf : f ∈ tail9) {a b : Fin 11} (hab : a ≠ b) :
    (rowSet f a b).card = 10 := by
  have hbf : emb b ∉ tail9.erase f := fun h =>
    emb_notMem_tail9 b (Finset.mem_of_mem_erase h)
  have haf : emb a ∉ insert (emb b) (tail9.erase f) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hab (emb_injective h)
    · exact emb_notMem_tail9 a (Finset.mem_of_mem_erase h)
  rw [rowSet, Finset.card_insert_of_notMem haf, Finset.card_insert_of_notMem hbf,
    Finset.card_erase_of_mem hf, tail9_card]

/-! ### `σ` shifts row sets -/

lemma tail9_erase_map_σ (f : Fin 20) :
    (tail9.erase f).map σ.toEmbedding = tail9.erase f := by
  rw [Finset.map_eq_image]
  have h : Finset.image (⇑σ.toEmbedding) (tail9.erase f) =
      Finset.image id (tail9.erase f) :=
    Finset.image_congr fun x hx =>
      σ_fixed (mem_tail9.mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hx)))
  rw [h, Finset.image_id]

lemma rowSet_map_sigma (f : Fin 20) (a b : Fin 11) :
    (rowSet f a b).map σ.toEmbedding = rowSet f (a + 1) (b + 1) := by
  have ha : σ.toEmbedding (emb a) = emb (a + 1) := by
    show σ (emb a) = emb (a + 1)
    rw [σ_emb, finRotate_apply]
  have hb : σ.toEmbedding (emb b) = emb (b + 1) := by
    show σ (emb b) = emb (b + 1)
    rw [σ_emb, finRotate_apply]
  unfold rowSet
  rw [Finset.map_insert, Finset.map_insert, tail9_erase_map_σ, ha, hb]

private lemma map_mul_perm (g h : Equiv.Perm (Fin 20)) (s : Finset (Fin 20)) :
    s.map (g * h).toEmbedding = (s.map h.toEmbedding).map g.toEmbedding := by
  rw [Finset.map_map]
  rfl

lemma rowSet_map_sigma_pow (n : ℕ) (f : Fin 20) (a b : Fin 11) :
    (rowSet f a b).map (σ ^ n).toEmbedding =
      rowSet f (a + Fin.ofNat 11 n) (b + Fin.ofNat 11 n) := by
  induction n with
  | zero =>
    rw [pow_zero, ofNat_zero, add_zero, add_zero]
    ext t
    simp [Equiv.Perm.one_def]
  | succ n ih =>
    rw [pow_succ', map_mul_perm, ih, rowSet_map_sigma, ofNat_succ,
      ← add_assoc, ← add_assoc]

/-! ### Adjacency computations in `J(20,10)`

All are `|X ∩ Y| = 9` facts about row sets, proved by `Finset.ext` and
`omega` on `Fin.val` coordinates. -/

/-- A row set meets the clique-orbit vertex of either of its cycle points in
9 elements. -/
lemma inter_row_orbit {f : Fin 20} (hf : f ∈ tail9) {x y : Fin 11}
    (hxy : x ≠ y) :
    (rowSet f x y ∩ (orbitVertex x).1).card = 9 := by
  have hfv : 11 ≤ (f : ℕ) := mem_tail9.mp hf
  have hxv := x.isLt
  have hyv := y.isLt
  have hxyv : (x : ℕ) ≠ (y : ℕ) := fun h => hxy (Fin.ext h)
  have hset : rowSet f x y ∩ (orbitVertex x).1 = insert (emb x) (tail9.erase f) := by
    ext t
    simp only [rowSet, orbitVertex_coe, Finset.mem_inter, Finset.mem_insert,
      Finset.mem_erase, mem_tail9, Fin.ext_iff, emb_val]
    omega
  rw [hset, Finset.card_insert_of_notMem
      (fun h => emb_notMem_tail9 x (Finset.mem_of_mem_erase h)),
    Finset.card_erase_of_mem hf, tail9_card]

/-- Two row sets over the same removed fixed point, sharing exactly the cycle
point `z`, meet in 9 elements. -/
lemma inter_row_row_same {f : Fin 20} (hf : f ∈ tail9) {z u u' : Fin 11}
    (huz : u ≠ z) (hu'z : u' ≠ z) (huu' : u ≠ u') :
    (rowSet f z u ∩ rowSet f z u').card = 9 := by
  have hfv : 11 ≤ (f : ℕ) := mem_tail9.mp hf
  have hzv := z.isLt
  have huv := u.isLt
  have hu'v := u'.isLt
  have h1 : (u : ℕ) ≠ (z : ℕ) := fun h => huz (Fin.ext h)
  have h2 : (u' : ℕ) ≠ (z : ℕ) := fun h => hu'z (Fin.ext h)
  have h3 : (u : ℕ) ≠ (u' : ℕ) := fun h => huu' (Fin.ext h)
  have hset : rowSet f z u ∩ rowSet f z u' = insert (emb z) (tail9.erase f) := by
    ext t
    simp only [rowSet, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase,
      mem_tail9, Fin.ext_iff, emb_val]
    omega
  rw [hset, Finset.card_insert_of_notMem
      (fun h => emb_notMem_tail9 z (Finset.mem_of_mem_erase h)),
    Finset.card_erase_of_mem hf, tail9_card]

/-- Two row sets with the same cycle pair but different removed fixed points
meet in 9 elements. -/
lemma inter_row_row_cross {f f' : Fin 20} (hf : f ∈ tail9) (hf' : f' ∈ tail9)
    (hff' : f ≠ f') {z u : Fin 11} (hzu : z ≠ u) :
    (rowSet f z u ∩ rowSet f' z u).card = 9 := by
  have hfv : 11 ≤ (f : ℕ) := mem_tail9.mp hf
  have hf'v : 11 ≤ (f' : ℕ) := mem_tail9.mp hf'
  have hffv : (f : ℕ) ≠ (f' : ℕ) := fun h => hff' (Fin.ext h)
  have hzv := z.isLt
  have huv := u.isLt
  have hzuv : (z : ℕ) ≠ (u : ℕ) := fun h => hzu (Fin.ext h)
  have hset : rowSet f z u ∩ rowSet f' z u =
      insert (emb z) (insert (emb u) ((tail9.erase f).erase f')) := by
    ext t
    simp only [rowSet, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase,
      mem_tail9, Fin.ext_iff, emb_val]
    omega
  have hu9 : emb u ∉ (tail9.erase f).erase f' := fun h =>
    emb_notMem_tail9 u (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hz9 : emb z ∉ insert (emb u) ((tail9.erase f).erase f') := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hzu (emb_injective h)
    · exact emb_notMem_tail9 z
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hf'mem : f' ∈ tail9.erase f := Finset.mem_erase.mpr ⟨hff'.symm, hf'⟩
  rw [hset, Finset.card_insert_of_notMem hz9, Finset.card_insert_of_notMem hu9,
    Finset.card_erase_of_mem hf'mem, Finset.card_erase_of_mem hf, tail9_card]

/-! ### The twist iterated -/

lemma twist_pow {c : V → Fin 11} (htw : ∀ A, c (permAct σ A) = c A + 1) :
    ∀ (n : ℕ) (A : V), c (permAct (σ ^ n) A) = c A + Fin.ofNat 11 n := by
  intro n
  induction n with
  | zero =>
    intro A
    rw [pow_zero, map_one, Equiv.Perm.one_apply, ofNat_zero, add_zero]
  | succ n ih =>
    intro A
    rw [pow_succ, map_mul, Equiv.Perm.mul_apply, ih, htw, ofNat_succ]
    abel

/-! ### The color-`0` orbit members -/

section ZeroVertices

variable (c : V → Fin 11)

/-- The base vertex `(tail9 ∖ {fixedPt k}) ∪ {0, g+1}` of the `(k, g)` row
orbit. -/
def baseVertex (k : Fin 9) (g : Fin 5) : V :=
  ⟨rowSet (fixedPt k) 0 (gapv g),
    rowSet_card (fixedPt_mem_tail9 k) (zero_ne_gapv g)⟩

/-- The start of the color-`0` pair in the `(k, g)` row orbit: shifting the
base vertex by `-c(base)` steps of `σ` lands on color `0`. -/
def startOf (k : Fin 9) (g : Fin 5) : Fin 11 := -c (baseVertex k g)

/-- The color-`0` member of the `(k, g)` row orbit. -/
def zeroVertex (k : Fin 9) (g : Fin 5) : V :=
  permAct (σ ^ (startOf c k g).val) (baseVertex k g)

lemma zeroVertex_coe (k : Fin 9) (g : Fin 5) :
    (zeroVertex c k g).1 =
      rowSet (fixedPt k) (startOf c k g) (startOf c k g + gapv g) := by
  unfold zeroVertex
  rw [permAct_coe]
  show (rowSet (fixedPt k) 0 (gapv g)).map _ = _
  rw [rowSet_map_sigma_pow, ofNat_val, zero_add, add_comm (gapv g)]

lemma zeroVertex_color (htw : ∀ A, c (permAct σ A) = c A + 1)
    (k : Fin 9) (g : Fin 5) : c (zeroVertex c k g) = 0 := by
  unfold zeroVertex
  rw [twist_pow htw, ofNat_val, startOf]
  exact add_neg_cancel _

end ZeroVertices

/-! ### The reduction -/

/-- A normalized twisted proper coloring (clique-orbit colors `c (Aᵢ) = i`)
yields a 9-row starter system in `Z₁₁` — impossible. -/
theorem no_twisted_normalized (c : V → Fin 11) (hc : Proper c)
    (htw : ∀ A, c (permAct σ A) = c A + 1)
    (horb : ∀ i : Fin 11, c (orbitVertex i) = i) : False := by
  have hZc : ∀ k g, c (zeroVertex c k g) = 0 := zeroVertex_color c htw
  -- Two color-0 vertices sharing the removed point and a cycle point clash.
  have hclash : ∀ (k : Fin 9) (g g' : Fin 5) (z u u' : Fin 11), u ≠ z → u' ≠ z →
      u ≠ u' → (zeroVertex c k g).1 = rowSet (fixedPt k) z u →
      (zeroVertex c k g').1 = rowSet (fixedPt k) z u' → False := by
    intro k g g' z u u' huz hu'z huu' h1 h2
    have hadj : Adj (zeroVertex c k g) (zeroVertex c k g') := by
      unfold Adj
      rw [h1, h2]
      exact inter_row_row_same (fixedPt_mem_tail9 k) huz hu'z huu'
    exact hc _ _ hadj (by rw [hZc, hZc])
  apply starter_system_impossible
  refine ⟨startOf c, ?_, ?_, ?_, ?_⟩
  · -- (a) the pair avoids 0: start ≠ 0
    intro k g
    have hadj : Adj (zeroVertex c k g) (orbitVertex (startOf c k g)) := by
      unfold Adj
      rw [zeroVertex_coe]
      exact inter_row_orbit (fixedPt_mem_tail9 k) (add_gapv_ne _ g).symm
    have hne := hc _ _ hadj
    rw [hZc, horb] at hne
    exact hne.symm
  · -- (a) the pair avoids 0: start + gap ≠ 0
    intro k g
    have hadj : Adj (zeroVertex c k g)
        (orbitVertex (startOf c k g + gapv g)) := by
      unfold Adj
      rw [zeroVertex_coe, rowSet_comm]
      exact inter_row_orbit (fixedPt_mem_tail9 k) (add_gapv_ne _ g)
    have hne := hc _ _ hadj
    rw [hZc, horb] at hne
    exact hne.symm
  · -- (b) rows are matchings: pairs of different gaps are disjoint
    intro k g g' hgg'
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- start = start'
      intro hEq
      apply hclash k g g' (startOf c k g) (startOf c k g + gapv g)
        (startOf c k g' + gapv g')
      · exact add_gapv_ne _ g
      · rw [hEq]; exact add_gapv_ne _ g'
      · intro h
        rw [hEq] at h
        exact hgg' (gapv_injective _ _ (add_left_cancel h))
      · exact zeroVertex_coe c k g
      · rw [hEq]; exact zeroVertex_coe c k g'
    · -- start = start' + gap'
      intro hEq
      apply hclash k g g' (startOf c k g) (startOf c k g + gapv g)
        (startOf c k g')
      · exact add_gapv_ne _ g
      · intro h
        exact add_gapv_ne _ g' (by rw [← hEq]; exact h.symm)
      · intro h
        rw [hEq, add_assoc] at h
        have h0 : startOf c k g' + (gapv g' + gapv g) = startOf c k g' + 0 := by
          rw [h, add_zero]
        exact gapv_add_gapv_ne_zero g' g (add_left_cancel h0)
      · exact zeroVertex_coe c k g
      · rw [zeroVertex_coe, rowSet_comm, ← hEq]
    · -- start + gap = start'
      intro hEq
      apply hclash k g g' (startOf c k g') (startOf c k g)
        (startOf c k g' + gapv g')
      · intro h
        exact add_gapv_ne _ g (hEq.trans h.symm)
      · exact add_gapv_ne _ g'
      · intro h
        rw [← hEq, add_assoc] at h
        have h0 : startOf c k g + (gapv g + gapv g') = startOf c k g + 0 := by
          rw [← h, add_zero]
        exact gapv_add_gapv_ne_zero g g' (add_left_cancel h0)
      · rw [zeroVertex_coe, rowSet_comm, hEq]
      · exact zeroVertex_coe c k g'
    · -- start + gap = start' + gap'
      intro hEq
      apply hclash k g g' (startOf c k g + gapv g) (startOf c k g)
        (startOf c k g')
      · exact (add_gapv_ne _ g).symm
      · rw [hEq]; exact (add_gapv_ne _ g').symm
      · intro h
        rw [h] at hEq
        exact hgg' (gapv_injective _ _ (add_left_cancel hEq))
      · rw [zeroVertex_coe, rowSet_comm]
      · rw [zeroVertex_coe, rowSet_comm, ← hEq]
  · -- (c) rows are edge-disjoint: same-gap starts differ across rows
    intro k k' g hkk' hEq
    have hadj : Adj (zeroVertex c k g) (zeroVertex c k' g) := by
      unfold Adj
      rw [zeroVertex_coe, zeroVertex_coe, ← hEq]
      exact inter_row_row_cross (fixedPt_mem_tail9 k) (fixedPt_mem_tail9 k')
        (fun h => hkk' (fixedPt_injective h)) (add_gapv_ne _ g).symm
    exact hc _ _ hadj (by rw [hZc, hZc])

/-- **The twisted system is unsatisfiable** (Erdős #835, Stage 2 — proved via
the starter-system obstruction, no SAT/LRAT): there is no proper 11-coloring
`c` of `J(20,10)` with `c (σ • A) = c A + 1` for all `A`. -/
theorem twistedUnsat : TwistedUnsat := by
  rintro ⟨c, hc, htw⟩
  -- Normalize: subtract the color of the base clique vertex.
  refine no_twisted_normalized (fun A => c A - c (orbitVertex 0)) ?_ ?_ ?_
  · simpa using hc.comp_perm (Equiv.subRight (c (orbitVertex 0)))
  · intro A
    show c (permAct σ A) - _ = c A - _ + 1
    rw [htw]
    abel
  · -- clique-orbit colors are normalized to `c (Aᵢ) = i`
    have horbN : ∀ n : ℕ,
        c (orbitVertex (Fin.ofNat 11 n)) - c (orbitVertex 0) = Fin.ofNat 11 n := by
      intro n
      induction n with
      | zero => rw [ofNat_zero, sub_self]
      | succ n ih =>
        have hrot : orbitVertex (Fin.ofNat 11 (n + 1)) =
            permAct σ (orbitVertex (Fin.ofNat 11 n)) := by
          rw [permAct_σ_orbitVertex, finRotate_apply, ofNat_succ]
        rw [hrot, htw, ofNat_succ]
        conv_rhs => rw [← ih]
        abel
    intro i
    have h := horbN i.val
    rwa [ofNat_val] at h

end Johnson835
end ErdosattackM
