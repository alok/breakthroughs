import Mathlib
/-!
# Johnson graph `J(20,10)`: definitions (Erdős #835, Stage 1)

Basic objects for the symmetry-obstruction theorem of Erdős problem #835
(Erdős–Rosenfeld: is `χ(J(2k,k)) = k+1` for some `k > 2`?  First open case
`k = 10`).

This file defines:

* `V`, the vertex set of `J(20,10)`: 10-element subsets of `Fin 20`;
* `Adj`, Johnson adjacency (`|A ∩ B| = 9`) and `Proper`, proper 11-colorings;
* the natural `S₂₀ × Z₂` action on `V`:
  - `permAct : Equiv.Perm (Fin 20) →* Equiv.Perm V` (relabel the ground set),
  - `complAct : Equiv.Perm V` (complement in `Fin 20`),
  - `cAct ε g = (if ε then complAct else 1) * permAct g`;
* `σ : Equiv.Perm (Fin 20)`, the 11-cycle `(0 1 … 10)` fixing `{11, …, 19}`,
  realized as `(finRotate 11).extendDomain`;
* `TwistedUnsat`, the single externally-verified hypothesis (Stage 2
  discharges it by LRAT checking): the `C₁₁`-twisted coloring system
  `c (permAct σ A) = c A + 1` has no proper solution.

Basic transport lemmas (`permAct` is a graph automorphism, `complAct`
commutes with `permAct`) are also proved here.
-/

namespace ErdosattackM
namespace Johnson835

/-- Vertices of the Johnson graph `J(20,10)`: the 10-element subsets of
`Fin 20`. -/
abbrev V : Type := {s : Finset (Fin 20) // s.card = 10}

/-- Johnson graph adjacency: two 10-sets are adjacent iff they share exactly
9 elements.  (This forces `A ≠ B`, since `|A ∩ A| = 10`.) -/
def Adj (A B : V) : Prop := (A.1 ∩ B.1).card = 9

/-- `c` is a proper 11-coloring of `J(20,10)`. -/
def Proper (c : V → Fin 11) : Prop := ∀ A B, Adj A B → c A ≠ c B

/-! ### The natural `S₂₀ × Z₂` action on `V` -/

/-- The permutation of `V` induced by relabelling the ground set along
`g : Equiv.Perm (Fin 20)`. -/
def permApply (g : Equiv.Perm (Fin 20)) : Equiv.Perm V where
  toFun A := ⟨A.1.map g.toEmbedding, by rw [Finset.card_map]; exact A.2⟩
  invFun A := ⟨A.1.map g.symm.toEmbedding, by rw [Finset.card_map]; exact A.2⟩
  left_inv A := by
    apply Subtype.ext
    ext x
    simp [Finset.mem_map_equiv]
  right_inv A := by
    apply Subtype.ext
    ext x
    simp [Finset.mem_map_equiv]

/-- The ground-set relabelling action, bundled as a group homomorphism
`Equiv.Perm (Fin 20) →* Equiv.Perm V`. -/
def permAct : Equiv.Perm (Fin 20) →* Equiv.Perm V :=
  MonoidHom.mk' permApply fun g h => by
    apply Equiv.ext
    intro A
    apply Subtype.ext
    show A.1.map (g * h).toEmbedding = (A.1.map h.toEmbedding).map g.toEmbedding
    rw [Finset.map_map]
    rfl

@[simp] lemma permAct_coe (g : Equiv.Perm (Fin 20)) (A : V) :
    (permAct g A).1 = A.1.map g.toEmbedding := rfl

/-- Complementation `A ↦ Aᶜ`, an automorphism of `J(20,10)`. -/
def complAct : Equiv.Perm V where
  toFun A := ⟨A.1ᶜ, by rw [Finset.card_compl, A.2, Fintype.card_fin]⟩
  invFun A := ⟨A.1ᶜ, by rw [Finset.card_compl, A.2, Fintype.card_fin]⟩
  left_inv A := Subtype.ext (compl_compl A.1)
  right_inv A := Subtype.ext (compl_compl A.1)

@[simp] lemma complAct_coe (A : V) : (complAct A).1 = A.1ᶜ := rfl

lemma complAct_mul_self : complAct * complAct = 1 := by
  apply Equiv.ext
  intro A
  apply Subtype.ext
  show (A.1ᶜ)ᶜ = A.1
  exact compl_compl A.1

/-- Mapping by a permutation commutes with complementation on `Finset`s. -/
lemma compl_map (g : Equiv.Perm (Fin 20)) (s : Finset (Fin 20)) :
    sᶜ.map g.toEmbedding = (s.map g.toEmbedding)ᶜ := by
  ext x
  simp [Finset.mem_map_equiv]

/-- Complementation commutes with the relabelling action. -/
lemma complAct_comm (g : Equiv.Perm (Fin 20)) : Commute complAct (permAct g) := by
  have h : complAct * permAct g = permAct g * complAct := by
    apply Equiv.ext
    intro A
    apply Subtype.ext
    show ((permAct g A).1)ᶜ = (complAct A).1.map g.toEmbedding
    rw [complAct_coe, permAct_coe, compl_map]
  exact h

/-- The full `S₂₀ × Z₂` action: permute the ground set by `g`, then complement
if `ε = true`. -/
def cAct (ε : Bool) (g : Equiv.Perm (Fin 20)) : Equiv.Perm V :=
  (cond ε complAct 1) * permAct g

lemma cAct_false (g : Equiv.Perm (Fin 20)) : cAct false g = permAct g :=
  one_mul _

lemma cAct_true (g : Equiv.Perm (Fin 20)) : cAct true g = complAct * permAct g :=
  rfl

/-! ### The 11-cycle `σ = (0 1 … 10)` -/

/-- The inclusion `Fin 11 → Fin 20` on values. -/
def emb (i : Fin 11) : Fin 20 := ⟨i.1, by omega⟩

@[simp] lemma emb_val (i : Fin 11) : (emb i : ℕ) = i.1 := rfl

/-- `Fin 11` is equivalent to the subtype `{x : Fin 20 // x < 11}`. -/
def embSubtype : Fin 11 ≃ {x : Fin 20 // (x : ℕ) < 11} where
  toFun i := ⟨emb i, i.isLt⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `σ`: the 11-cycle `(0 1 … 10)` in `S₂₀`, fixing `{11, …, 19}` pointwise.
Realized as `finRotate 11` extended along `embSubtype`. -/
def σ : Equiv.Perm (Fin 20) := (finRotate 11).extendDomain embSubtype

lemma σ_emb (i : Fin 11) : σ (emb i) = emb (finRotate 11 i) :=
  Equiv.Perm.extendDomain_apply_image (finRotate 11) embSubtype i

lemma σ_fixed {x : Fin 20} (hx : 11 ≤ (x : ℕ)) : σ x = x :=
  Equiv.Perm.extendDomain_apply_not_subtype (finRotate 11) embSubtype (by omega)

lemma σ_cycleType : σ.cycleType = {11} := by
  unfold σ
  rw [Equiv.Perm.cycleType_extendDomain]
  exact cycleType_finRotate

lemma σ_orderOf : orderOf σ = 11 := by
  rw [← Equiv.Perm.lcm_cycleType, σ_cycleType]
  decide

/-! ### The externally verified hypothesis -/

/-- **The twisted system is unsatisfiable** (Stage 2 target; verified
externally by 5× SAT runs plus a DRAT certificate): there is no proper
11-coloring `c` of `J(20,10)` with `c (σ • A) = c A + 1` for all `A`. -/
def TwistedUnsat : Prop :=
  ¬ ∃ c : V → Fin 11, Proper c ∧ ∀ A, c (permAct σ A) = c A + 1

/-! ### Transport lemmas -/

/-- The relabelling action is a graph automorphism. -/
lemma adj_permAct (g : Equiv.Perm (Fin 20)) {A B : V} :
    Adj (permAct g A) (permAct g B) ↔ Adj A B := by
  unfold Adj
  rw [permAct_coe, permAct_coe, ← Finset.map_inter, Finset.card_map]

/-- Pulling back a proper coloring along the relabelling action stays proper. -/
lemma Proper.comp_permAct {c : V → Fin 11} (hc : Proper c) (g : Equiv.Perm (Fin 20)) :
    Proper (fun A => c (permAct g A)) := fun _ _ hAB =>
  hc _ _ ((adj_permAct g).mpr hAB)

/-- Post-composing a proper coloring with a color permutation stays proper. -/
lemma Proper.comp_perm {c : V → Fin 11} (hc : Proper c) (ρ : Equiv.Perm (Fin 11)) :
    Proper (fun A => ρ (c A)) := fun A B hAB h =>
  hc A B hAB (ρ.injective h)

end Johnson835
end ErdosattackM
