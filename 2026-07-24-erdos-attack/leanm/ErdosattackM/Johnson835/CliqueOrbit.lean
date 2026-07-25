import ErdosattackM.Johnson835.Defs
/-!
# The `σ`-orbit 11-clique of `J(20,10)` (Erdős #835)

The `σ`-orbit `{Aᵢ = {11, …, 19} ∪ {i} : i ∈ {0, …, 10}}` is an 11-clique of
`J(20,10)`: any two of its members intersect exactly in the 9-set
`{11, …, 19}`.  Consequently every proper 11-coloring is injective on the
orbit, hence surjective onto `Fin 11`.

Main declarations:

* `orbitVertex i` — the vertex `{11, …, 19} ∪ {i}`;
* `orbitVertex_adj` — distinct orbit vertices are adjacent (11-clique);
* `permAct_σ_orbitVertex` — `σ` rotates the orbit:
  `σ • Aᵢ = A_{finRotate 11 i}`;
* `Proper.surjective` — proper 11-colorings of `J(20,10)` are surjective.
-/

namespace ErdosattackM
namespace Johnson835

/-- The 9-element tail `{11, …, 19} ⊆ Fin 20`, fixed pointwise by `σ`. -/
def tail9 : Finset (Fin 20) := Finset.univ.filter fun x => 11 ≤ (x : ℕ)

lemma mem_tail9 {x : Fin 20} : x ∈ tail9 ↔ 11 ≤ (x : ℕ) := by
  simp [tail9]

lemma tail9_card : tail9.card = 9 := by decide

lemma emb_notMem_tail9 (i : Fin 11) : emb i ∉ tail9 := by
  rw [mem_tail9, emb_val]
  omega

/-- The orbit vertex `Aᵢ = {11, …, 19} ∪ {i}` for `i ∈ {0, …, 10}`. -/
def orbitVertex (i : Fin 11) : V :=
  ⟨insert (emb i) tail9, by
    rw [Finset.card_insert_of_notMem (emb_notMem_tail9 i), tail9_card]⟩

@[simp] lemma orbitVertex_coe (i : Fin 11) :
    (orbitVertex i).1 = insert (emb i) tail9 := rfl

lemma orbitVertex_inter {i j : Fin 11} (hij : i ≠ j) :
    (orbitVertex i).1 ∩ (orbitVertex j).1 = tail9 := by
  have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  ext x
  simp only [orbitVertex_coe, Finset.mem_inter, Finset.mem_insert, mem_tail9,
    Fin.ext_iff, emb_val]
  omega

/-- The orbit is an 11-clique: distinct orbit vertices are adjacent. -/
lemma orbitVertex_adj {i j : Fin 11} (hij : i ≠ j) :
    Adj (orbitVertex i) (orbitVertex j) := by
  unfold Adj
  rw [orbitVertex_inter hij, tail9_card]

lemma tail9_map_σ : tail9.map σ.toEmbedding = tail9 := by
  rw [Finset.map_eq_image]
  have h : Finset.image (⇑σ.toEmbedding) tail9 = Finset.image id tail9 :=
    Finset.image_congr fun x hx => σ_fixed (mem_tail9.mp (Finset.mem_coe.mp hx))
  rw [h, Finset.image_id]

/-- `σ` rotates the clique orbit: `σ • Aᵢ = A_{i+1 (mod 11)}`. -/
lemma permAct_σ_orbitVertex (i : Fin 11) :
    permAct σ (orbitVertex i) = orbitVertex (finRotate 11 i) := by
  apply Subtype.ext
  simp only [permAct_coe, orbitVertex_coe, Finset.map_insert,
    Equiv.coe_toEmbedding, σ_emb, tail9_map_σ]

/-- A proper 11-coloring of `J(20,10)` uses all 11 colors: it is injective on
the 11-clique `{orbitVertex i}`. -/
theorem Proper.surjective {c : V → Fin 11} (hc : Proper c) :
    Function.Surjective c := by
  have hinj : Function.Injective fun i : Fin 11 => c (orbitVertex i) := by
    intro i j hij
    by_contra hne
    exact hc _ _ (orbitVertex_adj hne) hij
  intro y
  obtain ⟨i, hi⟩ := Finite.injective_iff_surjective.mp hinj y
  exact ⟨orbitVertex i, hi⟩

end Johnson835
end ErdosattackM
