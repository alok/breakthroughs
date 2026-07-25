import ErdosattackM.Johnson835.Defs
/-!
# Order-11 symmetries of `J(20,10)`: `ε`-triviality and conjugacy (Erdős #835)

Group-theoretic reductions for the symmetry-obstruction theorem:

* `permAct_injective` — the `S₂₀`-action on `V` is faithful;
* `permAct_ne_complAct` — no ground-set relabelling equals complementation;
* `order_eleven_facts` — an order-11 element `cAct ε g` of the natural
  `S₂₀ × Z₂` action has trivial `Z₂`-part (`ε = false`, since 11 is odd) and
  `orderOf g = 11`;
* `cycleType_eq_of_orderOf_eq_prime` — a permutation of prime order `p` on
  fewer than `2p` points is a single `p`-cycle;
* `isConj_sigma` — every order-11 element of `S₂₀` is conjugate to `σ`.
-/

namespace ErdosattackM
namespace Johnson835

/-! ### Faithfulness of the action -/

/-- The relabelling action of `S₂₀` on 10-subsets is faithful: if `g` moves
`x`, then `g` moves any 10-set containing `x` but not `g x`. -/
lemma permAct_injective : Function.Injective permAct := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ x :=
    not_forall.mp fun hall => hne (Equiv.ext hall)
  have hsub : ({x} : Finset (Fin 20)) ⊆ {g x}ᶜ := by
    simp only [Finset.singleton_subset_iff, Finset.mem_compl, Finset.mem_singleton]
    exact Ne.symm hx
  obtain ⟨S, hxS, hSc, hcard⟩ := Finset.exists_subsuperset_card_eq hsub
    (n := 10) (by simp) (by simp [Finset.card_compl])
  have hA : permAct g ⟨S, hcard⟩ = ⟨S, hcard⟩ := by rw [hg]; rfl
  have hgx : g x ∈ S := by
    have hmem : g x ∈ (permAct g ⟨S, hcard⟩).1 := by
      rw [permAct_coe]
      exact Finset.mem_map_of_mem _ (Finset.singleton_subset_iff.mp hxS)
    rwa [hA] at hmem
  have h2 : g x ∈ ({g x}ᶜ : Finset (Fin 20)) := hSc hgx
  simp at h2

/-- No ground-set relabelling acts as complementation on 10-subsets: pick a
10-set containing both `0` and `g 0`; its image contains `g 0`, its complement
does not. -/
lemma permAct_ne_complAct (g : Equiv.Perm (Fin 20)) : permAct g ≠ complAct := by
  intro h
  obtain ⟨S, hsS, -, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (insert (g 0) {(0 : Fin 20)}))
    (n := 10) ((Finset.card_insert_le _ _).trans (by simp)) (by simp)
  have h0S : (0 : Fin 20) ∈ S := hsS (by simp)
  have hg0S : g 0 ∈ S := hsS (by simp)
  have hmem : g 0 ∈ (permAct g ⟨S, hcard⟩).1 := by
    rw [permAct_coe]
    exact Finset.mem_map_of_mem _ h0S
  rw [h, complAct_coe, Finset.mem_compl] at hmem
  exact hmem hg0S

/-! ### `ε`-triviality: odd order kills the `Z₂`-part -/

lemma complAct_pow_eleven : complAct ^ 11 = complAct := by
  have h2 : complAct ^ 2 = 1 := by
    rw [sq]
    exact complAct_mul_self
  have h10 : complAct ^ 10 = 1 := by
    have h : complAct ^ 10 = (complAct ^ 2) ^ 5 := by rw [← pow_mul]
    rw [h, h2, one_pow]
  rw [show (11 : ℕ) = 10 + 1 from rfl, pow_succ, h10, one_mul]

/-- An order-11 element of the natural `S₂₀ × Z₂` action has trivial
complementation part, and its `S₂₀`-part has order 11. -/
lemma order_eleven_facts {ε : Bool} {g : Equiv.Perm (Fin 20)}
    (hord : orderOf (cAct ε g) = 11) : ε = false ∧ orderOf g = 11 := by
  have hε : ε = false := by
    cases ε with
    | false => rfl
    | true =>
      exfalso
      have hpow : cAct true g ^ 11 = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one _
      rw [cAct_true, (complAct_comm g).mul_pow, complAct_pow_eleven, ← map_pow] at hpow
      have h : permAct (g ^ 11) = complAct := by
        have h1 : complAct * (complAct * permAct (g ^ 11)) = complAct * 1 := by
          rw [hpow]
        rwa [← mul_assoc, complAct_mul_self, one_mul, mul_one] at h1
      exact permAct_ne_complAct _ h
  subst hε
  rw [cAct_false, orderOf_injective permAct permAct_injective] at hord
  exact ⟨rfl, hord⟩

/-! ### Cycle type of prime-order elements on few points -/

/-- A permutation of prime order `p` of a finite type with fewer than `2p`
elements is a single `p`-cycle: every cycle length divides (hence equals) `p`,
and two `p`-cycles would need `2p` points. -/
lemma cycleType_eq_of_orderOf_eq_prime {β : Type*} [Fintype β] [DecidableEq β]
    {f : Equiv.Perm β} {p : ℕ} (hp : p.Prime)
    (hf : orderOf f = p) (hcard : Fintype.card β < 2 * p) :
    f.cycleType = {p} := by
  have hne : f ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hf
    exact hp.one_lt.ne' hf.symm
  have hall : ∀ r ∈ f.cycleType, r = p := by
    intro r hr
    have hdvd : r ∣ p := by
      rw [← hf, ← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hr
    rcases hp.eq_one_or_self_of_dvd r hdvd with h1 | h
    · have := Equiv.Perm.two_le_of_mem_cycleType hr
      omega
    · exact h
  have hrep : f.cycleType = Multiset.replicate (Multiset.card f.cycleType) p :=
    Multiset.eq_replicate_card.mpr hall
  have hsum : f.cycleType.sum ≤ Fintype.card β := Equiv.Perm.sum_cycleType_le f
  have hpos : Multiset.card f.cycleType ≠ 0 := fun h0 =>
    hne (Equiv.Perm.card_cycleType_eq_zero.mp h0)
  have hlt : Multiset.card f.cycleType < 2 := by
    by_contra hge
    have hge2 : 2 ≤ Multiset.card f.cycleType := Nat.le_of_not_lt hge
    have h2p : 2 * p ≤ f.cycleType.sum := by
      rw [hrep, Multiset.sum_replicate, smul_eq_mul]
      exact Nat.mul_le_mul_right p hge2
    omega
  have h1 : Multiset.card f.cycleType = 1 := by omega
  rw [hrep, h1, Multiset.replicate_one]

/-- Sanity check (non-vacuity of the order-11 hypothesis): the action does
have order-11 elements — `σ` itself acts on `V` with order 11. -/
lemma orderOf_cAct_false_sigma : orderOf (cAct false σ) = 11 := by
  rw [cAct_false, orderOf_injective permAct permAct_injective]
  exact σ_orderOf

/-- Every order-11 element of `S₂₀` is conjugate to the standard 11-cycle `σ`
(an order-11 permutation of 20 points is a single 11-cycle; two 11-cycles
would need 22 points). -/
lemma isConj_sigma {g : Equiv.Perm (Fin 20)} (hg : orderOf g = 11) : IsConj σ g := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq, σ_cycleType]
  exact (cycleType_eq_of_orderOf_eq_prime (by norm_num) hg
    (by rw [Fintype.card_fin]; norm_num)).symm

end Johnson835
end ErdosattackM
