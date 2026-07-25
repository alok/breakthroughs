import ErdosattackM.Johnson835.Conjugacy
import ErdosattackM.Johnson835.CliqueOrbit
/-!
# No proper 11-coloring of `J(20,10)` has an order-11 symmetry (Erdős #835)

Main theorem of Stage 1: given the externally verified `TwistedUnsat`
(the `C₁₁`-twisted coloring system is UNSAT — Stage 2 discharges this by LRAT
checking), **no proper 11-coloring of the Johnson graph `J(20,10)` is
equivariant under an order-11 element of the natural `S₂₀ × Z₂` action**, for
any permutation `π` of the 11 colors.

Proof skeleton (see `p835/LEMMA.md`):

1. 11 is odd, so an order-11 element of `S₂₀ × Z₂` has trivial `Z₂`-part and
   its `S₂₀`-part `g` has order 11 (`order_eleven_facts`);
2. `g` is a single 11-cycle, hence conjugate to `σ` (`isConj_sigma`);
   transporting the coloring along the conjugator reduces to the case `g = σ`;
3. `σ¹¹ = 1` forces `π¹¹ = 1` (proper colorings are surjective by the clique
   orbit), so `π = 1` or `π` is an 11-cycle;
4. `π = 1` would make the coloring constant on the 11-clique orbit —
   contradiction; `π` an 11-cycle is conjugate to `+1`, and relabelling the
   colors produces a solution of the twisted system — contradicting
   `TwistedUnsat`.
-/

namespace ErdosattackM
namespace Johnson835

/-- Core case `g = σ`: no proper 11-coloring satisfies
`c (σ • A) = π (c A)` for any color permutation `π`, given `TwistedUnsat`. -/
theorem no_sigma_twist (hT : TwistedUnsat) {c : V → Fin 11} (hc : Proper c)
    (π : Equiv.Perm (Fin 11)) (heq : ∀ A, c (permAct σ A) = π (c A)) : False := by
  -- Iterate the equivariance: `c ((σ^n) • A) = π^n (c A)`.
  have hpow : ∀ (n : ℕ) (A : V), c (permAct (σ ^ n) A) = (π ^ n) (c A) := by
    intro n
    induction n with
    | zero => intro A; simp
    | succ n ih =>
      intro A
      rw [pow_succ, map_mul, Equiv.Perm.mul_apply, ih, heq, pow_succ,
        Equiv.Perm.mul_apply]
  -- `σ^11 = 1` and surjectivity of `c` force `π^11 = 1`.
  have hπ11 : π ^ 11 = 1 := by
    have hσ : σ ^ 11 = 1 := by
      rw [← σ_orderOf]
      exact pow_orderOf_eq_one σ
    have hAll : ∀ A : V, c A = (π ^ 11) (c A) := by
      intro A
      have h := hpow 11 A
      rwa [hσ, map_one, Equiv.Perm.one_apply] at h
    apply Equiv.ext
    intro x
    obtain ⟨A, rfl⟩ := hc.surjective x
    rw [Equiv.Perm.one_apply]
    exact (hAll A).symm
  have hdvd : orderOf π ∣ 11 := orderOf_dvd_of_pow_eq_one hπ11
  have hp : Nat.Prime 11 := by norm_num
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h11
  · -- Case `π = 1`: the coloring is constant on the adjacent pair `A₀, A₁`.
    have hπ1 : π = 1 := orderOf_eq_one_iff.mp h1
    have h01 : c (orbitVertex 1) = c (orbitVertex 0) := by
      have h := heq (orbitVertex 0)
      rw [permAct_σ_orbitVertex, hπ1, Equiv.Perm.one_apply] at h
      have h0 : finRotate 11 (0 : Fin 11) = 1 := by decide
      rwa [h0] at h
    exact hc _ _ (orbitVertex_adj (show (0 : Fin 11) ≠ 1 by decide)) h01.symm
  · -- Case `π` an 11-cycle: conjugate the colors to the `+1` twist.
    have hπCT : π.cycleType = {11} :=
      cycleType_eq_of_orderOf_eq_prime hp h11 (by rw [Fintype.card_fin]; norm_num)
    have hconj : IsConj (finRotate 11) π := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hπCT]
      exact cycleType_finRotate
    obtain ⟨ρ, hρ⟩ := isConj_iff.mp hconj
    apply hT
    refine ⟨fun A => ρ⁻¹ (c A), hc.comp_perm ρ⁻¹, fun A => ?_⟩
    show ρ⁻¹ (c (permAct σ A)) = ρ⁻¹ (c A) + 1
    rw [heq]
    have hmul : ρ⁻¹ * π = finRotate 11 * ρ⁻¹ := by rw [← hρ]; group
    have happ := congrArg (fun e : Equiv.Perm (Fin 11) => e (c A)) hmul
    simp only [Equiv.Perm.mul_apply] at happ
    rw [happ, finRotate_apply]

/-- **Main theorem** (Erdős #835 symmetry obstruction, Stage 1).

Given the externally verified `TwistedUnsat`, no proper 11-coloring `c` of the
Johnson graph `J(20,10)` admits an order-11 symmetry from the natural
`S₂₀ × Z₂` action: there is no `(ε, g)` with `orderOf (cAct ε g) = 11` and no
color permutation `π` such that `c (cAct ε g A) = π (c A)` for all `A`. -/
theorem no_order11_symmetry (hT : TwistedUnsat)
    (c : V → Fin 11) (hc : Proper c)
    (ε : Bool) (g : Equiv.Perm (Fin 20)) (π : Equiv.Perm (Fin 11))
    (hord : orderOf (cAct ε g) = 11)
    (heq : ∀ A, c (cAct ε g A) = π (c A)) : False := by
  obtain ⟨hε, hg⟩ := order_eleven_facts hord
  subst hε
  simp only [cAct_false] at heq
  -- Conjugate `g` to `σ` and transport the coloring.
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_sigma hg)
  have hτσ : τ * σ = g * τ := by rw [← hτ]; group
  refine no_sigma_twist hT (hc.comp_permAct τ) π fun A => ?_
  show c (permAct τ (permAct σ A)) = π (c (permAct τ A))
  rw [← Equiv.Perm.mul_apply, ← map_mul, hτσ, map_mul, Equiv.Perm.mul_apply]
  exact heq _

/-- Variant with the order-11 hypothesis in the weaker
`(action)¹¹ = 1 ∧ action ≠ 1` form (equivalent, since 11 is prime). -/
theorem no_order11_symmetry' (hT : TwistedUnsat)
    (c : V → Fin 11) (hc : Proper c)
    (ε : Bool) (g : Equiv.Perm (Fin 20)) (π : Equiv.Perm (Fin 11))
    (hpow : cAct ε g ^ 11 = 1) (hne : cAct ε g ≠ 1)
    (heq : ∀ A, c (cAct ε g A) = π (c A)) : False := by
  have hord : orderOf (cAct ε g) = 11 := by
    have hp : Nat.Prime 11 := by norm_num
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h
  exact no_order11_symmetry hT c hc ε g π hord heq

/-- Human-readable corollary: given `TwistedUnsat`, there is **no**
`π`-equivariant proper 11-coloring of `J(20,10)` for **any** order-11 element
of the natural `S₂₀ × Z₂` action and **any** color permutation `π`. -/
theorem no_order11_equivariant_coloring (hT : TwistedUnsat) :
    ¬ ∃ (c : V → Fin 11) (ε : Bool) (g : Equiv.Perm (Fin 20))
        (π : Equiv.Perm (Fin 11)),
        Proper c ∧ orderOf (cAct ε g) = 11 ∧ ∀ A, c (cAct ε g A) = π (c A) := by
  rintro ⟨c, ε, g, π, hc, hord, heq⟩
  exact no_order11_symmetry hT c hc ε g π hord heq

end Johnson835
end ErdosattackM
