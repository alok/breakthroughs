# Lean formalization design — #835 symmetry obstruction

Target theorem (Stage 1, mathlib-based, `TwistedUnsat` as named hypothesis;
Stage 2 discharges it by LRAT checking):

```lean
-- V = 10-subsets of Fin 20; adjacency = |A ∩ B| = 9 (Johnson graph J(20,10))
abbrev V := {s : Finset (Fin 20) // s.card = 10}
def Adj (A B : V) : Prop := (A.1 ∩ B.1).card = 9
def Proper (c : V → Fin 11) : Prop := ∀ A B, Adj A B → c A ≠ c B

-- natural S20 × Z2 action: permute the ground set, optionally complement
def permAct (g : Equiv.Perm (Fin 20)) (A : V) : V := ⟨A.1.map g.toEmbedding, by simp [A.2]⟩
def cAct (ε : Bool) (g : Equiv.Perm (Fin 20)) (A : V) : V :=
  if ε then ⟨(permAct g A).1ᶜ, by simp [...]⟩ else permAct g A

-- σ = the 11-cycle (0 1 ... 10) fixing 11..19  (finRotate 11 embedded)
def TwistedUnsat : Prop :=
  ¬ ∃ c : V → Fin 11, Proper c ∧ ∀ A, c (permAct σ A) = c A + 1

theorem no_order11_symmetry (hT : TwistedUnsat)
    (c : V → Fin 11) (hc : Proper c)
    (ε : Bool) (g : Equiv.Perm (Fin 20)) (π : Equiv.Perm (Fin 11))
    (hord : orderOf (cActEquiv ε g) = 11)
    (heq : ∀ A, c (cAct ε g A) = π (c A)) : False
```

## Proof skeleton

1. **ε = false forced**: `(cActEquiv ε g)^11` has complement-part `ε` (11 odd);
   order 11 ⇒ ε = false. (Formalize the action as `Equiv.Perm V` products;
   complementation commutes with permAct.)
2. **Cycle type**: `orderOf g' = 11` for `g' = permAct-part`... more precisely
   order-11 of the induced action forces orderOf g ∈ {11} (the action of g on
   V is faithful for g ≠ 1... easier: hord on the V-action gives (g-action)^11
   = 1; g acts faithfully on V — prove: if g ≠ 1, some 10-subset moved; then
   orderOf g divides 11, g ≠ 1 case ⇒ = 11). 11 prime, 11 ≤ 20 < 22 ⇒
   `g.cycleType = {11}` (parts lcm = 11, sum ≤ 20 ⇒ exactly one 11-part).
   Hence `IsConj σ g` via `Equiv.Perm.isConj_iff_cycleType_eq`.
3. **Transport to σ**: g = τ σ τ⁻¹; c'' := c ∘ permAct τ is proper
   (permAct τ is a graph automorphism: `card_inter` preserved under
   `Finset.map`) and satisfies c''(σA) = π(c''(A)).
4. **π case split** via surjectivity of c'' (the σ-orbit
   `Aᵢ = {11,…,19} ∪ {i}` (0-indexed) is an 11-clique, so a proper coloring
   is surjective): π^11 = 1 from c'' ∘ (σ-action)^11 = π^11 ∘ c''.
   - π = 1: c'' constant on the clique orbit {Aᵢ} — contradicts Proper.
   - π an 11-cycle: `π.cycleType = {11}` ⇒ IsConj (finRotate 11) π, get ρ
     with ρπρ⁻¹ = +1; c' := ρ ∘ c'' is proper with c'(σA) = c'(A)+1 —
     contradicts hT.
5. Mathlib tools: `Equiv.Perm.cycleType`, `orderOf`, `Equiv.Perm.lcm_cycleType`,
   `Equiv.Perm.sum_cycleType`, `isConj_iff_cycleType_eq`, `finRotate`,
   `Finset.card_map`, `Finset.map_inter`.

## Stage 2 (`TwistedUnsat` discharge)

Bridge V-statement → orbit CNF (16,796 reps table, generated) → core clauses
entailment → LRAT check of `core.lrat` via `Std.Tactic.BVDecide.LRAT` /
LeanSAT checker. Expect either kernel-checked (slow, hours) or
`ofReduceBool`-based (fast, one extra standard-ish axiom) — decide when core
artifacts land. Until then Stage 1 is a complete sorry-free artifact modulo
one honestly-named hypothesis verified externally (5× SAT + DRAT `s VERIFIED`).
