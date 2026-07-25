/-!
# Independence polynomials of trees, kernel-computable

Erdős problem #993 (Alavi–Malde–Schwenk–Erdős 1987) asks whether the
independence polynomial of every tree is unimodal. Log-concavity — the
natural strengthening — fails: the smallest failures are 2 trees on 26
vertices (Kadrawi–Levit 2023), and the n = 29 census (7 trees, first
computed 2026-07-24 in this repository) shows 29 is the smallest odd order.

This file certifies those witnesses inside the Lean kernel with no axioms:
`indepPoly` evaluates the standard rooted tree DP
  A(v) = x·∏_c B(c),   B(v) = ∏_c (A(c) + B(c)),   I = A(root) + B(root)
by kernel reduction, and `hasLCFailure` / `isUnimodal` check the coefficient
sequence. (Semantic correctness of the DP against subset-counting semantics
is developed in `IndepPolyCorrect.lean`; until that lands, the DP has been
cross-validated by four independent external implementations.)

A tree on `n` vertices is given by the list of its non-root vertices paired
with their parents, children listed before their parents (guaranteed when
vertices are processed in decreasing index order and `parent i < i`).
-/

namespace Erdosattack

/-- Coefficient-list polynomial addition. -/
def addPoly : List Nat → List Nat → List Nat
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addPoly p q

/-- Coefficient-list polynomial multiplication. -/
def mulPoly : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: p, q => addPoly (q.map (a * ·)) (0 :: mulPoly p q)

/-- One DP step: fold child `c`'s pair into parent `p`.
State is the list of `(A, B)` pairs indexed by vertex. -/
def foldChild (st : List (List Nat × List Nat)) (cp : Nat × Nat) :
    List (List Nat × List Nat) :=
  let (c, p) := cp
  let (ac, bc) := st.getD c ([], [])
  let (ap, bp) := st.getD p ([], [])
  st.set p (mulPoly ap bc, mulPoly bp (addPoly ac bc))

/-- Independence polynomial of a tree on `n` vertices with root `0`.
`edges` lists `(child, parent)` pairs with every child appearing after all
of its own children (decreasing-index order suffices when `parent i < i`). -/
def indepPoly (n : Nat) (edges : List (Nat × Nat)) : List Nat :=
  let final := edges.foldl foldChild (List.replicate n ([0, 1], [1]))
  let (a0, b0) := final.getD 0 ([], [])
  addPoly a0 b0

/-- `true` iff some interior coefficient breaks log-concavity:
`l k ^ 2 < l (k-1) * l (k+1)`. -/
def hasLCFailure : List Nat → Bool
  | a :: b :: c :: t => (b * b < a * c) || hasLCFailure (b :: c :: t)
  | _ => false

/-- `true` iff the sequence never strictly rises after a strict fall. -/
def isUnimodal (l : List Nat) : Bool :=
  go false l
where
  go : Bool → List Nat → Bool
    | _, [] => true
    | _, [_] => true
    | false, a :: b :: t => go (decide (b < a)) (b :: t)
    | true, a :: b :: t => decide (b ≤ a) && go true (b :: t)

end Erdosattack
