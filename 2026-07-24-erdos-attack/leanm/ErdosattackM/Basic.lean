import Mathlib
/-!
# Independence polynomials of rose trees: definitions

Companion (mathlib) package to the mathlib-free core package in `../lean/`,
for Erdős problem #993 (unimodality of tree independence polynomials).

This file defines:

* the coefficient-list polynomial operations `addPoly`/`mulPoly`
  (verbatim copies of `lean/Erdosattack/IndepPoly.lean`);
* rose trees `RT` and the structural DP `RT.dpA`/`RT.dpB` computing
  `A(v) = x·∏_c B(c)` and `B(v) = ∏_c (A(c) + B(c))`, with
  `indepPolyRT t = A(root) + B(root)`;
* a vertex labelling by contiguous subtree intervals: the root of `t` gets
  label `0` and each child's subtree gets a contiguous block, via `RT.size`
  and `RT.edges` (the *first* child in the list receives the *last* block,
  so the list-cons structure matches block-append on the right);
* the subset-counting semantics `IndepIn`, `icount`/`icountRoot`/`icountNoRoot`
  and `RT.indepCount`: the number of independent `k`-subsets of the vertex set
  `range t.size` with respect to the edge list `t.edges`;
* `RT.toEdges`, flattening a rose tree to the exact `(n, edges)` format
  consumed by the core package (`(child, parent)` pairs, decreasing child
  order);
* the semantic predicates `NLCAt` (log-concavity failure at `k`) and
  `UnimodalAt` (single peak at `m`), and the bundle `GoodTree`.

The main theorem `indepPolyRT_correct` — the DP computes `RT.indepCount` —
is proved in `ErdosattackM/Correct.lean`.
-/

namespace ErdosattackM

/-- Coefficient-list polynomial addition (identical to the core package). -/
def addPoly : List Nat → List Nat → List Nat
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addPoly p q

/-- Coefficient-list polynomial multiplication (identical to the core package). -/
def mulPoly : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: p, q => addPoly (q.map (a * ·)) (0 :: mulPoly p q)

/-- Rose trees: a rooted tree is a (possibly empty) list of child subtrees. -/
inductive RT where
  | node : List RT → RT
deriving Repr

mutual
/-- Number of vertices of a rose tree. -/
def RT.size : RT → Nat
  | .node cs => RT.sizeF cs + 1
/-- Total number of vertices of a forest. -/
def RT.sizeF : List RT → Nat
  | [] => 0
  | c :: cs => c.size + RT.sizeF cs
end

/-- Shift both endpoints of every edge by `o`. -/
def shiftEdges (o : Nat) (E : List (Nat × Nat)) : List (Nat × Nat) :=
  E.map fun e => (e.1 + o, e.2 + o)

mutual
/-- `(child, parent)` edge list of a rose tree, in the contiguous-interval
labelling: the root is `0`; the last child of the list gets the block
starting at `1`, and earlier children get later blocks. Edges come out in
*increasing* child order, and every non-root vertex occurs exactly once as
a child. -/
def RT.edges : RT → List (Nat × Nat)
  | .node cs => RT.edgesF cs
/-- Edge list of a forest hanging from root `0`, blocks of later list
elements first. The head child `c` of `c :: cs` occupies the block
`[sizeF cs + 1, sizeF cs + 1 + size c)`. -/
def RT.edgesF : List RT → List (Nat × Nat)
  | [] => []
  | c :: cs =>
    RT.edgesF cs ++ ((RT.sizeF cs + 1, 0) :: shiftEdges (RT.sizeF cs + 1) c.edges)
end

mutual
/-- Coefficients of `A(root t)`: generating polynomial of independent sets
that **contain** the root. -/
def RT.dpA : RT → List Nat
  | .node cs => RT.dpAF cs
/-- `A` of a root with children forest `F`: `x · ∏_{c ∈ F} B(c)`. -/
def RT.dpAF : List RT → List Nat
  | [] => [0, 1]
  | c :: cs => mulPoly (RT.dpAF cs) c.dpB
/-- Coefficients of `B(root t)`: generating polynomial of independent sets
that **avoid** the root. -/
def RT.dpB : RT → List Nat
  | .node cs => RT.dpBF cs
/-- `B` of a root with children forest `F`: `∏_{c ∈ F} (A(c) + B(c))`. -/
def RT.dpBF : List RT → List Nat
  | [] => [1]
  | c :: cs => mulPoly (RT.dpBF cs) (addPoly c.dpA c.dpB)
end

/-- The independence polynomial of a rose tree, via the standard rooted DP. -/
def indepPolyRT (t : RT) : List Nat := addPoly t.dpA t.dpB

/-- Flatten a rose tree to the `(n, edges)` format of the core package:
`(child, parent)` pairs in decreasing child order (so every vertex is
processed after all of its own children, as the core DP requires). -/
def RT.toEdges (t : RT) : Nat × List (Nat × Nat) := (t.size, t.edges.reverse)

/-! ### Subset-counting semantics -/

/-- `S` is independent with respect to the edge list `E`: no edge has both
endpoints in `S`. -/
def IndepIn (E : List (Nat × Nat)) (S : Finset ℕ) : Prop :=
  ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)

instance (E : List (Nat × Nat)) (S : Finset ℕ) : Decidable (IndepIn E S) :=
  inferInstanceAs (Decidable (∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)))

/-- Number of independent `k`-subsets of `range n` w.r.t. `E`. -/
def icount (n k : Nat) (E : List (Nat × Nat)) : Nat :=
  (((Finset.range n).powersetCard k).filter fun S => IndepIn E S).card

/-- Number of independent `k`-subsets of `range n` containing vertex `0`. -/
def icountRoot (n k : Nat) (E : List (Nat × Nat)) : Nat :=
  (((Finset.range n).powersetCard k).filter fun S => IndepIn E S ∧ 0 ∈ S).card

/-- Number of independent `k`-subsets of `range n` avoiding vertex `0`. -/
def icountNoRoot (n k : Nat) (E : List (Nat × Nat)) : Nat :=
  (((Finset.range n).powersetCard k).filter fun S => IndepIn E S ∧ 0 ∉ S).card

/-- The number of independent sets of size `k` in the rose tree `t`
(vertex set `range t.size`, edges `t.edges`). -/
def RT.indepCount (t : RT) (k : Nat) : Nat := icount t.size k t.edges

/-! ### Semantic shape predicates -/

/-- The sequence `f` breaks log-concavity at index `k`:
`f k ^ 2 < f (k-1) * f (k+1)`. -/
def NLCAt (f : ℕ → ℕ) (k : ℕ) : Prop :=
  f k * f k < f (k - 1) * f (k + 1)

/-- The sequence `f` is unimodal with peak at `m`: weakly increasing up to
`m`, weakly decreasing from `m` on (over **all** of `ℕ`). -/
def UnimodalAt (f : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ i, i < m → f i ≤ f (i + 1)) ∧ ∀ i, m ≤ i → f (i + 1) ≤ f i

/-- Bundle: the independence counts of `t` are exactly the entries of `L`
(and `0` beyond), fail log-concavity at `kb`, and are unimodal with peak
`pk`. -/
def GoodTree (t : RT) (L : List Nat) (kb pk : ℕ) : Prop :=
  (∀ k, t.indepCount k = L.getD k 0) ∧ NLCAt t.indepCount kb ∧ UnimodalAt t.indepCount pk

end ErdosattackM
