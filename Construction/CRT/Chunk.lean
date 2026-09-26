/-
The chunk step and the truth-table words.

Per coordinate and chunk `c` (width `w_c`, first bit `8 c`): the tree over the chunk's bits from
its zero labels (garbler) or held labels (evaluator), one cast of width `L` per leaf, and the pin
`P_c = Σ_α A_{c,α} + Δ⃗` (dense, `L` blocks). The evaluator casts every cold leaf and recovers the
hot cast as `P_c - Σ_{α ≠ α_c} A^E_{c,α}` (L3).

The word of an odd modulus `m` of width `ell` is the free combination
`W_m = reduce_ell (Σ_c Σ_α T_{c,m}(α) • A_{c,α})`, an arithmetic label of
`σ_m = Σ_c T_{c,m}(α_c)` (L4, L5).

The per-chunk results are stored as total functions of natural indices (`0` off range), so that the
per-chunk records have one type for every chunk width.
-/

import Construction.CRT.Tree

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC

/-! ### Casts -/

/-- A cast of width `l`: `castAnswers l` answers at `tagOf part`, read block-aligned (D11). -/
def castM (l : Nat) (label : Block) (tagOf : Nat → Nat) : CM (Lanes l) :=
  hlongM label tagOf (castAnswers l) >>= fun value => pure (materialize (castLanes l value))

/-- The sum of a finite family of lanes, lane by lane, stored. -/
def sumLanes {l count : Nat} (family : Fin count → Lanes l) : Lanes l :=
  materialize (∑ index, family index)

/-! ### Tags -/

/-- The tag of a chunk-tree material. -/
def chunkTreeTag (coord c level slot : Nat) : Nat := tagCode Family.chunkTree coord c 0 level slot 0

/-- The tag of part `part` of the cast of leaf `leaf` of chunk `c`. -/
def chunkCastTag (coord c leaf part : Nat) : Nat := tagCode Family.chunkCast coord c 0 0 leaf part

/-! ### The garbler -/

/-- What the garbler keeps of one chunk: leaf labels, casts, published joins and pin. -/
structure ChunkGarbled (L : Nat) where
  /-- Leaf label of leaf `α` (`0` off range). -/
  leaves : Nat → Block
  /-- Cast of leaf `α`. -/
  casts : Nat → Lanes L
  /-- Published join of tree level `n` (`1 ≤ n < w_c`). -/
  joins : Nat → Block
  /-- The pin `Σ_α A_α + Δ⃗`. -/
  pin : Lanes L

/-- The garbler's chunk `c` of coordinate `coord` from the coordinate's zero labels. -/
def chunkGarbleM (T : CrtTable) (coord : Nat) (delta : Block) (zeroLabel : Nat → Block) (c : Nat) :
    CM (ChunkGarbled T.castWidth) :=
  let width := T.chunkWidth c
  let bitMask : Nat → Block := fun n => zeroLabel (T.chunkOffset c + n)
  treeGarbleM (chunkTreeTag coord c) delta (bitMask 0) width >>= fun tree =>
    tableM (2 ^ width) (fun leaf => castM T.castWidth (tree.1 leaf) (chunkCastTag coord c leaf.val))
      >>= fun casts =>
        pure { leaves := atNat tree.1 0
               casts := atNat casts 0
               joins := fun n => tree.2 n ^^^ bitMask n
               pin := materialize (sumLanes casts + deltaLanes T.castWidth delta) }

/-! ### The evaluator -/

/-- What the evaluator holds of one chunk: leaf labels and casts (the hot cast recovered). -/
structure ChunkEval (L : Nat) where
  leaves : Nat → Block
  casts : Nat → Lanes L

/-- The evaluator's chunk `c`: `labels j` is its label of coordinate bit `j`, `v` the value,
`joins` and `pin` the published material of the chunk. -/
def chunkEvalM (T : CrtTable) (coord : Nat) (labels : Nat → Block) (v : Nat) (joins : Nat → Block)
    (pin : Lanes T.castWidth) (c : Nat) : CM (ChunkEval T.castWidth) :=
  let width := T.chunkWidth c
  let value := T.chunkValue v c
  let bitLabel : Nat → Block := fun n => labels (T.chunkOffset c + n)
  treeEvalM (chunkTreeTag coord c) value bitLabel joins width >>= fun tree =>
    tableM (2 ^ width) (fun leaf =>
      if leaf.val = value then pure 0
      else castM T.castWidth (tree leaf) (chunkCastTag coord c leaf.val)) >>= fun casts =>
        let cold := sumLanes fun leaf : Fin (2 ^ width) => if leaf.val = value then 0 else casts leaf
        let hot := materialize (pin - cold)
        pure { leaves := atNat tree 0
               casts := fun leaf => if leaf = value then hot else atNat casts 0 leaf }

/-! ### Words -/

/-- The truth-table word of modulus `m` of width `ell` from the chunks' casts (garbler masks or
evaluator labels alike): `reduce_ell (Σ_c Σ_α T_{c,m}(α) • A_{c,α})`. -/
def truthWord (T : CrtTable) (m ell : Nat) (casts : Nat → Nat → Lanes T.castWidth) : Lanes ell :=
  materialize (reduceTo ell (fun lane =>
    ∑ c : Fin T.chunkCount, ∑ leaf : Fin (2 ^ T.chunkWidth c.val),
      ((T.truth m c.val leaf.val : Nat) : ZMod (2 ^ T.castWidth)) * casts c.val leaf.val lane))

/-! ### Budgets -/

/-- Garbler queries of chunk `c`: its tree and `2 ^ w_c` casts. -/
def chunkGarbleBudget (T : CrtTable) (c : Nat) : Nat :=
  treeGarbleBudget (T.chunkWidth c) + 2 ^ T.chunkWidth c * castAnswers T.castWidth

/-- Evaluator queries of chunk `c`: its tree and `2 ^ w_c - 1` casts. -/
def chunkEvalBudget (T : CrtTable) (c : Nat) : Nat :=
  treeEvalBudget (T.chunkWidth c) + (2 ^ T.chunkWidth c - 1) * castAnswers T.castWidth

end Kriterion.CRT
