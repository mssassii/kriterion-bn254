/-
The fused extraction stage (Duty-Free Bits' `extract.rs`) as query
programs: the garbler and the round-ordered evaluator.

A stage takes a remainder `R` (an arithmetic label of width `rb` of a value `σ < 2 ^ rb`), a width
`w ≤ rb`, and casts of width `rb` (in schedule T9 stages 0 and 1 are never last; stage 2, of width
1, is free and is not a stage here). It writes `s = σ mod 2 ^ w`.

Garbler: `sub = reduce_w R`, `b_0 = laneBit sub 0`; the tree over `w` bits from `(b_0 ⊕ Δ, b_0)`
(levels `1 .. w - 1` hashed); casts `A_α` of every leaf; class sums
`res_n = Σ_α (α mod 2 ^ n) • A_α`; bits `b_n = laneBit (sub - reduce_w res_n) n`; joins
`J_n = Y_n ⊕ b_n`; pin `P = Σ_α A_α + Δ⃗`; next remainder `peelDiv R res_w w`.

Evaluator (the order is forced): round 0 expands the closed level-1 sibling `(s mod 2) xor 1`
(both level-1 slots hold `b_0^E`); round `n = 1 .. w - 1` computes
`res_n^E = R_n + q_n • (P - T_n)` (`q_n = s mod 2 ^ n`, `R_n`, `T_n` the class sums and cast sums
over the leaves expanded so far), `b_n^E`, the hot material `b_n^E ⊕ J_n ⊕ Y_n`, the two children
of the active node, keeps the one selected by bit `n` of `s` and expands the other at level
`n + 1`. An expansion of a closed node at level `λ` hashes its subtree level by level (levels
ascending, slots ascending) and then casts its leaves (ascending, parts ascending); each node is
hashed once and the active path never. Finally `U^E = R_w + s • (P - T_w)` and the next remainder
is `peelDiv R^E U^E w`.

The pure definitions these programs must equal are those of `ExtractSpec`; the program is
the object the evaluator runs.
-/

import Construction.CRT.Chunk

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC

variable {rb : Nat}

/-! ### Garbler -/

/-- What the garbler keeps of one stage. -/
structure StageGarbled (rb w : Nat) where
  /-- Leaf labels (`α < 2 ^ w`). -/
  leaves : Nat → Label
  /-- Bit masks `b_n` (`n < w`). -/
  bits : Nat → Label
  /-- Published joins `J_n` (`1 ≤ n < w`). -/
  joins : Nat → Label
  /-- Published pin. -/
  pin : Lanes rb
  /-- Next remainder mask. -/
  next : Lanes (rb - w)

/-- The garbler of one fused stage. `treeTag level slot` and `castTag leaf part` are the tags. -/
def extStageGarbleM (w : Nat) (treeTag castTag : Nat → Nat → Nat) (delta : Label)
    (remainder : Lanes rb) : CM (StageGarbled rb w) :=
  let sub := materialize (reduceTo w remainder)
  let bit0 := laneBit sub 0
  treeGarbleM treeTag delta bit0 w >>= fun tree =>
    tableM (2 ^ w) (fun leaf => castM rb (tree.1 leaf) (castTag leaf.val)) >>= fun casts =>
      let classSum : Fin (w + 1) → Lanes rb := stored fun n =>
        sumLanes fun leaf : Fin (2 ^ w) => scaleLanes (leaf.val % 2 ^ n.val) (casts leaf)
      let bits : Fin w → Label := stored fun n =>
        if n.val = 0 then bit0
        else laneBit (sub - reduceTo w (atNat classSum 0 n.val)) n.val
      pure { leaves := atNat tree.1 0
             bits := atNat bits 0
             joins := fun n => tree.2 n ^^^ atNat bits 0 n
             pin := materialize (sumLanes casts + deltaLanes rb delta)
             next := materialize (peelDiv remainder (atNat classSum 0 w) w) }

/-! ### Evaluator -/

/-- The evaluator's state between rounds. -/
structure StageState (rb : Nat) where
  /-- XOR of the hashed materials of each level. -/
  levelSum : Nat → Label
  /-- `R_j`: `Σ (α mod 2 ^ j) • A^E_α` over the leaves of subtrees expanded at levels `≤ j`. -/
  classSum : Nat → Lanes rb
  /-- `T_j`: `Σ A^E_α` over the same leaves. -/
  castSum : Nat → Lanes rb
  /-- Leaf labels known so far. -/
  leaves : Nat → Label
  /-- The active node's label. -/
  active : Label
  /-- Bit labels `b_n^E` known so far. -/
  bits : Nat → Label

/-- The subtree below a closed node at level `start`, slot `slot`: its labels at relative depth
`depth` (relative slot `t` is absolute slot `slot + 2 ^ start * t`) and the XOR of the hashed
materials by absolute level. -/
def subtreeM (treeTag : Nat → Nat → Nat) (start slot : Nat) (label : Label) :
    (depth : Nat) → CM ((Fin (2 ^ depth) → Label) × (Nat → Label))
  | 0 => pure (fun _ => label, fun _ => 0)
  | d + 1 =>
      subtreeM treeTag start slot label d >>= fun previous =>
        garbleStepM d (fun t => treeTag (start + d) (slot + 2 ^ start * t)) previous.1 >>= fun step =>
          pure (step.1, fun level => if level = start + d then step.2 else previous.2 level)

/-- Expand the closed node at level `start`, slot `slot`, with label `label`: hash its subtree,
cast its leaves, and add them to the state's sums. -/
def expandM (w : Nat) (treeTag castTag : Nat → Nat → Nat) (start slot : Nat) (label : Label)
    (state : StageState rb) : CM (StageState rb) :=
  subtreeM treeTag start slot label (w - start) >>= fun subtree =>
    tableM (2 ^ (w - start)) (fun t =>
      castM rb (subtree.1 t) (castTag (slot + 2 ^ start * t.val))) >>= fun casts =>
      let classSum : Fin (w + 1) → Lanes rb := stored fun j =>
        if start ≤ j.val then
          materialize (state.classSum j.val + sumLanes fun t : Fin (2 ^ (w - start)) =>
            scaleLanes ((slot + 2 ^ start * t.val) % 2 ^ j.val) (casts t))
        else state.classSum j.val
      let added := sumLanes casts
      let castSum : Fin (w + 1) → Lanes rb := stored fun j =>
        if start ≤ j.val then materialize (state.castSum j.val + added) else state.castSum j.val
      pure { levelSum := fun level => state.levelSum level ^^^ subtree.2 level
             classSum := atNat classSum 0
             castSum := atNat castSum 0
             leaves := fun leaf =>
               if leaf < 2 ^ w ∧ leaf % 2 ^ start = slot then atNat subtree.1 0 (leaf / 2 ^ start)
               else state.leaves leaf
             active := state.active
             bits := state.bits }

/-- Round `n ≥ 1` of the evaluator. -/
def stageRoundM (w : Nat) (treeTag castTag : Nat → Nat → Nat) (sub : Lanes w) (value : Nat)
    (joins : Nat → Label) (pin : Lanes rb) (n : Nat) (state : StageState rb) :
    CM (StageState rb) :=
  let prefixValue := value % 2 ^ n
  let classSum := materialize (state.classSum n + scaleLanes prefixValue (pin - state.castSum n))
  let bit := laneBit (sub - reduceTo w classSum) n
  let hot := bit ^^^ joins n ^^^ state.levelSum n
  let left := state.active ^^^ hot
  let right := hot
  let bits := fun k => if k = n then bit else state.bits k
  if value.testBit n then
    expandM w treeTag castTag (n + 1) prefixValue left { state with active := right, bits }
  else
    expandM w treeTag castTag (n + 1) (prefixValue + 2 ^ n) right { state with active := left, bits }

/-- Rounds `n, n + 1, ..., n + remaining - 1`. -/
def stageRoundsM (w : Nat) (treeTag castTag : Nat → Nat → Nat) (sub : Lanes w) (value : Nat)
    (joins : Nat → Label) (pin : Lanes rb) : (remaining n : Nat) → StageState rb → CM (StageState rb)
  | 0, _, state => pure state
  | remaining + 1, n, state =>
      stageRoundM w treeTag castTag sub value joins pin n state >>=
        stageRoundsM w treeTag castTag sub value joins pin remaining (n + 1)

/-- What the evaluator obtains from one stage. -/
structure StageEval (rb w : Nat) where
  /-- Leaf labels (`α < 2 ^ w`). -/
  leaves : Nat → Label
  /-- Bit labels `b_n^E` (`n < w`). -/
  bits : Nat → Label
  /-- Next remainder label. -/
  next : Lanes (rb - w)

/-- The evaluator of one fused stage: `value` is the stage value `s = σ mod 2 ^ w`, `joins` and
`pin` the stage's published material. -/
def extStageEvalM (w : Nat) (treeTag castTag : Nat → Nat → Nat) (remainder : Lanes rb)
    (value : Nat) (joins : Nat → Label) (pin : Lanes rb) : CM (StageEval rb w) :=
  let sub := materialize (reduceTo w remainder)
  let bit0 := laneBit sub 0
  let start : StageState rb :=
    { levelSum := fun _ => 0
      classSum := fun _ => 0
      castSum := fun _ => 0
      leaves := fun _ => 0
      active := bit0
      bits := fun k => if k = 0 then bit0 else 0 }
  expandM w treeTag castTag 1 ((value % 2) ^^^ 1) bit0 start >>= fun afterZero =>
    stageRoundsM w treeTag castTag sub value joins pin (w - 1) 1 afterZero >>= fun final =>
      let upcast := materialize (final.classSum w + scaleLanes value (pin - final.castSum w))
      let leaves : Fin (2 ^ w) → Label := stored fun leaf =>
        if leaf.val = value then final.active else final.leaves leaf.val
      let bits : Fin w → Label := stored fun n => final.bits n.val
      pure { leaves := atNat leaves 0
             bits := atNat bits 0
             next := materialize (peelDiv remainder upcast w) }

/-! ### Budgets -/

/-- Garbler queries of a stage: the tree and `2 ^ w` casts of width `rb`. -/
def extGarbleBudget (rb w : Nat) : Nat := treeGarbleBudget w + 2 ^ w * castAnswers rb

/-- Evaluator queries of a stage: `2 ^ w - w - 1` materials and `2 ^ w - 1` casts. -/
def extEvalBudget (rb w : Nat) : Nat := (2 ^ w - w - 1) + (2 ^ w - 1) * castAnswers rb

end Kriterion.CRT
