/-
The one-hot tree of the CRT layer (adapted from xinshu's `bin-to-hot`,
`Construction/PGS/OneHot.lean`): the chunk trees, the extraction trees and the growth of the kept
one-hot all use one level step.

A level of `2 ^ n` labels is extended by one bit exactly as xinshu's `extendLevel`: the right child
of slot `s` is the material `y_s`, the left child is `G_s ⊕ y_s`, entries `0 .. 2 ^ n - 1` of the new
level are the left children, so the hot index moves from `h` to `h + b * 2 ^ n` (little-endian).
The material is one field-hash block, `y_s = hLabel(G_s, tag(level n, slot s))`, one query per slot.
Level 0 is the constant wire (garbler `Δ`, evaluator `0`); step 0 is free and appends the bit-0
label, so level 1 is `(z ⊕ Δ, z)` for the garbler and `(z ⊕ b Δ, z ⊕ b Δ)` for the evaluator.

The garbler hashes every slot of levels `1 .. levels - 1` and reports the XOR of each level's
materials (`levelSum`; the published join of level `n` is `levelSum n ⊕ (bit-`n` mask)`). The
evaluator with known bits (chunk trees, growth) hashes every slot but the active one
(`value mod 2 ^ n`, xinshu's `activeAt`), in ascending slot order, and recovers the active right
child from the join. The fused extraction's evaluator, whose bits are not known in advance, is in
`Extract.lean`.
-/

import Construction.CRT.Query

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC

/-- The XOR of a finite family of blocks. -/
def xorFold {width count : Nat} (family : Fin count → BitVec width) : BitVec width :=
  Fin.foldl count (fun acc entry => acc ^^^ family entry) 0

/-- The XOR of a finite family of blocks with one entry skipped. -/
def xorFoldExcept {width count : Nat} (skip : Fin count) (family : Fin count → BitVec width) : BitVec width :=
  Fin.foldl count (fun acc entry => if entry = skip then acc else acc ^^^ family entry) 0

/-- Extend one level: entries `0 .. 2 ^ n - 1` are the left children `parent ⊕ right`, entries
`2 ^ n .. 2 ^ (n + 1) - 1` the right children `right`. -/
def extendLevel (n : Nat) (parent right : Fin (2 ^ n) → Label) : Fin (2 ^ (n + 1)) → Label :=
  fun entry =>
    if below : entry.val < 2 ^ n then
      parent ⟨entry.val, below⟩ ^^^ right ⟨entry.val, below⟩
    else
      right ⟨entry.val - 2 ^ n, by
        have expand : (2 : Nat) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
        have bound := entry.isLt
        omega⟩

/-- The active slot at level `n`: the low `n` bits of the value. -/
def activeAt (value n : Nat) : Fin (2 ^ n) :=
  ⟨value % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-! ### One level -/

/-- The garbler's step at level `n ≥ 1`: hash every slot (ascending) at `tagOf slot`, extend.
Returns the new level and the XOR of the materials. -/
def garbleStepM (n : Nat) (tagOf : Nat → Nat) (parent : Fin (2 ^ n) → Label) :
    CM ((Fin (2 ^ (n + 1)) → Label) × Label) :=
  tableM (2 ^ n) (fun slot => hLabelM (parent slot) (tagOf slot.val)) >>= fun materials =>
    pure (stored (extendLevel n parent materials), xorFold materials)

/-- The evaluator's step at level `n ≥ 1`: hash every slot but `active` (ascending); the active
slot's material is `join ⊕ bitLabel ⊕ (XOR of the others)`. -/
def evalStepM (n : Nat) (tagOf : Nat → Nat) (active : Fin (2 ^ n)) (bitLabel join : Label)
    (parent : Fin (2 ^ n) → Label) : CM (Fin (2 ^ (n + 1)) → Label) :=
  tableM (2 ^ n) (fun slot => if slot = active then pure 0 else hLabelM (parent slot) (tagOf slot.val))
    >>= fun materials =>
      pure (stored (extendLevel n parent fun slot =>
        if slot = active then join ^^^ bitLabel ^^^ xorFoldExcept active materials
        else materials slot))

/-! ### Trees from the constant wire -/

/-- The garbler's tree over `levels` bits from the constant wire `Δ` and the bit-0 label `bit0`:
the labels of level `levels` and the XOR of the materials of each hashed level `1 .. levels - 1`
(`0` elsewhere). `tagOf level slot` is the tag of a material. -/
def treeGarbleM (tagOf : Nat → Nat → Nat) (delta bit0 : Label) :
    (levels : Nat) → CM ((Fin (2 ^ levels) → Label) × (Nat → Label))
  | 0 => pure (fun _ => delta, fun _ => 0)
  | n + 1 =>
      treeGarbleM tagOf delta bit0 n >>= fun previous =>
        if n = 0 then
          pure (stored (extendLevel n previous.1 fun _ => bit0), previous.2)
        else
          garbleStepM n (tagOf n) previous.1 >>= fun step =>
            pure (step.1, fun level => if level = n then step.2 else previous.2 level)

/-- The evaluator's tree with known bits: `value` is the tree's value (its low `n` bits give the
active slot of level `n`), `bitLabel n` the evaluator's label of bit `n`, `join n` the published
join of level `n`. -/
def treeEvalM (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel join : Nat → Label) :
    (levels : Nat) → CM (Fin (2 ^ levels) → Label)
  | 0 => pure fun _ => 0
  | n + 1 =>
      treeEvalM tagOf value bitLabel join n >>= fun previous =>
        if n = 0 then
          pure (stored (extendLevel n previous fun _ => bitLabel 0))
        else
          evalStepM n (tagOf n) (activeAt value n) (bitLabel n) (join n) previous

/-! ### Growth from a given level -/

/-- The garbler's growth of a one-hot of `2 ^ start` labels by `count` bits at levels
`start, start + 1, ...`: the grown labels and each level's material XOR. -/
def growGarbleM (tagOf : Nat → Nat → Nat) (start : Nat) (labels : Fin (2 ^ start) → Label) :
    (count : Nat) → CM ((Fin (2 ^ (start + count)) → Label) × (Nat → Label))
  | 0 => pure (labels, fun _ => 0)
  | k + 1 =>
      growGarbleM tagOf start labels k >>= fun previous =>
        garbleStepM (start + k) (tagOf (start + k)) previous.1 >>= fun step =>
          pure (step.1, fun level => if level = start + k then step.2 else previous.2 level)

/-- The evaluator's growth with known bits. -/
def growEvalM (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel join : Nat → Label) (start : Nat)
    (labels : Fin (2 ^ start) → Label) : (count : Nat) → CM (Fin (2 ^ (start + count)) → Label)
  | 0 => pure labels
  | k + 1 =>
      growEvalM tagOf value bitLabel join start labels k >>= fun previous =>
        evalStepM (start + k) (tagOf (start + k)) (activeAt value (start + k))
          (bitLabel (start + k)) (join (start + k)) previous

/-! ### Budgets -/

/-- Garbler queries of a tree over `levels` bits: `2 ^ levels - 2` for `levels ≥ 1`. -/
def treeGarbleBudget : Nat → Nat
  | 0 => 0
  | n + 1 => treeGarbleBudget n + (if n = 0 then 0 else 2 ^ n)

/-- Evaluator queries of a tree over `levels` bits: `2 ^ levels - levels - 1` for `levels ≥ 1`. -/
def treeEvalBudget : Nat → Nat
  | 0 => 0
  | n + 1 => treeEvalBudget n + (if n = 0 then 0 else 2 ^ n - 1)

/-- Garbler queries of a growth by `count` bits from level `start`. -/
def growGarbleBudget (start : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => growGarbleBudget start k + 2 ^ (start + k)

/-- Evaluator queries of a growth by `count` bits from level `start`. -/
def growEvalBudget (start : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => growEvalBudget start k + (2 ^ (start + k) - 1)

end Kriterion.CRT
