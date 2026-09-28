/-
The pure definition of one fused extraction stage, parametric in the tree material
`mat level slot label` and the leaf cast `castF leaf label`: the garbler by
node recursion, the evaluator by rounds. It is the text of `Proof/Correctness/CRT/ExtractStage.lean`
(sections "The stage: parameters and the garbler" and "The evaluator", and `xsum`), copied unchanged
except for the namespace; its C3
invariant (L8 to L10) is proved against exactly these definitions.

The programs `extStageGarbleM` and `extStageEvalM` of `Extract.lean` ask the queries of this
structure in round order and must equal these definitions at
`mat level slot label = hLabel H label (treeTag level slot)` and
`castF leaf label = castLanes rb (hlong H (embed label) (castTag leaf) (castAnswers rb))` (L20, package C6).
-/

import Construction.CRT.Lanes
import Mathlib.Algebra.BigOperators.Pi

namespace Kriterion.CRT.ExtractSpec

open scoped BigOperators
open Cryptography Kriterion.CRT

/-- XOR of a family of blocks over a finset. -/
def xsum {ι : Type} (s : Finset ι) (f : ι → Label) : Label := s.fold (fun a b : Label => a ^^^ b) 0 f

/-! ### The stage: parameters and the garbler -/

/-- One fused stage: width `w ≤ rb`, tree material `mat level slot label` (hashed at levels
`1 .. w - 1`), and leaf casts `castF leaf label : Lanes rb`. -/
structure StageParams (rb : Nat) where
  w : Nat
  hw : w ≤ rb
  mat : Nat → Nat → Label → Label
  castF : Nat → Label → Lanes rb

section Stage

variable {rb : Nat} (sp : StageParams rb)

/-- Step material of level `n` at slot `x` with label `lab`: the free bit `b_0` at level 0,
`mat n x lab` above. -/
def stepMat (b0 : Label) : Nat → Nat → Label → Label
  | 0, _, _ => b0
  | n + 1, x, lab => sp.mat (n + 1) x lab

/-- Garbler node labels: level `n`, slot `x` (read modulo `2 ^ n`). The root is `Δ`; the right
child (bit `n` set) is the material, the left child the parent XOR the material. -/
def gNode (b0 Δ : Label) : Nat → Nat → Label
  | 0, _ => Δ
  | n + 1, x =>
    if x.testBit n then stepMat sp b0 n (x % 2 ^ n) (gNode b0 Δ n (x % 2 ^ n))
    else gNode b0 Δ n (x % 2 ^ n) ^^^ stepMat sp b0 n (x % 2 ^ n) (gNode b0 Δ n (x % 2 ^ n))

/-- `b_0 = laneBit (reduce_w R) 0`. -/
def gBit0 (R : Lanes rb) : Label := laneBit (reduceTo sp.w R) 0

/-- Leaf `α` of the garbler's tree. -/
def gLeaf (R : Lanes rb) (Δ : Label) (α : Nat) : Label := gNode sp (gBit0 sp R) Δ sp.w α

/-- Cast of leaf `α`. -/
def gCast (R : Lanes rb) (Δ : Label) (α : Nat) : Lanes rb := sp.castF α (gLeaf sp R Δ α)

/-- Class sum `res_n = Σ_α (α mod 2^n) • A_α`. -/
def gRes (R : Lanes rb) (Δ : Label) (n : Nat) : Lanes rb :=
  ∑ α ∈ Finset.range (2 ^ sp.w), ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • gCast sp R Δ α

/-- Bit mask `b_n` (`b_0` for `n = 0`, else `laneBit (sub - reduce_w res_n) n`). -/
def gBit (R : Lanes rb) (Δ : Label) (n : Nat) : Label :=
  if n = 0 then gBit0 sp R else laneBit (reduceTo sp.w R - reduceTo sp.w (gRes sp R Δ n)) n

/-- Level sum `Y_n = ⊕_x mat n x (G_{n,x})`. -/
def gLevelSum (R : Lanes rb) (Δ : Label) (n : Nat) : Label :=
  xsum (Finset.range (2 ^ n)) fun x => sp.mat n x (gNode sp (gBit0 sp R) Δ n x)

/-- Join `J_n = Y_n ⊕ b_n` (published for `n = 1 .. w - 1`). -/
def gJoin (R : Lanes rb) (Δ : Label) (n : Nat) : Label := gLevelSum sp R Δ n ^^^ gBit sp R Δ n

/-- Pin `P = Σ_α A_α + Δ⃗`. -/
def gPin (R : Lanes rb) (Δ : Label) : Lanes rb :=
  ∑ α ∈ Finset.range (2 ^ sp.w), gCast sp R Δ α + deltaLanes rb Δ

/-- The peeled remainder `R' = peelDiv R res_w w`. -/
def gNext (R : Lanes rb) (Δ : Label) : Lanes (rb - sp.w) := peelDiv R (gRes sp R Δ sp.w) sp.w

/-! ### The evaluator -/

/-- Labels of nodes off the active path of `s`, from the closed labels `cl j` (the sibling of the
active node at level `j + 1`). -/
def offPath (s : Nat) (cl : Nat → Label) : Nat → Nat → Label
  | 0, _ => 0
  | n + 1, x =>
    if x % 2 ^ n = s % 2 ^ n then cl n
    else if x.testBit n then sp.mat n (x % 2 ^ n) (offPath s cl n (x % 2 ^ n))
    else offPath s cl n (x % 2 ^ n) ^^^ sp.mat n (x % 2 ^ n) (offPath s cl n (x % 2 ^ n))

/-- The leaves outside the level-`n` active class. -/
def eClass (s n : Nat) : Finset Nat :=
  (Finset.range (2 ^ sp.w)).filter fun α => α % 2 ^ n ≠ s % 2 ^ n

/-- The evaluator's cast of an off-path leaf. -/
def eCast (s : Nat) (cl : Nat → Label) (α : Nat) : Lanes rb :=
  sp.castF α (offPath sp s cl sp.w α)

/-- `res^E_n = R_n + q_n • (P - T_n)`. -/
def eRes (s : Nat) (cl : Nat → Label) (P : Lanes rb) (n : Nat) : Lanes rb :=
  ∑ α ∈ eClass sp s n, ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • eCast sp s cl α +
    ((s % 2 ^ n : Nat) : ZMod (2 ^ rb)) • (P - ∑ α ∈ eClass sp s n, eCast sp s cl α)

/-- The evaluator's bit label of round `n`. -/
def eBit (RE : Lanes rb) (s : Nat) (cl : Nat → Label) (P : Lanes rb) (n : Nat) : Label :=
  if n = 0 then laneBit (reduceTo sp.w RE) 0
  else laneBit (reduceTo sp.w RE - reduceTo sp.w (eRes sp s cl P n)) n

/-- The XOR of the cold materials of level `n`. -/
def eLevelSum (s : Nat) (cl : Nat → Label) (n : Nat) : Label :=
  xsum ((Finset.range (2 ^ n)).erase (s % 2 ^ n)) fun x => sp.mat n x (offPath sp s cl n x)

/-- The solved hot material of level `n` (`b^E_0` at level 0). -/
def eHot (RE : Lanes rb) (s : Nat) (J : Nat → Label) (P : Lanes rb) (cl : Nat → Label) (n : Nat) :
    Label :=
  if n = 0 then eBit sp RE s cl P 0 else eBit sp RE s cl P n ^^^ J n ^^^ eLevelSum sp s cl n

/-- The rounds: after `n` rounds, the active label at level `n` and the closed labels `cl j`,
`j < n`. -/
def eRounds (RE : Lanes rb) (s : Nat) (J : Nat → Label) (P : Lanes rb) : Nat → Label × (Nat → Label)
  | 0 => (0, fun _ => 0)
  | n + 1 =>
    let st := eRounds RE s J P n
    let y := eHot sp RE s J P st.2 n
    (if s.testBit n then y else st.1 ^^^ y,
      fun j => if j = n then (if s.testBit n then st.1 ^^^ y else y) else st.2 j)

/-- The evaluator's leaf labels. -/
def eLeaf (RE : Lanes rb) (s : Nat) (J : Nat → Label) (P : Lanes rb) (α : Nat) : Label :=
  if α = s then (eRounds sp RE s J P sp.w).1 else offPath sp s (eRounds sp RE s J P sp.w).2 sp.w α

/-- The evaluator's bit label `b^E_n`. -/
def eBitOut (RE : Lanes rb) (s : Nat) (J : Nat → Label) (P : Lanes rb) (n : Nat) : Label :=
  eBit sp RE s (eRounds sp RE s J P n).2 P n

/-- The evaluator's upcast `U^E = R_w + s • (P - T_w)`. -/
def eUp (RE : Lanes rb) (s : Nat) (J : Nat → Label) (P : Lanes rb) : Lanes rb :=
  eRes sp s (eRounds sp RE s J P sp.w).2 P sp.w

/-- The evaluator's peeled remainder. -/
def eNext (RE : Lanes rb) (s : Nat) (J : Nat → Label) (P : Lanes rb) : Lanes (rb - sp.w) :=
  peelDiv RE (eUp sp RE s J P) sp.w

end Stage

end Kriterion.CRT.ExtractSpec
