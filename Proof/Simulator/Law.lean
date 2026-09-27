/-
**The machine's sampler laws** (xinshu's release-r1 samplers, kept for the CRT machine).

`fieldCellLaw` (bounded rejection over `254` coins below `p`, `rejectLaw`, whose machine realisation starts
from `memSem_sampleWord`), `wordLaw` (a uniform coin word), `curvePointLaw` and `tailLaw` (a uniform finite
point by `x`-rejection and a fair sign; `90` of them and the clamp check), `lambdaLaw`, `pairLaw` and `liftLaw` (the lift
randomiser pairs), `preimageLaw` (the `sampleFp` preimage of a collector's mask). The CRT machine's law
(`Proof/Simulator/CRT/LawShape.lean`, `Bounded.lean`) is stated with these.
-/

import Proof.Simulator.Sampling
import Proof.Privacy.Phase3.Glue.AbstractSimulator

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography GarbledCircuit Cryptography.BoundedMachine
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### The machine's sampler laws -/

/-- A RAM word read as a field element. -/
def wordField (value : Word) : BaseField := (value.toNat : BaseField)

/-- A RAM word read as a block. -/
def wordBlock (value : Word) : Block := BitVec.ofNat 128 value.toNat

/-- One field cell: bounded rejection below `p` (`Stage1.fieldCell`). -/
def fieldCellLaw : PMF (Option BaseField) :=
  (rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts).map
    (Option.map fun (value : Nat) => ((value : Nat) : BaseField))

/-- A uniform `width`-bit word (`Stage1.wordCell`). -/
def wordLaw (width : Nat) : PMF Nat := (PMF.uniformOfFintype (Fin (2 ^ width))).map Fin.val

/-- A finite family read as a total function (zero outside). -/
def total {count : Nat} {α : Type} (zero : α) (family : Fin count → α) (index : Nat) : α :=
  if inside : index < count then family ⟨index, inside⟩ else zero

/-- The machine's `x`-acceptance: `x < p` and `x³ + 3` a square, witnessed by its
`(p + 1) / 4`-th power. -/
def curveXAccept (value : Nat) : Bool :=
  decide (value < pNat) &&
    decide (((value : BaseField) ^ 3 + 3) ^ sqrtExponent * ((value : BaseField) ^ 3 + 3) ^ sqrtExponent =
      (value : BaseField) ^ 3 + 3)

/-- The point of an accepted `x` and a sign. -/
def curvePointOf (value : Nat) (sign : Bool) : Option FieldMacToECMac.AffineOffset :=
  let root := ((value : BaseField) ^ 3 + 3) ^ sqrtExponent
  let y := if sign then -root else root
  if onCurve : y ^ 2 = (value : BaseField) ^ 3 + 3 then
    some ⟨⟨value, y⟩, onCurve⟩
  else none

/-- One tail point: `x` by bounded rejection, then a fair sign (`Opening.tailOne`). -/
def curvePointLaw : PMF (Option FieldMacToECMac.AffineOffset) :=
  (rejectLaw fieldWidth curveXAccept attempts).bind fun drawn => match drawn with
    | none => PMF.pure none
    | some value => (PMF.uniformOfFintype Bool).map (curvePointOf value)

/-- **The machine's tail law**: `90` points, then the clamp check (`Opening.head` aborts when
`β · H = O`). -/
def tailLaw [FieldCertificate] [GroupCertificate] :
    PMF (Option (Vector FieldMacToECMac.AffineOffset 90)) :=
  (optionProduct 90 fun _ => curvePointLaw).map fun points => points.bind fun points =>
    if FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0 then none
    else some (Vector.ofFn points)

/-- One lift randomiser in `[1, p)` (`Opening.nonZeroCell`). -/
def lambdaLaw : PMF (Option NonZeroBase) :=
  (rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts).map
    fun drawn => drawn.bind fun value =>
      if nonzero : (value : BaseField) ≠ 0 then some ⟨value, nonzero⟩ else none

/-- One randomiser pair `(λ, t)` (`Opening.lambdaOne`): `λ`, then `t`. -/
def pairLaw : PMF (Option (NonZeroBase × NonZeroBase)) :=
  (optionProduct 2 fun _ => lambdaLaw).map (Option.map fun pair => (pair 0, pair 1))

/-- **The machine's lift law**: `91` randomiser pairs. -/
def liftLaw : PMF (Option (Fin digitCount → NonZeroBase × NonZeroBase)) :=
  optionProduct digitCount fun _ => pairLaw

/-- **The machine's preimage law** (`Opening.preimageOne`): `m < q + [y < ρ]` by bounded
rejection over `131` coins, then the limbs of `y + p · m`. -/
def preimageLaw (value : BaseField) : PMF (Option (Block × Block × Block)) :=
  (rejectLaw multiplierWidth
      (fun candidate => decide (candidate < preimageQuotient + (if value.val < preimageRemainder then 1 else 0)))
      attempts).map
    (Option.map fun multiplier => limbs (value.val + baseFieldModulus * multiplier))

end

end Kriterion.ArgoMAC.PlanB.SimMachine
