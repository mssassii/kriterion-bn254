/-
**The rows kernel of the normalized rows** (`HW`'s target rows) and its opening bound (`HW → H`).

The construction normalizes each digit's rows by scales read off its own row offsets (`Construction/CRT/Rows.lean`);
the public-first core (`Core/BmrNorm.lean`) shows that the evaluator's corrected target rows are distributed as the
unscaled rows at independent uniform scales `(ρ, τ)`, the sign row at `τ²`: `BMR.nTargets` at the coins' row
randomizers (`normTrueRows`, `normRealRows`). Against the old kernel (`Security.Phase3.realRows`) the only change is
digit zero's sign row, `τ² b x²` instead of `τ² b`: it is the lift of `K` at `(ρ, τ x)` (`x ≠ 0` on the curve), so
the opening's kernel bound carries over digit by digit with the sign multiplier `x` at digit zero
(`normRows_etvDist_le`, `455/#Point`), and so does the doubling mass (`normRowsDoubling_le`, `364/#Point`).
-/

import Proof.Privacy.Phase3.OpeningBound
import Proof.Privacy.CRT.Core.BmrNorm
import Construction.CRT.Entry

set_option maxRecDepth 8000

namespace Kriterion.CRT.Privacy.NormRows

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3
open Kriterion.ArgoMAC.Scheme (Coins)
open scoped ENNReal

noncomputable section

/-! ### 1. The kernel -/

/-- The unscaled rows of the scheme's coins. -/
def nctxOf (scalar : NonZeroScalar) (coins : Coins) : BMR.NContext :=
  ⟨fun d => Rows.unscaledOf (Entry.outputKeysOf scalar coins) d⟩

/-- The row randomizers `(ρ, τ)` of the scheme's coins (unused by the construction; the kernel's scales). -/
def scalesOf (coins : Coins) : Fin 91 → NonZeroBase × NonZeroBase :=
  fun d => ((coins.pointRandomness.get d).rho, (coins.pointRandomness.get d).tau)

/-- **The corrected true rows** of the coins at the input. -/
def normTrueRows (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput) :
    Fin 91 → FieldMacToECMac.HomogeneousValue :=
  BMR.nTargets (nctxOf scalar coins) input (scalesOf coins)

/-- **The rows kernel of `HW`**: the corrected true rows under the coins' law. -/
def normRealRows [FieldCertificate] (scalar : NonZeroScalar) : RowsKernel := fun input _ =>
  letI : Fintype Coins := Fintype.ofFinite Coins
  (PMF.uniformOfFintype Coins).map fun coins => some (normTrueRows scalar coins input)

variable [FieldCertificate] [GroupCertificate]

/-! ### 2. The corrected rows as real rows -/

/-- The zero digits of a scalar. -/
def zeros (scalar : NonZeroScalar) (d : Fin 91) : Bool := decide ((digitsOf scalar).get d = .zero)

/-- **The normalized real row**: at a zero digit the lift of `K` at `(ρ, τ x)`, else the real row. -/
def normRealRowOf (zero : Bool) (x : BaseField) (T K : Point) (rho tau : BaseField) :
    FieldMacToECMac.HomogeneousValue :=
  if zero then lift K rho (tau * x) else realRowOf T K rho tau

/-- The normalized real rows of a (tail, randomiser pairs) sample. -/
def normRealRowsOf (multiples : Fin 91 → Point) (zero : Fin 91 → Bool) (x : BaseField)
    (sample : GoodTails × (Fin 91 → NonZeroBase × NonZeroBase)) : Fin 91 → FieldMacToECMac.HomogeneousValue :=
  fun digit => normRealRowOf (zero digit) x (multiples digit) (clampOffsets radixMap sample.1.1 digit)
    (sample.2 digit).1.value (sample.2 digit).2.value

/-- A nonzero digit's corrected row is the old row. -/
theorem nTargets_some (offset input : AffineInput) (phi : BaseField) (rho tau : NonZeroBase) :
    (⟨rho.value ^ 2 * Coordinates.evaluate (Rows.unscaledRows offset (some phi)).x input,
      tau.value ^ 2 * Coordinates.evaluate (Rows.unscaledRows offset (some phi)).y input,
      rho.value * Coordinates.evaluate (Rows.unscaledRows offset (some phi)).z input⟩ :
        FieldMacToECMac.HomogeneousValue) =
      FieldMacToECMac.evaluateRow (Coordinates.rows offset (some phi) rho.value tau.value) input := by
  rw [FieldMacToECMac.evaluateRowsSome]
  simp only [Rows.unscaledRows, Coordinates.evaluateScaleSome, one_pow, one_mul, pow_one]
  rfl

/-- The key of a digit of the scheme's coins. -/
theorem outputKey_get (scalar : NonZeroScalar) (coins : Coins) (d : Fin 91) :
    (Entry.outputKeysOf scalar coins).get d =
      { digit := (digitsOf scalar).get d, offset := coins.offsets.values.get d } :=
  outputKeys_get scalar coins.offsets d

/-- **The corrected true rows are the normalized real rows** of the coins' tail and randomisers. -/
theorem normTrueRows_eq (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    normTrueRows scalar coins input = normRealRowsOf (multiplesOf scalar point) (zeros scalar) input.x (tailRho coins) := by
  funext d
  have keyEq := outputKey_get scalar coins d
  have pointEq := values_point _ coins.offsetsClamped d
  unfold normTrueRows normRealRowsOf normRealRowOf BMR.nTargets
  simp only [nctxOf, scalesOf, Rows.unscaledOf]
  rw [keyEq]
  simp only
  unfold zeros
  by_cases hz : (digitsOf scalar).get d = .zero
  · rw [if_pos (decide_eq_true hz), hz]
    rw [show clampOffsets radixMap (tailRho coins).1.1 d = (coins.offsets.values.get d).point from pointEq.symm,
      JacobianMixed.affineOffsetPoint_eq]
    simp only [digitEndomorphismBase, Rows.unscaledRows, Rows.zeroSign, Coordinates.scale, Coordinates.evaluate, lift]
    congr 1 <;> ring
  · rw [if_neg (fun same => hz (of_decide_eq_true same))]
    have trow := trueRow_eq { digit := (digitsOf scalar).get d, offset := coins.offsets.values.get d }
      (coins.pointRandomness.get d).rho (coins.pointRandomness.get d).tau input point decoded
    simp only at trow
    cases selected : digitEndomorphismBase ((digitsOf scalar).get d) with
    | none =>
      exfalso
      apply hz
      revert selected
      cases (digitsOf scalar).get d <;> simp [digitEndomorphismBase]
    | some phi =>
      rw [selected] at trow
      rw [nTargets_some, trow, pointEq]
      rfl

end

end Kriterion.CRT.Privacy.NormRows
