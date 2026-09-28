/-
**Row normalization** (research note §2): the digit rows with their `Z` and sign-row constants
normalized to bits.

A digit with offset `K = (a, b)` and digit endomorphism `φ` has the *unscaled* rows `R*`:
the Jacobian `X` and `Z` rows of `Coordinates.rows` at randomizer `1`, and the sign row
`Coordinates.signCoefficients` for a nonzero digit, `b · x²` for digit zero (`zeroSign`; on the
curve `x ≠ 0`, so it has the character of `b = y_R`). Their normalizing coefficients `z₀` (the
`Z` constant: `−a`, or `1` for digit zero) and `s₄` (the sign row's `x²` coefficient:
`3ab(27 − b²)φ⁸`, or `b`) are nonzero.

With `K_z`, `K_c` the element offsets of the collectors `rowZ_x9` and `rowY_cubic`, the garbler sets

* `ε_Z = [K_z = 0]`, `ρ = (K_z + ε_Z) / z₀`, and scales `X` by `ρ²`, `Z` by `ρ`;
* `ε_S = [K_c = 0]`, `κ = (K_c + ε_S) / s₄`, and scales the sign row by `κ`;
* `ν = [χ(κ) = −1]`.

Then the published `Z` and sign-row constants of `Biquadratic.garbleZ`/`garbleY` are exactly `ε_Z`
and `ε_S` (`garbleZ_norm`, `garbleY_norm`, in `Proof/Correctness/CRT/Rows.lean`), so a digit publishes
`NormRow`: the `X` constant and three bits. The evaluator reads the rows with the flags as constants
and negates the sign row when `ν` (`evaluateNormRow`): `(−1)^ν κ = χ(κ) κ` is a nonzero square, so the
old decoder (`Garbling.decodeHomogeneous`) applies.
-/

import Construction.Garbling
import Construction.ArgoMAC.NormRow

namespace Kriterion.CRT.Rows

open Kriterion Kriterion.BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-- A coefficient table times a field element. -/
def multiply (factor : BaseField) (coefficients : Coordinates.Coefficients) : Coordinates.Coefficients :=
  { constant := factor * coefficients.constant
    x := factor * coefficients.x
    y := factor * coefficients.y
    xy := factor * coefficients.xy
    xSquared := factor * coefficients.xSquared
    ySquared := factor * coefficients.ySquared }

/-- Digit zero's sign row `b · x²`. -/
def zeroSign (offset : AffineInput) : Coordinates.Coefficients :=
  { constant := 0, x := 0, y := 0, xy := 0, xSquared := offset.y, ySquared := 0 }

/-- **The unscaled rows** of an offset and a digit endomorphism. -/
def unscaledRows (offset : AffineInput) (endomorphismBase : Option BaseField) : Coordinates.Rows :=
  { x := Coordinates.scale endomorphismBase 1 2 offset.x (Coordinates.xCoefficients offset)
    y := match endomorphismBase with
      | none => zeroSign offset
      | some phi => Coordinates.scale (some phi) 1 2 offset.y (Coordinates.signCoefficients offset)
    z := Coordinates.scale endomorphismBase 1 1 1 (Coordinates.zCoefficients offset) }

/-- A bit as a field element. -/
def flagValue (flag : Bool) : BaseField := if flag then 1 else 0

/-- `[k = 0]`. -/
def zeroFlag (k : BaseField) : Bool := decide (k = 0)

/-- **The normalizing scale** of a coefficient `c` against an offset `k`: `(k + [k = 0]) · c⁻¹`. -/
def scaleOf (c k : BaseField) : BaseField := (k + flagValue (zeroFlag k)) * c⁻¹

/-- `ρ`, from the `Z` constant and the offset of `rowZ_x9`. -/
def rhoOf (rows : Coordinates.Rows) (K : Biquadratic.Values) : BaseField :=
  scaleOf rows.z.constant (K (.inl .rowZ_x9))

/-- `κ`, from the sign row's `x²` coefficient and the offset of `rowY_cubic`. -/
def kappaOf (rows : Coordinates.Rows) (K : Biquadratic.Values) : BaseField :=
  scaleOf rows.y.xSquared (K (.inl .rowY_cubic))

/-- Rows scaled by `ρ²` (`X`), `κ` (sign row) and `ρ` (`Z`). -/
def scaled (rho kappa : BaseField) (rows : Coordinates.Rows) : Coordinates.Rows :=
  { x := multiply (rho ^ 2) rows.x, y := multiply kappa rows.y, z := multiply rho rows.z }

/-- **The normalized rows** of unscaled rows and the digit's element offsets. -/
def normRows (rows : Coordinates.Rows) (K : Biquadratic.Values) : Coordinates.Rows :=
  scaled (rhoOf rows K) (kappaOf rows K) rows

/-- `ν = [χ(κ) = −1]`, by the square-and-multiply power. -/
def signBit (kappa : BaseField) : Bool :=
  decide (Garbling.fieldPower kappa Garbling.characterExponent = -1)

/-- **The published row data** of a digit. -/
def garbleNormRow (rows : Coordinates.Rows) (K : Biquadratic.Values) : NormRow :=
  { xC0 := (Biquadratic.garbleX (normRows rows K).x.constant K).c0
    zFlag := zeroFlag (K (.inl .rowZ_x9))
    sFlag := zeroFlag (K (.inl .rowY_cubic))
    sign := signBit (kappaOf rows K) }

/-- `(−1)^ν s`. -/
def signed (sign : Bool) (value : BaseField) : BaseField := if sign then -value else value

/-- **The evaluator's homogeneous value** of a digit: the three rows with the flags as their constants,
the sign row negated when `ν`. -/
def evaluateNormRow (row : NormRow) (input : AffineInput) (values : Biquadratic.Values) :
    FieldMacToECMac.HomogeneousValue :=
  { x := Biquadratic.evaluateX { c0 := row.xC0 } input values
    y := signed row.sign (Biquadratic.evaluateY { c4 := flagValue row.sFlag } input values)
    z := Biquadratic.evaluateZ { c0 := flagValue row.zFlag } input values }

/-- The evaluator's 91 homogeneous values. -/
def evaluateNormRows (rows : Vector NormRow FieldMacToECMac.outputMacCount)
    (values : FieldMacToECMac.DigitValues) (input : AffineInput) :
    Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount :=
  Vector.ofFn fun index => evaluateNormRow (rows.get index) input (values index)

/-- The unscaled rows of every output key. -/
def unscaledOf (keys : FieldMacToECMac.OutputKeys) (index : Fin FieldMacToECMac.outputMacCount) :
    Coordinates.Rows :=
  unscaledRows (keys.get index).offset.coordinates (digitEndomorphismBase (keys.get index).digit)

/-- The normalized rows of every output key, from the element offsets. -/
def normRowsOf (keys : FieldMacToECMac.OutputKeys) (K : FieldMacToECMac.DigitValues)
    (index : Fin FieldMacToECMac.outputMacCount) : Coordinates.Rows :=
  normRows (unscaledOf keys index) (K index)

end Kriterion.CRT.Rows
