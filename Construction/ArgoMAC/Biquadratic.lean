/-
This file defines the three sparse biquadratic rows of one recoded digit.

Plan B removes the 254-row `DigitAdaptor` tables: a row no longer garbles its own adaptors, it
consumes the affine element values the projectivized garbling scheme delivers. A digit consumes
eight element slots -- five against the `x` coordinate and three against the `y` coordinate -- and
publishes four field elements: `X` and `Z` their constants, `Y` its constant and its `x²`
coefficient. Every other row coefficient is **carried in the slopes** (Lazar's coefficient cut,
entry `d9a8327`): an element's slope is the coefficient of the monomial it rides on, so the row
needs no published constant for it.

* `X = c0 + c1 x + c2 y + c4 x²`: `x7` (x bits, multiplier `x`, slope `c4`), `x9` (x bits,
  multiplier `1`, slope `c1 - K7`), `y10` (y bits, multiplier `1`, slope `c2`); publishes
  `c0 - K9 - K10`.
* `Y = c0 + c2 y + c3 x y + c4 x² + c5 y²`, the four-element row that uses the curve equation:
  the *cubic* element `x7` (x bits, multiplier `x²`, slope `-r4`), the *mixed* element `x9` (x bits,
  multiplier `y`, slope `c3`), `y8` (y bits, multiplier `y`, slope `r4 + c5`), `y10` (y bits,
  multiplier `1`, slope `c2 - K8 - K9`); publishes `c0 - 3 r4 - K10` and `c4 - K7`. Its value is the
  `Y` polynomial plus `r4 (y² - x³ - 3)`, so it is exact on the curve `y² = x³ + 3`.
* `Z = c0 + c1 x`: `x9` (x bits, multiplier `1`, slope `c1`); publishes `c0 - K9`.

The randomness structures keep all eight randomisers; only the `Y` row's `r4` is read.
The plan source is `2026-09-17-planB.md`, sections D.1 and D.4.
-/

import Construction.ArgoMAC.Input
import Construction.ArgoMAC.Coordinates
import Construction.PGS.Elements

namespace Kriterion.ArgoMAC.Biquadratic

open BN254 Kriterion.ArgoMAC.PlanB

/-- The eight element slots one digit consumes: five x-type and three y-type. -/
abbrev Element := XElement ⊕ YElement

/-- One value per element slot of a digit. The garbler uses this for the element offsets
`K e = b_e = O[e]`, the evaluator for the delivered values `a_e * coord + b_e`. -/
abbrev Values := Element → BaseField

/-- The coordinate an element slot is chunked against. -/
def coordValue (input : AffineInput) : Element → BaseField
  | .inl _ => input.x
  | .inr _ => input.y

@[simp] theorem coordValue_inl (input : AffineInput) (element : XElement) :
    coordValue input (.inl element) = input.x := rfl

@[simp] theorem coordValue_inr (input : AffineInput) (element : YElement) :
    coordValue input (.inr element) = input.y := rfl

/-- The `X` row randomizers: monomials `1, x, y, x²`. -/
structure XRandomness where
  /-- The randomizer of the `x` monomial. -/
  r1 : BaseField
  /-- The randomizer of the `y` monomial. -/
  r2 : BaseField
  /-- The randomizer of the `x²` monomial. -/
  r4 : BaseField

/-- The `Y` row randomizers: monomials `1, y, x y, x², y²`. -/
structure YRandomness where
  /-- The randomizer of the `y` monomial. -/
  r2 : BaseField
  /-- The randomizer of the `x y` monomial. -/
  r3 : BaseField
  /-- The randomizer of the `x²` monomial. -/
  r4 : BaseField
  /-- The randomizer of the `y²` monomial. -/
  r5 : BaseField

/-- The `Z` row randomizer: monomials `1, x`. -/
structure ZRandomness where
  /-- The randomizer of the `x` monomial. -/
  r1 : BaseField

/-- The published constant of the `X` row. -/
structure XGamma where
  /-- The constant monomial. -/
  c0 : BaseField

/-- The two published constants of the `Y` row: the constant and the `x²` coefficient (the
cubic element's offset is absorbed there). -/
structure YGamma where
  /-- The constant monomial. -/
  c0 : BaseField
  /-- The `x²` monomial. -/
  c4 : BaseField

/-- The published constant of the `Z` row. -/
structure ZGamma where
  /-- The constant monomial. -/
  c0 : BaseField

/-! ### Slopes

`K e` is the element offset the projectivized garbling scheme delivers -- the PGS output mask
`O[e]`, which the garbler can compute from the tape alone before any slope exists. That is what
keeps the chains `x7 → x9` (`X` row) and `y8, x9 → y10` (`Y` row) resolvable in one pass. The
slopes carry the row coefficients. -/

/-- The slope of every element slot of one digit. -/
def slopes (rows : Coordinates.Rows) (x : XRandomness) (y : YRandomness) (z : ZRandomness)
    (K : Values) : Values
  | .inl .rowX_x7 => rows.x.xSquared
  | .inl .rowX_x9 => rows.x.x - K (.inl .rowX_x7)
  | .inr .rowX_y10 => rows.x.y
  | .inl .rowY_x7 => -y.r4
  | .inl .rowY_x9 => rows.y.xy
  | .inr .rowY_y8 => y.r4 + rows.y.ySquared
  | .inr .rowY_y10 => rows.y.y - K (.inr .rowY_y8) - K (.inl .rowY_x9)
  | .inl .rowZ_x9 => rows.z.x

/-- The value the evaluator obtains for every element slot of one digit. -/
def delivered (rows : Coordinates.Rows) (x : XRandomness) (y : YRandomness) (z : ZRandomness)
    (K : Values) (input : AffineInput) : Values :=
  fun element => slopes rows x y z K element * coordValue input element + K element

/-! ### Garbling and evaluation -/

/-- The `X` row: the three consumed elements are `x7`, `x9` and `y10`. -/
def garbleX (c0 : BaseField) (K : Values) : XGamma := {
  c0 := c0 - K (.inl .rowX_x9) - K (.inr .rowX_y10) }

/-- The four-element `Y` row: the consumed elements are the cubic `x7`, the mixed `x9`, `y8`
and `y10`. -/
def garbleY (c0 c4 : BaseField) (randomness : YRandomness) (K : Values) : YGamma := {
  c0 := c0 - 3 * randomness.r4 - K (.inr .rowY_y10)
  c4 := c4 - K (.inl .rowY_x7) }

/-- The `Z` row: the single consumed element is `x9`. -/
def garbleZ (c0 : BaseField) (K : Values) : ZGamma := {
  c0 := c0 - K (.inl .rowZ_x9) }

/-- The `X` row value: `c0 + x7 · x + x9 + y10`. -/
def evaluateX (gamma : XGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.c0 + values (.inl .rowX_x7) * input.x + values (.inl .rowX_x9) + values (.inr .rowX_y10)

/-- The `Y` row value: `c0 + c4 x² + x7 · x² + x9 · y + y8 · y + y10`. -/
def evaluateY (gamma : YGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.c0 + gamma.c4 * input.x ^ 2 + values (.inl .rowY_x7) * input.x ^ 2 +
    values (.inl .rowY_x9) * input.y + values (.inr .rowY_y8) * input.y +
    values (.inr .rowY_y10)

/-- The `Z` row value: `c0 + x9`. -/
def evaluateZ (gamma : ZGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.c0 + values (.inl .rowZ_x9)

/-! ### Correctness

Each row's published constants cancel the offsets of the elements it consumes, and each
element's slope carries the coefficient of the monomial it rides on. -/

/-- The `X` row evaluates to its four-monomial value. -/
theorem evaluateEncodedX (rows : Coordinates.Rows) (x : XRandomness) (y : YRandomness)
    (z : ZRandomness) (K : Values) (input : AffineInput) :
    evaluateX (garbleX rows.x.constant K) input (delivered rows x y z K input) =
      rows.x.constant + rows.x.x * input.x + rows.x.y * input.y +
        rows.x.xSquared * input.x ^ 2 := by
  simp only [evaluateX, garbleX, delivered, slopes, coordValue]
  ring

/-- The `Y` row evaluates to its five-monomial value plus `r4 (y² - x³ - 3)`, at every input. -/
theorem evaluateEncodedYCubic (rows : Coordinates.Rows) (x : XRandomness) (y : YRandomness)
    (z : ZRandomness) (K : Values) (input : AffineInput) :
    evaluateY (garbleY rows.y.constant rows.y.xSquared y K) input (delivered rows x y z K input) =
      rows.y.constant + rows.y.y * input.y + rows.y.xy * input.x * input.y +
        rows.y.xSquared * input.x ^ 2 + rows.y.ySquared * input.y ^ 2 +
        y.r4 * (input.y ^ 2 - input.x ^ 3 - 3) := by
  simp only [evaluateY, garbleY, delivered, slopes, coordValue]
  ring

/-- On the curve the `Y` row evaluates to its five-monomial value. -/
theorem evaluateEncodedY (rows : Coordinates.Rows) (x : XRandomness) (y : YRandomness)
    (z : ZRandomness) (K : Values) (input : AffineInput) (onCurve : OnCurve input) :
    evaluateY (garbleY rows.y.constant rows.y.xSquared y K) input (delivered rows x y z K input) =
      rows.y.constant + rows.y.y * input.y + rows.y.xy * input.x * input.y +
        rows.y.xSquared * input.x ^ 2 + rows.y.ySquared * input.y ^ 2 := by
  rw [evaluateEncodedYCubic]
  unfold OnCurve at onCurve
  linear_combination y.r4 * onCurve

/-- The `Z` row evaluates to its two-monomial value. -/
theorem evaluateEncodedZ (rows : Coordinates.Rows) (x : XRandomness) (y : YRandomness)
    (z : ZRandomness) (K : Values) (input : AffineInput) :
    evaluateZ (garbleZ rows.z.constant K) input (delivered rows x y z K input) =
      rows.z.constant + rows.z.x * input.x := by
  simp only [evaluateZ, garbleZ, delivered, slopes, coordValue]
  ring

end Kriterion.ArgoMAC.Biquadratic
