/-
**The normalized body-mask-row layer** (row normalization, research note §2).

The construction scales each digit's unscaled rows (`NContext.rows`, the digit's `Rows.unscaledRows`) by
`ρ = (K_z + ε_Z)/z₀` and `κ = (K_c + ε_S)/s₄`, read off the layer's own row offsets `K_z` (`rowZ_x9`) and
`K_c` (`rowY_cubic`), and publishes `NormRow`: the `X` constant, `ε_Z`, `ε_S` and `ν = [χ(κ) = −1]`
(`nRealOut`). This file reduces the normalized layer to P45's fixed-context layer (`BodyMaskRow*.lean`):

* **field scales** (`fsScales`): `(K_z/z₀, K_c/s₄)`, zero allowed; on the good event `K_z K_c ≠ 0` they are the
  construction's scales, and the layer is P45's layer at the fixed context `fsContext s` (the unscaled rows
  scaled by `s`), whose published `Z` and sign-row constants are `0` (`nRealOut_eq_conv`);
* **the dynamic bijection** (`nEquiv`): the coins against the field scales and P45's compact image (the joins, the
  `X` constants, the curve constants, the visible cells, the residual): P45's inverse at `fsContext s` recovers
  `K_z = z₀ ρ̂`, `K_c = s₄ κ̂` from the zero constants.

The ideal side (`nIdealOut`) reads corrected target rows `(X, (−1)^ν S, Z)` and the stage-1 source's `ν`; at the
targets of scales `(ρ, τ)` it is the fixed-context ideal output at `(ρ, (−1)^ν τ²)` (`nIdealOut_eq_conv`).
-/

import Proof.Privacy.CRT.Core.BmrCore
import Proof.Privacy.CRT.Core.BodyMaskRowOff
import Proof.Correctness.CRT.Rows

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

/-! ### 1. The normalized layer -/

/-- The quantities outside the normalized layer: the unscaled rows of each digit. -/
structure NContext where
  rows : Fin 91 → Coordinates.Rows

/-- The normalizing coefficients are nonzero (`z₀` and `s₄`, `Proof/Correctness/CRT/Rows.lean`). -/
def NContext.Valid (nctx : NContext) : Prop :=
  ∀ d, (nctx.rows d).z.constant ≠ 0 ∧ (nctx.rows d).y.xSquared ≠ 0

/-- The unscaled rows carry only the monomials their tables read. -/
def NContext.Sparse (nctx : NContext) : Prop := ∀ d, FieldMacToECMac.SparseRow (nctx.rows d)

/-- Per digit a pair of field elements: the field scales `(ρ̂, κ̂)`, or the source's two hidden cells. -/
abbrev Scales := Fin 91 → BaseField × BaseField

/-- Both entries of every digit nonzero. -/
def GoodScales (s : Scales) : Prop := ∀ d, (s d).1 ≠ 0 ∧ (s d).2 ≠ 0

instance (s : Scales) : Decidable (GoodScales s) := by unfold GoodScales; infer_instance

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- A digit's element offsets. -/
def offsetsOf (c : Coins T) (d : Fin 91) : Biquadratic.Values := fun element => rowOffset c (d, element)

/-- **A digit's normalized rows.** -/
def nRows (nctx : NContext) (c : Coins T) (d : Fin 91) : Coordinates.Rows :=
  Rows.normRows (nctx.rows d) (offsetsOf c d)

/-- The digit's seven slopes. -/
def nDigitSlopes (nctx : NContext) (c : Coins T) (d : Fin 91) : Biquadratic.Values :=
  let rand := rowRand (c.r4 d) (c.unused d)
  Biquadratic.slopes (nRows nctx c d) rand.1 rand.2.1 rand.2.2 (offsetsOf c d)

/-- The slope of every encoding. -/
def nSlope (nctx : NContext) (c : Coins T) : Enc → BaseField
  | .inl (.inl (d, x)) => nDigitSlopes nctx c d (.inl x)
  | .inr (.inl (d, y)) => nDigitSlopes nctx c d (.inr y)
  | .inl (.inr x) => CurveMembership.slopes c.r1 c.r2 (curveK c) (.inl x)
  | .inr (.inr y) => CurveMembership.slopes c.r1 c.r2 (curveK c) (.inr y)

/-- The residue joins. -/
def nJoin (nctx : NContext) (c : Coins T) (e : Enc) (i : Fin T.count) : ZMod (T.modulus i) :=
  ∑ ρ : ZMod (T.modulus i), c.pads i ρ e + ((nSlope nctx c e).val : ZMod (T.modulus i))

/-- **The published row data** of a digit. -/
def nGamma (nctx : NContext) (c : Coins T) (d : Fin 91) : NormRow :=
  Rows.garbleNormRow (nctx.rows d) (offsetsOf c d)

variable (T)

/-- The published cells of the normalized layer: the residue joins, the row data, the curve constants. -/
abbrev NPub := Joins T × (Fin 91 → NormRow) × (BaseField × BaseField × BaseField)

/-- **The source of the ideal side**: the joins, per digit a `RowGamma` (its `X` constant, and two cells that are
never published: `zC0` and `yC4`, whose zero event pays for the normalization's bad event), the signs `ν`, the curve
constants. -/
abbrev NSource := Joins T × (Fin 91 → RowGamma) × (Fin 91 → Bool) × (BaseField × BaseField × BaseField)

/-- The normalized outputs: (published cells, hints), visible cells, collector masks, bridge key. -/
abbrev NOut (u : AffineInput) := (NPub T × (Enc → Bool)) × Visible T u × (Collector → BaseField) × BaseField

/-- The normalized outputs off the curve. -/
abbrev NOutOff (u : AffineInput) := (NPub T × (Enc → Bool)) × Cold T u

variable {T}

/-- **The real outputs** of the normalized layer. -/
def nRealOut (nctx : NContext) (u : AffineInput) (c : Coins T) : NOut T u :=
  (((nJoin nctx c, nGamma nctx c, curveTable c), hint c), (coldOf u c, fun r => c.mask r.1),
    fun r => c.mask r.1, c.bridge)

/-- The real outputs off the curve. -/
def nRealOutOff (nctx : NContext) (u : AffineInput) (c : Coins T) : NOutOff T u :=
  (((nJoin nctx c, nGamma nctx c, curveTable c), hint c), coldOf u c)

/-- A source digit's published row: its `X` constant, the flags clear, its sign. -/
def srcRow (row : RowGamma) (sign : Bool) : NormRow := { xC0 := row.xC0, zFlag := false, sFlag := false, sign }

/-- The published cells of a source. -/
def nPublish (src : NSource T) : NPub T := (src.1, fun d => srcRow (src.2.1 d) (src.2.2.1 d), src.2.2.2)

/-- The source's two hidden cells per digit, `(zC0, yC4)`. -/
def hiddenCells (src : NSource T) : Scales := fun d => ((src.2.1 d).zC0, (src.2.1 d).yC4)

/-- **The normalization flag of the ideal side**: a hidden cell is zero. -/
def normBad (src : NSource T) : Prop := ¬ GoodScales (hiddenCells src)

/-- **The collector solve** of the normalized rows: the target's sign row is corrected (`(−1)^ν`), the flags are the
`Z` and sign-row constants. -/
def nCollectorSolve (target : FieldMacToECMac.HomogeneousValue) (g : NormRow) (u : AffineInput)
    (values : Biquadratic.Values) : Biquadratic.Element → BaseField
  | .inl .rowX_x9 => target.x - (g.xC0 + values (.inl .rowX_x7) * u.x + values (.inr .rowX_y10))
  | .inl .rowY_cubic => (Rows.signed g.sign target.y - (Rows.flagValue g.sFlag * u.x ^ 2 +
      values (.inr .rowY_y8) * u.y + values (.inr .rowY_y10))) * (u.x * u.x)⁻¹
  | .inl .rowZ_x9 => target.z - Rows.flagValue g.zFlag
  | _ => 0

/-- **The ideal outputs** at `u` from corrected target rows and cells: hints `0`, the collector masks of the solve. -/
def nIdealOut (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) (u : AffineInput)
    (cells : NSource T × Visible T u) : NOut T u :=
  let src := cells.1
  let vis := cells.2
  let v0 := deliveredIdeal u src.1 vis.1
  let rowValue (d : Fin 91) : Biquadratic.Values := fun element =>
    if h : IsCollector element then 0 else v0 (rowEnc (d, element)) - vis.2 ⟨(d, element), h⟩
  ((nPublish src, fun _ => false), vis,
    fun r => v0 (rowEnc r.1) - nCollectorSolve (targets r.1.1) (srcRow (src.2.1 r.1.1) (src.2.2.1 r.1.1)) u
      (rowValue r.1.1) r.1.2,
    CurveMembership.evaluate src.2.2.2 u fun element => v0 (curveEnc element))

/-- The ideal outputs off the curve. -/
def nIdealOutOff (u : AffineInput) (cells : NSource T × Cold T u) : NOutOff T u :=
  ((nPublish cells.1, fun _ => false), cells.2)

/-- **The corrected target rows** of the unscaled rows at scales `(ρ, τ)`: `(ρ² X*, τ² S*, ρ Z*)`. -/
def nTargets (nctx : NContext) (u : AffineInput) (scales : Fin 91 → NonZeroBase × NonZeroBase) (d : Fin 91) :
    FieldMacToECMac.HomogeneousValue :=
  { x := (scales d).1.value ^ 2 * Coordinates.evaluate (nctx.rows d).x u
    y := (scales d).2.value ^ 2 * Coordinates.evaluate (nctx.rows d).y u
    z := (scales d).1.value * Coordinates.evaluate (nctx.rows d).z u }

/-! ### 2. The field scales and the fixed context -/

/-- **The field scales** of the coins: `(K_z/z₀, K_c/s₄)`, zero allowed. -/
def fsScales (nctx : NContext) (c : Coins T) : Scales := fun d =>
  (rowOffset c (d, .inl .rowZ_x9) * ((nctx.rows d).z.constant)⁻¹,
    rowOffset c (d, .inl .rowY_cubic) * ((nctx.rows d).y.xSquared)⁻¹)

/-- **P45's fixed context of field scales `s`**: the unscaled rows scaled by `(ρ̂, κ̂)`. -/
def fsContext (nctx : NContext) (s : Scales) : Context where
  rows d := Rows.scaled (s d).1 (s d).2 (nctx.rows d)
  rho _ := ⟨1, one_ne_zero_base⟩

/-- **The conversion** of a fixed-context output to the normalized one: the published `X` constants with clear flags
and the signs of the `κ̂`s. -/
def conv (s : Scales) {u : AffineInput} (o : Out T u) : NOut T u :=
  (((o.1.1.1, fun d => { xC0 := (o.1.1.2.1 d).xC0, zFlag := false, sFlag := false,
      sign := Rows.signBit (s d).2 }, o.1.1.2.2), o.1.2), o.2)

/-- The conversion off the curve. -/
def convOff (s : Scales) {u : AffineInput} (o : OutOff T u) : NOutOff T u :=
  ((o.1.1.1, fun d => { xC0 := (o.1.1.2.1 d).xC0, zFlag := false, sFlag := false,
      sign := Rows.signBit (s d).2 }, o.1.1.2.2), o.1.2), o.2)

section Real

variable [FieldCertificate] (nctx : NContext) (valid : nctx.Valid)
include valid

theorem fsScales_good_iff (c : Coins T) :
    GoodScales (fsScales nctx c) ↔ ∀ d, rowOffset c (d, .inl .rowZ_x9) ≠ 0 ∧ rowOffset c (d, .inl .rowY_cubic) ≠ 0 := by
  unfold GoodScales fsScales
  refine forall_congr' fun d => ?_
  simp only [ne_eq, mul_eq_zero, inv_eq_zero, (valid d).1, (valid d).2, or_false]

/-- On the good event the construction's rows are the field-scale rows. -/
theorem nRows_eq (c : Coins T) (good : GoodScales (fsScales nctx c)) (d : Fin 91) :
    nRows nctx c d = (fsContext nctx (fsScales nctx c)).rows d := by
  have nz := ((fsScales_good_iff nctx valid c).mp good d)
  show Rows.scaled (Rows.rhoOf (nctx.rows d) (offsetsOf c d)) (Rows.kappaOf (nctx.rows d) (offsetsOf c d))
    (nctx.rows d) = Rows.scaled _ _ (nctx.rows d)
  unfold Rows.rhoOf Rows.kappaOf Rows.scaleOf fsScales offsetsOf
  rw [Rows.add_flagValue_of_ne _ nz.1, Rows.add_flagValue_of_ne _ nz.2]

theorem nSlope_eq (c : Coins T) (good : GoodScales (fsScales nctx c)) :
    nSlope nctx c = slope (fsContext nctx (fsScales nctx c)) c := by
  funext e
  rcases e with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y))
  · show Biquadratic.slopes (nRows nctx c d) _ _ _ _ (.inl x) = Biquadratic.slopes _ _ _ _ _ (.inl x)
    rw [nRows_eq nctx valid c good d]
    rfl
  · rfl
  · show Biquadratic.slopes (nRows nctx c d) _ _ _ _ (.inr y) = Biquadratic.slopes _ _ _ _ _ (.inr y)
    rw [nRows_eq nctx valid c good d]
    rfl
  · rfl

theorem nJoin_eq (c : Coins T) (good : GoodScales (fsScales nctx c)) :
    nJoin nctx c = join (fsContext nctx (fsScales nctx c)) c := by
  funext e i
  unfold nJoin join
  rw [nSlope_eq nctx valid c good]

/-- The field-scale gammas have zero `Z` and sign-row constants, at every coin (the field scales are exact). -/
theorem gamma_fs (c : Coins T) (d : Fin 91) :
    gamma (fsContext nctx (fsScales nctx c)) c d =
      ⟨(gamma (fsContext nctx (fsScales nctx c)) c d).xC0, 0, 0⟩ := by
  unfold gamma FieldMacToECMac.garbleRow Biquadratic.garbleX Biquadratic.garbleY Biquadratic.garbleZ
  simp only [fsContext, Rows.scaled, Rows.multiply, fsScales, RowGamma.mk.injEq, true_and]
  constructor
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (valid d).2, one_mul, sub_self]
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (valid d).1, one_mul, sub_self]

/-- On the good event the published row data is the field-scale `X` constant, the flags clear, the sign of `κ̂`. -/
theorem nGamma_eq (c : Coins T) (good : GoodScales (fsScales nctx c)) (d : Fin 91) :
    nGamma nctx c d = { xC0 := (gamma (fsContext nctx (fsScales nctx c)) c d).xC0, zFlag := false,
      sFlag := false, sign := Rows.signBit (fsScales nctx c d).2 } := by
  have nz := ((fsScales_good_iff nctx valid c).mp good d)
  have rows := nRows_eq nctx valid c good d
  unfold nRows at rows
  unfold nGamma Rows.garbleNormRow
  simp only [NormRow.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rows]
    rfl
  · simp [Rows.zeroFlag, offsetsOf, nz.1]
  · simp [Rows.zeroFlag, offsetsOf, nz.2]
  · unfold Rows.kappaOf Rows.scaleOf fsScales offsetsOf
    rw [Rows.add_flagValue_of_ne _ nz.2]

/-- **On the good event the normalized real outputs are the converted fixed-context ones.** -/
theorem nRealOut_eq_conv (u : AffineInput) (c : Coins T) (good : GoodScales (fsScales nctx c)) :
    nRealOut nctx u c = conv (fsScales nctx c) (realOut (fsContext nctx (fsScales nctx c)) u c) := by
  unfold nRealOut conv realOut
  simp only
  rw [nJoin_eq nctx valid c good]
  congr 3
  funext d
  exact nGamma_eq nctx valid c good d

theorem nRealOutOff_eq_conv (u : AffineInput) (c : Coins T) (good : GoodScales (fsScales nctx c)) :
    nRealOutOff nctx u c = convOff (fsScales nctx c) (realOutOff (fsContext nctx (fsScales nctx c)) u c) := by
  unfold nRealOutOff convOff realOutOff
  simp only
  rw [nJoin_eq nctx valid c good]
  congr 3
  funext d
  exact nGamma_eq nctx valid c good d

end Real

end

end Kriterion.CRT.Privacy.BMR
