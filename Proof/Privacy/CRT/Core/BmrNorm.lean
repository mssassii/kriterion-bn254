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
import Proof.Privacy.Phase3.Glue.AbstractSimulator

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

/-- A fixed-context digit's published row as normalized row data: its `X` constant, the flags clear, the sign of
`κ̂`. -/
def convRow (kappa : BaseField) (g : RowGamma) : NormRow :=
  { xC0 := g.xC0, zFlag := false, sFlag := false, sign := Rows.signBit kappa }

/-- **The conversion** of a fixed-context output to the normalized one. -/
def conv (s : Scales) {u : AffineInput} (o : Out T u) : NOut T u :=
  (((o.1.1.1, fun d => convRow (s d).2 (o.1.1.2.1 d), o.1.1.2.2), o.1.2), o.2)

/-- The conversion off the curve. -/
def convOff (s : Scales) {u : AffineInput} (o : OutOff T u) : NOutOff T u :=
  (((o.1.1.1, fun d => convRow (s d).2 (o.1.1.2.1 d), o.1.1.2.2), o.1.2), o.2)

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
  · show nDigitSlopes nctx c d (.inl x) = digitSlopes (fsContext nctx (fsScales nctx c)) c d (.inl x)
    unfold nDigitSlopes digitSlopes
    rw [nRows_eq nctx valid c good d]
    rfl
  · rfl
  · show nDigitSlopes nctx c d (.inr y) = digitSlopes (fsContext nctx (fsScales nctx c)) c d (.inr y)
    unfold nDigitSlopes digitSlopes
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
  · rw [mul_assoc, inv_mul_cancel₀ (valid d).2, mul_one, sub_self]
  · rw [mul_assoc, inv_mul_cancel₀ (valid d).1, mul_one, sub_self]

/-- On the good event the published row data is the field-scale `X` constant, the flags clear, the sign of `κ̂`. -/
theorem nGamma_eq (c : Coins T) (good : GoodScales (fsScales nctx c)) (d : Fin 91) :
    nGamma nctx c d = convRow (fsScales nctx c d).2 (gamma (fsContext nctx (fsScales nctx c)) c d) := by
  have nz := ((fsScales_good_iff nctx valid c).mp good d)
  have rows := nRows_eq nctx valid c good d
  unfold nRows at rows
  unfold nGamma Rows.garbleNormRow convRow
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
  have gammas : nGamma nctx c = fun d => convRow (fsScales nctx c d).2 (gamma (fsContext nctx (fsScales nctx c)) c d) :=
    funext (nGamma_eq nctx valid c good)
  unfold nRealOut conv realOut
  rw [nJoin_eq nctx valid c good, gammas]

theorem nRealOutOff_eq_conv (u : AffineInput) (c : Coins T) (good : GoodScales (fsScales nctx c)) :
    nRealOutOff nctx u c = convOff (fsScales nctx c) (realOutOff (fsContext nctx (fsScales nctx c)) u c) := by
  have gammas : nGamma nctx c = fun d => convRow (fsScales nctx c d).2 (gamma (fsContext nctx (fsScales nctx c)) c d) :=
    funext (nGamma_eq nctx valid c good)
  unfold nRealOutOff convOff realOutOff
  rw [nJoin_eq nctx valid c good, gammas]

end Real

/-! ### 3. The dynamic bijection -/

variable (T) in
/-- The compact source: the joins, the `X` constants, the curve constants. -/
abbrev CSource := Joins T × (Fin 91 → BaseField) × (BaseField × BaseField × BaseField)

/-- The full source of a compact one: `Z` and sign-row constants zero. -/
def expandSrc (cs : CSource T) : Source T := (cs.1, fun d => ⟨cs.2.1 d, 0, 0⟩, cs.2.2)

/-- The compact source of a full one. -/
def compressSrc (src : Source T) : CSource T := (src.1, fun d => (src.2.1 d).xC0, src.2.2)

theorem compressSrc_expandSrc (cs : CSource T) : compressSrc (expandSrc cs) = cs := rfl

variable (T) in
/-- The normalized image on the curve: the field scales, the compact cells and P45's residual. -/
abbrev NImage (u : AffineInput) := Scales × ((CSource T × Visible T u) × Residual)

variable (T) in
/-- The normalized image off the curve. -/
abbrev NImageOff (u : AffineInput) := Scales × ((CSource T × Cold T u) × ResidualOff)

instance nImageFintype (u : AffineInput) : Fintype (NImage T u) := instFintypeProd _ _
instance nImageOffFintype (u : AffineInput) : Fintype (NImageOff T u) := instFintypeProd _ _

instance cSourceNonempty : Nonempty (CSource T) := ⟨(fun _ _ => 0, fun _ => 0, (0, 0, 0))⟩

instance nImageNonempty (u : AffineInput) : Nonempty (NImage T u) :=
  ⟨(fun _ => (0, 0), (Classical.arbitrary _, Classical.arbitrary _), Classical.arbitrary _)⟩

instance nImageOffNonempty (u : AffineInput) : Nonempty (NImageOff T u) :=
  ⟨(fun _ => (0, 0), (Classical.arbitrary _, Classical.arbitrary _), Classical.arbitrary _)⟩

/-- The forward map on the curve: the field scales, and P45's image at their fixed context, compressed. -/
def nForward (nctx : NContext) (u : AffineInput) (c : Coins T) : NImage T u :=
  (fsScales nctx c, ((compressSrc (Joint.forward (fsContext nctx (fsScales nctx c)) u c).1.1,
    (Joint.forward (fsContext nctx (fsScales nctx c)) u c).1.2), (Joint.forward (fsContext nctx (fsScales nctx c)) u c).2))

/-- The forward map off the curve. -/
def nForwardOff (nctx : NContext) (u : AffineInput) (c : Coins T) : NImageOff T u :=
  (fsScales nctx c, ((compressSrc (Off.forwardOff (fsContext nctx (fsScales nctx c)) u c).1.1,
    (Off.forwardOff (fsContext nctx (fsScales nctx c)) u c).1.2), (Off.forwardOff (fsContext nctx (fsScales nctx c)) u c).2))

section Bijection

variable [FieldCertificate] (nctx : NContext) (valid : nctx.Valid)

/-- The inverse on the curve: P45's inverse at the fixed context of the scales. -/
def nBackward (u : AffineInput) (good : u.x ≠ 0 ∧ u.y ≠ 0) (x : NImage T u) : Coins T :=
  Joint.backward (fsContext nctx x.1) u good ((expandSrc x.2.1.1, x.2.1.2), x.2.2)

/-- The inverse off the curve. -/
def nBackwardOff (u : AffineInput) (x : NImageOff T u) : Coins T :=
  Off.backwardOff (fsContext nctx x.1) u ((expandSrc x.2.1.1, x.2.1.2), x.2.2)

include valid

theorem expand_compress_fs (c : Coins T) (src : Source T)
    (gammas : src.2.1 = gamma (fsContext nctx (fsScales nctx c)) c) : expandSrc (compressSrc src) = src := by
  obtain ⟨J, g, cur⟩ := src
  simp only at gammas
  subst gammas
  unfold expandSrc compressSrc
  simp only [Prod.mk.injEq, true_and, and_true]
  funext d
  exact (gamma_fs nctx valid c d).symm

theorem nBackward_nForward (u : AffineInput) (good : u.x ≠ 0 ∧ u.y ≠ 0) (c : Coins T) :
    nBackward nctx u good (nForward nctx u c) = c := by
  unfold nBackward nForward
  simp only
  rw [expand_compress_fs nctx valid c _ rfl]
  exact Joint.backward_forward _ u good c

theorem nBackwardOff_nForwardOff (u : AffineInput) (c : Coins T) :
    nBackwardOff nctx u (nForwardOff nctx u c) = c := by
  unfold nBackwardOff nForwardOff
  simp only
  rw [expand_compress_fs nctx valid c _ rfl]
  exact Off.backwardOff_forwardOff _ u c

theorem fsScales_nBackward (u : AffineInput) (good : u.x ≠ 0 ∧ u.y ≠ 0) (x : NImage T u) :
    fsScales nctx (nBackward nctx u good x) = x.1 := by
  funext d
  unfold fsScales nBackward
  rw [Joint.rowOffset_backward, Joint.rowOffset_backward]
  simp only [Joint.recovered, rowEquiv, Equiv.coe_fn_symm_mk, solvedK, fsContext, Rows.scaled, Rows.multiply,
    expandSrc, sub_zero]
  rw [mul_assoc, mul_inv_cancel₀ (valid d).1, mul_one, mul_assoc, mul_inv_cancel₀ (valid d).2, mul_one]

theorem fsScales_nBackwardOff (u : AffineInput) (x : NImageOff T u) :
    fsScales nctx (nBackwardOff nctx u x) = x.1 := by
  funext d
  unfold fsScales nBackwardOff
  rw [Off.rowOffset_backwardOff, Off.rowOffset_backwardOff]
  simp only [Off.bOff, fsContext, Rows.scaled, Rows.multiply, expandSrc, sub_zero]
  rw [mul_assoc, mul_inv_cancel₀ (valid d).1, mul_one, mul_assoc, mul_inv_cancel₀ (valid d).2, mul_one]

theorem nForward_nBackward (u : AffineInput) (good : u.x ≠ 0 ∧ u.y ≠ 0) (x : NImage T u) :
    nForward nctx u (nBackward nctx u good x) = x := by
  have scales := fsScales_nBackward nctx valid u good x
  have image := Joint.forward_backward (fsContext nctx x.1) u good ((expandSrc x.2.1.1, x.2.1.2), x.2.2)
  unfold nForward
  rw [scales]
  unfold nBackward at image ⊢
  rw [image]
  rfl

theorem nForwardOff_nBackwardOff (u : AffineInput) (x : NImageOff T u) :
    nForwardOff nctx u (nBackwardOff nctx u x) = x := by
  have scales := fsScales_nBackwardOff nctx valid u x
  have image := Off.forwardOff_backwardOff (fsContext nctx x.1) u ((expandSrc x.2.1.1, x.2.1.2), x.2.2)
  unfold nForwardOff
  rw [scales]
  unfold nBackwardOff at image ⊢
  rw [image]
  rfl

variable (T) in
/-- **The normalized bijection on the curve.** -/
def nEquiv (u : AffineInput) (good : u.x ≠ 0 ∧ u.y ≠ 0) : Coins T ≃ NImage T u where
  toFun := nForward nctx u
  invFun := nBackward nctx u good
  left_inv := nBackward_nForward nctx valid u good
  right_inv := nForward_nBackward nctx valid u good

variable (T) in
/-- **The normalized bijection off the curve.** -/
def nEquivOff (u : AffineInput) : Coins T ≃ NImageOff T u where
  toFun := nForwardOff nctx u
  invFun := nBackwardOff nctx u
  left_inv := nBackwardOff_nForwardOff nctx valid u
  right_inv := nForwardOff_nBackwardOff nctx valid u

end Bijection

/-! ### 4. Both sides through the fixed-context ideal outputs -/

/-- **The fixed-context ideal output at field scales `s`**, converted. -/
def nG (nctx : NContext) (u : AffineInput) (s : Scales) (y : CSource T × Visible T u) : NOut T u :=
  conv s (idealOut (fsContext nctx s) u (expandSrc y.1, y.2))

/-- The same off the curve. -/
def nGOff (s : Scales) {u : AffineInput} (y : CSource T × Cold T u) : NOutOff T u :=
  convOff s (idealOutOff u (expandSrc y.1, y.2))

/-- The window of compact cells. -/
def CWindow {u : AffineInput} (y : CSource T × Cold T u) : Prop := ∃ e, InWindow T (evalInt u y.1.1 y.2 e)

section Relations

variable [FieldCertificate] (nctx : NContext) (valid : nctx.Valid)
include valid

/-- **The real outputs on the curve, on the good event and off the window, are `nG` of their image.** -/
theorem nRealOut_eq_nG (facts : TableFacts T) (u : AffineInput) (onCurve : OnCurve u) (c : Coins T)
    (good : GoodScales (fsScales nctx c)) (outside : ¬ CWindow ((nForward nctx u c).2.1.1, (nForward nctx u c).2.1.2.1)) :
    nRealOut nctx u c = nG nctx u (nForward nctx u c).1 (nForward nctx u c).2.1 := by
  have noWrap : ∀ e, hint c e = false := fun e =>
    hint_false_of_window facts (fsContext nctx (fsScales nctx c)) u c e fun w => outside ⟨e, w⟩
  rw [nRealOut_eq_conv nctx valid u c good,
    bmr_real_eq_ideal T facts (fsContext nctx (fsScales nctx c)) u onCurve c noWrap]
  unfold nG nForward
  simp only
  rw [expand_compress_fs nctx valid c _ rfl]
  rfl

/-- **The real outputs off the curve, on the good event and off the window, are `nGOff` of their image.** -/
theorem nRealOutOff_eq_nGOff (facts : TableFacts T) (u : AffineInput) (c : Coins T)
    (good : GoodScales (fsScales nctx c)) (outside : ¬ CWindow (nForwardOff nctx u c).2.1) :
    nRealOutOff nctx u c = nGOff (nForwardOff nctx u c).1 (nForwardOff nctx u c).2.1 := by
  have noWrap : ∀ e, hint c e = false := fun e =>
    hint_false_of_window facts (fsContext nctx (fsScales nctx c)) u c e fun w => outside ⟨e, w⟩
  rw [nRealOutOff_eq_conv nctx valid u c good,
    bmr_real_eq_ideal_off T (fsContext nctx (fsScales nctx c)) u c noWrap]
  unfold nGOff nForwardOff
  simp only
  rw [expand_compress_fs nctx valid c _ rfl]
  rfl

end Relations


/-! ### 5. The quadratic character and the sign split -/

section Character

variable [FieldCertificate]

/-- `χ(x) = x^((p−1)/2)`. -/
def chi (x : BaseField) : BaseField := x ^ Garbling.characterExponent

theorem characterExponent_odd : Odd Garbling.characterExponent := by
  rw [Nat.odd_iff]
  unfold Garbling.characterExponent baseFieldModulus
  norm_num

theorem rootExponent_two : Garbling.rootExponent * 2 = Garbling.characterExponent + 1 := by
  unfold Garbling.rootExponent Garbling.characterExponent baseFieldModulus
  norm_num

theorem chi_mul (a b : BaseField) : chi (a * b) = chi a * chi b := mul_pow a b _

theorem chi_neg_one : chi (-1) = -1 := characterExponent_odd.neg_one_pow

theorem chi_one : chi 1 = 1 := one_pow _

theorem chi_sq_ne (x : BaseField) (ne : x ≠ 0) : chi (x ^ 2) = 1 := by
  unfold chi
  rw [← pow_mul, JacobianMixed.two_characterExponent]
  exact ZMod.pow_card_sub_one_eq_one ne

theorem chi_cases (x : BaseField) (ne : x ≠ 0) : chi x = 1 ∨ chi x = -1 := by
  have sq : chi x ^ 2 = 1 := by
    unfold chi
    rw [← pow_mul, mul_comm Garbling.characterExponent 2, JacobianMixed.two_characterExponent]
    exact ZMod.pow_card_sub_one_eq_one ne
  exact sq_eq_one_iff.mp sq

theorem one_ne_neg_one : (1 : BaseField) ≠ -1 := by
  intro same
  have two : (2 : BaseField) = 0 := by linear_combination same
  exact Rows.two_ne_zero_base two

theorem signed_false (a : BaseField) : Rows.signed false a = a := if_neg Bool.false_ne_true

theorem signed_true (a : BaseField) : Rows.signed true a = -a := if_pos rfl

theorem signed_mul (sign : Bool) (a b : BaseField) : Rows.signed sign (a * b) = Rows.signed sign a * b := by
  cases sign
  · rw [signed_false, signed_false]
  · rw [signed_true, signed_true, neg_mul]

theorem signed_signed (sign : Bool) (a : BaseField) : Rows.signed sign (Rows.signed sign a) = a := by
  cases sign
  · rw [signed_false, signed_false]
  · rw [signed_true, signed_true, neg_neg]

theorem signed_ne_zero (sign : Bool) (a : BaseField) (ne : a ≠ 0) : Rows.signed sign a ≠ 0 := by
  cases sign
  · rw [signed_false]
    exact ne
  · rw [signed_true]
    exact neg_ne_zero.mpr ne

theorem chi_signed (sign : Bool) (a : BaseField) : chi (Rows.signed sign a) = Rows.signed sign (chi a) := by
  cases sign
  · rw [signed_false, signed_false]
  · rw [signed_true, signed_true, show -a = -1 * a by ring, chi_mul, chi_neg_one]
    ring


/-- The square root `x^((p+1)/4)`. -/
def root (x : BaseField) : BaseField := x ^ Garbling.rootExponent

theorem root_sq (x : BaseField) (square : chi x = 1) : root x ^ 2 = x := by
  unfold root
  rw [← pow_mul, rootExponent_two, pow_succ]
  unfold chi at square
  rw [square, one_mul]

theorem chi_root (x : BaseField) (square : chi x = 1) : chi (root x) = 1 := by
  unfold chi root
  rw [← pow_mul, mul_comm, pow_mul]
  unfold chi at square
  rw [square, one_pow]

theorem root_ne_zero (x : BaseField) (ne : x ≠ 0) : root x ≠ 0 := pow_ne_zero _ ne

theorem root_sq_elem (tau : BaseField) : root (tau ^ 2) = chi tau * tau := by
  unfold root chi
  rw [← pow_mul, mul_comm 2, rootExponent_two, pow_succ]

/-- `±r` by a bit. -/
def signedRoot (b : Bool) (x : BaseField) : BaseField := if b then root x else -root x

theorem signedRoot_false (x : BaseField) : signedRoot false x = -root x := if_neg Bool.false_ne_true

theorem signedRoot_true (x : BaseField) : signedRoot true x = root x := if_pos rfl

theorem signedRoot_ne_zero (b : Bool) (x : BaseField) (ne : x ≠ 0) : signedRoot b x ≠ 0 := by
  cases b
  · rw [signedRoot_false]
    exact neg_ne_zero.mpr (root_ne_zero x ne)
  · rw [signedRoot_true]
    exact root_ne_zero x ne

theorem signedRoot_sq (b : Bool) (x : BaseField) (square : chi x = 1) : signedRoot b x ^ 2 = x := by
  cases b
  · rw [signedRoot_false, neg_sq, root_sq x square]
  · rw [signedRoot_true, root_sq x square]

theorem chi_signedRoot (b : Bool) (x : BaseField) (square : chi x = 1) :
    chi (signedRoot b x) = Rows.signed (!b) 1 := by
  cases b
  · rw [signedRoot_false, Bool.not_false, signed_true, show -root x = -1 * root x by ring, chi_mul, chi_neg_one,
      chi_root x square, mul_one]
  · rw [signedRoot_true, Bool.not_true, signed_false, chi_root x square]

theorem nz_ext {a b : NonZeroBase} (h : a.value = b.value) : a = b := by
  cases a
  cases b
  subst h
  rfl

/-- `[χ(x) = 1]`. -/
def sqBit (x : BaseField) : Bool := decide (chi x = 1)

/-- `[χ(x) = −1]`. -/
def negBit (x : BaseField) : Bool := decide (chi x = -1)

theorem sqBit_true (x : BaseField) (h : chi x = 1) : sqBit x = true := decide_eq_true h

theorem sqBit_false (x : BaseField) (h : chi x ≠ 1) : sqBit x = false := decide_eq_false h

theorem negBit_true (x : BaseField) (h : chi x = -1) : negBit x = true := decide_eq_true h

theorem negBit_false (x : BaseField) (h : chi x ≠ -1) : negBit x = false := decide_eq_false h

theorem negBit_signed_one (sign : Bool) (a : BaseField) (h : chi a = Rows.signed sign 1) : negBit a = sign := by
  cases sign
  · rw [signed_false] at h
    exact negBit_false a (by rw [h]; exact one_ne_neg_one)
  · rw [signed_true] at h
    exact negBit_true a h

/-- The sign split of one digit's sign scale: `(τ, ν) ↦ ((−1)^ν τ², [χ(τ) = 1])`. -/
def signSplit (p : NonZeroBase × Bool) : NonZeroBase × Bool :=
  (⟨Rows.signed p.2 (p.1.value ^ 2), signed_ne_zero _ _ (pow_ne_zero 2 p.1.nonzero)⟩, sqBit p.1.value)

/-- Its inverse. -/
def signJoin (q : NonZeroBase × Bool) : NonZeroBase × Bool :=
  (⟨signedRoot q.2 (Rows.signed (negBit q.1.value) q.1.value),
      signedRoot_ne_zero _ _ (signed_ne_zero _ _ q.1.nonzero)⟩, negBit q.1.value)

theorem signSplit_fst (p : NonZeroBase × Bool) :
    (signSplit p).1.value = Rows.signed p.2 (p.1.value ^ 2) := by
  dsimp only [signSplit]

theorem signSplit_snd (p : NonZeroBase × Bool) : (signSplit p).2 = sqBit p.1.value := by
  dsimp only [signSplit]

theorem signJoin_fst (q : NonZeroBase × Bool) :
    (signJoin q).1.value = signedRoot q.2 (Rows.signed (negBit q.1.value) q.1.value) := by
  dsimp only [signJoin]

theorem signJoin_snd (q : NonZeroBase × Bool) : (signJoin q).2 = negBit q.1.value := by
  dsimp only [signJoin]

theorem signJoin_signSplit (p : NonZeroBase × Bool) : signJoin (signSplit p) = p := by
  obtain ⟨⟨tau, ne⟩, sign⟩ := p
  have signEq : negBit (Rows.signed sign (tau ^ 2)) = sign := by
    refine negBit_signed_one sign _ ?_
    rw [chi_signed, chi_sq_ne tau ne]
  refine Prod.ext (nz_ext ?_) ?_
  · rw [signJoin_fst, signSplit_fst, signSplit_snd, signEq, signed_signed]
    rcases chi_cases tau ne with one | minus
    · rw [sqBit_true tau one, signedRoot_true, root_sq_elem, one, one_mul]
    · rw [sqBit_false tau (by rw [minus]; exact one_ne_neg_one.symm), signedRoot_false, root_sq_elem, minus]
      ring
  · rw [signJoin_snd, signSplit_fst]
    exact signEq

theorem signSplit_signJoin (q : NonZeroBase × Bool) : signSplit (signJoin q) = q := by
  obtain ⟨⟨kappa, ne⟩, b⟩ := q
  have square : chi (Rows.signed (negBit kappa) kappa) = 1 := by
    rw [chi_signed]
    rcases chi_cases kappa ne with one | minus
    · rw [negBit_false kappa (by rw [one]; exact one_ne_neg_one), one, signed_false]
    · rw [negBit_true kappa minus, minus, signed_true, neg_neg]
  refine Prod.ext (nz_ext ?_) ?_
  · rw [signSplit_fst, signJoin_fst, signJoin_snd, signedRoot_sq _ _ square, signed_signed]
  · rw [signSplit_snd, signJoin_fst]
    dsimp only
    have chiRoot := chi_signedRoot b _ square
    cases b
    · rw [Bool.not_false, signed_true] at chiRoot
      exact sqBit_false _ (by rw [chiRoot]; exact one_ne_neg_one.symm)
    · rw [Bool.not_true, signed_false] at chiRoot
      exact sqBit_true _ chiRoot

theorem signBit_eq_negBit (x : BaseField) : Rows.signBit x = negBit x := by
  unfold Rows.signBit negBit chi
  rw [JacobianMixed.fieldPower_eq _ _ JacobianMixed.characterExponent_lt]

/-- **`ν` of `(−1)^ν τ²` is `ν`.** -/
theorem signBit_signed_sq (sign : Bool) (tau : BaseField) (ne : tau ≠ 0) :
    Rows.signBit (Rows.signed sign (tau ^ 2)) = sign := by
  rw [signBit_eq_negBit]
  refine negBit_signed_one sign _ ?_
  rw [chi_signed, chi_sq_ne tau ne]

/-- **The sign split is a bijection.** -/
def signEquiv : NonZeroBase × Bool ≃ NonZeroBase × Bool :=
  ⟨signSplit, signJoin, signJoin_signSplit, signSplit_signJoin⟩

end Character

/-! ### 6. The ideal side through `nG` -/

/-- The field scales of kernel scales `(ρ, τ)` and signs `ν`: `(ρ, (−1)^ν τ²)`. -/
def kScales (rt : Fin 91 → NonZeroBase × NonZeroBase) (sign : Fin 91 → Bool) : Scales :=
  fun d => ((rt d).1.value, Rows.signed (sign d) ((rt d).2.value ^ 2))

/-- The compact cells of a normalized source. -/
def compactOf (src : NSource T) : CSource T := (src.1, fun d => (src.2.1 d).xC0, src.2.2.2)

/-- P45's row target of scaled sparse rows. -/
theorem rowTarget_scaled (rho kappa : BaseField) (rows : Coordinates.Rows) (sparse : FieldMacToECMac.SparseRow rows)
    (u : AffineInput) :
    rowTarget (Rows.scaled rho kappa rows) u =
      ⟨rho ^ 2 * Coordinates.evaluate rows.x u, kappa * Coordinates.evaluate rows.y u,
        rho * Coordinates.evaluate rows.z u⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sparse
  simp only [rowTarget, Rows.scaled, Rows.multiply, Coordinates.evaluate, h1, h2, h3, h4, h5, h6, h7, h8,
    FieldMacToECMac.HomogeneousValue.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- The normalized solve at a corrected target is P45's solve at the raw target with zero flags. -/
theorem nCollectorSolve_eq (target raw : FieldMacToECMac.HomogeneousValue) (row : RowGamma) (sign : Bool)
    (u : AffineInput) (values : Biquadratic.Values) (e : Biquadratic.Element)
    (hx : raw.x = target.x) (hy : raw.y = Rows.signed sign target.y) (hz : raw.z = target.z) :
    nCollectorSolve target (srcRow row sign) u values e = collectorSolve raw ⟨row.xC0, 0, 0⟩ u values e := by
  have flag0 : Rows.flagValue false = 0 := if_neg Bool.false_ne_true
  rcases e with (_ | _ | _ | _) | (_ | _ | _)
  · rfl
  · show target.x - _ = raw.x - _
    rw [hx]
    rfl
  · show (Rows.signed sign target.y - (Rows.flagValue false * u.x ^ 2 + _ + _)) * _ =
      (raw.y - (0 * u.x ^ 2 + _ + _)) * _
    rw [hy, flag0]
  · show target.z - Rows.flagValue false = raw.z - 0
    rw [hz, flag0]
  · rfl
  · rfl
  · rfl

section Ideal

variable [FieldCertificate] (nctx : NContext) (sparse : nctx.Sparse)
include sparse

/-- **The ideal outputs at the corrected targets of `(ρ, τ)` are `nG` at the field scales `(ρ, (−1)^ν τ²)`.** -/
theorem nIdealOut_eq_nG (u : AffineInput) (rt : Fin 91 → NonZeroBase × NonZeroBase) (cells : NSource T × Visible T u) :
    nIdealOut (nTargets nctx u rt) u cells = nG nctx u (kScales rt cells.1.2.2.1) (compactOf cells.1, cells.2) := by
  obtain ⟨⟨J, rows, signs, cur⟩, vis⟩ := cells
  have pub : (fun d => srcRow (rows d) (signs d)) =
      fun d => convRow (kScales rt signs d).2 (⟨(rows d).xC0, 0, 0⟩ : RowGamma) := by
    funext d
    unfold srcRow convRow kScales
    rw [signBit_signed_sq (signs d) (rt d).2.value (rt d).2.nonzero]
  have solve : ∀ (d : Fin 91) (values : Biquadratic.Values) (e : Biquadratic.Element),
      nCollectorSolve (nTargets nctx u rt d) (srcRow (rows d) (signs d)) u values e =
        collectorSolve (rowTarget ((fsContext nctx (kScales rt signs)).rows d) u) ⟨(rows d).xC0, 0, 0⟩ u values e := by
    intro d values e
    refine nCollectorSolve_eq _ _ _ _ u values e ?_ ?_ ?_
    · show (rowTarget (Rows.scaled _ _ (nctx.rows d)) u).x = _
      rw [rowTarget_scaled _ _ _ (sparse d)]
      rfl
    · show (rowTarget (Rows.scaled _ _ (nctx.rows d)) u).y = _
      rw [rowTarget_scaled _ _ _ (sparse d)]
      show Rows.signed (signs d) ((rt d).2.value ^ 2) * Coordinates.evaluate (nctx.rows d).y u =
        Rows.signed (signs d) ((rt d).2.value ^ 2 * Coordinates.evaluate (nctx.rows d).y u)
      rw [signed_mul]
    · show (rowTarget (Rows.scaled _ _ (nctx.rows d)) u).z = _
      rw [rowTarget_scaled _ _ _ (sparse d)]
      rfl
  unfold nIdealOut nG conv idealOut nPublish
  simp only
  rw [pub]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  funext r
  simp only
  rw [solve]
  rfl

end Ideal

/-! ### 7. Uniform sums -/

section Sums

open scoped ENNReal

theorem tsum_uniform_prod {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (f : A × B → ℝ≥0∞) :
    ∑' x, PMF.uniformOfFintype (A × B) x * f x =
      ∑' a, PMF.uniformOfFintype A a * ∑' b, PMF.uniformOfFintype B b * f (a, b) := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun a => tsum_congr fun b => ?_
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  ring

theorem tsum_uniform_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (e : A ≃ B)
    (f : B → ℝ≥0∞) :
    ∑' a, PMF.uniformOfFintype A a * f (e a) = ∑' b, PMF.uniformOfFintype B b * f b := by
  rw [← e.tsum_eq]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem tsum_uniform_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ≥0∞) :
    ∑' a, PMF.uniformOfFintype A a * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem tsum_map_mul' {α β : Type*} (μ : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' o, (μ.map g) o * f o = ∑' a, μ a * f (g a) := by
  classical
  simp only [PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (g a)]
  · rw [if_pos rfl]
  · intro o different
    rw [if_neg different, zero_mul]

theorem tsum_uniform_map {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (g : A → B)
    (law : (PMF.uniformOfFintype A).map g = PMF.uniformOfFintype B) (f : B → ℝ≥0∞) :
    ∑' a, PMF.uniformOfFintype A a * f (g a) = ∑' b, PMF.uniformOfFintype B b * f b := by
  rw [← tsum_map_mul', law]

/-- **Restricting a uniform sum to a subtype.** -/
theorem tsum_uniform_restrict {A : Type*} [Fintype A] [Nonempty A] (p : A → Prop) [DecidablePred p]
    [Nonempty {a // p a}] (f : A → ℝ≥0∞) :
    ∑' a, PMF.uniformOfFintype A a * (if p a then f a else 0) =
      (∑' a, PMF.uniformOfFintype A a * (if p a then 1 else 0)) *
        ∑' a : {a // p a}, PMF.uniformOfFintype {a // p a} a * f a.1 := by
  classical
  have split : ∀ g : A → ℝ≥0∞, ∑' a, (if p a then g a else 0) = ∑' a : {a // p a}, g a.1 := by
    intro g
    rw [tsum_fintype, tsum_fintype, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun a => by simp) g
  have cardPos : (Fintype.card {a // p a} : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have cardFin : (Fintype.card {a // p a} : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [PMF.uniformOfFintype_apply, mul_ite, mul_one, mul_zero]
  rw [split (fun a => (Fintype.card A : ℝ≥0∞)⁻¹ * f a), split (fun _ => (Fintype.card A : ℝ≥0∞)⁻¹),
    tsum_fintype (fun _ : {a // p a} => (Fintype.card A : ℝ≥0∞)⁻¹), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_
  rw [mul_comm (Fintype.card {a // p a} : ℝ≥0∞) _, mul_assoc, ← mul_assoc (Fintype.card {a // p a} : ℝ≥0∞),
    ENNReal.mul_inv_cancel cardPos cardFin, one_mul]

end Sums

/-! ### 8. The kernel scales against the good field scales -/

/-- The good field scales as nonzero pairs. -/
def goodEquiv : (Fin 91 → NonZeroBase × NonZeroBase) ≃ {s : Scales // GoodScales s} where
  toFun g := ⟨fun d => ((g d).1.value, (g d).2.value), fun d => ⟨(g d).1.nonzero, (g d).2.nonzero⟩⟩
  invFun s := fun d => (⟨(s.1 d).1, (s.2 d).1⟩, ⟨(s.1 d).2, (s.2 d).2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

instance goodScalesNonempty : Nonempty {s : Scales // GoodScales s} := ⟨goodEquiv fun _ => (⟨1, one_ne_zero_base⟩, ⟨1, one_ne_zero_base⟩)⟩

section Kernel

variable [FieldCertificate]

/-- One digit's sign split: `((ρ, τ), ν) ↦ ((ρ, (−1)^ν τ²), [χ(τ) = 1])`. -/
def digitEquiv : (NonZeroBase × NonZeroBase) × Bool ≃ (NonZeroBase × NonZeroBase) × Bool :=
  (Equiv.prodAssoc _ _ _).trans (((Equiv.refl NonZeroBase).prodCongr signEquiv).trans (Equiv.prodAssoc _ _ _).symm)

/-- **The kernel split**: every digit's sign split. -/
def kEquiv : (Fin 91 → NonZeroBase × NonZeroBase) × (Fin 91 → Bool) ≃
    (Fin 91 → NonZeroBase × NonZeroBase) × (Fin 91 → Bool) :=
  (Equiv.arrowProdEquivProdArrow _ _ _).symm.trans
    ((Equiv.piCongrRight fun _ => digitEquiv).trans (Equiv.arrowProdEquivProdArrow _ _ _))

/-- **Uniform kernel scales and uniform signs give uniform field scales.** -/
theorem kScales_law :
    (PMF.uniformOfFintype ((Fin 91 → NonZeroBase × NonZeroBase) × (Fin 91 → Bool))).map
        (fun x => (kEquiv x).1) = PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase) := by
  have factor : (fun x => (kEquiv x).1) = Prod.fst ∘ kEquiv := rfl
  rw [factor, ← PMF.map_comp, uniform_map_equiv, uniform_map_fst]

theorem kEquiv_fst (x : (Fin 91 → NonZeroBase × NonZeroBase) × (Fin 91 → Bool)) (d : Fin 91) :
    (kEquiv x).1 d = ((x.1 d).1, (signSplit ((x.1 d).2, x.2 d)).1) := rfl

theorem kScales_eq (x : (Fin 91 → NonZeroBase × NonZeroBase) × (Fin 91 → Bool)) :
    kScales x.1 x.2 = (goodEquiv (kEquiv x).1).1 := by
  funext d
  show ((x.1 d).1.value, Rows.signed (x.2 d) ((x.1 d).2.value ^ 2)) =
    (((kEquiv x).1 d).1.value, ((kEquiv x).1 d).2.value)
  rw [kEquiv_fst, signSplit_fst]

end Kernel

/-! ### 9. The cores -/

instance normBadDecidable (src : NSource T) : Decidable (normBad src) := by
  unfold normBad
  infer_instance

/-- The ideal cells as compact cells, hidden cells and signs. -/
def cellsEquiv (u : AffineInput) :
    NSource T × Visible T u ≃ ((CSource T × Visible T u) × Scales) × (Fin 91 → Bool) where
  toFun c := (((compactOf c.1, c.2), hiddenCells c.1), c.1.2.2.1)
  invFun x := ((x.1.1.1.1, fun d => ⟨x.1.1.1.2.1 d, (x.1.2 d).2, (x.1.2 d).1⟩, x.2, x.1.1.1.2.2), x.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The ideal cells off the curve as compact cells, hidden cells and signs. -/
def cellsEquivOff (u : AffineInput) :
    NSource T × Cold T u ≃ ((CSource T × Cold T u) × Scales) × (Fin 91 → Bool) where
  toFun c := (((compactOf c.1, c.2), hiddenCells c.1), c.1.2.2.1)
  invFun x := ((x.1.1.1.1, fun d => ⟨x.1.1.1.2.1 d, (x.1.2 d).2, (x.1.2 d).1⟩, x.2, x.1.1.1.2.2), x.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

instance nSourceFintype : Fintype (NSource T) := instFintypeProd _ _

instance nSourceNonempty : Nonempty (NSource T) :=
  ⟨(fun _ _ => 0, fun _ => ⟨0, 0, 0⟩, fun _ => false, (0, 0, 0))⟩

section Core

open scoped ENNReal
open Classical

/-- The two-sided window of the compact cells on the curve. -/
def CWindowOn {u : AffineInput} (y : CSource T × Visible T u) : Prop := CWindow (y.1, y.2.1)

/-- The weight of field scales on the curve: the compact cells off the window through `nG`. -/
def qOn (nctx : NContext) (u : AffineInput) (F : NOut T u → ℝ≥0∞) (s : Scales) : ℝ≥0∞ :=
  ∑' y : CSource T × Visible T u, PMF.uniformOfFintype (CSource T × Visible T u) y *
    (if CWindowOn y then 0 else F (nG nctx u s y))

/-- The same off the curve. -/
def qOff (u : AffineInput) (F : NOutOff T u → ℝ≥0∞) (s : Scales) : ℝ≥0∞ :=
  ∑' y : CSource T × Cold T u, PMF.uniformOfFintype (CSource T × Cold T u) y *
    (if CWindow y then 0 else F (nGOff s y))

/-- The mass of good field scales. -/
def goodMass : ℝ≥0∞ := ∑' s : Scales, PMF.uniformOfFintype Scales s * (if GoodScales s then 1 else 0)

theorem tsum_uniform_ite {A : Type*} [Fintype A] [Nonempty A] (P : Prop) [Decidable P] (f : A → ℝ≥0∞) :
    ∑' a, PMF.uniformOfFintype A a * (if P then f a else 0) = if P then ∑' a, PMF.uniformOfFintype A a * f a else 0 := by
  split_ifs <;> simp

/-- **A sum over images whose weight reads only the scales and the compact cells.** -/
theorem image_sum {Y R : Type*} [Fintype Y] [Nonempty Y] [Fintype R] [Nonempty R] (w : Scales → Y → ℝ≥0∞) :
    ∑' x : Scales × (Y × R), PMF.uniformOfFintype (Scales × (Y × R)) x *
        (if GoodScales x.1 then w x.1 x.2.1 else 0) =
      goodMass * ∑' g : {s // GoodScales s}, PMF.uniformOfFintype {s // GoodScales s} g *
        ∑' y, PMF.uniformOfFintype Y y * w g.1 y := by
  rw [tsum_uniform_prod]
  have inner : ∀ s : Scales, ∑' b : Y × R, PMF.uniformOfFintype (Y × R) b * (if GoodScales s then w s b.1 else 0) =
      if GoodScales s then ∑' y, PMF.uniformOfFintype Y y * w s y else 0 := by
    intro s
    rw [tsum_uniform_ite, tsum_uniform_prod]
    congr 1
    refine tsum_congr fun y => ?_
    rw [tsum_uniform_const]
  simp only [inner]
  exact tsum_uniform_restrict GoodScales _

/-- The kernel's and the signs' average of a weight of field scales is the good scales' average. -/
theorem kernel_sum [FieldCertificate] (q : Scales → ℝ≥0∞) :
    ∑' rt, PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase) rt *
        ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * q (kScales rt sign) =
      ∑' g : {s // GoodScales s}, PMF.uniformOfFintype {s // GoodScales s} g * q g.1 := by
  rw [← tsum_uniform_prod (fun x => q (kScales x.1 x.2))]
  simp only [kScales_eq]
  rw [tsum_uniform_map (fun x => (kEquiv x).1) kScales_law (fun g => q (goodEquiv g).1)]
  exact tsum_uniform_equiv goodEquiv (fun g => q g.1)

section Weighted

variable [FieldCertificate] (facts : TableFacts T) (nctx : NContext) (valid : nctx.Valid)

include facts valid in
/-- The real side on the curve is at least the good scales' average. -/
theorem real_ge (u : AffineInput) (onCurve : OnCurve u) (F : NOut T u → ℝ≥0∞) :
    goodMass * ∑' g : {s // GoodScales s}, PMF.uniformOfFintype {s // GoodScales s} g * qOn nctx u F g.1 ≤
      ∑' c, PMF.uniformOfFintype (Coins T) c * F (nRealOut nctx u c) := by
  have good : u.x ≠ 0 ∧ u.y ≠ 0 :=
    ⟨Security.Phase3.onCurve_x_ne_zero u onCurve, Security.Phase3.onCurve_y_ne_zero u onCurve⟩
  have step : ∑' c, PMF.uniformOfFintype (Coins T) c *
      (if GoodScales (nForward nctx u c).1 then
        (if CWindowOn (nForward nctx u c).2.1 then 0 else F (nG nctx u (nForward nctx u c).1 (nForward nctx u c).2.1))
        else 0) ≤ ∑' c, PMF.uniformOfFintype (Coins T) c * F (nRealOut nctx u c) := by
    refine ENNReal.tsum_le_tsum fun c => mul_le_mul' le_rfl ?_
    split_ifs with g w
    · exact zero_le
    · rw [nRealOut_eq_nG nctx valid facts u onCurve c g w]
    · exact zero_le
  refine le_trans (le_of_eq ?_) step
  have reindex := tsum_uniform_equiv (nEquiv T nctx valid u good) (fun x : NImage T u => if GoodScales x.1 then
    (if CWindowOn x.2.1 then 0 else F (nG nctx u x.1 x.2.1)) else 0)
  exact (image_sum (fun s y => if CWindowOn y then 0 else F (nG nctx u s y))).symm.trans reindex.symm

include facts valid in
/-- The real side off the curve is at least the good scales' average. -/
theorem real_ge_off (u : AffineInput) (F : NOutOff T u → ℝ≥0∞) :
    goodMass * ∑' g : {s // GoodScales s}, PMF.uniformOfFintype {s // GoodScales s} g * qOff u F g.1 ≤
      ∑' c, PMF.uniformOfFintype (Coins T) c * F (nRealOutOff nctx u c) := by
  have step : ∑' c, PMF.uniformOfFintype (Coins T) c *
      (if GoodScales (nForwardOff nctx u c).1 then
        (if CWindow (nForwardOff nctx u c).2.1 then 0 else F (nGOff (nForwardOff nctx u c).1 (nForwardOff nctx u c).2.1))
        else 0) ≤ ∑' c, PMF.uniformOfFintype (Coins T) c * F (nRealOutOff nctx u c) := by
    refine ENNReal.tsum_le_tsum fun c => mul_le_mul' le_rfl ?_
    split_ifs with g w
    · exact zero_le
    · rw [nRealOutOff_eq_nGOff nctx valid facts u c g w]
    · exact zero_le
  refine le_trans (le_of_eq ?_) step
  have reindex := tsum_uniform_equiv (nEquivOff T nctx valid u) (fun x : NImageOff T u => if GoodScales x.1 then
    (if CWindow x.2.1 then 0 else F (nGOff x.1 x.2.1)) else 0)
  exact (image_sum (fun s y => if CWindow y then 0 else F (nGOff s y))).symm.trans reindex.symm

end Weighted

/-- A weight of ideal cells that reads the hidden cells only through their zero event. -/
theorem cells_sum {Y : Type*} [Fintype Y] [Nonempty Y] (w : Y → (Fin 91 → Bool) → ℝ≥0∞) :
    ∑' x : (Y × Scales) × (Fin 91 → Bool), PMF.uniformOfFintype ((Y × Scales) × (Fin 91 → Bool)) x *
        (if GoodScales x.1.2 then w x.1.1 x.2 else 0) =
      goodMass * ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign *
        ∑' y, PMF.uniformOfFintype Y y * w y sign := by
  rw [tsum_uniform_prod, tsum_uniform_prod]
  have each : ∀ (y : Y) (σ : Scales), ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign *
      (if GoodScales σ then w y sign else 0) =
      (if GoodScales σ then 1 else 0) * ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * w y sign := by
    intro y σ
    rw [tsum_uniform_ite]
    split_ifs <;> simp
  have inner : ∀ y : Y, ∑' σ : Scales, PMF.uniformOfFintype Scales σ *
      ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * (if GoodScales σ then w y sign else 0) =
      goodMass * ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * w y sign := by
    intro y
    simp only [each]
    unfold goodMass
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun σ => ?_
    ring
  simp only [inner]
  calc ∑' y, PMF.uniformOfFintype Y y * (goodMass * ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * w y sign)
      = goodMass * ∑' y, ∑' sign, PMF.uniformOfFintype Y y * (PMF.uniformOfFintype (Fin 91 → Bool) sign * w y sign) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        rw [ENNReal.tsum_mul_left]
        ring
    _ = goodMass * ∑' sign, ∑' y, PMF.uniformOfFintype Y y * (PMF.uniformOfFintype (Fin 91 → Bool) sign * w y sign) := by
        rw [ENNReal.tsum_comm]
    _ = _ := by
        congr 1
        refine tsum_congr fun sign => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        ring

section Weighted

variable [FieldCertificate] (facts : TableFacts T) (nctx : NContext) (valid : nctx.Valid) (sparse : nctx.Sparse)

include facts valid sparse in
/-- **The normalized core on the curve** (weighted): the ideal outputs at uniform kernel scales and uniform cells,
flagged on the window and on the hidden cells' zero event, weigh at most the real outputs at uniform coins. -/
theorem nCore_weighted (u : AffineInput) (onCurve : OnCurve u)
    (flag : (Fin 91 → NonZeroBase × NonZeroBase) → NSource T × Visible T u → Prop)
    (outside : ∀ rt cells, ¬ flag rt cells → ¬ CWindow (compactOf cells.1, cells.2.1))
    (norm : ∀ rt cells, ¬ flag rt cells → ¬ normBad cells.1)
    (F : NOut T u → ℝ≥0∞) :
    ∑' rt, PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase) rt *
        ∑' cells, PMF.uniformOfFintype (NSource T × Visible T u) cells *
          (if flag rt cells then 0 else F (nIdealOut (nTargets nctx u rt) u cells)) ≤
      ∑' c, PMF.uniformOfFintype (Coins T) c * F (nRealOut nctx u c) := by
  refine le_trans ?_ (real_ge facts nctx valid u onCurve F)
  have each : ∀ rt, ∑' cells, PMF.uniformOfFintype (NSource T × Visible T u) cells *
      (if flag rt cells then 0 else F (nIdealOut (nTargets nctx u rt) u cells)) ≤
      goodMass * ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * qOn nctx u F (kScales rt sign) := by
    intro rt
    calc _ ≤ ∑' cells, PMF.uniformOfFintype (NSource T × Visible T u) cells *
          (fun x : ((CSource T × Visible T u) × Scales) × (Fin 91 → Bool) =>
            if GoodScales x.1.2 then (if CWindowOn x.1.1 then 0 else F (nG nctx u (kScales rt x.2) x.1.1)) else 0)
            (cellsEquiv u cells) := by
          refine ENNReal.tsum_le_tsum fun cells => mul_le_mul' le_rfl ?_
          by_cases flagged : flag rt cells
          · rw [if_pos flagged]
            exact zero_le
          · rw [if_neg flagged]
            have g : GoodScales (hiddenCells cells.1) := not_not.mp (norm rt cells flagged)
            have w : ¬ CWindowOn ((compactOf cells.1, cells.2) : CSource T × Visible T u) := outside rt cells flagged
            show _ ≤ if GoodScales (hiddenCells cells.1) then
              (if CWindowOn ((compactOf cells.1, cells.2) : CSource T × Visible T u) then 0 else
                F (nG nctx u (kScales rt cells.1.2.2.1) (compactOf cells.1, cells.2))) else 0
            rw [if_pos g, if_neg w, nIdealOut_eq_nG nctx sparse u rt cells]
      _ = ∑' x, PMF.uniformOfFintype (((CSource T × Visible T u) × Scales) × (Fin 91 → Bool)) x *
            (if GoodScales x.1.2 then (if CWindowOn x.1.1 then 0 else F (nG nctx u (kScales rt x.2) x.1.1)) else 0) :=
          tsum_uniform_equiv (cellsEquiv u) (fun x : ((CSource T × Visible T u) × Scales) × (Fin 91 → Bool) =>
            if GoodScales x.1.2 then (if CWindowOn x.1.1 then 0 else F (nG nctx u (kScales rt x.2) x.1.1)) else 0)
      _ = _ := cells_sum fun y sign => if CWindowOn y then 0 else F (nG nctx u (kScales rt sign) y)
  calc _ ≤ ∑' rt, PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase) rt *
        (goodMass * ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * qOn nctx u F (kScales rt sign)) :=
        ENNReal.tsum_le_tsum fun rt => mul_le_mul' le_rfl (each rt)
    _ = goodMass * ∑' rt, PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase) rt *
        ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * qOn nctx u F (kScales rt sign) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun rt => ?_
        ring
    _ = _ := by rw [kernel_sum]

/-- `nGOff` reads the scales only through the signs of the `κ̂`s. -/
theorem nGOff_congr {u : AffineInput} (s s' : Scales) (same : ∀ d, Rows.signBit (s d).2 = Rows.signBit (s' d).2)
    (y : CSource T × Cold T u) : nGOff s y = nGOff s' y := by
  unfold nGOff convOff convRow
  simp only [same]

omit sparse in
include facts valid in
/-- **The normalized core off the curve** (weighted). -/
theorem nCoreOff_weighted (u : AffineInput) (flag : NSource T × Cold T u → Prop)
    (outside : ∀ cells, ¬ flag cells → ¬ CWindow (compactOf cells.1, cells.2))
    (norm : ∀ cells, ¬ flag cells → ¬ normBad cells.1)
    (F : NOutOff T u → ℝ≥0∞) :
    ∑' cells, PMF.uniformOfFintype (NSource T × Cold T u) cells *
        (if flag cells then 0 else F (nIdealOutOff u cells)) ≤
      ∑' c, PMF.uniformOfFintype (Coins T) c * F (nRealOutOff nctx u c) := by
  refine le_trans ?_ (real_ge_off facts nctx valid u F)
  let one : Fin 91 → NonZeroBase × NonZeroBase := fun _ => (⟨1, one_ne_zero_base⟩, ⟨1, one_ne_zero_base⟩)
  have ideal : ∀ cells : NSource T × Cold T u,
      nIdealOutOff u cells = nGOff (kScales one cells.1.2.2.1) (compactOf cells.1, cells.2) := by
    intro cells
    obtain ⟨⟨J, rows, signs, cur⟩, cold⟩ := cells
    unfold nIdealOutOff nGOff convOff idealOutOff nPublish
    simp only
    have pub : (fun d => srcRow (rows d) (signs d)) =
        fun d => convRow (kScales one signs d).2 (⟨(rows d).xC0, 0, 0⟩ : RowGamma) := by
      funext d
      unfold srcRow convRow kScales
      rw [signBit_signed_sq (signs d) (one d).2.value (one d).2.nonzero]
    rw [pub]
    rfl
  have signs : ∀ rt sign, qOff u F (kScales one sign) = qOff u F (kScales rt sign) := by
    intro rt sign
    unfold qOff
    refine tsum_congr fun y => ?_
    rw [nGOff_congr (kScales one sign) (kScales rt sign) (fun d => by
      unfold kScales
      rw [signBit_signed_sq _ _ (one d).2.nonzero, signBit_signed_sq _ _ (rt d).2.nonzero]) y]
  calc _ ≤ ∑' cells, PMF.uniformOfFintype (NSource T × Cold T u) cells *
        (fun x : ((CSource T × Cold T u) × Scales) × (Fin 91 → Bool) =>
          if GoodScales x.1.2 then (if CWindow x.1.1 then 0 else F (nGOff (kScales one x.2) x.1.1)) else 0)
          (cellsEquivOff u cells) := by
        refine ENNReal.tsum_le_tsum fun cells => mul_le_mul' le_rfl ?_
        by_cases flagged : flag cells
        · rw [if_pos flagged]
          exact zero_le
        · rw [if_neg flagged]
          have g : GoodScales (hiddenCells cells.1) := not_not.mp (norm cells flagged)
          have w : ¬ CWindow ((compactOf cells.1, cells.2) : CSource T × Cold T u) := outside cells flagged
          show _ ≤ if GoodScales (hiddenCells cells.1) then
            (if CWindow ((compactOf cells.1, cells.2) : CSource T × Cold T u) then 0 else
              F (nGOff (kScales one cells.1.2.2.1) (compactOf cells.1, cells.2))) else 0
          rw [if_pos g, if_neg w, ideal]
    _ = ∑' x, PMF.uniformOfFintype (((CSource T × Cold T u) × Scales) × (Fin 91 → Bool)) x *
          (if GoodScales x.1.2 then (if CWindow x.1.1 then 0 else F (nGOff (kScales one x.2) x.1.1)) else 0) :=
        tsum_uniform_equiv (cellsEquivOff u) (fun x : ((CSource T × Cold T u) × Scales) × (Fin 91 → Bool) =>
          if GoodScales x.1.2 then (if CWindow x.1.1 then 0 else F (nGOff (kScales one x.2) x.1.1)) else 0)
    _ = goodMass * ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * qOff u F (kScales one sign) :=
        cells_sum fun y sign => if CWindow y then 0 else F (nGOff (kScales one sign) y)
    _ = goodMass * ∑' rt, PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase) rt *
          ∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * qOff u F (kScales rt sign) := by
        congr 1
        rw [← tsum_uniform_const (A := Fin 91 → NonZeroBase × NonZeroBase)
          (∑' sign, PMF.uniformOfFintype (Fin 91 → Bool) sign * qOff u F (kScales one sign))]
        refine tsum_congr fun rt => ?_
        simp only [signs rt]
    _ = _ := by rw [kernel_sum]

end Weighted

end Core

end

end Kriterion.CRT.Privacy.BMR
