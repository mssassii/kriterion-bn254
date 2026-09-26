/-
**P45 off the curve** (rows T5, T6).

Off the curve the masks and the bridge are hidden, so the visible cells are the cold pad entries only. The bijection
sends the coins to the published cells (joins, row constants, curve constants) and the cold entries, with the
residual: per digit the masks of the four row encodings whose offsets no constant absorbs (`rowX_x7`, `rowX_y10`,
`rowY_x9`, `rowY_y8`), `r4`, the unused randomizers and the curve mask. No division occurs, so the input is
arbitrary.

The inverse per digit: the four residual encodings have slopes that do not read any offset (`c4`, `c2`, `c3`,
`r4 + c5`), so their hot pads, offsets and row offsets `b = (O : F_p) − π` come first; then the slopes of `rowX_x9`
and `rowY_y10`; the four absorbed row offsets come from the constants (`X.c0`, `Y.c0`, `Y.c4`, `Z.c0`), and their
masks are `(O : F_p) − b`. The curve is as on the curve.
-/

import Proof.Privacy.CRT.Core.BodyMaskRowJoint

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

namespace Off

open Joint

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- The four residual row elements of a digit. -/
def residualElem : Fin 4 → Biquadratic.Element := ![.inl .rowX_x7, .inr .rowX_y10, .inl .rowY_x9, .inr .rowY_y8]

/-- The forward map off the curve. -/
def forwardOff (ctx : Context) (u : AffineInput) (c : Coins T) : (Source T × Cold T u) × ResidualOff :=
  (((join ctx c, gamma ctx c, curveTable c), coldOf u c),
    (fun d k => c.mask (d, residualElem k), c.r4, (c.unused, c.2.2.2.2.2.1)))

section Inverse

variable (ctx : Context) (u : AffineInput) (out : (Source T × Cold T u) × ResidualOff)

/-- The field offset of a row encoding at a given slope. -/
def kAt (d : Fin 91) (element : Biquadratic.Element) (a : BaseField) : BaseField :=
  padOffset (fullPad u out.1.1.1 out.1.2 a (rowEnc (d, element)))

/-- The row offsets of a digit, recovered. -/
def bOff (d : Fin 91) : Biquadratic.Values
  | .inl .rowX_x7 => kAt u out d (.inl .rowX_x7) (ctx.rows d).x.xSquared - out.2.1 d 0
  | .inr .rowX_y10 => kAt u out d (.inr .rowX_y10) (ctx.rows d).x.y - out.2.1 d 1
  | .inl .rowY_x9 => kAt u out d (.inl .rowY_x9) (ctx.rows d).y.xy - out.2.1 d 2
  | .inr .rowY_y8 => kAt u out d (.inr .rowY_y8) (out.2.2.1 d + (ctx.rows d).y.ySquared) - out.2.1 d 3
  | .inl .rowX_x9 => (ctx.rows d).x.constant - (out.1.1.2.1 d).xC0 -
      (kAt u out d (.inr .rowX_y10) (ctx.rows d).x.y - out.2.1 d 1)
  | .inr .rowY_y10 => (ctx.rows d).y.constant - 3 * out.2.2.1 d - (out.1.1.2.1 d).yC0
  | .inl .rowY_x7 => (ctx.rows d).y.xSquared - (out.1.1.2.1 d).yC4
  | .inl .rowZ_x9 => (ctx.rows d).z.constant - (out.1.1.2.1 d).zC0

/-- The curve randomizers and offsets in the chain order. -/
def r1Off : BaseField := out.1.1.2.2.2.1 - out.2.2.2.2.1
def r2Off : BaseField := out.1.1.2.2.2.2 + out.2.2.2.2.1
def kx3Off : BaseField := padOffset (fullPad u out.1.1.1 out.1.2 (-r1Off u out) (curveEnc (.inl .x3)))
def kx5Off : BaseField := padOffset (fullPad u out.1.1.1 out.1.2 (-kx3Off u out) (curveEnc (.inl .x5)))
def kx7Off : BaseField := padOffset (fullPad u out.1.1.1 out.1.2 (-kx5Off u out) (curveEnc (.inl .x7)))
def ky4Off : BaseField := padOffset (fullPad u out.1.1.1 out.1.2 (-r2Off u out) (curveEnc (.inr .y4)))
def ky6Off : BaseField := padOffset (fullPad u out.1.1.1 out.1.2 (-ky4Off u out) (curveEnc (.inr .y6)))

/-- The slope of every encoding, recovered. -/
def slopeOff : Enc → BaseField
  | .inl (.inl (d, x)) =>
    let rand := rowRand (out.2.2.1 d) (out.2.2.2.1 d)
    Biquadratic.slopes (ctx.rows d) rand.1 rand.2.1 rand.2.2 (bOff ctx u out d) (.inl x)
  | .inr (.inl (d, y)) =>
    let rand := rowRand (out.2.2.1 d) (out.2.2.2.1 d)
    Biquadratic.slopes (ctx.rows d) rand.1 rand.2.1 rand.2.2 (bOff ctx u out d) (.inr y)
  | .inl (.inr .x3) => -r1Off u out
  | .inl (.inr .x5) => -kx3Off u out
  | .inl (.inr .x7) => -kx5Off u out
  | .inr (.inr .y4) => -r2Off u out
  | .inr (.inr .y6) => -ky4Off u out

def padsOff : Pads T := fun i ρ e => fullPad u out.1.1.1 out.1.2 (slopeOff ctx u out e) e i ρ

def masksOff : RowEnc → BaseField := fun r =>
  padOffset (fun i ρ => padsOff ctx u out i ρ (rowEnc r)) - bOff ctx u out r.1 r.2

def bridgeOff : BaseField := out.1.1.2.2.1 - 3 * out.2.2.2.2.1 + ky6Off u out + kx7Off u out

/-- **The inverse off the curve.** -/
def backwardOff : Coins T :=
  (padsOff ctx u out, masksOff ctx u out, out.2.2.1, out.2.2.2.1,
    (bridgeOff u out, out.2.2.2.2, r1Off u out, r2Off u out))

end Inverse

section Left

variable (ctx : Context) (u : AffineInput) (c : Coins T)

theorem r1Off_forward : r1Off u (forwardOff ctx u c) = c.r1 := by
  simp only [r1Off, forwardOff, curveTable, CurveMembership.garble, Coins.curveMask, Coins.r1]
  ring

theorem r2Off_forward : r2Off u (forwardOff ctx u c) = c.r2 := by
  simp only [r2Off, forwardOff, curveTable, CurveMembership.garble, Coins.curveMask, Coins.r2]
  ring

theorem padOffset_forwardOff (e : Enc) (a : BaseField) (ha : a = slope ctx c e) :
    padOffset (fullPad u (forwardOff ctx u c).1.1.1 (forwardOff ctx u c).1.2 a e) = offsetF c e := by
  subst ha
  show padOffset (fullPad u (join ctx c) (coldOf u c) (slope ctx c e) e) = _
  rw [fullPad_join]
  rfl

theorem kx3Off_forward : kx3Off u (forwardOff ctx u c) = curveK c (.inl .x3) :=
  padOffset_forwardOff ctx u c _ _ (by rw [r1Off_forward]; rfl)
theorem kx5Off_forward : kx5Off u (forwardOff ctx u c) = curveK c (.inl .x5) :=
  padOffset_forwardOff ctx u c _ _ (by rw [kx3Off_forward]; rfl)
theorem kx7Off_forward : kx7Off u (forwardOff ctx u c) = curveK c (.inl .x7) :=
  padOffset_forwardOff ctx u c _ _ (by rw [kx5Off_forward]; rfl)
theorem ky4Off_forward : ky4Off u (forwardOff ctx u c) = curveK c (.inr .y4) :=
  padOffset_forwardOff ctx u c _ _ (by rw [r2Off_forward]; rfl)
theorem ky6Off_forward : ky6Off u (forwardOff ctx u c) = curveK c (.inr .y6) :=
  padOffset_forwardOff ctx u c _ _ (by rw [ky4Off_forward]; rfl)

theorem kAt_forward (d : Fin 91) (element : Biquadratic.Element) (a : BaseField)
    (ha : a = slope ctx c (rowEnc (d, element))) :
    kAt u (forwardOff ctx u c) d element a = offsetF c (rowEnc (d, element)) :=
  padOffset_forwardOff ctx u c _ _ ha

theorem bOff_forward (d : Fin 91) : bOff ctx u (forwardOff ctx u c) d = fun element => rowOffset c (d, element) := by
  funext element
  rcases element with (_ | _ | _ | _ | _) | (_ | _ | _)
  · show kAt u (forwardOff ctx u c) d (.inl .rowX_x7) (ctx.rows d).x.xSquared - c.mask (d, .inl .rowX_x7) = _
    rw [kAt_forward ctx u c d (.inl .rowX_x7) (ctx.rows d).x.xSquared rfl]
    rfl
  · show (ctx.rows d).x.constant - (gamma ctx c d).xC0 -
      (kAt u (forwardOff ctx u c) d (.inr .rowX_y10) (ctx.rows d).x.y - c.mask (d, .inr .rowX_y10)) = _
    rw [kAt_forward ctx u c d (.inr .rowX_y10) (ctx.rows d).x.y rfl]
    simp only [gamma, FieldMacToECMac.garbleRow, Biquadratic.garbleX]
    unfold rowOffset
    ring
  · simp only [bOff, forwardOff, gamma, FieldMacToECMac.garbleRow, Biquadratic.garbleY]
    ring
  · show kAt u (forwardOff ctx u c) d (.inl .rowY_x9) (ctx.rows d).y.xy - c.mask (d, .inl .rowY_x9) = _
    rw [kAt_forward ctx u c d (.inl .rowY_x9) (ctx.rows d).y.xy rfl]
    rfl
  · simp only [bOff, forwardOff, gamma, FieldMacToECMac.garbleRow, Biquadratic.garbleZ]
    ring
  · show kAt u (forwardOff ctx u c) d (.inr .rowX_y10) (ctx.rows d).x.y - c.mask (d, .inr .rowX_y10) = _
    rw [kAt_forward ctx u c d (.inr .rowX_y10) (ctx.rows d).x.y rfl]
    rfl
  · show kAt u (forwardOff ctx u c) d (.inr .rowY_y8) (c.r4 d + (ctx.rows d).y.ySquared) -
      c.mask (d, .inr .rowY_y8) = _
    rw [kAt_forward ctx u c d (.inr .rowY_y8) (c.r4 d + (ctx.rows d).y.ySquared) rfl]
    rfl
  · simp only [bOff, forwardOff, gamma, FieldMacToECMac.garbleRow, Biquadratic.garbleY, rowRand, Coins.r4]
    ring

theorem slopeOff_forward (e : Enc) : slopeOff ctx u (forwardOff ctx u c) e = slope ctx c e := by
  rcases e with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y))
  · simp only [slopeOff, bOff_forward]; rfl
  · rcases x with _ | _ | _
    · simp only [slopeOff, r1Off_forward]; rfl
    · simp only [slopeOff, kx3Off_forward]; rfl
    · simp only [slopeOff, kx5Off_forward]; rfl
  · simp only [slopeOff, bOff_forward]; rfl
  · rcases y with _ | _
    · simp only [slopeOff, r2Off_forward]; rfl
    · simp only [slopeOff, ky4Off_forward]; rfl

theorem padsOff_forward : padsOff ctx u (forwardOff ctx u c) = c.pads := by
  funext i ρ e
  show fullPad u (join ctx c) (coldOf u c) (slopeOff ctx u (forwardOff ctx u c) e) e i ρ = _
  rw [slopeOff_forward, fullPad_join]

theorem masksOff_forward : masksOff ctx u (forwardOff ctx u c) = c.mask := by
  funext r
  unfold masksOff
  rw [padsOff_forward, bOff_forward]
  show offsetF c (rowEnc r) - rowOffset c r = c.mask r
  unfold rowOffset
  rw [sub_sub_cancel]

theorem bridgeOff_forward : bridgeOff u (forwardOff ctx u c) = c.bridge := by
  unfold bridgeOff
  rw [kx7Off_forward, ky6Off_forward]
  show (curveTable c).1 - 3 * c.curveMask + curveK c (.inr .y6) + curveK c (.inl .x7) = c.bridge
  unfold curveTable CurveMembership.garble
  ring

theorem backwardOff_forwardOff : backwardOff ctx u (forwardOff ctx u c) = c := by
  obtain ⟨pads, masks, r4, unused, t, mask, r1, r2⟩ := c
  show (padsOff ctx u _, masksOff ctx u _, r4, unused, (bridgeOff u _, mask, r1Off u _, r2Off u _)) =
    (pads, masks, r4, unused, t, mask, r1, r2)
  rw [padsOff_forward, masksOff_forward, bridgeOff_forward, r1Off_forward, r2Off_forward]
  rfl

end Left

section Right

variable (ctx : Context) (u : AffineInput) (out : (Source T × Cold T u) × ResidualOff)

theorem rowOffset_backwardOff (d : Fin 91) (element : Biquadratic.Element) :
    rowOffset (backwardOff ctx u out) (d, element) = bOff ctx u out d element := by
  simp only [rowOffset, backwardOff, masksOff, Coins.mask, offsetF, offset, readout, Coins.pads]
  show padOffset _ - (padOffset _ - _) = _
  rw [sub_sub_cancel]

theorem slope_backwardOff (e : Enc) : slope ctx (backwardOff ctx u out) e = slopeOff ctx u out e := by
  rcases e with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y))
  · simp only [slope, digitSlopes, slopeOff, rowOffset_backwardOff]; rfl
  · rcases x with _ | _ | _
    · rfl
    · simp only [slope, CurveMembership.slopes, slopeOff]; rfl
    · simp only [slope, CurveMembership.slopes, slopeOff]; rfl
  · simp only [slope, digitSlopes, slopeOff, rowOffset_backwardOff]; rfl
  · rcases y with _ | _
    · rfl
    · simp only [slope, CurveMembership.slopes, slopeOff]; rfl

theorem join_backwardOff : join ctx (backwardOff ctx u out) = out.1.1.1 := by
  funext e i
  unfold join
  rw [slope_backwardOff]
  exact join_fullPad u out.1.1.1 out.1.2 _ e i

theorem coldOf_backwardOff : coldOf u (backwardOff ctx u out) = out.1.2 := by
  funext i e ρ
  exact fullPad_cold u out.1.1.1 out.1.2 _ e i ρ

theorem gamma_backwardOff (d : Fin 91) : gamma ctx (backwardOff ctx u out) d = out.1.1.2.1 d := by
  unfold gamma
  simp only [rowOffset_backwardOff]
  show FieldMacToECMac.garbleRow _ _ (bOff ctx u out d) = _
  simp only [FieldMacToECMac.garbleRow, Biquadratic.garbleX, Biquadratic.garbleY, Biquadratic.garbleZ, bOff,
    rowRand, backwardOff, Coins.r4, Coins.unused]
  obtain ⟨xC0, yC0, yC4, zC0⟩ := out.1.1.2.1 d
  simp only [RowGamma.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem curveTable_backwardOff : curveTable (backwardOff ctx u out) = out.1.1.2.2 := by
  unfold curveTable CurveMembership.garble
  show (3 * out.2.2.2.2.1 + bridgeOff u out - ky6Off u out - kx7Off u out, out.2.2.2.2.1 + r1Off u out,
    -out.2.2.2.2.1 + r2Off u out) = out.1.1.2.2
  unfold bridgeOff r1Off r2Off
  obtain ⟨c0, c1, c2⟩ := out.1.1.2.2
  simp only [Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem residual_backwardOff :
    (fun d k => (backwardOff ctx u out).mask (d, residualElem k)) = out.2.1 := by
  funext d k
  show masksOff ctx u out (d, residualElem k) = _
  unfold masksOff
  fin_cases k
  · show padOffset (fullPad u out.1.1.1 out.1.2 (ctx.rows d).x.xSquared (rowEnc (d, .inl .rowX_x7))) -
      (padOffset (fullPad u out.1.1.1 out.1.2 (ctx.rows d).x.xSquared (rowEnc (d, .inl .rowX_x7))) -
        out.2.1 d 0) = out.2.1 d 0
    rw [sub_sub_cancel]
  · show padOffset (fullPad u out.1.1.1 out.1.2 (ctx.rows d).x.y (rowEnc (d, .inr .rowX_y10))) -
      (padOffset (fullPad u out.1.1.1 out.1.2 (ctx.rows d).x.y (rowEnc (d, .inr .rowX_y10))) -
        out.2.1 d 1) = out.2.1 d 1
    rw [sub_sub_cancel]
  · show padOffset (fullPad u out.1.1.1 out.1.2 (ctx.rows d).y.xy (rowEnc (d, .inl .rowY_x9))) -
      (padOffset (fullPad u out.1.1.1 out.1.2 (ctx.rows d).y.xy (rowEnc (d, .inl .rowY_x9))) -
        out.2.1 d 2) = out.2.1 d 2
    rw [sub_sub_cancel]
  · show padOffset (fullPad u out.1.1.1 out.1.2 (out.2.2.1 d + (ctx.rows d).y.ySquared) (rowEnc (d, .inr .rowY_y8))) -
      (padOffset (fullPad u out.1.1.1 out.1.2 (out.2.2.1 d + (ctx.rows d).y.ySquared) (rowEnc (d, .inr .rowY_y8))) -
        out.2.1 d 3) = out.2.1 d 3
    rw [sub_sub_cancel]

theorem forwardOff_backwardOff : forwardOff ctx u (backwardOff ctx u out) = out := by
  have joinEq := join_backwardOff ctx u out
  have coldEq := coldOf_backwardOff ctx u out
  have gammaEq : gamma ctx (backwardOff ctx u out) = out.1.1.2.1 := funext (gamma_backwardOff ctx u out)
  have tableEq := curveTable_backwardOff ctx u out
  have residEq := residual_backwardOff ctx u out
  show (((join ctx _, gamma ctx _, curveTable _), coldOf u _),
    (fun d k => (backwardOff ctx u out).mask (d, residualElem k), out.2.2.1, (out.2.2.2.1, out.2.2.2.2))) = out
  rw [joinEq, gammaEq, tableEq, coldEq, residEq]

end Right

end Off

open Off

variable (T : CrtTable) [∀ i, NeZero (T.modulus i)]

/-- **(P45-off.a)** The bijection off the curve (no division; every input). -/
def bmrEquivOff (ctx : Context) (u : AffineInput) : Coins T ≃ (Source T × Cold T u) × ResidualOff where
  toFun := forwardOff ctx u
  invFun := backwardOff ctx u
  left_inv c := backwardOff_forwardOff ctx u c
  right_inv out := forwardOff_backwardOff ctx u out

/-- **(P45-off.b)** Off the wrap event the real outputs off the curve are the ideal outputs of the image. -/
theorem bmr_real_eq_ideal_off (ctx : Context) (u : AffineInput) (c : Coins T) (noWrap : ∀ e, hint c e = false) :
    realOutOff ctx u c = idealOutOff u (bmrEquivOff T ctx u c).1 := by
  unfold realOutOff idealOutOff
  simp only [bmrEquivOff, Equiv.coe_fn_mk, forwardOff]
  exact Prod.ext (Prod.ext rfl (funext noWrap)) rfl

/-- **The exact core off the curve.** -/
theorem bmr_core_off (ctx : Context) (u : AffineInput) :
    (PMF.uniformOfFintype (Coins T)).map (fun c => idealOutOff u (bmrEquivOff T ctx u c).1) =
      (PMF.uniformOfFintype (Source T × Cold T u)).map (idealOutOff u) := by
  have factor : (fun c => idealOutOff u (bmrEquivOff T ctx u c).1) =
      idealOutOff u ∘ Prod.fst ∘ bmrEquivOff T ctx u := rfl
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, uniform_map_equiv, uniform_map_fst]

end

end Kriterion.CRT.Privacy.BMR
