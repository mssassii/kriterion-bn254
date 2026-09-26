/-
**P45.a, P45.b and the core: the joint body-mask-row bijection** (rows T2, T3).

`bmrEquiv` is written with its forward map and its inverse explicitly:

* forward: the residue joins, the row constants, the curve constants, the cold pad entries, and for every
  non-collector the **ideal shear** `π'_e = v⁰_e − u_e` (the evaluator's hint-free value minus the row value), with
  the unused randomizers and the curve mask as the residual;
* inverse: `v⁰` from the joins and the cold entries; the non-collector row values `u = v⁰ − π'`; per digit the row
  offsets and `r4` by `rowEquiv.symm`; the curve randomizers from the curve constants; the slopes (row encodings
  from the offsets and `r4`, curve encodings in the chain `x3 → x5 → x7`, `y4 → y6`); every hot pad entry from its
  join, its cold entries and its slope; the masks `π_e = (O_e : F_p) − b_e`; and `t` from the first curve constant.

The forward map uses `π'`, not the real mask: on the wrap event the real mask is `v⁰ − u + M` and the real map is
not a bijection, while `π'` gives one for all coins; off the wrap event `π' = π` (`noWrap_delivered`), which is
`bmr_real_eq_ideal`.
-/

import Proof.Privacy.CRT.Core.BodyMaskRowParts
import Proof.Privacy.CRT.Core.WrapMass

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

namespace Joint

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- A sum over the whole group is the sum over the cold slots plus the hot slot. -/
theorem sum_split {M : Type*} [AddCommMonoid M] {m : ℕ} [NeZero m] (h : ZMod m) (f : ZMod m → M) :
    ∑ ρ : {ρ : ZMod m // ρ ≠ h}, f ρ.1 + f h = ∑ ρ, f ρ := by
  rw [← Finset.sum_subtype (Finset.univ.erase h) (fun ρ => by simp) f, add_comm,
    Finset.add_sum_erase _ _ (Finset.mem_univ h)]

/-- The pads of one encoding with the hot entry solved from its join, its cold entries and its slope. -/
def fullPad (u : AffineInput) (J : Joins T) (cold : Cold T u) (a : BaseField) (e : Enc) :
    (i : Fin T.count) → ZMod (T.modulus i) → ZMod (T.modulus i) := fun i ρ =>
  if h : ρ = hotRes T u e i then
    J e i - (∑ σ : {σ : ZMod (T.modulus i) // σ ≠ hotRes T u e i}, cold i e σ) - ((a.val : ℕ) : ZMod (T.modulus i))
  else cold i e ⟨ρ, h⟩

/-- The field offset `(O : F_p)` of one encoding's pads. -/
def padOffset (pad : (i : Fin T.count) → ZMod (T.modulus i) → ZMod (T.modulus i)) : BaseField :=
  ((T.crt fun i => (∑ ρ : ZMod (T.modulus i), ρ * pad i ρ).val : ℕ) : BaseField)

theorem padOffset_pads (c : Coins T) (e : Enc) : padOffset (fun i ρ => c.pads i ρ e) = offsetF c e := rfl

/-- The pads of the coins are the full pads of their joins, cold entries and slopes. -/
theorem fullPad_join (ctx : Context) (u : AffineInput) (c : Coins T) (e : Enc) :
    fullPad u (join ctx c) (coldOf u c) (slope ctx c e) e = fun i ρ => c.pads i ρ e := by
  funext i ρ
  unfold fullPad
  split_ifs with h
  · subst h
    have := sum_split (hotRes T u e i) fun ρ => c.pads i ρ e
    unfold join coldOf
    rw [← this]
    ring
  · rfl

/-- The joins of full pads are the joins. -/
theorem join_fullPad (u : AffineInput) (J : Joins T) (cold : Cold T u) (a : BaseField) (e : Enc)
    (i : Fin T.count) :
    ∑ ρ, fullPad u J cold a e i ρ + ((a.val : ℕ) : ZMod (T.modulus i)) = J e i := by
  rw [← sum_split (hotRes T u e i)]
  have hot : fullPad u J cold a e i (hotRes T u e i) =
      J e i - (∑ σ : {σ : ZMod (T.modulus i) // σ ≠ hotRes T u e i}, cold i e σ) -
        ((a.val : ℕ) : ZMod (T.modulus i)) := by
    unfold fullPad
    exact dif_pos rfl
  have coldSum : ∑ ρ : {ρ : ZMod (T.modulus i) // ρ ≠ hotRes T u e i}, fullPad u J cold a e i ρ.1 =
      ∑ σ, cold i e σ :=
    Finset.sum_congr rfl fun ρ _ => by unfold fullPad; rw [dif_neg ρ.2]
  rw [hot, coldSum]
  ring

/-- The cold entries of full pads are the cold entries. -/
theorem fullPad_cold (u : AffineInput) (J : Joins T) (cold : Cold T u) (a : BaseField) (e : Enc)
    (i : Fin T.count) (ρ : {ρ : ZMod (T.modulus i) // ρ ≠ hotRes T u e i}) :
    fullPad u J cold a e i ρ.1 = cold i e ρ := by
  unfold fullPad
  rw [dif_neg ρ.2]

/-! ### The forward map -/

/-- The real row value `u_e = a_e x + b_e` of a row encoding. -/
def rowValue (ctx : Context) (u : AffineInput) (c : Coins T) (r : RowEnc) : BaseField :=
  let rand := rowRand (c.r4 r.1) (c.unused r.1)
  Biquadratic.delivered (ctx.rows r.1) rand.1 rand.2.1 rand.2.2 (fun element => rowOffset c (r.1, element)) u r.2

/-- The forward map: the published cells, the cold entries, the ideal shear of the non-collector masks, and the
residual. -/
def forward (ctx : Context) (u : AffineInput) (c : Coins T) : (Source T × Visible T u) × Residual :=
  (((join ctx c, gamma ctx c, curveTable c),
      (coldOf u c, fun r => deliveredIdeal u (join ctx c) (coldOf u c) (rowEnc r.1) - rowValue ctx u c r.1)),
    (c.unused, c.2.2.2.2.2.1))

/-! ### The inverse -/

section Inverse

variable [FieldCertificate] (ctx : Context) (u : AffineInput) (good : u.x ≠ 0 ∧ u.y ≠ 0)
  (out : (Source T × Visible T u) × Residual)

/-- The non-collector row values `u = v⁰ − π'` of a digit. -/
def ncValues (d : Fin 91) : NonCollectorElem → BaseField := fun element =>
  deliveredIdeal u out.1.1.1 out.1.2.1 (rowEnc (d, element.1)) - out.1.2.2 ⟨(d, element.1), element.2⟩

/-- A digit's row offsets and `r4`, by the cut-row bijection. -/
def recovered (d : Fin 91) : Biquadratic.Values × BaseField :=
  (rowEquiv (ctx.rows d) (ctx.rho d) u good).symm (out.1.1.2.1 d, ncValues u out d)

/-- The curve randomizers `r1 = c1 − mask`, `r2 = c2 + mask`. -/
def r1Inv : BaseField := out.1.1.2.2.2.1 - out.2.2.1
def r2Inv : BaseField := out.1.1.2.2.2.2 + out.2.2.1

/-- The curve offsets in the chain order. -/
def kx3 : BaseField := padOffset (fullPad u out.1.1.1 out.1.2.1 (-r1Inv u out) (curveEnc (.inl .x3)))
def kx5 : BaseField := padOffset (fullPad u out.1.1.1 out.1.2.1 (-kx3 u out) (curveEnc (.inl .x5)))
def kx7 : BaseField := padOffset (fullPad u out.1.1.1 out.1.2.1 (-kx5 u out) (curveEnc (.inl .x7)))
def ky4 : BaseField := padOffset (fullPad u out.1.1.1 out.1.2.1 (-r2Inv u out) (curveEnc (.inr .y4)))
def ky6 : BaseField := padOffset (fullPad u out.1.1.1 out.1.2.1 (-ky4 u out) (curveEnc (.inr .y6)))

/-- The slope of every encoding, recovered. -/
def slopeInv : Enc → BaseField
  | .inl (.inl (d, x)) =>
    let br := recovered ctx u good out d
    let rand := rowRand br.2 (out.2.1 d)
    Biquadratic.slopes (ctx.rows d) rand.1 rand.2.1 rand.2.2 br.1 (.inl x)
  | .inr (.inl (d, y)) =>
    let br := recovered ctx u good out d
    let rand := rowRand br.2 (out.2.1 d)
    Biquadratic.slopes (ctx.rows d) rand.1 rand.2.1 rand.2.2 br.1 (.inr y)
  | .inl (.inr .x3) => -r1Inv u out
  | .inl (.inr .x5) => -kx3 u out
  | .inl (.inr .x7) => -kx5 u out
  | .inr (.inr .y4) => -r2Inv u out
  | .inr (.inr .y6) => -ky4 u out

/-- The recovered pads. -/
def padsInv : Pads T := fun i ρ e => fullPad u out.1.1.1 out.1.2.1 (slopeInv ctx u good out e) e i ρ

/-- The recovered masks `π_e = (O_e : F_p) − b_e`. -/
def masksInv : RowEnc → BaseField := fun r =>
  padOffset (fun i ρ => padsInv ctx u good out i ρ (rowEnc r)) - (recovered ctx u good out r.1).1 r.2

/-- The recovered `t` from the first curve constant. -/
def bridgeInv : BaseField := out.1.1.2.2.1 - 3 * out.2.2.1 + ky6 u out + kx7 u out

/-- **The inverse.** -/
def backward : Coins T :=
  (padsInv ctx u good out, masksInv ctx u good out, fun d => (recovered ctx u good out d).2, out.2.1,
    (bridgeInv u out, out.2.2, r1Inv u out, r2Inv u out))

/-! ### The left inverse -/

section Left

variable (c : Coins T)

theorem ncValues_forward (d : Fin 91) :
    ncValues u (forward ctx u c) d = fun element => rowValue ctx u c (d, element.1) := by
  funext element
  simp only [ncValues, forward, sub_sub_cancel]

theorem recovered_forward (d : Fin 91) :
    recovered ctx u good (forward ctx u c) d = (fun element => rowOffset c (d, element), c.r4 d) := by
  have apply := rowEquiv_apply (ctx.rows d) (ctx.rho d) u good (fun element => rowOffset c (d, element))
    (c.r4 d) (c.unused d)
  unfold recovered
  rw [ncValues_forward]
  rw [Equiv.symm_apply_eq, apply]
  rfl

theorem r1Inv_forward : r1Inv u (forward ctx u c) = c.r1 := by
  simp only [r1Inv, forward, curveTable, CurveMembership.garble, Coins.curveMask, Coins.r1]
  ring

theorem r2Inv_forward : r2Inv u (forward ctx u c) = c.r2 := by
  simp only [r2Inv, forward, curveTable, CurveMembership.garble, Coins.curveMask, Coins.r2]
  ring

/-- The full pads of an encoding at a slope equal to its real slope are its pads. -/
theorem padOffset_forward (e : Enc) (a : BaseField) (ha : a = slope ctx c e) :
    padOffset (fullPad u (forward ctx u c).1.1.1 (forward ctx u c).1.2.1 a e) = offsetF c e := by
  subst ha
  show padOffset (fullPad u (join ctx c) (coldOf u c) (slope ctx c e) e) = _
  rw [fullPad_join]
  rfl

theorem kx3_forward : kx3 u (forward ctx u c) = curveK c (.inl .x3) :=
  padOffset_forward ctx u c _ _ (by rw [r1Inv_forward]; rfl)

theorem kx5_forward : kx5 u (forward ctx u c) = curveK c (.inl .x5) :=
  padOffset_forward ctx u c _ _ (by rw [kx3_forward]; rfl)

theorem kx7_forward : kx7 u (forward ctx u c) = curveK c (.inl .x7) :=
  padOffset_forward ctx u c _ _ (by rw [kx5_forward]; rfl)

theorem ky4_forward : ky4 u (forward ctx u c) = curveK c (.inr .y4) :=
  padOffset_forward ctx u c _ _ (by rw [r2Inv_forward]; rfl)

theorem ky6_forward : ky6 u (forward ctx u c) = curveK c (.inr .y6) :=
  padOffset_forward ctx u c _ _ (by rw [ky4_forward]; rfl)

theorem slopeInv_forward (e : Enc) : slopeInv ctx u good (forward ctx u c) e = slope ctx c e := by
  rcases e with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y))
  · simp only [slopeInv, recovered_forward]; rfl
  · rcases x with _ | _ | _
    · simp only [slopeInv, r1Inv_forward]; rfl
    · simp only [slopeInv, kx3_forward]; rfl
    · simp only [slopeInv, kx5_forward]; rfl
  · simp only [slopeInv, recovered_forward]; rfl
  · rcases y with _ | _
    · simp only [slopeInv, r2Inv_forward]; rfl
    · simp only [slopeInv, ky4_forward]; rfl

theorem padsInv_forward : padsInv ctx u good (forward ctx u c) = c.pads := by
  funext i ρ e
  show fullPad u (join ctx c) (coldOf u c) (slopeInv ctx u good (forward ctx u c) e) e i ρ = _
  rw [slopeInv_forward, fullPad_join]

theorem masksInv_forward : masksInv ctx u good (forward ctx u c) = c.mask := by
  funext r
  unfold masksInv
  rw [padsInv_forward, recovered_forward]
  show offsetF c (rowEnc r) - rowOffset c r = c.mask r
  unfold rowOffset
  rw [sub_sub_cancel]

theorem bridgeInv_forward : bridgeInv u (forward ctx u c) = c.bridge := by
  unfold bridgeInv
  rw [kx7_forward, ky6_forward]
  show (curveTable c).1 - 3 * c.curveMask + curveK c (.inr .y6) + curveK c (.inl .x7) = c.bridge
  unfold curveTable CurveMembership.garble
  ring

theorem backward_forward : backward ctx u good (forward ctx u c) = c := by
  obtain ⟨pads, masks, r4, unused, t, mask, r1, r2⟩ := c
  show (padsInv ctx u good _, masksInv ctx u good _, fun d => (recovered ctx u good _ d).2, unused,
    (bridgeInv u _, mask, r1Inv u _, r2Inv u _)) = (pads, masks, r4, unused, t, mask, r1, r2)
  rw [padsInv_forward, masksInv_forward, bridgeInv_forward, r1Inv_forward, r2Inv_forward]
  have r4Eq : (fun d => (recovered ctx u good (forward ctx u (pads, masks, r4, unused, t, mask, r1, r2)) d).2) = r4 := by
    funext d
    rw [recovered_forward]
    rfl
  rw [r4Eq]
  rfl

end Left

/-! ### The right inverse -/

section Right

/-- The recovered coins' row offsets are the recovered offsets. -/
theorem rowOffset_backward (d : Fin 91) (element : Biquadratic.Element) :
    rowOffset (backward ctx u good out) (d, element) = (recovered ctx u good out d).1 element := by
  simp only [rowOffset, backward, masksInv, Coins.mask, offsetF, offset, readout, Coins.pads]
  show padOffset _ - (padOffset _ - _) = _
  rw [sub_sub_cancel]

theorem curveK_backward_x3 : curveK (backward ctx u good out) (.inl .x3) = kx3 u out := rfl
theorem curveK_backward_x5 : curveK (backward ctx u good out) (.inl .x5) = kx5 u out := rfl
theorem curveK_backward_x7 : curveK (backward ctx u good out) (.inl .x7) = kx7 u out := rfl
theorem curveK_backward_y4 : curveK (backward ctx u good out) (.inr .y4) = ky4 u out := rfl
theorem curveK_backward_y6 : curveK (backward ctx u good out) (.inr .y6) = ky6 u out := rfl

theorem slope_backward (e : Enc) : slope ctx (backward ctx u good out) e = slopeInv ctx u good out e := by
  rcases e with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y))
  · simp only [slope, digitSlopes, slopeInv, rowOffset_backward]; rfl
  · rcases x with _ | _ | _
    · rfl
    · simp only [slope, CurveMembership.slopes, slopeInv, curveK_backward_x3]
    · simp only [slope, CurveMembership.slopes, slopeInv, curveK_backward_x5]
  · simp only [slope, digitSlopes, slopeInv, rowOffset_backward]; rfl
  · rcases y with _ | _
    · rfl
    · simp only [slope, CurveMembership.slopes, slopeInv, curveK_backward_y4]

theorem join_backward : join ctx (backward ctx u good out) = out.1.1.1 := by
  funext e i
  unfold join
  rw [slope_backward]
  exact join_fullPad u out.1.1.1 out.1.2.1 _ e i

theorem coldOf_backward : coldOf u (backward ctx u good out) = out.1.2.1 := by
  funext i e ρ
  exact fullPad_cold u out.1.1.1 out.1.2.1 _ e i ρ

theorem rowEquiv_recovered (d : Fin 91) :
    let br := recovered ctx u good out d
    let rand := rowRand br.2 (out.2.1 d)
    (FieldMacToECMac.garbleRow (ctx.rows d) ⟨ctx.rho d, rand.1, rand.2.1, rand.2.2⟩ br.1,
      fun element : NonCollectorElem =>
        Biquadratic.delivered (ctx.rows d) rand.1 rand.2.1 rand.2.2 br.1 u element.1) =
      (out.1.1.2.1 d, ncValues u out d) := by
  intro br rand
  rw [← rowEquiv_apply (ctx.rows d) (ctx.rho d) u good br.1 br.2 (out.2.1 d)]
  exact Equiv.apply_symm_apply _ _

theorem gamma_backward (d : Fin 91) : gamma ctx (backward ctx u good out) d = out.1.1.2.1 d := by
  have := congrArg Prod.fst (rowEquiv_recovered ctx u good out d)
  simp only at this
  rw [← this]
  unfold gamma
  simp only [rowOffset_backward]
  rfl

theorem curveTable_backward : curveTable (backward ctx u good out) = out.1.1.2.2 := by
  unfold curveTable CurveMembership.garble
  rw [curveK_backward_y6, curveK_backward_x7]
  show (3 * out.2.2.1 + bridgeInv u out - ky6 u out - kx7 u out, out.2.2.1 + r1Inv u out,
    -out.2.2.1 + r2Inv u out) = out.1.1.2.2
  unfold bridgeInv r1Inv r2Inv
  obtain ⟨c0, c1, c2⟩ := out.1.1.2.2
  simp only [Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem shear_backward (r : NonCollector) :
    deliveredIdeal u (join ctx (backward ctx u good out)) (coldOf u (backward ctx u good out)) (rowEnc r.1) -
      rowValue ctx u (backward ctx u good out) r.1 = out.1.2.2 r := by
  obtain ⟨⟨d, element⟩, notCollector⟩ := r
  have := congrFun (congrArg Prod.snd (rowEquiv_recovered ctx u good out d)) ⟨element, notCollector⟩
  simp only at this
  rw [join_backward, coldOf_backward]
  have rv : rowValue ctx u (backward ctx u good out) (d, element) = ncValues u out d ⟨element, notCollector⟩ := by
    rw [← this]
    unfold rowValue
    simp only [rowOffset_backward]
    rfl
  rw [rv]
  simp only [ncValues, sub_sub_cancel]

theorem forward_backward : forward ctx u (backward ctx u good out) = out := by
  have joinEq := join_backward ctx u good out
  have coldEq := coldOf_backward ctx u good out
  have gammaEq : gamma ctx (backward ctx u good out) = out.1.1.2.1 := funext (gamma_backward ctx u good out)
  have tableEq := curveTable_backward ctx u good out
  have shearEq : (fun r : NonCollector => deliveredIdeal u (join ctx (backward ctx u good out))
      (coldOf u (backward ctx u good out)) (rowEnc r.1) - rowValue ctx u (backward ctx u good out) r.1) =
      out.1.2.2 := funext (shear_backward ctx u good out)
  show (((join ctx _, gamma ctx _, curveTable _), (coldOf u _, fun r : NonCollector =>
      deliveredIdeal u (join ctx _) (coldOf u _) (rowEnc r.1) - rowValue ctx u _ r.1)), (out.2.1, out.2.2)) = out
  rw [shearEq, joinEq, gammaEq, tableEq, coldEq]

end Right

end Inverse

end Joint

open Joint

variable (T : CrtTable) [∀ i, NeZero (T.modulus i)] [FieldCertificate]

/-- **(P45.a) Formulation 1 of F2, on the curve.** -/
def bmrEquiv (ctx : Context) (u : AffineInput) (onCurve : OnCurve u) :
    Coins T ≃ (Source T × Visible T u) × Residual where
  toFun := forward ctx u
  invFun := backward ctx u ⟨Security.Phase3.onCurve_x_ne_zero u onCurve, Security.Phase3.onCurve_y_ne_zero u onCurve⟩
  left_inv c := backward_forward ctx u _ c
  right_inv out := forward_backward ctx u _ out

/-- **The exact core of the layer** (`CoreUntilBad`'s `realCore = simCore`): the ideal outputs at the image of
uniform coins have the law of the ideal outputs at uniform cells. -/
theorem bmr_core (ctx : Context) (u : AffineInput) (onCurve : OnCurve u) :
    (PMF.uniformOfFintype (Coins T)).map (fun c => idealOut ctx u (bmrEquiv T ctx u onCurve c).1) =
      (PMF.uniformOfFintype (Source T × Visible T u)).map (idealOut ctx u) := by
  have factor : (fun c => idealOut ctx u (bmrEquiv T ctx u onCurve c).1) =
      idealOut ctx u ∘ Prod.fst ∘ bmrEquiv T ctx u onCurve := rfl
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, uniform_map_equiv, uniform_map_fst]

/-- **(P45.b)** Off the wrap event the real outputs are the ideal outputs of the image. -/
theorem bmr_real_eq_ideal (facts : TableFacts T) (ctx : Context) (u : AffineInput) (onCurve : OnCurve u)
    (c : Coins T) (noWrap : ∀ e, hint c e = false) :
    realOut ctx u c = idealOut ctx u (bmrEquiv T ctx u onCurve c).1 := by
  -- the evaluator's hint-free value is `a_e v + (O_e : F_p)` at every encoding
  have v0 : ∀ e, deliveredIdeal u (join ctx c) (coldOf u c) e =
      slope ctx c e * (coordValue u (coordOf e) : BaseField) + offsetF c e :=
    fun e => (noWrap_delivered facts ctx u c e (noWrap e)).2
  have coordX : ((coordValue u 0 : ℕ) : BaseField) = u.x := by simp [coordValue]
  have coordY : ((coordValue u 1 : ℕ) : BaseField) = u.y := by simp [coordValue]
  -- the real mask of a row encoding is `v⁰ − u`
  have rowMask : ∀ r : RowEnc, deliveredIdeal u (join ctx c) (coldOf u c) (rowEnc r) - rowValue ctx u c r = c.mask r := by
    rintro ⟨d, (x | y)⟩
    · rw [v0]
      simp only [rowValue, Biquadratic.delivered, Biquadratic.coordValue, rowEnc, slope, coordOf, coordX, digitSlopes,
        rowOffset, offsetF]
      ring
    · rw [v0]
      simp only [rowValue, Biquadratic.delivered, Biquadratic.coordValue, rowEnc, slope, coordOf, coordY, digitSlopes,
        rowOffset, offsetF]
      ring
  -- the ideal row values of a digit are the non-collector delivered values
  have rowValues : ∀ d : Fin 91, (fun element : Biquadratic.Element =>
      if h : IsCollector element then (0 : BaseField) else
        deliveredIdeal u (join ctx c) (coldOf u c) (rowEnc (d, element)) -
          (deliveredIdeal u (join ctx c) (coldOf u c) (rowEnc (d, element)) - rowValue ctx u c (d, element))) =
      nonCollectorValues (let rand := rowRand (c.r4 d) (c.unused d)
        Biquadratic.delivered (ctx.rows d) rand.1 rand.2.1 rand.2.2 (fun element => rowOffset c (d, element)) u) := by
    intro d
    funext element
    unfold nonCollectorValues
    split_ifs <;> simp [rowValue]
  unfold realOut idealOut
  simp only [bmrEquiv, Equiv.coe_fn_mk, forward]
  refine Prod.ext (Prod.ext rfl (funext noWrap)) (Prod.ext (Prod.ext rfl ?_) (Prod.ext ?_ ?_))
  · funext r
    exact (rowMask r.1).symm
  · funext r
    obtain ⟨⟨d, element⟩, collector⟩ := r
    simp only
    rw [rowValues d]
    have solve := collector_eq_solve (ctx.rows d) (ctx.rho d) (c.r4 d) (c.unused d)
      (fun element => rowOffset c (d, element)) u onCurve element collector
    simp only at solve
    have gammaEq : gamma ctx c d = FieldMacToECMac.garbleRow (ctx.rows d)
        ⟨ctx.rho d, (rowRand (c.r4 d) (c.unused d)).1, (rowRand (c.r4 d) (c.unused d)).2.1,
          (rowRand (c.r4 d) (c.unused d)).2.2⟩ (fun element => rowOffset c (d, element)) := rfl
    rw [gammaEq, ← solve]
    exact (rowMask (d, element)).symm
  · have curveValues : (fun element => deliveredIdeal u (join ctx c) (coldOf u c) (curveEnc element)) =
        CurveMembership.delivered c.r1 c.r2 (curveK c) u := by
      funext element
      rw [v0]
      rcases element with x | y
      · simp only [CurveMembership.delivered, CurveMembership.coordValue, curveEnc, slope, coordOf, coordX, curveK]
      · simp only [CurveMembership.delivered, CurveMembership.coordValue, curveEnc, slope, coordOf, coordY, curveK]
    rw [curveValues]
    exact (CurveMembership.evaluateEncodedOnCurve _ _ _ _ _ u onCurve).symm

end

end Kriterion.CRT.Privacy.BMR
