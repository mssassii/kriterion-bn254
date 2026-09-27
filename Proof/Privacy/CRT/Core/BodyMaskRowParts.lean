/-
**The building blocks of P45** (rows P45.2 to P45.4).

* `collector_eq_solve` (P45.2, proved): on the curve, a collector's row-level value is the route-M solve at the true
  rows from the published constants and the other elements' values (the cut rows' algebra; xinshu's
  `designated_eq_solve` without the switch factor).
* `rowEquiv` (P45.2): a digit's seven row offsets against its three published constants and its four
  non-collector row values (the cut-row form of xinshu's `digitEquiv`, `JointExactness.lean:731`); the sign row's
  `(y8, y10)` block has determinant `(3 - y²) / 3`, never zero because `3` is not a square.
* `curveEquivCrt` (P45.3): `(t, r1, r2)` against the curve constants, the curve mask fixed.
* `noWrap_delivered` (P45.4): off the wrap event the evaluator delivers `a_e v + (O_e : F_p)`.
-/

import Proof.Privacy.CRT.Core.BodyMaskRow
import Proof.Privacy.Phase3.OnCurveNonzero
import Proof.Correctness.CRT.Arith

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

/-- The row-level values a digit's rows see: every element's delivered value, collectors set to `0` (the form the
solve reads). -/
def nonCollectorValues (values : Biquadratic.Values) : Biquadratic.Values := fun element =>
  if IsCollector element then 0 else values element

/-- **P45.2, the collector solve.** On the curve, every collector's delivered value is the route-M solve at the
true rows. -/
theorem collector_eq_solve [FieldCertificate] (rows : Coordinates.Rows) (r4 : BaseField)
    (unused : Fin 7 → BaseField) (offsets : Biquadratic.Values) (u : AffineInput) (onCurve : OnCurve u)
    (element : Biquadratic.Element) (collector : IsCollector element) :
    let rand := rowRand r4 unused
    Biquadratic.delivered rows rand.1 rand.2.1 rand.2.2 offsets u element =
      collectorSolve (rowTarget rows u) (FieldMacToECMac.garbleRow rows offsets) u
        (nonCollectorValues (Biquadratic.delivered rows rand.1 rand.2.1 rand.2.2 offsets u)) element := by
  intro rand
  have xRow := Biquadratic.evaluateEncodedX rows rand.1 rand.2.1 rand.2.2 offsets u
  have yRow := Biquadratic.evaluateEncodedY rows rand.1 rand.2.1 rand.2.2 offsets u onCurve
  have zRow := Biquadratic.evaluateEncodedZ rows rand.1 rand.2.1 rand.2.2 offsets u
  have xNe := Security.Phase3.onCurve_x_ne_zero u onCurve
  simp only [Biquadratic.evaluateX, Biquadratic.garbleX] at xRow
  simp only [Biquadratic.evaluateY, Biquadratic.garbleY] at yRow
  simp only [Biquadratic.evaluateZ, Biquadratic.garbleZ] at zRow
  rcases collector with rfl | rfl | rfl
  · simp only [collectorSolve, rowTarget, FieldMacToECMac.garbleRow, nonCollectorValues, IsCollector,
      Biquadratic.garbleX, Sum.inl.injEq, reduceCtorEq, or_self, or_false, false_or, if_false]
    linear_combination xRow
  · simp only [collectorSolve, rowTarget, FieldMacToECMac.garbleRow, nonCollectorValues, IsCollector,
      Biquadratic.garbleY, Sum.inl.injEq, reduceCtorEq, or_self, or_false, false_or, if_false]
    field_simp
    linear_combination yRow
  · simp only [collectorSolve, rowTarget, FieldMacToECMac.garbleRow, nonCollectorValues, IsCollector,
      Biquadratic.garbleZ, Sum.inl.injEq, reduceCtorEq, or_self, or_false, false_or, if_false]
    linear_combination zRow

/-- The four non-collector elements. -/
abbrev NonCollectorElem := {element : Biquadratic.Element // ¬ IsCollector element}

/-- The four non-collector elements, named. -/
def ncXx7 : NonCollectorElem := ⟨.inl .rowX_x7, by simp [IsCollector]⟩
def ncXy10 : NonCollectorElem := ⟨.inr .rowX_y10, by simp [IsCollector]⟩
def ncYy8 : NonCollectorElem := ⟨.inr .rowY_y8, by simp [IsCollector]⟩
def ncYy10 : NonCollectorElem := ⟨.inr .rowY_y10, by simp [IsCollector]⟩

/-- The forward map of the cut-row bijection: the three published constants and the four non-collector delivered
values of a digit, from its seven row offsets (no randomizer enters). -/
def rowForward (rows : Coordinates.Rows) (u : AffineInput) (offsets : Biquadratic.Values) :
    RowGamma × (NonCollectorElem → BaseField) :=
  let rand := rowRand 0 fun _ => 0
  (FieldMacToECMac.garbleRow rows offsets,
    fun element => Biquadratic.delivered rows rand.1 rand.2.1 rand.2.2 offsets u element.1)

/-- The determinant of the sign row's `(y8, y10)` block, `3 - y²`: never zero, since `3` is not a square. -/
def signDet (u : AffineInput) : BaseField := 3 - u.y ^ 2

theorem signDet_ne_zero [FieldCertificate] (u : AffineInput) : signDet u ≠ 0 := by
  intro zero
  exact Security.Phase3.three_not_square ⟨u.y, by unfold signDet at zero; linear_combination zero⟩

/-- `3⁻¹`, as the construction's `inverseThree`. -/
theorem inverseThree_eq [FieldCertificate] : Biquadratic.inverseThree = (3 : BaseField)⁻¹ :=
  (eq_inv_of_mul_eq_one_right Biquadratic.three_mul_inverseThree)

/-- The `y8` offset solved from the two sign-row values (the `(y8, y10)` block's inverse). -/
def solvedY8 (rows : Coordinates.Rows) (u : AffineInput) (v : NonCollectorElem → BaseField) : BaseField :=
  (3 * v ncYy8 - (rows.y.constant - v ncYy10 + rows.y.y * u.y + 3 * rows.y.ySquared) * u.y) * (signDet u)⁻¹

/-- The offsets solved in xinshu's order (`JointExactness.lean:458-480`, cut rows). -/
def solvedK (rows : Coordinates.Rows) (u : AffineInput) (g : RowGamma) (v : NonCollectorElem → BaseField) :
    Biquadratic.Values
  | .inl .rowX_x7 => v ncXx7 - rows.x.xSquared * u.x
  | .inr .rowX_y10 => v ncXy10 - rows.x.y * u.y
  | .inl .rowX_x9 => rows.x.constant - g.xC0 - (v ncXy10 - rows.x.y * u.y)
  | .inl .rowY_cubic => rows.y.xSquared - g.yC4
  | .inr .rowY_y8 => solvedY8 rows u v
  | .inr .rowY_y10 => v ncYy10 - (rows.y.y - solvedY8 rows u v) * u.y
  | .inl .rowZ_x9 => rows.z.constant - g.zC0

section RowEquiv

variable [FieldCertificate]

/-- **P45.2, the cut-row bijection**: the seven row offsets against the three published constants and the four
non-collector row values. It divides only by `3 - y²`, which is never zero, so it holds at every input; the
`good` argument is kept for the callers' uniform signature. -/
def rowEquiv (rows : Coordinates.Rows) (u : AffineInput) (_good : u.x ≠ 0 ∧ u.y ≠ 0) :
    Biquadratic.Values ≃ RowGamma × (NonCollectorElem → BaseField) where
  toFun := rowForward rows u
  invFun out := solvedK rows u out.1 out.2
  left_inv K := by
    have det := signDet_ne_zero u
    have three : (3 : BaseField) ≠ 0 := left_ne_zero_of_mul_eq_one Biquadratic.three_mul_inverseThree
    have y8eq : solvedY8 rows u (rowForward rows u K).2 = K (.inr .rowY_y8) := by
      simp only [solvedY8, rowForward, Biquadratic.delivered, Biquadratic.slopes, Biquadratic.coordValue,
        Biquadratic.signShift, ncYy8, ncYy10, inverseThree_eq]
      unfold signDet at det ⊢
      field_simp
      ring
    funext element
    rcases element with (_ | _ | _ | _) | (_ | _ | _) <;>
      simp only [solvedK, y8eq] <;>
      simp only [rowForward, FieldMacToECMac.garbleRow, Biquadratic.garbleX, Biquadratic.garbleY,
        Biquadratic.garbleZ, Biquadratic.delivered, Biquadratic.slopes, Biquadratic.coordValue, ncXx7,
        ncXy10, ncYy8, ncYy10, rowRand] <;>
      ring
  right_inv out := by
    obtain ⟨g, v⟩ := out
    have det := signDet_ne_zero u
    have three : (3 : BaseField) ≠ 0 := left_ne_zero_of_mul_eq_one Biquadratic.three_mul_inverseThree
    refine Prod.ext ?_ ?_
    · simp only [rowForward, FieldMacToECMac.garbleRow, Biquadratic.garbleX, Biquadratic.garbleY,
        Biquadratic.garbleZ, solvedK]
      cases g
      simp only [RowGamma.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    · funext element
      obtain ⟨element, notCollector⟩ := element
      rcases element with (_ | _ | _ | _) | (_ | _ | _)
      · simp only [rowForward, Biquadratic.delivered, Biquadratic.slopes, Biquadratic.coordValue, solvedK,
          rowRand, ncXx7]
        ring
      · exact (notCollector (Or.inl rfl)).elim
      · exact (notCollector (Or.inr (Or.inl rfl))).elim
      · exact (notCollector (Or.inr (Or.inr rfl))).elim
      · simp only [rowForward, Biquadratic.delivered, Biquadratic.slopes, Biquadratic.coordValue, solvedK,
          rowRand, ncXy10]
        ring
      · simp only [rowForward, Biquadratic.delivered, Biquadratic.slopes, Biquadratic.coordValue, solvedK,
          Biquadratic.signShift, rowRand, ncYy8, ncYy10, solvedY8, inverseThree_eq]
        unfold signDet at det ⊢
        field_simp
        ring
      · simp only [rowForward, Biquadratic.delivered, Biquadratic.slopes, Biquadratic.coordValue, solvedK,
          rowRand, ncYy10]
        ring

/-- The unused randomizers do not enter the delivered values. -/
theorem delivered_rowRand (rows : Coordinates.Rows) (K : Biquadratic.Values) (u : AffineInput)
    (r4 r4' : BaseField) (unused unused' : Fin 7 → BaseField) :
    Biquadratic.delivered rows (rowRand r4 unused).1 (rowRand r4 unused).2.1 (rowRand r4 unused).2.2 K u =
      Biquadratic.delivered rows (rowRand r4' unused').1 (rowRand r4' unused').2.1 (rowRand r4' unused').2.2 K u := by
  funext element
  rcases element with (_ | _ | _ | _) | (_ | _ | _) <;> rfl

/-- `rowEquiv` computes the construction's constants and the delivered values, for any randomizers. -/
theorem rowEquiv_apply (rows : Coordinates.Rows) (u : AffineInput) (good : u.x ≠ 0 ∧ u.y ≠ 0)
    (offsets : Biquadratic.Values) (r4 : BaseField) (unused : Fin 7 → BaseField) :
    let rand := rowRand r4 unused
    rowEquiv rows u good offsets =
      (FieldMacToECMac.garbleRow rows offsets,
        fun element => Biquadratic.delivered rows rand.1 rand.2.1 rand.2.2 offsets u element.1) := by
  intro rand
  show rowForward rows u offsets = _
  refine Prod.ext rfl ?_
  funext element
  exact congrFun (delivered_rowRand rows offsets u 0 r4 (fun _ => 0) unused) element.1

end RowEquiv

/-- **P45.3, the curve bijection**, the curve mask and the curve offsets fixed. -/
def curveEquivCrt (mask : BaseField) (K : CurveMembership.Values) :
    BaseField × BaseField × BaseField ≃ BaseField × BaseField × BaseField where
  toFun coins := CurveMembership.garble coins.1 mask coins.2.1 coins.2.2 K
  invFun table := (table.1 - 3 * mask + K (.inr .y6) + K (.inl .x7), table.2.1 - mask, table.2.2 + mask)
  left_inv coins := by
    obtain ⟨t, r1, r2⟩ := coins
    simp only [CurveMembership.garble, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  right_inv table := by
    obtain ⟨c0, c1, c2⟩ := table
    simp only [CurveMembership.garble, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

/-- `T.crt` is the idempotent combination (the stored idempotents are reduced mod `M`, which changes
nothing mod `M`). -/
theorem tableCrt_eq (T : CrtTable) (r : Fin T.count → ℕ) : T.crt r = SliceC.crt T.modulus r := by
  unfold CrtTable.crt SliceC.crt CrtTable.idempotent SliceC.idem SliceC.crtModulus CrtTable.inverseMod
    CrtTable.product
  simp only []
  rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- The evaluator's residue is the garbler's readout plus the hot residue times the slope (over `ZMod m`). -/
theorem evalResidue_eq (ctx : Context) (u : AffineInput) (c : Coins T) (e : Enc) (i : Fin T.count) :
    evalResidue u (join ctx c) (coldOf u c) e i =
      readout c e i + hotRes T u e i * ((slope ctx c e).val : ZMod (T.modulus i)) := by
  set h := hotRes T u e i
  have split : ∀ f : ZMod (T.modulus i) → ZMod (T.modulus i),
      ∑ ρ : {ρ : ZMod (T.modulus i) // ρ ≠ h}, f ρ.1 + f h = ∑ ρ, f ρ := by
    intro f
    rw [← Finset.sum_subtype (Finset.univ.erase h) (fun ρ => by simp) f, add_comm,
      Finset.add_sum_erase _ _ (Finset.mem_univ h)]
  have pads := split fun ρ => c.pads i ρ e
  have weighted := split fun ρ => ρ * c.pads i ρ e
  unfold evalResidue readout join coldOf
  simp only
  rw [← pads, ← weighted]
  ring

/-- **P45.4.** Off the wrap event the evaluator delivers `a_e v + (O_e : F_p)` (`wrapDecode_crt`
with `T.crt`). -/
theorem noWrap_delivered (facts : TableFacts T) (ctx : Context) (u : AffineInput) (c : Coins T) (e : Enc)
    (noWrap : hint c e = false) :
    delivered u (join ctx c) (hint c) (coldOf u c) e = deliveredIdeal u (join ctx c) (coldOf u c) e ∧
      deliveredIdeal u (join ctx c) (coldOf u c) e =
        slope ctx c e * (coordValue u (coordOf e) : BaseField) + offsetF c e := by
  have first : delivered u (join ctx c) (hint c) (coldOf u c) e = deliveredIdeal u (join ctx c) (coldOf u c) e := by
    unfold delivered deliveredIdeal
    rw [noWrap]
    simp [wrapDecode]
  refine ⟨first, ?_⟩
  rw [← first]
  have hpos := facts.pos
  have hco : Pairwise (Function.onFun Nat.Coprime T.modulus) := fun i j hij => facts.coprime i j hij
  set a := slope ctx c e
  set v := coordValue u (coordOf e)
  have hv : v < baseFieldModulus := by
    simp only [v, coordValue]
    split_ifs <;> exact ZMod.val_lt _
  have hu : a.val * v < T.wrapBound := by
    rw [facts.wrapBound_eq]
    unfold wrapBound
    have ha : a.val ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt a)
    have hv' : v ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt hv
    rw [sq]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul ha hv')
  have hmod : ∀ (r : Fin T.count → ℕ) j, T.crt r % T.modulus j = r j % T.modulus j := fun r j => by
    rw [tableCrt_eq]; exact SliceC.crt_spec hpos hco r j
  have hlt : ∀ r : Fin T.count → ℕ, T.crt r < ∏ i, T.modulus i := fun r => by
    rw [tableCrt_eq]; exact SliceC.crt_lt hpos r
  have cong : ∀ j, (evalResidue u (join ctx c) (coldOf u c) e j).val ≡
      (readout c e j).val + a.val * v [MOD T.modulus j] := by
    intro j
    rw [← ZMod.natCast_eq_natCast_iff, evalResidue_eq]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    simp only [hotRes, v, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  have hMB : 2 * T.wrapBound ≤ (∏ i, T.modulus i) + 1 := by
    have := facts.wrap_room
    unfold CrtTable.product at this
    omega
  have decoded := SliceC.wrapDecode_crt hpos hco T.crt hmod hlt hu hMB
    (fun j => (evalResidue u (join ctx c) (coldOf u c) e j).val) (fun j => (readout c e j).val) cong
  unfold delivered hint evalInt offset
  unfold CrtTable.product
  rw [decoded]
  unfold offsetF offset
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id]
  ring

end

end Kriterion.CRT.Privacy.BMR
