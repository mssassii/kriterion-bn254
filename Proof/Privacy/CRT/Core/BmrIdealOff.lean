/-
**P45 off the curve: the core with the window flag and the ideal side's source** (H8's `CrtBmrSplitOff`).

* `core_below_off`: at every context and input, the law of the off-curve ideal outputs at uniform cells
  (`BMR.idealOutOff`), flagged wherever an encoding's CRT value lies in the two-sided wrap window, is below the law of
  the off-curve real outputs at uniform coins (`BMR.realOutOff`). Each unflagged cell is the image under `bmrEquivOff`
  of `|ResidualOff|` coin vectors, none of which wraps (`hint_false_of_window`), and at each of them the real output
  is the ideal output of the cell (`bmr_real_eq_ideal_off`). The mirror of `BMR.core_below`.
* Off the curve: the scheme's function is `none` only where `validate` is false, and no tape doubles there (an
  exceptional input lies on the curve).
* The ideal side's source: the P45 cells a uniform source publishes (`srcOf`: the joins its records carry, its row
  and curve constants) are uniform on `BMR.Source` (`uniform_srcOf`); the published records are the hint-free records
  of those joins (`publish_recX`, `publish_recY`); route M's off-curve reveal is the window event of P45's `evalInt`
  (`replayWraps_iff`).
-/

import Proof.Privacy.CRT.Core.BmrCore
import Proof.Privacy.CRT.Core.BmrNorm
import Proof.Privacy.CRT.Core.BodyMaskRowOff
import Proof.Privacy.CRT.Core.ReplayDelivered
import Proof.Privacy.CRT.Core.SourceSplit
import Proof.Privacy.CRT.Core.EncIndex
import Proof.Correctness.CRT.EntryDelivery
import Proof.Correctness.JacobianMixed

namespace Kriterion.CRT.Privacy.BmrOff

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.BMR
open scoped ENNReal

noncomputable section

/-! ### 1. The P45 core off the curve, with the window flag -/

section Core

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)] [FieldCertificate]

/-- `bmrEquivOff`'s first component reads the joins and the cold pads of the coins. -/
theorem bmrEquivOff_join (ctx : Context) (u : AffineInput) (c : Coins T) :
    (bmrEquivOff T ctx u c).1.1.1 = join ctx c ∧ (bmrEquivOff T ctx u c).1.2 = coldOf u c :=
  ⟨rfl, rfl⟩

/-- **The P45 core off the curve, with the window flag.** -/
theorem core_below_off (facts : TableFacts T) (ctx : Context) (u : AffineInput)
    (flag : Source T × Cold T u → Prop) [DecidablePred flag]
    (window : ∀ cells, ¬ flag cells → ∀ e, ¬ InWindow T (evalInt u cells.1.1 cells.2 e)) (o : OutOff T u) :
    (PMF.uniformOfFintype (Source T × Cold T u)).map
        (fun cells => if flag cells then none else some (idealOutOff u cells)) (some o) ≤
      (PMF.uniformOfFintype (Coins T)).map (fun c => some (realOutOff ctx u c)) (some o) := by
  set e := bmrEquivOff T ctx u
  have same : ∀ cells res, ¬ flag cells → realOutOff ctx u (e.symm (cells, res)) = idealOutOff u cells := by
    intro cells res flagged
    have image : e (e.symm (cells, res)) = (cells, res) := e.apply_symm_apply _
    have noWrap : ∀ enc, hint (e.symm (cells, res)) enc = false := by
      intro enc
      apply hint_false_of_window facts ctx u
      have parts := bmrEquivOff_join ctx u (e.symm (cells, res))
      rw [← parts.1, ← parts.2]
      show ¬ InWindow T (evalInt u (e (e.symm (cells, res))).1.1.1 (e (e.symm (cells, res))).1.2 enc)
      rw [image]
      exact window cells flagged enc
    rw [bmr_real_eq_ideal_off T ctx u _ noWrap]
    show idealOutOff u (e (e.symm (cells, res))).1 = _
    rw [image]
  rw [← uniform_map_fst (A := Source T × Cold T u) (B := ResidualOff), PMF.map_comp,
    ← uniform_map_equiv e.symm, PMF.map_comp]
  refine map_le_map_of_imp _ _ _ _ _ fun x hit => ?_
  obtain ⟨cells, res⟩ := x
  simp only [Function.comp_apply] at hit ⊢
  by_cases flagged : flag cells
  · rw [if_pos flagged] at hit
    exact absurd hit (Option.some_ne_none o).symm
  · rw [if_neg flagged] at hit
    rw [same cells res flagged, hit]

end Core

/-! ### 2. Off the curve -/

section OffCurve

variable [FieldCertificate] [GroupCertificate]

open Kriterion.CRT.Privacy.Instance

/-- **Where the scheme's function is `none`, the input is off the curve.** -/
theorem not_onCurve_of_function {scalar : NonZeroScalar} {u : AffineInput}
    (undefined : (crtEntry.scheme inferInstance inferInstance).function scalar u = none) : ¬ OnCurve u := by
  intro onCurve
  have defined : decodePoint u ≠ none := (decodePoint_defined u).mpr onCurve
  have unfolded : (crtEntry.scheme inferInstance inferInstance).function scalar u =
      (decodePoint u).map (scalarMultiplication scalar.value) := rfl
  rw [unfolded] at undefined
  exact defined (Option.map_eq_none_iff.mp undefined)

/-- **Where the scheme's function is `none`, `validate` is false.** -/
theorem validate_false_of_function {scalar : NonZeroScalar} {u : AffineInput}
    (undefined : (crtEntry.scheme inferInstance inferInstance).function scalar u = none) : validate u = false := by
  cases hv : validate u
  · rfl
  · exact absurd ((validate_eq_true_iff u).mp hv) (not_onCurve_of_function undefined)

/-- An exceptional input lies on the curve (xinshu's `exceptionalInput_onCurve`, restated to avoid its import). -/
theorem exceptionalInput_onCurve' (phi : BaseField) (phiSix : phi ^ 6 = 1) (offset : AffineInput)
    (onCurve : OnCurve offset) : OnCurve (Exception.exceptionalInput phi offset) := by
  unfold OnCurve at onCurve ⊢
  simp only [Exception.exceptionalInput]
  calc (phi ^ 3 * offset.y) ^ 2 = phi ^ 6 * offset.y ^ 2 := by ring
    _ = offset.y ^ 2 := by rw [phiSix, one_mul]
    _ = offset.x ^ 3 + 3 := onCurve
    _ = phi ^ 6 * offset.x ^ 3 + 3 := by rw [phiSix, one_mul]
    _ = (phi ^ 2 * offset.x) ^ 3 + 3 := by ring

/-- **Off the curve no tape doubles**: every exceptional input lies on the curve. -/
theorem not_doubling_of_off (scalar : NonZeroScalar) (tape : TableTape crtEntry) {u : AffineInput}
    (off : ¬ OnCurve u) : ¬ H8.Doubling crtEntry scalar tape u := by
  rintro ⟨o, hexc⟩
  change Kriterion.CRT.Entry.exceptional scalar tape.1 o = some u at hexc
  obtain ⟨inRange, phi, hphi, kinds⟩ := Kriterion.CRT.Entry.exceptional_cases scalar tape.1 o u hexc
  have six := digitEndomorphismBasePowSix _ phi hphi
  have kOn := ((Kriterion.CRT.Entry.outputKeysOf scalar tape.1).get ⟨o / 2, inRange⟩).offset.onCurve
  rcases kinds with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact off (exceptionalInput_onCurve' phi six _ kOn)
  · exact off (exceptionalInput_onCurve' phi six _ (Kriterion.ArgoMAC.JacobianMixed.doubleOffset_onCurve _ kOn))

end OffCurve

/-! ### 3. The ideal side's source -/

section Source

/-- The entry's table. -/
abbrev Tb : CrtTable := Kriterion.CRT.Entry.table

/-- A residue below a positive modulus as an element of `ZMod`. -/
def finZMod (m : ℕ) [NeZero m] : Fin m ≃ ZMod m where
  toFun r := (r.val : ZMod m)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv r := Fin.ext (ZMod.val_cast_of_lt r.isLt)
  right_inv z := ZMod.natCast_zmod_val z

/-- A natural below `M` as its residue vector in `ZMod`. -/
def residuesEquiv : Fin Tb.product ≃ ((i : Fin Tb.count) → ZMod (Tb.modulus i)) :=
  Tb.mixedRadixEquiv.symm.trans (Equiv.piCongrRight fun i => finZMod (Tb.modulus i))

theorem residuesEquiv_apply (r : Fin Tb.product) (i : Fin Tb.count) :
    residuesEquiv r i = ((r.val / Tb.radix i % Tb.modulus i : ℕ) : ZMod (Tb.modulus i)) := by
  show ((Tb.mixedRadixEquiv.symm r i).val : ZMod (Tb.modulus i)) = _
  rw [CrtTable.mixedRadixEquiv_symm_val]

/-- The records of both coordinates as P45's joins. -/
def recJoinsEquiv : (Fin Kriterion.CRT.Entry.xCount → Fin Tb.product) × (Fin Kriterion.CRT.Entry.yCount → Fin Tb.product) ≃
    Joins Tb :=
  ((Equiv.prodCongr (Equiv.arrowCongr xEncEquiv.symm (Equiv.refl _))
      (Equiv.arrowCongr yEncEquiv.symm (Equiv.refl _))).trans
    (Equiv.sumArrowEquivProdArrow XEnc YEnc (Fin Tb.product)).symm).trans
    (Equiv.arrowCongr (Equiv.refl Enc) residuesEquiv)

theorem recJoinsEquiv_inl (rx : Fin Kriterion.CRT.Entry.xCount → Fin Tb.product)
    (ry : Fin Kriterion.CRT.Entry.yCount → Fin Tb.product) (x : XEnc) :
    recJoinsEquiv (rx, ry) (.inl x) = residuesEquiv (rx (xFlat x)) := rfl

theorem recJoinsEquiv_inr (rx : Fin Kriterion.CRT.Entry.xCount → Fin Tb.product)
    (ry : Fin Kriterion.CRT.Entry.yCount → Fin Tb.product) (y : YEnc) :
    recJoinsEquiv (rx, ry) (.inr y) = residuesEquiv (ry (yFlat y)) := rfl

/-- A record of a source, as a natural. -/
theorem publish_recX_val (s : Kriterion.CRT.Entry.Source) (e : Fin Kriterion.CRT.Entry.xCount) :
    ((Kriterion.CRT.Entry.publish s).recX.get e).val = (s.recX e).val := by
  rw [show (Kriterion.CRT.Entry.publish s).recX = Vector.ofFn fun e => Kriterion.CRT.Entry.toRecord (s.recX e).val
    from rfl, Vector.get_ofFn]
  refine EntryDelivery.toRecord_val _ ?_
  have lt : (s.recX e).val < Tb.product := (s.recX e).isLt
  have fits : 2 * Tb.product ≤ 256 ^ 78 := Kriterion.CRT.bn254Table_record_fits
  exact Nat.lt_of_lt_of_le lt (le_trans (Nat.le_mul_of_pos_left _ two_pos) fits)

theorem publish_recY_val (s : Kriterion.CRT.Entry.Source) (e : Fin Kriterion.CRT.Entry.yCount) :
    ((Kriterion.CRT.Entry.publish s).recY.get e).val = (s.recY e).val := by
  rw [show (Kriterion.CRT.Entry.publish s).recY = Vector.ofFn fun e => Kriterion.CRT.Entry.toRecord (s.recY e).val
    from rfl, Vector.get_ofFn]
  refine EntryDelivery.toRecord_val _ ?_
  have lt : (s.recY e).val < Tb.product := (s.recY e).isLt
  have fits : 2 * Tb.product ≤ 256 ^ 78 := Kriterion.CRT.bn254Table_record_fits
  exact Nat.lt_of_lt_of_le lt (le_trans (Nat.le_mul_of_pos_left _ two_pos) fits)

/-- **The joins the published records carry are the source's records read as residues.** -/
theorem bmrJoinsOf_publish (s : Kriterion.CRT.Entry.Source) :
    H8.bmrJoinsOf (Kriterion.CRT.Entry.publish s) = recJoinsEquiv (s.recX, s.recY) := by
  funext e i
  rcases e with x | y
  · rw [recJoinsEquiv_inl, residuesEquiv_apply]
    show ((recordJoin Tb Tb.product Tb.radix ((Kriterion.CRT.Entry.publish s).recX.get (xFlat x)).val i : ℕ) :
      ZMod (Tb.modulus i)) = _
    rw [publish_recX_val]
    unfold recordJoin
    rw [Nat.mod_eq_of_lt (s.recX (xFlat x)).isLt]
  · rw [recJoinsEquiv_inr, residuesEquiv_apply]
    show ((recordJoin Tb Tb.product Tb.radix ((Kriterion.CRT.Entry.publish s).recY.get (yFlat y)).val i : ℕ) :
      ZMod (Tb.modulus i)) = _
    rw [publish_recY_val]
    unfold recordJoin
    rw [Nat.mod_eq_of_lt (s.recY (yFlat y)).isLt]

/-- **The P45 cells of a source**: the joins its records carry, its row cells (the published `X` constant and the two
hidden cells), its signs, its curve constants. -/
def srcOf (s : Kriterion.CRT.Entry.Source) : NSource Tb :=
  (H8.bmrJoinsOf (Kriterion.CRT.Entry.publish s), s.rows, s.signs, s.curve)

/-- The source's cells other than P45's: the exception entries, the conversion joins and pins. -/
abbrev RestCells := (Fin digitCount → Exception.Entry) × (Fin 2 → Fin Kriterion.CRT.Entry.joinCount → Label) ×
  (Fin 2 → (k : Fin Kriterion.CRT.Entry.pinCount) → Lanes (Kriterion.CRT.Entry.pinWidth k))

/-- **A source's published cells are P45's cells and the rest.** -/
def cellsEquiv : EntrySplit.Cells ≃ NSource Tb × RestCells where
  toFun c := ((recJoinsEquiv (c.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2), c.2.1, c.2.2.1, c.1),
    (c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1))
  invFun p := (p.1.2.2.2, p.1.2.1, p.1.2.2.1, p.2.1, p.2.2.1, p.2.2.2, (recJoinsEquiv.symm p.1.1).1,
    (recJoinsEquiv.symm p.1.1).2)
  left_inv c := by
    obtain ⟨curve, rows, signs, exc, joins, pins, rx, ry⟩ := c
    simp only [Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨⟨J, rows, signs, curve⟩, exc, joins, pins⟩ := p
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

instance restCellsFinite : Finite RestCells :=
  Finite.of_surjective (fun c : EntrySplit.Cells => (cellsEquiv c).2) fun r =>
    ⟨cellsEquiv.symm (Classical.arbitrary _, r), by
      show (cellsEquiv (cellsEquiv.symm (Classical.arbitrary _, r))).2 = r
      rw [Equiv.apply_symm_apply]⟩

instance restCellsFintype : Fintype RestCells := Fintype.ofFinite _

instance restCellsNonempty : Nonempty RestCells := ⟨(cellsEquiv (Classical.arbitrary _)).2⟩

theorem srcOf_split (c : EntrySplit.Cells) (k : EntrySplit.LabelKey) :
    srcOf (EntrySplit.split.symm (c, k)) = (cellsEquiv c).1 := by
  show (H8.bmrJoinsOf (Kriterion.CRT.Entry.publish (EntrySplit.split.symm (c, k))), c.2.1, c.2.2.1, c.1) = _
  rw [bmrJoinsOf_publish]
  rfl

/-- **The P45 cells of a uniform source are uniform.** -/
theorem uniform_srcOf :
    (letI := Fintype.ofFinite Kriterion.CRT.Entry.Source
     (PMF.uniformOfFintype Kriterion.CRT.Entry.Source).map srcOf) = PMF.uniformOfFintype (NSource Tb) := by
  rw [EntrySplit.uniform_source, PMF.map_comp]
  have factor : srcOf ∘ EntrySplit.split.symm = Prod.fst ∘ cellsEquiv ∘ Prod.fst := by
    funext p
    exact srcOf_split p.1 p.2
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, uniform_map_fst, uniform_map_equiv, uniform_map_fst]

/-- The record natural of P45's joins and hints (`recordOf`). -/
def recordNat (J : Joins Tb) (hints : Enc → Bool) (e : Enc) : ℕ :=
  (if hints e then Tb.product else 0) + ∑ i : Fin Tb.count, (J e i).val * Tb.radix i

theorem residuesEquiv_mixed (r : Fin Tb.product) :
    ∑ i : Fin Tb.count, (residuesEquiv r i).val * Tb.radix i = r.val := by
  have back : Tb.mixedRadix (Tb.mixedRadixEquiv.symm r) = r.val := by
    rw [← CrtTable.mixedRadixEquiv_val, Equiv.apply_symm_apply]
  rw [← back]
  unfold CrtTable.mixedRadix
  refine Finset.sum_congr rfl fun i _ => ?_
  show (((Tb.mixedRadixEquiv.symm r i).val : ZMod (Tb.modulus i))).val * Tb.radix i = _
  rw [ZMod.val_cast_of_lt (Tb.mixedRadixEquiv.symm r i).isLt]

/-- **A published `x` record is the hint-free record of its joins.** -/
theorem publish_recX (s : Kriterion.CRT.Entry.Source) (e : Fin Kriterion.CRT.Entry.xCount) :
    (Kriterion.CRT.Entry.publish s).recX.get e =
      Kriterion.CRT.Entry.toRecord (recordNat (srcOf s).1 (fun _ => false) (.inl (xEncEquiv.symm e))) := by
  apply Fin.ext
  rw [publish_recX_val]
  unfold recordNat srcOf
  simp only [Bool.false_eq_true, if_false, zero_add]
  rw [bmrJoinsOf_publish, recJoinsEquiv_inl, residuesEquiv_mixed]
  show (s.recX e).val = (Kriterion.CRT.Entry.toRecord (s.recX (xEncEquiv (xEncEquiv.symm e))).val).val
  rw [Equiv.apply_symm_apply]
  exact (EntryDelivery.toRecord_val _ (by
    rw [← publish_recX_val s e]; exact ((Kriterion.CRT.Entry.publish s).recX.get e).isLt)).symm

/-- **A published `y` record is the hint-free record of its joins.** -/
theorem publish_recY (s : Kriterion.CRT.Entry.Source) (e : Fin Kriterion.CRT.Entry.yCount) :
    (Kriterion.CRT.Entry.publish s).recY.get e =
      Kriterion.CRT.Entry.toRecord (recordNat (srcOf s).1 (fun _ => false) (.inr (yEncEquiv.symm e))) := by
  apply Fin.ext
  rw [publish_recY_val]
  unfold recordNat srcOf
  simp only [Bool.false_eq_true, if_false, zero_add]
  rw [bmrJoinsOf_publish, recJoinsEquiv_inr, residuesEquiv_mixed]
  show (s.recY e).val = (Kriterion.CRT.Entry.toRecord (s.recY (yEncEquiv (yEncEquiv.symm e))).val).val
  rw [Equiv.apply_symm_apply]
  exact (EntryDelivery.toRecord_val _ (by
    rw [← publish_recY_val s e]; exact ((Kriterion.CRT.Entry.publish s).recY.get e).isLt)).symm

/-- The two-sided window flag of P45's cells off the curve. -/
def windowFlag (u : AffineInput) (cells : NSource Tb × Cold Tb u) : Prop :=
  ∃ e, InWindow Tb (evalInt u cells.1.1 cells.2 e)

theorem not_window (u : AffineInput) (cells : NSource Tb × Cold Tb u) (clear : ¬ windowFlag u cells) :
    ∀ e, ¬ InWindow Tb (evalInt u cells.1.1 cells.2 e) :=
  fun e hit => clear ⟨e, hit⟩

/-- **The normalization flag of a source is P45's hidden-cell flag of its cells.** -/
theorem normBadSrc_iff (s : Kriterion.CRT.Entry.Source) : H8.normBadSrc s ↔ normBad (srcOf s) := by
  unfold H8.normBadSrc normBad GoodScales hiddenCells srcOf
  simp only [not_forall, not_and_or, ne_eq, not_not]
  exact Iff.rfl

/-- **Route M's window event is the window event of P45's `evalInt`.** -/
theorem replayWindow_iff [FieldCertificate] [GroupCertificate] (s : Kriterion.CRT.Entry.Source) (u : AffineInput)
    (table : TagTable) :
    H8.replayWindow s u table ↔ windowFlag u (srcOf s, H8.bmrColdOf table u) := by
  have hx : ∀ x : XEnc, (H8.replayCrtValues s u table).1 (xFlat x) =
      evalInt u (H8.bmrJoinsOf (Kriterion.CRT.Entry.publish s)) (H8.bmrColdOf table u) (.inl x) :=
    fun x => H8.replayCrtValues_x s u table x
  have hy : ∀ y : YEnc, (H8.replayCrtValues s u table).2 (yFlat y) =
      evalInt u (H8.bmrJoinsOf (Kriterion.CRT.Entry.publish s)) (H8.bmrColdOf table u) (.inr y) :=
    fun y => H8.replayCrtValues_y s u table y
  unfold H8.replayWindow windowFlag srcOf
  constructor
  · rintro (⟨e, hit⟩ | ⟨e, hit⟩)
    · refine ⟨.inl (xEncEquiv.symm e), ?_⟩
      have flat : xFlat (xEncEquiv.symm e) = e := xEncEquiv.apply_symm_apply e
      have key := hx (xEncEquiv.symm e)
      rw [flat] at key
      rw [key] at hit
      exact hit
    · refine ⟨.inr (yEncEquiv.symm e), ?_⟩
      have flat : yFlat (yEncEquiv.symm e) = e := yEncEquiv.apply_symm_apply e
      have key := hy (yEncEquiv.symm e)
      rw [flat] at key
      rw [key] at hit
      exact hit
  · rintro ⟨e, hit⟩
    rcases e with x | y
    · left
      refine ⟨xFlat x, ?_⟩
      rw [hx]
      exact hit
    · right
      refine ⟨yFlat y, ?_⟩
      rw [hy]
      exact hit

/-- **Route M's off-curve reveal is the window event of P45's `evalInt` or the normalization flag.** -/
theorem replayWraps_iff [FieldCertificate] [GroupCertificate] (s : Kriterion.CRT.Entry.Source) (u : AffineInput)
    (table : TagTable) :
    H8.replayWraps s u table ↔ windowFlag u (srcOf s, H8.bmrColdOf table u) ∨ normBad (srcOf s) := by
  unfold H8.replayWraps
  rw [replayWindow_iff, normBadSrc_iff]

end Source

end

end Kriterion.CRT.Privacy.BmrOff
