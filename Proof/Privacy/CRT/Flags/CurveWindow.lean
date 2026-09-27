/-
**The mass of the curve-window bad event** (`StageTwo.CurveWindowMass`).

`curveNearEdge` asks whether one of the five curve encodings' CRT offsets (the `x` encodings `364, 365, 366`, the `y`
encodings `273, 274`) lies within `B` of an end of `[0, M)`: `O < B` or `M < O + 2B`. An offset is read from the
table's pads alone: the garbler asks only labelled inputs below `p`, where the scheme's hash of the table oracle is
`tagHash` (`CurveWindow.gxOf_tableOracle`), and there BmrEntry's `gxOf_offset` gives P45's offset of the pads. Under
the swapped table the pads are uniform, so each offset is uniform on `[0, M)` (`BMR.WrapMass.offset_uniform`) and is
near an edge with probability at most `3B / M`. Over the five encodings this is `15 ((p − 1)^2 + 1) / M`, below
`smudgeError = hiddenWindowError`.
-/

import Proof.Privacy.CRT.Flags.Wrap
import Proof.Privacy.CRT.Hidden.StageTwo
import Proof.Privacy.CRT.Core.BmrEntry


set_option autoImplicit false

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

noncomputable section

namespace CurveWindow

/-- A program's value depends on the hash only at the inputs its path asks. -/
theorem eval_congr_asked (H H' : HashN) {α : Type} :
    ∀ R : CM α, (∀ n ∈ Align.asked H R, H n = H' n) → R.eval H = R.eval H'
  | .pure _, _ => rfl
  | .query n next, agree => by
    have head : H n = H' n := agree n List.mem_cons_self
    show (next (H n)).eval H = (next (H' n)).eval H'
    rw [← head]
    exact eval_congr_asked H H' (next (H n)) fun m inside => agree m (List.mem_cons_of_mem _ inside)

/-- Below `p` the scheme's hash of the table oracle is `tagHash`. -/
theorem schemeHash_lt (table : TagTable) {n : ℕ} (small : n < baseFieldModulus) :
    schemeHash (tableOracle (FI := Empty) (EI := Empty) table) n = H8.tagHash table n := by
  show table (tagOfInput (n : BaseField)) = table _
  congr 1
  apply Fin.ext
  show ((n : BaseField)).val / 2 ^ 128 % 2 ^ 40 = n / 2 ^ 128 % 2 ^ 40
  rw [Align.val_natCast_of_lt small]

theorem gxOf_tableOracle (table : TagTable) (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    EntryCorrect.gxOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins =
      EntryCorrect.gxOf (H8.tagHash table) coins := by
  unfold EntryCorrect.gxOf
  refine eval_congr_asked _ _ _ fun n inside => ?_
  obtain ⟨k, -, range, label, rfl⟩ := Align.asked_of_tagged
    (Paths.coordGarbleM_tagged Entry.table Entry.xCount 0 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _
    inside
  exact schemeHash_lt table (Paths.hashInput_lt range)

theorem gyOf_tableOracle (table : TagTable) (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    EntryCorrect.gyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins =
      EntryCorrect.gyOf (H8.tagHash table) coins := by
  unfold EntryCorrect.gyOf
  refine eval_congr_asked _ _ _ fun n inside => ?_
  obtain ⟨k, -, range, label, rfl⟩ := Align.asked_of_tagged
    (Paths.coordGarbleM_tagged Entry.table Entry.yCount 1 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _
    inside
  exact schemeHash_lt table (Paths.hashInput_lt range)

/-- The CRT offset of an encoding, from the pads. -/
def offsetOfPads (P : BMR.Pads Entry.table) (e : BMR.Enc) : ℕ :=
  (BMR.WrapMass.crtFin Wrap.entryTableFacts (BMR.WrapMass.readoutHom e P)).val

/-- P45's offset of the coins of a table tape is the offset of the table's pads. -/
theorem offset_pads (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (e : BMR.Enc) :
    BMR.offset (BmrEntry.bmrCoinsOf coins table) e = offsetOfPads (padsOf table) e := by
  have same : (fun i => (BMR.readout (BmrEntry.bmrCoinsOf coins table) e i).val) =
      fun i => (BMR.WrapMass.readoutHom e (padsOf table) i).val := rfl
  unfold BMR.offset offsetOfPads BMR.WrapMass.crtFin
  rw [same]

theorem gx_offset (table : TagTable) (coins : Kriterion.ArgoMAC.Scheme.Coins) (x : BMR.XEnc) :
    (EntryCorrect.gxOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins).offset (BMR.xFlat x) =
      offsetOfPads (padsOf table) (.inl x) := by
  rw [gxOf_tableOracle, BmrEntry.gxOf_offset, offset_pads]

theorem gy_offset (table : TagTable) (coins : Kriterion.ArgoMAC.Scheme.Coins) (y : BMR.YEnc) :
    (EntryCorrect.gyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins).offset (BMR.yFlat y) =
      offsetOfPads (padsOf table) (.inr y) := by
  rw [gyOf_tableOracle, BmrEntry.gyOf_offset, offset_pads]

instance nearEdgeDecidable : DecidablePred StageTwo.nearEdge := fun n => by
  unfold StageTwo.nearEdge
  infer_instance

/-- The offsets near an edge: at most `3B` values below `M`. -/
theorem nearEdge_card :
    Fintype.card {w : Fin Entry.table.product // StageTwo.nearEdge w.val} ≤ 3 * Entry.table.wrapBound := by
  classical
  rw [Fintype.card_subtype]
  have sub : (Finset.univ.filter fun w : Fin Entry.table.product => StageTwo.nearEdge w.val).map
      Fin.valEmbedding ⊆ Finset.range Entry.table.wrapBound ∪
        Finset.Ico (Entry.table.product + 1 - 2 * Entry.table.wrapBound) Entry.table.product := by
    intro n member
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply] at member
    obtain ⟨w, edge, rfl⟩ := member
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rcases edge with low | high
    · left; exact low
    · right; exact ⟨by omega, w.isLt⟩
  have := Finset.card_le_card sub
  rw [Finset.card_map] at this
  refine this.trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range, Nat.card_Ico]
  omega

/-- **One encoding's offset is near an edge with probability at most `3B / M`.** -/
theorem nearEdge_one (e : BMR.Enc) :
    (swappedTableLaw crtLayout).toOuterMeasure {T | StageTwo.nearEdge (offsetOfPads (padsOf T) e)}
      ≤ ((3 * Entry.table.wrapBound : ℕ) : ℝ≥0∞) / (Entry.table.product : ℝ≥0∞) := by
  have : Nonempty (Fin Entry.table.product) :=
    ⟨⟨0, Nat.pos_of_ne_zero (by rw [Wrap.product_eq]; decide)⟩⟩
  have pre : {T : TagTable | StageTwo.nearEdge (offsetOfPads (padsOf T) e)} =
      padsOf ⁻¹' ((fun P => BMR.WrapMass.crtFin Wrap.entryTableFacts (BMR.WrapMass.readoutHom e P)) ⁻¹'
        {w | StageTwo.nearEdge w.val}) := rfl
  rw [pre, ← PMF.toOuterMeasure_map_apply, Wrap.swapped_pads_uniform, ← PMF.toOuterMeasure_map_apply,
    BMR.WrapMass.offset_uniform Wrap.entryTableFacts e, PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_fin]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast (le_of_eq (Fintype.card_congr' rfl)).trans nearEdge_card

/-- The tape law read at the table: the swapped table. -/
theorem tape_table (S : Set TagTable) :
    (swappedTableTape Instance.crtEntry).toOuterMeasure {tape | tape.2 ∈ S} =
      (swappedTableLaw crtLayout).toOuterMeasure S := by
  unfold swappedTableTape
  rw [PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply]
  have pre : ∀ coins : Instance.crtEntry.Coins,
      (fun table => (coins, table)) ⁻¹' {tape : TableTape Instance.crtEntry | tape.2 ∈ S} = S := fun _ => rfl
  simp only [pre]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, show Instance.crtEntry.layout = crtLayout from rfl]

/-- The bad event lies in the union of the five encodings' events. -/
theorem curveNearEdge_sub :
    {tape : TableTape Instance.crtEntry | StageTwo.curveNearEdge tape} ⊆
      (⋃ j : Fin 3, {tape | tape.2 ∈ {T | StageTwo.nearEdge (offsetOfPads (padsOf T)
          (.inl (BMR.xEncEquiv.symm ⟨364 + j.val, by omega⟩)))}}) ∪
        ⋃ j : Fin 2, {tape | tape.2 ∈ {T | StageTwo.nearEdge (offsetOfPads (padsOf T)
          (.inr (BMR.yEncEquiv.symm ⟨273 + j.val, by omega⟩)))}} := by
  intro tape bad
  simp only [Set.mem_ofPred_eq] at bad
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
  rcases bad with ⟨e, low, edge⟩ | ⟨e, low, edge⟩
  · left
    have lowN : 364 ≤ e.val := low
    refine ⟨⟨e.val - 364, by have := e.isLt; change e.val < 367 at this; omega⟩, ?_⟩
    have same : (⟨364 + (e.val - 364), by have := e.isLt; change e.val < 367 at this; omega⟩ : Fin Entry.xCount) = e :=
      Fin.ext (by show 364 + (e.val - 364) = e.val; omega)
    have value := gx_offset tape.2 tape.1 (BMR.xEncEquiv.symm e)
    have flat : BMR.xFlat (BMR.xEncEquiv.symm e) = e := BMR.xEncEquiv.apply_symm_apply e
    rw [flat] at value
    show StageTwo.nearEdge (offsetOfPads (padsOf tape.2) _)
    rw [same, ← value]
    exact edge
  · right
    have lowN : 273 ≤ e.val := low
    refine ⟨⟨e.val - 273, by have := e.isLt; change e.val < 275 at this; omega⟩, ?_⟩
    have same : (⟨273 + (e.val - 273), by have := e.isLt; change e.val < 275 at this; omega⟩ : Fin Entry.yCount) = e :=
      Fin.ext (by show 273 + (e.val - 273) = e.val; omega)
    have value := gy_offset tape.2 tape.1 (BMR.yEncEquiv.symm e)
    have flat : BMR.yFlat (BMR.yEncEquiv.symm e) = e := BMR.yEncEquiv.apply_symm_apply e
    rw [flat] at value
    show StageTwo.nearEdge (offsetOfPads (padsOf tape.2) _)
    rw [same, ← value]
    exact edge

end CurveWindow

open CurveWindow in
/-- **`CurveWindowMass`**: the curve encodings' offsets are near an edge with probability at most
`hiddenWindowError`. -/
theorem crtCurveWindowMass : StageTwo.CurveWindowMass := by
  unfold StageTwo.CurveWindowMass
  refine (MeasureTheory.measure_mono curveNearEdge_sub).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  refine (add_le_add (MeasureTheory.measure_iUnion_fintype_le _ _) (MeasureTheory.measure_iUnion_fintype_le _ _)).trans ?_
  simp only [tape_table]
  refine (add_le_add (Finset.sum_le_sum fun j _ => nearEdge_one _) (Finset.sum_le_sum fun j _ => nearEdge_one _)).trans ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, nsmul_eq_mul, ← add_mul, ← mul_div_assoc]
  rw [Wrap.wrapBound_eq, Wrap.product_eq]
  unfold hiddenWindowError smudgeError frac
  have Mpos : (0 : ℝ) < (BudgetData.M : ℝ) := by
    have : 0 < BudgetData.M := by decide
    exact_mod_cast this
  rw [ENNReal.ofReal_div_of_pos Mpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  refine ENNReal.div_le_div_right ?_ _
  have numer : (3 + 2) * (3 * ((BudgetData.p - 1) ^ 2 + 1)) ≤
      1284 * (BudgetData.p - 1) ^ 2 + 273 * BudgetData.p := by
    decide +kernel
  exact_mod_cast numer

end

end Kriterion.CRT.Privacy.Flags
