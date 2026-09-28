/-
**The wrap flag on the swapped table** (P8, `CrtFlagMass`'s wrap part).

The middle game reveals when some CRT value of the replay lies in the two-sided window `[0, B − 1) ∪ (M − B, M)`
(`H8.replayWraps`). On a tag table the replay's CRT values are P45's `evalInt` at the published joins and the table's
cold pads (`replayCrtValues_x`, `_y`). Under the swapped table the cold pads are uniform
(`swapped_cold_uniform`, from `swapped_pads_split`), so each CRT value is uniform on `[0, M)` (`evalInt_uniform`) and lies in the window with probability at most `2 (B − 1) / M`. Over the 642 encodings this is
`1284 (p − 1)^2 / M ≤ smudgeError`, for every source; the weighted sum over sources factors.
-/

import Proof.Privacy.CRT.Swap.PadLaw
import Proof.Privacy.CRT.Core.ReplayDelivered
import Proof.Privacy.CRT.Core.BmrFlags
import Proof.Correctness.CRT.RealTable
import Proof.Privacy.CRT.Glue.Budget
import Proof.Privacy.CRT.Flags.NormFlag

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

noncomputable section

namespace Wrap

/-- **The real table's facts for P45.** -/
theorem entryTableFacts : BMR.TableFacts Entry.table where
  pos := SliceC.bn254_correctTable.modulus_pos
  coprime := fun _ _ different => SliceC.bn254_correctTable.coprime different
  wrapBound_eq := rfl
  wrap_room := by decide +kernel

theorem product_eq : Entry.table.product = BudgetData.M := by decide +kernel

theorem wrapBound_eq : Entry.table.wrapBound = (BudgetData.p - 1) ^ 2 + 1 := by decide +kernel

instance windowDecidable : DecidablePred (BMR.InWindow Entry.table) := fun w => by
  unfold BMR.InWindow
  infer_instance

/-- Restricting the pads to the cold slots. -/
def restrictCold (u : AffineInput) : BMR.Pads Entry.table →+ BMR.Cold Entry.table u :=
  AddMonoidHom.mk' (fun P i e ρ => P i ρ.1 e) fun _ _ => rfl

theorem restrictCold_surjective (u : AffineInput) : Function.Surjective (restrictCold u) := by
  classical
  intro c
  refine ⟨fun i ρ e => if h : ρ = BMR.hotRes Entry.table u e i then 0 else c i e ⟨ρ, h⟩, ?_⟩
  funext i e ρ
  show (if h : ρ.1 = BMR.hotRes Entry.table u e i then 0 else c i e ⟨ρ.1, h⟩) = c i e ρ
  rw [dif_neg ρ.2]

theorem bmrColdOf_eq (T : TagTable) (u : AffineInput) : H8.bmrColdOf T u = restrictCold u (padsOf T) := by
  funext i e ρ
  cases e <;> rfl

theorem swapped_pads_uniform : (swappedTableLaw crtLayout).map padsOf = PMF.uniformOfFintype (BMR.Pads Entry.table) := by
  have split := swapped_pads_split (fun _ => ()) fun _ _ _ => rfl
  have fst := congrArg (PMF.map Prod.fst) split
  rw [PMF.map_comp, PMF.map_bind] at fst
  simp only [PMF.map_comp, Function.comp_def] at fst
  refine fst.trans ?_
  conv_rhs => rw [← PMF.bind_pure (PMF.uniformOfFintype (BMR.Pads Entry.table))]
  refine congrArg _ (funext fun P => ?_)
  exact PMF.map_const _ _

/-- **The cold pads of the swapped table are uniform.** -/
theorem swapped_cold_uniform (u : AffineInput) :
    (swappedTableLaw crtLayout).map (fun T => H8.bmrColdOf T u) = PMF.uniformOfFintype (BMR.Cold Entry.table u) := by
  have : (fun T => H8.bmrColdOf T u) = restrictCold u ∘ padsOf := funext fun T => bmrColdOf_eq T u
  rw [this, ← PMF.map_comp, swapped_pads_uniform]
  exact BMR.WrapMass.uniform_map_addHom _ (restrictCold_surjective u)

/-- The window has at most `2 (B − 1)` values below `M`. -/
theorem window_card :
    Fintype.card {w : Fin Entry.table.product // BMR.InWindow Entry.table w.val} ≤ 2 * (Entry.table.wrapBound - 1) := by
  classical
  rw [Fintype.card_subtype]
  have sub : (Finset.univ.filter fun w : Fin Entry.table.product => BMR.InWindow Entry.table w.val).map
      Fin.valEmbedding ⊆ Finset.range (Entry.table.wrapBound - 1) ∪
        Finset.Ico (Entry.table.product - Entry.table.wrapBound + 1) Entry.table.product := by
    intro n member
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply] at member
    obtain ⟨w, window, rfl⟩ := member
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rcases window with low | high
    · left; omega
    · right; exact ⟨by omega, w.isLt⟩
  have := Finset.card_le_card sub
  rw [Finset.card_map] at this
  refine this.trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range, Nat.card_Ico]
  omega

/-- **One encoding's CRT value is in the window with probability at most `2 (B − 1) / M`.** -/
theorem wrap_one (u : AffineInput) (J : BMR.Joins Entry.table) (e : BMR.Enc) :
    (swappedTableLaw crtLayout).toOuterMeasure {T | BMR.InWindow Entry.table (BMR.evalInt u J (H8.bmrColdOf T u) e)}
      ≤ ((2 * (Entry.table.wrapBound - 1) : ℕ) : ℝ≥0∞) / (Entry.table.product : ℝ≥0∞) := by
  have facts := entryTableFacts
  haveI : Nonempty (Fin Entry.table.product) := ⟨⟨0, Nat.pos_of_ne_zero (by rw [product_eq]; decide)⟩⟩
  have pre : {T : TagTable | BMR.InWindow Entry.table (BMR.evalInt u J (H8.bmrColdOf T u) e)} =
      (fun T => H8.bmrColdOf T u) ⁻¹' ((fun cold => BMR.WrapMass.crtFin facts fun i => BMR.evalResidue u J cold e i) ⁻¹'
        {w | BMR.InWindow Entry.table w.val}) := rfl
  rw [pre, ← PMF.toOuterMeasure_map_apply, swapped_cold_uniform, ← PMF.toOuterMeasure_map_apply,
    BMR.evalInt_uniform facts u J e, PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_fin]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast (le_of_eq (Fintype.card_congr' rfl)).trans window_card

/-- The window event is some encoding's `evalInt` in the window. -/
theorem replayWindow_sub [FieldCertificate] [GroupCertificate] (source : (Instance.view).Source) (u : AffineInput) :
    {T | H8.replayWindow source u T} ⊆ ⋃ e : BMR.Enc,
      {T | BMR.InWindow Entry.table (BMR.evalInt u (H8.bmrJoinsOf ((Instance.view).publish source)) (H8.bmrColdOf T u) e)} := by
  intro T wraps
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  rcases wraps with ⟨x', window⟩ | ⟨y', window⟩
  · refine ⟨.inl (BMR.xEncEquiv.symm x'), ?_⟩
    have same := H8.replayCrtValues_x source u T (BMR.xEncEquiv.symm x')
    have flat : BMR.xFlat (BMR.xEncEquiv.symm x') = x' := BMR.xEncEquiv.apply_symm_apply x'
    rw [flat] at same
    rw [← same]
    exact window
  · refine ⟨.inr (BMR.yEncEquiv.symm y'), ?_⟩
    have same := H8.replayCrtValues_y source u T (BMR.yEncEquiv.symm y')
    have flat : BMR.yFlat (BMR.yEncEquiv.symm y') = y' := BMR.yEncEquiv.apply_symm_apply y'
    rw [flat] at same
    rw [← same]
    exact window

/-- **The window event at one source: at most `smudgeError`.** -/
theorem window_source [FieldCertificate] [GroupCertificate] (source : (Instance.view).Source) (u : AffineInput) :
    (swappedTableLaw crtLayout).toOuterMeasure {T | H8.replayWindow source u T} ≤ ENNReal.ofReal smudgeError := by
  refine (MeasureTheory.measure_mono (replayWindow_sub source u)).trans ?_
  refine (MeasureTheory.measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun e _ => wrap_one u _ e).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have card : Fintype.card BMR.Enc = 642 := by
    rw [Fintype.card_sum, BMR.card_xEnc, BMR.card_yEnc]
  rw [card, wrapBound_eq, product_eq, Nat.add_sub_cancel]
  unfold smudgeError frac
  have Mpos : (0 : ℝ) < (BudgetData.M : ℝ) := by
    have : 0 < BudgetData.M := by decide
    exact_mod_cast this
  rw [ENNReal.ofReal_div_of_pos Mpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ← mul_div_assoc]
  refine ENNReal.div_le_div_right ?_ _
  have e : 642 * (2 * (BudgetData.p - 1) ^ 2) = 1284 * (BudgetData.p - 1) ^ 2 := by ring
  rw [← Nat.cast_mul, e]
  exact_mod_cast Nat.le_add_right _ _

end Wrap

/-- **The wrap reveal at one source**: the window, or the source's normalization flag. -/
theorem wrap_source [FieldCertificate] [GroupCertificate] (source : (Instance.view).Source) (u : AffineInput) :
    (swappedTableLaw crtLayout).toOuterMeasure {T | H8.replayWraps source u T} ≤
      ENNReal.ofReal smudgeError + NormFlag.badInd source := by
  by_cases bad : H8.normBadSrc source
  · rw [NormFlag.badInd, if_pos bad]
    refine le_trans (le_trans (MeasureTheory.measure_mono (Set.subset_univ _))
      (le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)))) le_add_self
  · rw [NormFlag.badInd, if_neg bad, add_zero]
    have same : {T | H8.replayWraps source u T} = {T | H8.replayWindow source u T} := by
      ext T
      exact ⟨fun w => w.resolve_right bad, Or.inl⟩
    rw [same]
    exact Wrap.window_source source u

/-- **The wrap flag on the swapped table** (for `CrtFlagMass`): against every weight on the published value, the
weighted mass of the wrap reveal is at most `smudgeError + normError` times the total weight. -/
theorem crtWrapTable_le [FieldCertificate] [GroupCertificate] (u : AffineInput)
    (weight : Instance.crtEntry.Public → ℝ≥0∞) :
    (letI := (PublicFirst.viewHere Instance.crtEntry).sourceFintype
     haveI := (PublicFirst.viewHere Instance.crtEntry).sourceNonempty
     ∑' source, PMF.uniformOfFintype _ source *
       (weight ((PublicFirst.viewHere Instance.crtEntry).publish source) *
         (swappedTableLaw crtLayout).toOuterMeasure {T | H8.replayWraps source u T}))
      ≤ ENNReal.ofReal (smudgeError + normError) *
        (letI := (PublicFirst.viewHere Instance.crtEntry).sourceFintype
         haveI := (PublicFirst.viewHere Instance.crtEntry).sourceNonempty
         ∑' source, PMF.uniformOfFintype _ source * weight ((PublicFirst.viewHere Instance.crtEntry).publish source)) := by
  letI := (PublicFirst.viewHere Instance.crtEntry).sourceFintype
  haveI := (PublicFirst.viewHere Instance.crtEntry).sourceNonempty
  have smudgeNonneg : 0 ≤ smudgeError := frac_nonneg _ _
  rw [ENNReal.ofReal_add smudgeNonneg normError_nonneg, add_mul]
  calc _ ≤ ∑' source, PMF.uniformOfFintype (PublicFirst.viewHere Instance.crtEntry).Source source *
          (weight ((PublicFirst.viewHere Instance.crtEntry).publish source) *
            (ENNReal.ofReal smudgeError + NormFlag.badInd source)) :=
        ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl (mul_le_mul' le_rfl (wrap_source source u))
    _ = ENNReal.ofReal smudgeError * ∑' source, PMF.uniformOfFintype (PublicFirst.viewHere Instance.crtEntry).Source
            source * weight ((PublicFirst.viewHere Instance.crtEntry).publish source) +
          ∑' source, PMF.uniformOfFintype (PublicFirst.viewHere Instance.crtEntry).Source source *
            (weight ((PublicFirst.viewHere Instance.crtEntry).publish source) * NormFlag.badInd source) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun source => ?_
        ring
    _ ≤ _ := add_le_add le_rfl
        (@NormFlag.normFlag_le _ _ weight (PublicFirst.viewHere Instance.crtEntry).sourceFintype
          (PublicFirst.viewHere Instance.crtEntry).sourceNonempty)

end

end Kriterion.CRT.Privacy.Flags
