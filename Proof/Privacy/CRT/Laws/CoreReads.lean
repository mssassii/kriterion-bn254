/-
**The real reads**.

`Laws.RealReads Entry.table`: the parts of the real view that remain after each split of `realCore_factor` read the
tape off that split's hidden tags (and the coins up to that split's coin relation):

* the P45 part `realBmr` reads the coins' offsets, row randomness, bridge key and curve coins, and the table at the
  tags of families 6, 7 and 10 only (`realBmr_congr`): through `BmrReal.bmrPart_realView` it is the published part
  of `BMR.realOut` at `bmrCoinsOf coins table`, whose pads and masks are read from the site answers of the pad and
  mask sites (`bmrPadsOf_congr`, `bmrMasksOf_congr`), and the answers at the visible P45 tags;
* the rest part `realRest` reads the input labels of the coins and the table at the visible rest tags
  (`realRest_pair`);
* the exception entries read the coins and the table at the finals, family 9 (`DigestSplit.realGarbled_exception`);
* the conversion material of `y` reads the table at keys of coordinate 1 only (`Paths.coordGarbleM_tagged`).

The four reads then follow from the family of each hidden tag set (`realReads`).
-/

import Proof.Privacy.CRT.Laws.CoreParts
import Proof.Privacy.CRT.Core.BmrReal
import Proof.Privacy.CRT.Core.DigestSplit
import Proof.Privacy.CRT.Swap.TargetLaw
import Proof.Privacy.CRT.Hidden.AlignEntry
import Proof.Privacy.CRT.Hidden.DeltaView

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Laws.P4Reads

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-- The entry's table. -/
abbrev Tb : CrtTable := Kriterion.CRT.Entry.table

/-! ### 1. Tables that agree at the P45 families -/

/-- Two tables agree at every position of family 6, 7 or 10. -/
def FamAgree (t t' : TagTable) : Prop :=
  ∀ p : Fin (2 ^ 40), (tagFamily p.val = 6 ∨ tagFamily p.val = 7 ∨ tagFamily p.val = 10) → t p = t' p

/-- A site of the real layout is read at positions of family 6 or 7 only. -/
theorem siteAnswers_congr {t t' : TagTable} (agree : FamAgree t t') {s : SiteId} (member : s ∈ crtLayout.sites) :
    Laws.siteAnswersOf crtLayout t s = Laws.siteAnswersOf crtLayout t' s := by
  unfold Laws.siteAnswersOf
  refine List.map_congr_left fun tag inside => ?_
  obtain ⟨famLt, inRange⟩ := Laws.RefillLayout.fields_inRange member
  rw [Laws.RefillLayout.siteTags_eq] at inside
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp inside
  have range := inRange j (List.mem_range.mp hj)
  have val := Laws.RefillLayout.tagPos_tagCode famLt range
  apply agree
  rw [val, tagFamily_tagCode range]
  rcases List.mem_append.mp member with pad | mask
  · obtain ⟨κ, i, ρ, rfl, -⟩ := Layout.mem_padSites pad
    exact Or.inl rfl
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, -⟩ | ⟨k, rfl, -⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)

/-- A table's pad values at a body site are the reading of its site answers. -/
theorem padValues_siteAnswers (t : TagTable) (κ : ℕ) (i : Fin Entry.table.count) (ρ : ℕ) :
    H8.padValues t κ i ρ = PadLaw.readList κ i (Laws.siteAnswersOf crtLayout t (.pad κ i.val ρ)) := by
  unfold H8.padValues PadLaw.readList
  refine congrArg _ (funext fun j => ?_)
  show _ = (((List.range (Layout.padCount κ i.val)).map fun j => tagCode Family.body κ i.val 0 0 ρ j).map
      fun tag => t (tagPos tag)).getD j.val (0, 0)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range j.isLt,
    Option.map_some, Option.map_some, Option.getD_some]
  rfl

theorem bmrPadsOf_congr {t t' : TagTable} (agree : FamAgree t t') :
    BmrEntry.bmrPadsOf t = BmrEntry.bmrPadsOf t' := by
  funext i ρ e
  cases e with
  | inl x =>
      show H8.padValues t 0 i ρ.val _ = H8.padValues t' 0 i ρ.val _
      rw [padValues_siteAnswers, padValues_siteAnswers,
        siteAnswers_congr agree (PadLaw.pad_mem_sites (by norm_num) i (ZMod.val_lt ρ))]
  | inr y =>
      show H8.padValues t 1 i ρ.val _ = H8.padValues t' 1 i ρ.val _
      rw [padValues_siteAnswers, padValues_siteAnswers,
        siteAnswers_congr agree (PadLaw.pad_mem_sites (by norm_num) i (ZMod.val_lt ρ))]

theorem bmrMasksOf_congr {t t' : TagTable} (agree : FamAgree t t') :
    BmrEntry.bmrMasksOf t = BmrEntry.bmrMasksOf t' := by
  rw [TargetLaw.bmrMasksOf_eq, TargetLaw.bmrMasksOf_eq, TargetLaw.maskValues_eq, TargetLaw.maskValues_eq,
    TargetLaw.mvOfDraws_congr fun s mask => siteAnswers_congr agree (List.mem_append_right _ mask)]

theorem restrictBmr_congr (u : AffineInput) {t t' : TagTable} (agree : FamAgree t t') :
    BmrSplit.restrictBmr u t = BmrSplit.restrictBmr u t' := by
  funext tag
  exact agree tag.1.1 tag.2

/-! ### 2. The real P45 part -/

section Real

variable [FieldCertificate] [GroupCertificate]

/-- The real P45 part at a pair tape. -/
theorem realBmr_pair (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (c : crtEntry.Coins)
    (t : TagTable) :
    Laws.realBmr Tb parameter scalar u (c, t) =
      BmrSplit.bmrOf u (BMR.realOut (BmrEntry.bmrContextOf scalar c) u (BmrEntry.bmrCoinsOf c t))
        (BmrSplit.restrictBmr u t) := by
  rw [← Laws.bmrPart_realView]
  exact BmrReal.bmrPart_realView parameter scalar u (c, t)

/-- **The real P45 part reads the coins off the input labels and the exception pads, and the table at the families
6, 7 and 10.** -/
theorem realBmr_congr (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) {c c' : crtEntry.Coins}
    {t t' : TagTable} (offsets : c.offsets = c'.offsets) (points : c.pointRandomness = c'.pointRandomness)
    (bridge : c.bridgeKey = c'.bridgeKey) (mask : c.curveMask = c'.curveMask) (r1 : c.curveR1 = c'.curveR1)
    (r2 : c.curveR2 = c'.curveR2) (agree : FamAgree t t') :
    Laws.realBmr Tb parameter scalar u (c, t) = Laws.realBmr Tb parameter scalar u (c', t') := by
  rw [realBmr_pair, realBmr_pair]
  have ctx : BmrEntry.bmrContextOf scalar c = BmrEntry.bmrContextOf scalar c' :=
    BmrSplit.bmrContextOf_congr scalar (show BmrSplit.ctxPart c = BmrSplit.ctxPart c' by
      unfold BmrSplit.ctxPart
      rw [offsets, points])
  have coins : BmrEntry.bmrCoinsOf c t = BmrEntry.bmrCoinsOf c' t' := by
    unfold BmrEntry.bmrCoinsOf
    simp only [bmrPadsOf_congr agree, bmrMasksOf_congr agree, points, bridge, mask, r1, r2]
  rw [ctx, coins, restrictBmr_congr u agree]

/-! ### 3. The real rest part, the exception entries, the conversion material of `y` -/

/-- The real rest part at a pair tape. -/
theorem realRest_pair (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (c : crtEntry.Coins)
    (t : TagTable) :
    Laws.realRest Tb parameter scalar u (c, t) =
      ((crtEntry.scheme inferInstance inferInstance).encode c.inputMacKey u,
        fun tag : RestTags Tb u => t tag.1.1) := by
  unfold Laws.realRest
  rw [show realGarbled crtEntry parameter scalar (c, t) = _ from BmrReal.realGarbled_pair parameter scalar c t]

theorem inputMacKey_congr {c c' : crtEntry.Coins} (zero : c.inputZero = c'.inputZero)
    (delta : c.inputDelta = c'.inputDelta) : c.inputMacKey = c'.inputMacKey := by
  unfold Kriterion.ArgoMAC.Scheme.Coins.inputMacKey
  rw [zero, delta]

/-- **The real rest part reads the input labels and the table at the visible rest tags.** -/
theorem realRest_congr (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) {c c' : crtEntry.Coins}
    {t t' : TagTable} (zero : c.inputZero = c'.inputZero) (delta : c.inputDelta = c'.inputDelta)
    (agree : ∀ tag : RestTags Tb u, t tag.1.1 = t' tag.1.1) :
    Laws.realRest Tb parameter scalar u (c, t) = Laws.realRest Tb parameter scalar u (c', t') := by
  rw [realRest_pair, realRest_pair, inputMacKey_congr zero delta]
  exact congrArg _ (funext agree)

theorem finalPos_family (s : ℕ) (small : s < 65536) : tagFamily (DigestSplit.finalPos s).val = 9 := by
  rw [DigestSplit.finalPos_val s small]
  exact tagFamily_tagCode ⟨by decide, by decide, by decide, by decide, small, by decide⟩

/-- **The exception entries read the coins and the table at the finals.** -/
theorem exception_congr (parameter : ℕ) (scalar : NonZeroScalar) (c : crtEntry.Coins) {t t' : TagTable}
    (agree : ∀ p : Fin (2 ^ 40), tagFamily p.val = 9 → t p = t' p) :
    (realGarbled crtEntry parameter scalar (c, t)).1.exception =
      (realGarbled crtEntry parameter scalar (c, t')).1.exception := by
  rw [DigestSplit.realGarbled_exception, DigestSplit.realGarbled_exception]
  refine congrArg Vector.ofFn (funext fun o => ?_)
  dsimp only
  have h0 : 2 * o.val < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  have h1 : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  rw [agree _ (finalPos_family _ h0), agree _ (finalPos_family _ h1)]

/-- **The conversion material of `y` reads the table at keys of coordinate 1 only.** -/
theorem crtY_congr (parameter : ℕ) (scalar : NonZeroScalar) (c : crtEntry.Coins) {t t' : TagTable}
    (agree : ∀ p : Fin (2 ^ 40), tagCoord p.val = 1 → t p = t' p) :
    (realGarbled crtEntry parameter scalar (c, t)).1.crtY =
      (realGarbled crtEntry parameter scalar (c, t')).1.crtY := by
  rw [ConvSplit.realGarbled_crtY, ConvSplit.realGarbled_crtY]
  dsimp only
  refine congrArg _ (congrArg _ (BmrReal.eval_congr_asked _ _ _ fun n asked => ?_))
  have tagged := Paths.coordGarbleM_tagged Entry.table Entry.yCount 1 (Paths.bn254_ranges _ (by decide))
    (by norm_num) (c.inputDelta .y) (atNat (c.inputZero .y) 0)
  obtain ⟨k, member, range, label, rfl⟩ := Align.asked_of_tagged tagged _ n asked
  have small := Paths.TagKey.code_lt range
  show DeltaView.hashOf t (hashInput label k.code) = DeltaView.hashOf t' (hashInput label k.code)
  rw [DeltaView.hashOf_hashInput t label k.code small, DeltaView.hashOf_hashInput t' label k.code small]
  apply agree
  show tagCoord (tagCode k.fam k.coord k.idx k.stage k.level k.slot k.part) = 1
  rw [tagCoord_tagCode (Align.tagInRange_of_key range)]
  exact member.2

/-! ### 4. The families of the hidden tags -/

/-- A visible tag of a family below 7 is cold. -/
theorem hot_false_of_visible (u : AffineInput) {tag : ℕ} (visible : visTag Tb u tag = true)
    (low : tagFamily tag ≤ 6) : hotTag Tb u tag = false := by
  unfold visTag at visible
  split at visible <;> first | omega | simpa using visible

/-- A visible digest label is the label of `u`'s bit. -/
theorem part_of_visible (u : AffineInput) {tag : ℕ} (visible : visTag Tb u tag = true) (eight : tagFamily tag = 8) :
    tagPart tag = inputBit u (tagCoord tag) (tagSlot tag) := by
  unfold visTag at visible
  simp only [eight] at visible
  simpa using visible

/-- The doubling event reads the coins only. -/
theorem doubling_congr (scalar : NonZeroScalar) (u : AffineInput) (c : crtEntry.Coins) (t t' : TagTable) :
    Doubling crtEntry scalar (c, t) u ↔ Doubling crtEntry scalar (c, t') u :=
  BmrSplit.doubling_congr scalar u t t' rfl

end Real

end

end Kriterion.CRT.Privacy.Laws.P4Reads

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open Kriterion.CRT.Privacy.Laws.P4Reads

noncomputable section

open Classical in
/-- **The real reads.** -/
theorem realReads : RealReads Entry.table := by
  intro _ _ parameter scalar u
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨c, t⟩ ⟨c', t'⟩ same agree
    dsimp only at same agree ⊢
    subst same
    have fam : FamAgree t t' := fun p families => agree p fun hot => by
      obtain ⟨low, -, -⟩ := hot
      omega
    have rest : ∀ tag : RestTags Tb u, t tag.1.1 = t' tag.1.1 := fun tag => agree _ fun hot => by
      obtain ⟨low, -, isHot⟩ := hot
      rw [hot_false_of_visible u tag.1.2 (by omega)] at isHot
      exact absurd isHot (by decide)
    by_cases D : Doubling crtEntry scalar (c, t) u
    · rw [if_pos D, if_pos ((doubling_congr scalar u c t t').mp D)]
    · rw [if_neg D, if_neg fun D' => D ((doubling_congr scalar u c t t').mpr D'),
        crtY_congr parameter scalar c (t' := t') fun p coord => agree p fun hot => by
          obtain ⟨-, coordZero, -⟩ := hot
          omega,
        exception_congr parameter scalar c (t' := t') fun p nine => agree p fun hot => by
          obtain ⟨low, -, -⟩ := hot
          omega,
        realRest_congr parameter scalar u rfl rfl rest,
        realBmr_congr parameter scalar u rfl rfl rfl rfl rfl rfl fam]
  · rintro ⟨c, t⟩ ⟨c', t'⟩ same agree
    dsimp only at same agree ⊢
    subst same
    have fam : FamAgree t t' := fun p families => agree p fun hot => by
      obtain ⟨low, -, -⟩ := hot
      omega
    have rest : ∀ tag : RestTags Tb u, t tag.1.1 = t' tag.1.1 := fun tag => agree _ fun hot => by
      obtain ⟨low, -, isHot⟩ := hot
      rw [hot_false_of_visible u tag.1.2 (by omega)] at isHot
      exact absurd isHot (by decide)
    by_cases D : Doubling crtEntry scalar (c, t) u
    · rw [if_pos D, if_pos ((doubling_congr scalar u c t t').mp D)]
    · rw [if_neg D, if_neg fun D' => D ((doubling_congr scalar u c t t').mpr D'),
        exception_congr parameter scalar c (t' := t') fun p nine => agree p fun hot => by
          obtain ⟨low, -, -⟩ := hot
          omega,
        realRest_congr parameter scalar u rfl rfl rest,
        realBmr_congr parameter scalar u rfl rfl rfl rfl rfl rfl fam]
  · rintro ⟨c, t⟩ ⟨c', t'⟩ same agree
    dsimp only at same agree ⊢
    obtain ⟨offsets, points, bridge, mask, r1, r2, zero, delta⟩ := same
    have fam : FamAgree t t' := fun p families => agree p fun hidden => by
      rcases hidden with nine | ⟨eight, -⟩ <;> omega
    have rest : ∀ tag : RestTags Tb u, t tag.1.1 = t' tag.1.1 := fun tag => agree _ fun hidden => by
      rcases hidden with nine | ⟨eight, other⟩
      · rcases tag.2 with low | eight' <;> omega
      · exact other (part_of_visible u tag.1.2 eight)
    exact Prod.ext (realRest_congr parameter scalar u zero delta rest)
      (realBmr_congr parameter scalar u offsets points bridge mask r1 r2 fam)
  · rintro ⟨c, t⟩ ⟨c', t'⟩ same agree
    dsimp only at same agree ⊢
    obtain ⟨offsets, points, -, bridge, mask, r1, r2⟩ := same
    exact realBmr_congr parameter scalar u offsets points bridge mask r1 r2 fun p families =>
      agree p fun hidden => by
        obtain ⟨-, restFam⟩ := hidden
        omega

end

end Kriterion.CRT.Privacy.Laws
