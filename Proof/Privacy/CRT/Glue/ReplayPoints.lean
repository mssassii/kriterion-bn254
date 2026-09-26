/-
**The points of route M's private replay** (for `OnDecomp` of (B)).

`HW`'s private replay stores, at a pad or mask site, the whole site at the query's label (`stepState`). This file
shows that the replay asks every point of every site it touches, so the points the table run stores are exactly the
inputs it asks (`runPoints_iff`):

* the asked inputs of the mask programs, which do not depend on the hash (`asked_siteAnswersM`,
  `asked_collectorMasksM`, `asked_nonCollectorMasksM`), and of route M's replay and of the full replay
  (`asked_viewReplay`, `asked_entryReplay`);
* `SiteClosed p`: along every path, every point of a site of an asked input is asked, with its combinators; the pad
  vectors and the mask sites are whole sites of `crtLayout`, and the conversion blocks ask no site;
* **`runPoints_iff`**: for route M's replay on any table, a point is stored exactly when the replay asks it.
-/

import Proof.Privacy.CRT.Glue.ReplayCold
import Proof.Privacy.CRT.Paths.Refill
import Proof.Privacy.CRT.Paths.SameVisible

namespace Kriterion.CRT.Privacy.Contain

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_askN asked_tableM asked_padVectorM
  asked_materializeM hashInput_div flatMap_singleton_eq_map asked_of_tagged tagFamily_key)
open Kriterion.CRT.Privacy.Laws (runPoints pointsOf Canonical tableFinal)
open Kriterion.CRT.Privacy.Layout (padS padCount layoutAnswers tableFacts)
open Kriterion.ArgoMAC.PlanB (digitCount)

/-! ### The mask programs and the two replays -/

section Asked

variable (H : HashN)

theorem asked_siteAnswersM (K : Block) (stage site count : ℕ) :
    asked H (siteAnswersM K stage site count) =
      (List.finRange count).map fun j => hashInput K (maskTag stage site j.val) := by
  unfold siteAnswersM
  rw [asked_tableM]
  simp only [asked_askN]
  exact flatMap_singleton_eq_map _ _

theorem asked_collectorMasksM (K : Block) (digits : ℕ) :
    asked H (collectorMasksM K digits) = (List.finRange (collectorSites digits)).flatMap fun c =>
      (List.finRange 2).map fun j => hashInput K (maskTag 0 c.val j.val) := by
  unfold collectorMasksM
  rw [asked_tableM]
  simp only [asked_bind, asked_siteAnswersM, asked_pure, List.append_nil]

theorem asked_nonCollectorMasksM (K : Block) (digits : ℕ) :
    asked H (nonCollectorMasksM K digits) =
      ((List.finRange (pairSites digits)).flatMap fun k =>
        (List.finRange 3).map fun j => hashInput K (maskTag 1 k.val j.val)) ++
      (if singleSites digits = 1 then
        (List.finRange 2).map fun j => hashInput K (maskTag 1 (pairSites digits) j.val) else []) := by
  unfold nonCollectorMasksM pairMasksM singleMaskM
  simp only [asked_bind, asked_tableM, asked_siteAnswersM, asked_pure, List.append_nil]
  split <;> simp only [asked_bind, asked_siteAnswersM, asked_pure, List.append_nil]

/-- The key `K` the replays derive from their conversion value on `H`. -/
def keyOf (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature) : Block :=
  (H (maskKeyInput (Kriterion.CRT.Entry.curveOutput pub u ((Kriterion.CRT.Entry.replayConv pub u labels).eval H)))).1

/-- **Route M's replay asks** its conversion blocks, the key and the non-collector mask sites. -/
theorem asked_viewReplay [FieldCertificate] [GroupCertificate] (published : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : LamportSignature) :
    asked H ((Instance.view).replayProgram published u labels) =
      asked H (Kriterion.CRT.Entry.replayConv published u labels) ++
        (maskKeyInput (Kriterion.CRT.Entry.curveOutput published u
            ((Kriterion.CRT.Entry.replayConv published u labels).eval H)) ::
          asked H (nonCollectorMasksM (keyOf H published u labels) digitCount)) := by
  unfold RouteMView.replayProgram keyOf
  dsimp only [Instance.view]
  simp only [asked_bind, asked_askN, asked_pure, List.append_nil, EntryReading.nonCollectorReplay,
    EntryReading.keyField_val, List.singleton_append, eval_askN, FreeQuery.eval_bind, FreeQuery.eval_pure]

/-- **The full replay asks** its conversion blocks, the key, the collector sites and the non-collector sites. -/
theorem asked_entryReplay (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature) :
    asked H (Kriterion.CRT.Entry.replay pub u labels) =
      asked H (Kriterion.CRT.Entry.replayConv pub u labels) ++
        (maskKeyInput (Kriterion.CRT.Entry.curveOutput pub u ((Kriterion.CRT.Entry.replayConv pub u labels).eval H)) ::
          (asked H (collectorMasksM (keyOf H pub u labels) digitCount) ++
            asked H (nonCollectorMasksM (keyOf H pub u labels) digitCount))) := by
  unfold Kriterion.CRT.Entry.replay maskAnswersM keyM keyOf
  simp only [asked_bind, asked_askN, asked_pure, List.append_nil, List.singleton_append, FreeQuery.eval_bind,
    FreeQuery.eval_pure, eval_askN]

end Asked

/-! ### Site closure -/

section Closed

variable {α β : Type}

/-- Every point of the site of an input of the list, read at the input's label, is an input of the list. -/
def ClosedList (l : List ℕ) : Prop :=
  ∀ x ∈ l, ∀ site, siteOf (x / 2 ^ 128) = some site → ∀ y ∈ sitePoints crtLayout site (x % 2 ^ 128),
    ∃ z ∈ l, y = (z : BaseField)

theorem ClosedList.append {l l' : List ℕ} (first : ClosedList l) (second : ClosedList l') : ClosedList (l ++ l') := by
  intro x inside site decode y member
  rcases List.mem_append.mp inside with a | b
  · obtain ⟨z, zin, same⟩ := first x a site decode y member
    exact ⟨z, List.mem_append_left _ zin, same⟩
  · obtain ⟨z, zin, same⟩ := second x b site decode y member
    exact ⟨z, List.mem_append_right _ zin, same⟩

theorem ClosedList.flatMap {ι : Type} (index : List ι) (f : ι → List ℕ) (each : ∀ i ∈ index, ClosedList (f i)) :
    ClosedList (index.flatMap f) := by
  intro x inside site decode y member
  obtain ⟨i, imem, xin⟩ := List.mem_flatMap.mp inside
  obtain ⟨z, zin, same⟩ := each i imem x xin site decode y member
  exact ⟨z, List.mem_flatMap.mpr ⟨i, imem, zin⟩, same⟩

theorem ClosedList.of_nonSite {l : List ℕ} (none : ∀ x ∈ l, siteOf (x / 2 ^ 128) = none) : ClosedList l := by
  intro x inside site decode
  rw [none x inside] at decode
  cases decode

/-- Along every path, the asked inputs are closed under sites. -/
def SiteClosed (program : CM α) : Prop := ∀ H : HashN, ClosedList (asked H program)

namespace SiteClosed

theorem pure' (value : α) : SiteClosed (Pure.pure value : CM α) := fun H => by
  rw [asked_pure]
  exact ClosedList.of_nonSite fun _ inside => absurd inside List.not_mem_nil

theorem bind {program : CM α} {next : α → CM β} (first : SiteClosed program) (second : ∀ a, SiteClosed (next a)) :
    SiteClosed (program >>= next) := fun H => by
  rw [asked_bind]
  exact (first H).append (second _ H)

theorem tableM {count : ℕ} {program : Fin count → CM α} (each : ∀ i, SiteClosed (program i)) :
    SiteClosed (Kriterion.CRT.tableM count program) := fun H => by
  rw [asked_tableM]
  exact ClosedList.flatMap _ _ fun i _ => each i H

theorem ite {c : Prop} [Decidable c] {yes no : CM α} (onYes : c → SiteClosed yes) (onNo : ¬ c → SiteClosed no) :
    SiteClosed (if c then yes else no) := by
  split
  · exact onYes ‹_›
  · exact onNo ‹_›

theorem of_tagged {program : CM α} {S : Set Paths.TagKey} (tagged : Paths.Tagged S program)
    (fams : ∀ k ∈ S, k.fam ≠ 6 ∧ k.fam ≠ 7) : SiteClosed program := fun H => by
  refine ClosedList.of_nonSite fun x inside => ?_
  obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged tagged H x inside
  rw [hashInput_div]
  unfold siteOf
  rw [tagFamily_key range]
  obtain ⟨six, seven⟩ := fams k member
  split <;> simp_all

end SiteClosed

/-- A labelled input reads back its label. -/
theorem hashInput_mod (label : Block) (tag : ℕ) : hashInput label tag % 2 ^ 128 = label.toNat := by
  unfold hashInput
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt label.isLt]

/-- **A whole site at one label**: the queries at the label and the site's tags are closed. -/
theorem closedList_site (label : Block) (site : SiteId) (tags : List ℕ) (tagsEq : siteTags crtLayout site = tags)
    (decode : ∀ tag ∈ tags, siteOf tag = some site) :
    ClosedList (tags.map fun tag => hashInput label tag) := by
  intro x inside site' decode' y member
  obtain ⟨tag, tagIn, rfl⟩ := List.mem_map.mp inside
  rw [hashInput_div, decode tag tagIn] at decode'
  cases decode'
  rw [hashInput_mod] at member
  unfold sitePoints at member
  rw [tagsEq] at member
  obtain ⟨tag', tagIn', rfl⟩ := List.mem_map.mp member
  exact ⟨hashInput label tag', List.mem_map.mpr ⟨tag', tagIn', rfl⟩, rfl⟩

end Closed

/-! ### The sites of the real layout -/

section Sites

theorem siteOf_bodyTag {κ i r j : ℕ} (hκ : κ < 2) (hi : i < 128) (hr : r < 65536) (hj : j < 64) :
    siteOf (bodyTag κ i r j) = some (.pad κ i r) := by
  have range : TagInRange κ i 0 0 r j := ⟨hκ, hi, by norm_num, by norm_num, hr, hj⟩
  unfold siteOf bodyTag
  rw [tagFamily_tagCode range, tagCoord_tagCode range, tagIdx_tagCode range, tagSlot_tagCode range]
  rfl

theorem siteOf_maskTag {st k j : ℕ} (hst : st < 4) (hk : k < 65536) (hj : j < 64) :
    siteOf (maskTag st k j) = some (.mask st k) := by
  have range : TagInRange 0 0 st 0 k j := ⟨by norm_num, by norm_num, hst, by norm_num, hk, hj⟩
  unfold siteOf maskTag
  rw [tagFamily_tagCode range, tagStage_tagCode range, tagSlot_tagCode range]
  rfl

theorem siteTags_pad (κ i r : ℕ) :
    siteTags crtLayout (.pad κ i r) = (List.range (padCount κ i)).map fun j => bodyTag κ i r j := rfl

theorem siteTags_mask (st k : ℕ) :
    siteTags crtLayout (.mask st k) = (List.range (layoutAnswers (.mask st k))).map fun j => maskTag st k j := rfl

theorem padCount_eq (κ : ℕ) (hκ : κ < 2) (S : ℕ) (hS : S = padS κ) (i : Fin Kriterion.CRT.Entry.table.count) :
    padCount κ i.val = Kriterion.CRT.Entry.table.padAnswers S i := by
  unfold padCount
  rw [dif_pos i.isLt, hS]

/-- **A body's pad vectors are whole pad sites.** -/
theorem bodyEvalM_closed (κ : ℕ) (hκ : κ < 2) (S : ℕ) (hS : S = padS κ) (i : Fin Kriterion.CRT.Entry.table.count)
    (final : Fin (Kriterion.CRT.Entry.table.modulus i) → Block) (hot : ℕ) (joins : Fin S → ℕ) :
    SiteClosed (bodyEvalM (Kriterion.CRT.Entry.table.modulus i) S (Kriterion.CRT.Entry.table.padAnswers S i) κ i.val
      final hot joins) := by
  have hi : i.val < 128 := lt_of_lt_of_le i.isLt (by decide)
  have hm : Kriterion.CRT.Entry.table.modulus i < 65536 :=
    lt_of_le_of_lt (Paths.bn254_modulus_le i) (by norm_num)
  have hq : Kriterion.CRT.Entry.table.padAnswers S i < 64 := by
    rw [← padCount_eq κ hκ S hS i]
    have facts := tableFacts κ hκ i.val (lt_of_lt_of_eq i.isLt Paths.bn254_count)
    exact facts.2.2.2.2.2
  unfold bodyEvalM
  refine SiteClosed.bind (SiteClosed.tableM fun r => ?_) fun _ => SiteClosed.pure' _
  refine SiteClosed.ite (fun _ => SiteClosed.pure' _) fun _ => ?_
  intro H
  unfold padVectorM
  rw [asked_bind, asked_pure, List.append_nil, Align.asked_hlongM]
  have listEq : ((List.finRange (Kriterion.CRT.Entry.table.padAnswers S i)).map fun j =>
      hashInput (final r) (bodyTag κ i.val r.val j.val)) =
      ((List.range (padCount κ i.val)).map fun j => bodyTag κ i.val r.val j).map fun tag => hashInput (final r) tag := by
    rw [padCount_eq κ hκ S hS i, List.map_map, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [listEq]
  refine closedList_site (final r) (.pad κ i.val r.val) _ (siteTags_pad κ i.val r.val) fun tag tagIn => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp tagIn
  rw [List.mem_range, padCount_eq κ hκ S hS i] at hj
  exact siteOf_bodyTag hκ hi (lt_trans r.isLt hm) (lt_trans hj hq)

/-- **The non-collector mask sites are whole sites.** -/
theorem nonCollectorMasksM_closed (K : Block) : SiteClosed (nonCollectorMasksM K digitCount) := fun H => by
  rw [asked_nonCollectorMasksM]
  have pairs : pairSites digitCount = 227 := by decide
  have single : singleSites digitCount = 1 := by decide
  rw [if_pos single]
  refine ClosedList.append (ClosedList.flatMap _ _ fun k _ => ?_) ?_
  · have kLt : k.val < 227 := lt_of_lt_of_eq k.isLt pairs
    have answers : layoutAnswers (.mask 1 k.val) = 3 := by
      show (if k.val = 227 then 2 else 3) = 3
      rw [if_neg (by omega)]
    have listEq : ((List.finRange 3).map fun j => hashInput K (maskTag 1 k.val j.val)) =
        ((List.range (layoutAnswers (.mask 1 k.val))).map fun j => maskTag 1 k.val j).map
          fun tag => hashInput K tag := by
      rw [answers, List.map_map, ← List.map_coe_finRange_eq_range, List.map_map]
      rfl
    rw [listEq]
    refine closedList_site K (.mask 1 k.val) _ (siteTags_mask 1 k.val) fun tag tagIn => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp tagIn
    rw [List.mem_range, answers] at hj
    exact siteOf_maskTag (by norm_num) (by omega) (by omega)
  · have listEq : ((List.finRange 2).map fun j => hashInput K (maskTag 1 (pairSites digitCount) j.val)) =
        ((List.range (layoutAnswers (.mask 1 227))).map fun j => maskTag 1 227 j).map fun tag => hashInput K tag := by
      have answers : layoutAnswers (.mask 1 227) = 2 := rfl
      rw [answers, pairs, List.map_map, ← List.map_coe_finRange_eq_range, List.map_map]
      rfl
    rw [listEq]
    refine closedList_site K (.mask 1 227) _ (siteTags_mask 1 227) fun tag tagIn => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp tagIn
    rw [List.mem_range] at hj
    have : layoutAnswers (.mask 1 227) = 2 := rfl
    exact siteOf_maskTag (by norm_num) (by norm_num) (by omega)

end Sites

/-! ### The replay is closed -/

section Replay

theorem modEvalM_closed (κ : ℕ) (hκ : κ < 2) (S : ℕ) (hS : S = padS κ) (pub : ConvPublic)
    (joins : Fin Kriterion.CRT.Entry.table.count → Fin S → ℕ) (v : ℕ)
    (chunks : ℕ → ChunkEval Kriterion.CRT.Entry.table.castWidth) (i : Fin Kriterion.CRT.Entry.table.count) :
    SiteClosed (modEvalM Kriterion.CRT.Entry.table S κ pub joins v chunks i) := by
  have ranges := Paths.bn254_ranges S (by rw [hS]; unfold padS; split <;> norm_num)
  have hi : i.val < 128 := lt_of_lt_of_le i.isLt ranges.count
  unfold modEvalM
  dsimp only
  split
  · exact bodyEvalM_closed κ hκ S hS i _ _ _
  · rename_i row kind
    refine SiteClosed.bind (fun H => ?_) fun word => ?_
    · rw [asked_materializeM]
      exact ClosedList.of_nonSite fun _ inside => absurd inside List.not_mem_nil
    refine SiteClosed.bind (SiteClosed.of_tagged (Paths.conversionEvalM_tagged κ i.val row _ hκ hi
      (ranges.rows i row kind) (ranges.modulus i) _ word pub) fun k member => ?_) fun _ => bodyEvalM_closed κ hκ S hS i _ _ _
    simp only [Paths.convKeys, Set.mem_setOf_eq] at member
    omega

theorem coordEvalM_closed (κ : ℕ) (hκ : κ < 2) (S : ℕ) (hS : S = padS κ) (pub : ConvPublic) (records : Fin S → ℕ)
    (v : ℕ) (labels : ℕ → Block) :
    SiteClosed (coordEvalM Kriterion.CRT.Entry.table S κ pub records v labels) := by
  have ranges := Paths.bn254_ranges S (by rw [hS]; unfold padS; split <;> norm_num)
  unfold coordEvalM
  dsimp only
  refine SiteClosed.bind (SiteClosed.tableM fun c => ?_) fun _ => ?_
  · refine SiteClosed.of_tagged (Paths.chunkEvalM_tagged _ κ labels v _ _ c.val hκ
      (lt_of_lt_of_le c.isLt ranges.chunkCount) (ranges.chunkWidth c.val c.isLt) ranges.castAnswers)
      fun k member => ?_
    simp only [Paths.pairKeys, Set.mem_setOf_eq] at member
    omega
  · exact SiteClosed.bind (SiteClosed.tableM fun i => modEvalM_closed κ hκ S hS pub _ v _ i)
      fun _ => SiteClosed.pure' _

theorem replayConv_closed (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature) :
    SiteClosed (Kriterion.CRT.Entry.replayConv pub u labels) := by
  unfold Kriterion.CRT.Entry.replayConv
  exact SiteClosed.bind (coordEvalM_closed 0 (by norm_num) _ rfl _ _ _ _) fun _ =>
    SiteClosed.bind (coordEvalM_closed 1 (by norm_num) _ rfl _ _ _ _) fun _ => SiteClosed.pure' _

theorem keyInput_nonSite (t : BaseField) : siteOf (maskKeyInput t / 2 ^ 128) = none := by
  unfold maskKeyInput
  rw [hashInput_div]
  unfold siteOf
  rw [Align.maskKeyTag_family]
  rfl

/-- **Route M's replay is closed under sites.** -/
theorem viewReplay_closed [FieldCertificate] [GroupCertificate] (published : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : LamportSignature) :
    SiteClosed ((Instance.view).replayProgram published u labels) := fun H => by
  rw [asked_viewReplay]
  refine (replayConv_closed published u labels H).append ?_
  rw [← List.singleton_append]
  exact (ClosedList.of_nonSite fun x inside => by
    rw [List.mem_singleton.mp inside]
    exact keyInput_nonSite _).append (nonCollectorMasksM_closed _ H)

end Replay

/-! ### The points of the table run -/

section Run

theorem runPoints_eq (layout : SiteLayout) (T : TagTable) {α : Type} :
    ∀ R : CM α, runPoints layout T R = (asked (H8.tagHash T) R).flatMap (pointsOf layout)
  | .pure _ => rfl
  | .query n next => by
      show pointsOf layout n ++ runPoints layout T (next (H8.tagHash T n)) =
        (n :: asked (H8.tagHash T) (next (H8.tagHash T n))).flatMap (pointsOf layout)
      rw [List.flatMap_cons, runPoints_eq layout T (next (H8.tagHash T n))]

theorem canonical_asked (layout : SiteLayout) {α : Type} {R : CM α} (canon : Canonical layout R) (H : HashN) :
    ∀ n ∈ asked H R, ((n : BaseField)).val = n ∧
      ∀ site, siteOf (n / 2 ^ 128) = some site → site ∈ layout.sites ∧ n / 2 ^ 128 ∈ siteTags layout site := by
  induction canon with
  | pure value => intro n inside; exact absurd inside List.not_mem_nil
  | query m next small onSite rest ih =>
      intro n inside
      rcases List.mem_cons.mp inside with same | later
      · subst same
        exact ⟨small, onSite⟩
      · exact ih (H m) n later

/-- **The points of route M's replay are its inputs.** -/
theorem runPoints_iff [FieldCertificate] [GroupCertificate] (published : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : LamportSignature) (T : TagTable) (y : BaseField) :
    y ∈ runPoints crtLayout T ((Instance.view).replayProgram published u labels) ↔
      ∃ n ∈ asked (H8.tagHash T) ((Instance.view).replayProgram published u labels), y = (n : BaseField) := by
  have canon := canonical_asked crtLayout (Paths.replay_canonical published u labels) (H8.tagHash T)
  have closed := viewReplay_closed published u labels (H8.tagHash T)
  rw [runPoints_eq, List.mem_flatMap]
  constructor
  · rintro ⟨n, inside, member⟩
    unfold pointsOf at member
    split at member
    · rename_i none
      exact ⟨n, inside, List.mem_singleton.mp member⟩
    · rename_i site decode
      exact closed n inside site decode y member
  · rintro ⟨n, inside, rfl⟩
    refine ⟨n, inside, ?_⟩
    unfold pointsOf
    split
    · exact List.mem_singleton_self _
    · rename_i site decode
      exact Laws.self_mem_sitePoints crtLayout site n ((canon n inside).2 site decode).2

end Run

end Kriterion.CRT.Privacy.Contain
