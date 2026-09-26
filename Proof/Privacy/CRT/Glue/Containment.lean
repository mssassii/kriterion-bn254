/-
**`OnDecomp` for the CRT entry** (the on-curve input of `crtEntry_middleFactor`,
`Proof/Privacy/CRT/Laws/MiddleCrt.lean`).

At an input `u` on the curve and a source, `P` is the set of the tags of `u`'s 508 digest labels and `ds` their
inputs. The reach's transcript on the view's table is the full replay's inputs, then `u`'s digest labels, then the 91
finals; the filter keeps the first two (the replay's conversion inputs are cold, `ReplayCold.lean`; on the curve the
key and the masks are visible; the labels are at `u`'s bits) and drops the finals (`viewEntries_eq`). So the entries
off `ds` are the replay's (`restEntries_eq`), and the rest is the view table at `ds`.

The containment: route M's private state after its replay stores the table's answers at exactly the replay's inputs
(`ReplayPoints.lean`: every site it touches is asked whole), and the collector programs store the drawn answers at the
collector points. The full replay asks the same conversion inputs and key (the two hashes agree at them), the same
non-collector sites, and every collector site, where the view's table holds the drawn answers (`programmedTable_hit`).

The containment is proved over an abstract view table and hash (`lookup_core`), with the key and the input sets
compared by `keyOf_congr` and `mem_entryReplay` on abstract hashes (an `unfold`
of `keyOf` on the concrete tables evaluates the conversion program and exhausts memory).
-/

import Proof.Privacy.CRT.Glue.ContainParts

namespace Kriterion.CRT.Privacy.Contain

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_askN asked_tableM hashInput_div asked_of_tagged
  tagFamily_key ftranscript transcript_toProgram ftranscript_liftHash ftranscript_bind_pure asked_digestKeyM
  asked_digestEvalM digestLabelTag_fields inputBit_eq_coordBit maskKeyTag_family)
open Kriterion.CRT.Privacy.Laws
open Kriterion.CRT.Privacy.H8 (visTag viewTable viewEntries programmedTable collectorTag tagHash CoreView)
open Kriterion.CRT.Privacy.PublicFirst (viewHere)
open Kriterion.CRT.Paths (TagKey Tagged)
open Kriterion.ArgoMAC.PlanB (digitCount)

set_option autoImplicit false

noncomputable section

/-! ### Inputs and tags -/

section Tags

theorem labelled_tag {n : ℕ} (labelled : Paths.SameVisible.Labelled n) : n / 2 ^ 128 < 2 ^ 40 := by
  obtain ⟨k, range, label, rfl⟩ := labelled
  rw [hashInput_div]
  exact TagKey.code_lt range

/-- The tag position of a labelled input, as a table position. -/
theorem tagOfInput_labelled {n : ℕ} (labelled : Paths.SameVisible.Labelled n) :
    tagOfInput (n : BaseField) = tagPos (n / 2 ^ 128) :=
  tagOfInput_small labelled.val

theorem tagPos_val {τ : ℕ} (small : τ < 2 ^ 40) : (tagPos τ).val = τ := Nat.mod_eq_of_lt small

/-- The digest labels' inputs at `u`, coordinate, then position. -/
def digestList (labels : LamportSignature) (u : AffineInput) : List ℕ :=
  (List.finRange 2).flatMap fun c => (List.finRange coordinateBitCount).flatMap fun p =>
    [hashInput (Kriterion.CRT.Entry.labelsOf labels c p) (digestLabelTag c.val p.val (coordBit u c p.val))]

theorem digestList_eq (H : HashN) (labels : LamportSignature) (u : AffineInput) :
    asked H (digestKeyM coordinateBitCount (Kriterion.CRT.Entry.labelsOf labels) u) = digestList labels u :=
  asked_digestKeyM H _ _ _

theorem mem_digestList {labels : LamportSignature} {u : AffineInput} {n : ℕ} (inside : n ∈ digestList labels u) :
    ∃ c : Fin 2, ∃ p : Fin coordinateBitCount,
      n = hashInput (Kriterion.CRT.Entry.labelsOf labels c p) (digestLabelTag c.val p.val (coordBit u c p.val)) := by
  unfold digestList at inside
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at inside
  obtain ⟨c, p, rfl⟩ := inside
  exact ⟨c, p, rfl⟩

theorem digestLabel_range (u : AffineInput) (c : Fin 2) (p : Fin coordinateBitCount) :
    TagInRange c.val 0 0 0 p.val (coordBit u c p.val) :=
  ⟨c.isLt, by norm_num, by norm_num, by norm_num, lt_of_lt_of_le p.isLt (by decide),
    lt_of_lt_of_le (Paths.coordBit_lt u c p.val) (by norm_num)⟩

theorem digestList_labelled {labels : LamportSignature} {u : AffineInput} {n : ℕ} (inside : n ∈ digestList labels u) :
    Paths.SameVisible.Labelled n ∧ tagFamily (n / 2 ^ 128) = 8 ∧
      visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true := by
  obtain ⟨c, p, rfl⟩ := mem_digestList inside
  have range := digestLabel_range u c p
  have bit := Paths.coordBit_lt u c p.val
  obtain ⟨hf, hcoord, hslot, hpart⟩ := digestLabelTag_fields (b := coordBit u c p.val) c.isLt
    (lt_of_lt_of_le p.isLt (by decide)) (by omega)
  refine ⟨⟨⟨8, c.val, 0, 0, 0, p.val, coordBit u c p.val⟩, ⟨by norm_num, range.coord, range.idx, range.stage,
    range.level, range.slot, range.part⟩, _, rfl⟩, ?_, ?_⟩
  · rw [hashInput_div]
    exact hf
  · rw [hashInput_div, Paths.SameVisible.visTag_label hf, hcoord, hslot, hpart, inputBit_eq_coordBit]
    exact beq_self_eq_true _

end Tags

/-! ### The full replay's inputs on the curve -/

section Replay

variable (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature)

theorem replayConv_facts (H : HashN) :
    ∀ n ∈ asked H (Kriterion.CRT.Entry.replayConv pub u labels),
      Paths.SameVisible.Labelled n ∧ tagFamily (n / 2 ^ 128) ≤ 6 ∧ hotTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = false := by
  intro n inside
  obtain ⟨k, member, range, label, same⟩ := asked_of_tagged (Paths.replayConv_tagged pub u labels) H n inside
  refine ⟨⟨k, range, label, same⟩, ?_, replayConv_cold pub u labels H n inside⟩
  rw [same, hashInput_div, tagFamily_key range]
  exact Paths.replayConvKeys_fam k member

theorem maskTag_fields {st k j : ℕ} (hst : st < 4) (hk : k < 65536) (hj : j < 64) :
    tagFamily (maskTag st k j) = 7 ∧ tagStage (maskTag st k j) = st ∧ tagSlot (maskTag st k j) = k ∧
      tagPart (maskTag st k j) = j := by
  have range : TagInRange 0 0 st 0 k j := ⟨by norm_num, by norm_num, hst, by norm_num, hk, hj⟩
  unfold maskTag
  exact ⟨tagFamily_tagCode range, tagStage_tagCode range, tagSlot_tagCode range, tagPart_tagCode range⟩

theorem maskTag_labelled (K : Block) {st k j : ℕ} (hst : st < 4) (hk : k < 65536) (hj : j < 64) :
    Paths.SameVisible.Labelled (hashInput K (maskTag st k j)) :=
  ⟨⟨7, 0, 0, st, 0, k, j⟩, ⟨by norm_num, by norm_num, by norm_num, hst, by norm_num, hk, hj⟩, K, rfl⟩

theorem keyInput_labelled (t : BaseField) : Paths.SameVisible.Labelled (maskKeyInput t) :=
  ⟨Paths.keyKey, Paths.keyKey_range, _, rfl⟩

theorem keyInput_family (t : BaseField) : tagFamily (maskKeyInput t / 2 ^ 128) = 10 := by
  unfold maskKeyInput
  rw [hashInput_div]
  exact maskKeyTag_family

theorem mem_nonCollector {H : HashN} {K : Block} {n : ℕ} (inside : n ∈ asked H (nonCollectorMasksM K digitCount)) :
    ∃ k j, k < 228 ∧ j < 3 ∧ n = hashInput K (maskTag 1 k j) := by
  rw [asked_nonCollectorMasksM] at inside
  have pairs : pairSites digitCount = 227 := by decide
  have single : singleSites digitCount = 1 := by decide
  rw [if_pos single, List.mem_append] at inside
  rcases inside with inPairs | inSingle
  · obtain ⟨k, _, x_in⟩ := List.mem_flatMap.mp inPairs
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp x_in
    exact ⟨k.val, j.val, by have := k.isLt; omega, j.isLt, rfl⟩
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp inSingle
    exact ⟨pairSites digitCount, j.val, by omega, by have := j.isLt; omega, rfl⟩

theorem mem_collector {H : HashN} {K : Block} {n : ℕ} (inside : n ∈ asked H (collectorMasksM K digitCount)) :
    ∃ k j, k < 273 ∧ j < 2 ∧ n = hashInput K (maskTag 0 k j) := by
  rw [asked_collectorMasksM] at inside
  obtain ⟨k, _, x_in⟩ := List.mem_flatMap.mp inside
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp x_in
  exact ⟨k.val, j.val, k.isLt, j.isLt, rfl⟩

end Replay


/-! ### The full replay on the curve: labelled, visible, never a digest label -/

section Visible

variable (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature)

theorem entryReplay_facts (valid : validate u = true) (H : HashN) :
    ∀ n ∈ asked H (Kriterion.CRT.Entry.replay pub u labels),
      Paths.SameVisible.Labelled n ∧ visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true ∧
        tagFamily (n / 2 ^ 128) ≠ 8 := by
  intro n inside
  rw [asked_entryReplay, List.mem_append, List.mem_cons, List.mem_append] at inside
  rcases inside with inConv | inKey | inCollector | inRest
  · obtain ⟨labelled, family, cold⟩ := replayConv_facts pub u labels H n inConv
    refine ⟨labelled, ?_, by omega⟩
    rw [Paths.SameVisible.visTag_conv family, cold]
    rfl
  · subst inKey
    refine ⟨keyInput_labelled _, ?_, by rw [keyInput_family]; decide⟩
    rw [Paths.SameVisible.visTag_keyMask (Or.inr (keyInput_family _)), valid]
  · obtain ⟨k, j, hk, hj, rfl⟩ := mem_collector (H := H) inCollector
    have fields := maskTag_fields (st := 0) (by norm_num) (show k < 65536 by omega) (show j < 64 by omega)
    refine ⟨maskTag_labelled _ (by norm_num) (by omega) (by omega), ?_, ?_⟩
    · rw [hashInput_div, Paths.SameVisible.visTag_keyMask (Or.inl fields.1), valid]
    · rw [hashInput_div, fields.1]
      decide
  · obtain ⟨k, j, hk, hj, rfl⟩ := mem_nonCollector (H := H) inRest
    have fields := maskTag_fields (st := 1) (by norm_num) (show k < 65536 by omega) (show j < 64 by omega)
    refine ⟨maskTag_labelled _ (by norm_num) (by omega) (by omega), ?_, ?_⟩
    · rw [hashInput_div, Paths.SameVisible.visTag_keyMask (Or.inl fields.1), valid]
    · rw [hashInput_div, fields.1]
      decide

theorem digestFinal_invisible (key : Block) {o : ℕ} (ho : o < 65536) :
    visTag Kriterion.CRT.Entry.table u (hashInput key (digestFinalTag o) / 2 ^ 128) = false := by
  have range : TagInRange 0 0 0 0 o 0 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, ho, by norm_num⟩
  rw [hashInput_div]
  unfold digestFinalTag
  exact Paths.SameVisible.visTag_final (tagFamily_tagCode range)

end Visible

/-! ### The reach's transcript on a table -/

section Transcript

variable [FieldCertificate] [GroupCertificate]

/-- The transcript entry of an input on a table oracle. -/
def mkEntry (Vt : TagTable) (n : ℕ) : Entry Empty Empty := ⟨.hash (n : BaseField), Vt (tagOfInput (n : BaseField))⟩

theorem reach_transcript (Vt : TagTable) (pub : Kriterion.CRT.Entry.Public) (u : AffineInput)
    (labels : LamportSignature) :
    programTranscript (publicAnswer (tableOracle (FI := Empty) (EI := Empty) Vt))
        (EntryReading.reachProgram pub u labels) =
      (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) Vt)) (Paths.reachDecodedCM pub u labels)).map
        (mkEntry Vt) := by
  have boundedCM : (liftHash (FixedIndex := Empty) (EncIndex := Empty)
      (Paths.reachDecodedCM pub u labels)).Bounded Kriterion.CRT.Entry.evaluateBudget :=
    Paths.reachDecodedM_eq pub u labels ▸ EntryReading.bounded_reachDecodedM pub u labels
  have same : programTranscript (publicAnswer (tableOracle (FI := Empty) (EI := Empty) Vt))
      (EntryReading.reachProgram pub u labels) =
      programTranscript (publicAnswer (tableOracle (FI := Empty) (EI := Empty) Vt))
        (FreeQuery.toProgram (liftHash (Paths.reachDecodedCM pub u labels)) Kriterion.CRT.Entry.evaluateBudget
          boundedCM) := by
    unfold EntryReading.reachProgram
    exact Paths.ReachTranscript.transcript_eq (Paths.reachDecodedM_eq pub u labels) _ _ _
  rw [same, transcript_toProgram, ftranscript_liftHash]
  rfl

theorem asked_reachDecodedCM (H : HashN) (pub : Kriterion.CRT.Entry.Public) (u : AffineInput)
    (labels : LamportSignature) (valid : validate u = true) :
    asked H (Paths.reachDecodedCM pub u labels) =
      asked H (Kriterion.CRT.Entry.replay pub u labels) ++
        (digestList labels u ++ (List.finRange digitCount).flatMap fun o =>
          [hashInput (digestKey H coordinateBitCount (Kriterion.CRT.Entry.labelsOf labels) u) (digestFinalTag o.val)]) := by
  unfold Paths.reachDecodedCM
  rw [if_pos valid]
  unfold Kriterion.CRT.Entry.reachCM
  simp only [asked_bind, asked_pure, List.append_nil, asked_digestEvalM, digestList_eq]

end Transcript

/-! ### The view's entries for the CRT entry -/

section View

variable [FieldCertificate] [GroupCertificate] (source : Kriterion.CRT.Entry.Source) (u : AffineInput)

/-- The view's table of a table and draws. -/
abbrev vtOf (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) : TagTable :=
  viewTable Instance.crtEntry Kriterion.CRT.Entry.table u (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn)

theorem vtOf_apply (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (τ : Fin (2 ^ 40)) :
    vtOf source u table drawn τ =
      if visTag Kriterion.CRT.Entry.table u τ.val = true then programmedTable table drawn τ else (0, 0) := by
  unfold vtOf viewTable
  split <;> simp_all

/-- `u`'s digest-label inputs, as field elements. -/
def dsOf : List BaseField := (digestList (Kriterion.CRT.Entry.labels source u) u).map fun n : ℕ => (n : BaseField)

/-- The replay part of the view's entries. -/
def replayEntries (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    List (Entry Empty Empty) :=
  (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)))
    (Kriterion.CRT.Entry.replay (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u))).map
      (mkEntry (vtOf source u table drawn))

/-- **The view's entries**: the full replay's, then `u`'s digest labels. -/
theorem viewEntries_eq (valid : validate u = true) (table : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    viewEntries Instance.crtEntry Kriterion.CRT.Entry.table u
        (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn) =
      replayEntries source u table drawn ++ (digestList (Kriterion.CRT.Entry.labels source u) u).map
        (mkEntry (vtOf source u table drawn)) := by
  unfold viewEntries
  show (programTranscript (publicAnswer (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)))
      (EntryReading.reachProgram (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u))).filter _ = _
  rw [reach_transcript, asked_reachDecodedCM _ _ _ _ valid, List.map_append, List.map_append, List.filter_append,
    List.filter_append, List.filter_eq_self.mpr ?replay, List.filter_eq_self.mpr ?digest,
    List.filter_eq_nil_iff.mpr ?finals, List.append_nil]
  · rfl
  case replay =>
    intro e member
    obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨labelled, visible, _⟩ := entryReplay_facts _ u _ valid _ n inside
    show visTag Kriterion.CRT.Entry.table u ((n : BaseField).val / 2 ^ 128) = true
    rw [labelled.val]
    exact visible
  case digest =>
    intro e member
    obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨labelled, _, visible⟩ := digestList_labelled inside
    show visTag Kriterion.CRT.Entry.table u ((n : BaseField).val / 2 ^ 128) = true
    rw [labelled.val]
    exact visible
  case finals =>
    intro e member
    obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨o, _, n_in⟩ := List.mem_flatMap.mp inside
    rw [List.mem_singleton] at n_in
    subst n_in
    have ho : o.val < 65536 := lt_of_lt_of_le o.isLt (by decide)
    have labelled : Paths.SameVisible.Labelled (hashInput (digestKey (schemeHash (tableOracle (FI := Empty)
        (EI := Empty) (vtOf source u table drawn))) coordinateBitCount
        (Kriterion.CRT.Entry.labelsOf (Kriterion.CRT.Entry.labels source u)) u) (digestFinalTag o.val)) :=
      ⟨⟨9, 0, 0, 0, 0, o.val, 0⟩, ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ho,
        by norm_num⟩, _, rfl⟩
    show ¬ (visTag Kriterion.CRT.Entry.table u (((hashInput _ (digestFinalTag o.val) : ℕ) : BaseField).val / 2 ^ 128)
      = true)
    rw [labelled.val, digestFinal_invisible u _ ho]
    decide

theorem cast_ne_of_family {n d : ℕ} (labelledN : Paths.SameVisible.Labelled n)
    (labelledD : Paths.SameVisible.Labelled d) (famN : tagFamily (n / 2 ^ 128) ≠ 8)
    (famD : tagFamily (d / 2 ^ 128) = 8) : (n : BaseField) ≠ (d : BaseField) := fun same => by
  have values := congrArg ZMod.val same
  rw [labelledN.val, labelledD.val] at values
  subst values
  exact famN famD

/-- **The entries off `ds` are the full replay's.** -/
theorem restEntries_eq (valid : validate u = true) (table : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    restEntries Instance.crtEntry Kriterion.CRT.Entry.table u (dsOf source u)
        (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn) =
      replayEntries source u table drawn := by
  unfold restEntries
  rw [viewEntries_eq source u valid, List.filter_append]
  have none : List.filter (fun e : Entry Empty Empty => decide (entryInput e ∉ dsOf source u))
      ((digestList (Kriterion.CRT.Entry.labels source u) u).map (mkEntry (vtOf source u table drawn))) = [] := by
    refine List.filter_eq_nil_iff.mpr fun e member => ?_
    obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
    simp only [decide_eq_true_eq, not_not]
    exact List.mem_map.mpr ⟨n, inside, rfl⟩
  rw [none, List.append_nil]
  refine List.filter_eq_self.mpr fun e member => ?_
  unfold replayEntries at member
  obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
  obtain ⟨labelled, _, family⟩ := entryReplay_facts _ u _ valid _ n inside
  simp only [decide_eq_true_eq]
  intro inDs
  obtain ⟨d, dIn, same⟩ := List.mem_map.mp inDs
  obtain ⟨labelledD, famD, _⟩ := digestList_labelled dIn
  exact cast_ne_of_family labelled labelledD family famD same.symm

theorem tableEntries_eq (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    tableEntries (FI := Empty) (EI := Empty) (vtOf source u table drawn) (dsOf source u) =
      (digestList (Kriterion.CRT.Entry.labels source u) u).map (mkEntry (vtOf source u table drawn)) := by
  unfold tableEntries dsOf
  rw [List.map_map]
  exact List.map_congr_left fun n _ => rfl

end View

/-! ### The two hashes agree at the replay's inputs -/

section Agree

variable [FieldCertificate] [GroupCertificate] (source : Kriterion.CRT.Entry.Source) (u : AffineInput)

theorem collectorTag_ne {τ : ℕ} (small : τ < 2 ^ 40) (off : tagFamily τ ≠ 7 ∨ tagStage τ ≠ 0) (k j : ℕ)
    (hk : k < 273) (hj : j < 2) : tagPos τ ≠ collectorTag k j := fun same => by
  have fields := collectorTag_fields (show k < 65536 by omega) (show j < 64 by omega)
  have vals : τ = (collectorTag k j).val := by rw [← same, tagPos_val small]
  rw [← vals] at fields
  rcases off with f | s
  · exact f fields.1
  · exact s fields.2.1

/-- The collectors' tags of a draw. -/
theorem drawnTag_ne (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) {τ : ℕ} (small : τ < 2 ^ 40)
    (off : tagFamily τ ≠ 7 ∨ tagStage τ ≠ 0) :
    ∀ e ∈ drawn, ∀ j, j < 2 → tagPos τ ≠ collectorTag (collectorIndex e.1) j :=
  fun e _ j hj => collectorTag_ne small off _ j (collectorIndex_lt e.1) hj

/-- **The view's table is the table at a visible input off the collectors.** -/
theorem hash_agree (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) {n : ℕ}
    (labelled : Paths.SameVisible.Labelled n) (visible : visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true)
    (off : tagFamily (n / 2 ^ 128) ≠ 7 ∨ tagStage (n / 2 ^ 128) ≠ 0) :
    schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)) n = tagHash table n := by
  show vtOf source u table drawn (tagOfInput (n : BaseField)) = table (tagPos (n / 2 ^ 128))
  rw [tagOfInput_labelled labelled, vtOf_apply, tagPos_val (labelled_tag labelled), if_pos visible]
  exact programmedTable_off _ drawn table (drawnTag_ne drawn (labelled_tag labelled) off)

theorem conv_agree (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (pub : Kriterion.CRT.Entry.Public) (labels : LamportSignature) :
    ∀ n ∈ asked (tagHash table) (Kriterion.CRT.Entry.replayConv pub u labels),
      tagHash table n = schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)) n := by
  intro n inside
  obtain ⟨labelled, family, cold⟩ := replayConv_facts pub u labels _ n inside
  refine (hash_agree source u table drawn labelled ?_ (Or.inl (by omega))).symm
  rw [Paths.SameVisible.visTag_conv family, cold]
  rfl

end Agree

/-! ### The containment -/

section Containment

variable [FieldCertificate] [GroupCertificate] (source : Kriterion.CRT.Entry.Source) (u : AffineInput)

theorem viewReplay_key (H : HashN) (pub : Kriterion.CRT.Entry.Public) (labels : LamportSignature) :
    (((Instance.view).replayProgram pub u labels).eval H).key = keyOf H pub u labels := by
  unfold RouteMView.replayProgram keyOf
  dsimp only [Instance.view]
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, eval_askN, EntryReading.keyField_val]

theorem finOf_lookup (table : TagTable) (y : BaseField) :
    (finOf Instance.crtEntry table source u).hash.lookup y =
      if y ∈ runPoints crtLayout table ((Instance.view).replayProgram (Kriterion.CRT.Entry.publish source) u
          (Kriterion.CRT.Entry.labels source u))
      then some (Fintype.equivFin (Block × Block) (table (tagOfInput y))) else none :=
  ((tableRun_empty (FI := Empty) (EI := Empty) crtLayout crtLayout_points table
    (Paths.replay_canonical (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u))).2.2.2 y)

theorem requestAnswer_some {requests : List (BaseField × (Block × Block))} {y : BaseField} {a : Block × Block}
    (found : requestAnswer requests y = some a) : (y, a) ∈ requests := by
  unfold requestAnswer at found
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp found
  have same := List.find?_some hr
  simp only [decide_eq_true_eq] at same
  rw [← same]
  exact List.mem_of_find?_eq_some hr

theorem requestAnswer_none {requests : List (BaseField × (Block × Block))} {y : BaseField}
    (missing : requestAnswer requests y = none) : ∀ r ∈ requests, r.1 ≠ y := by
  unfold requestAnswer at missing
  rw [Option.map_eq_none_iff, List.find?_eq_none] at missing
  intro r inside same
  exact missing r inside (by simp [same])

theorem mem_programRequests {K : Block} {drawn : List (BMR.Collector × ((Block × Block × Block) × Block))}
    {r : BaseField × (Block × Block)} (inside : r ∈ programRequests K drawn) :
    ∃ e ∈ drawn, (r.1 = collectorPoint K (collectorIndex e.1) 0 ∧ r.2 = (e.2.1.1, e.2.1.2.1)) ∨
      (r.1 = collectorPoint K (collectorIndex e.1) 1 ∧ r.2 = (e.2.1.2.2, e.2.2)) := by
  unfold programRequests at inside
  obtain ⟨e, member, r_in⟩ := List.mem_flatMap.mp inside
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at r_in
  rcases r_in with rfl | rfl
  · exact ⟨e, member, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨e, member, Or.inr ⟨rfl, rfl⟩⟩

theorem collector_drawn {drawn : List (BMR.Collector × ((Block × Block × Block) × Block))}
    (complete : drawn.map Prod.fst = collectorList) {k : ℕ} (hk : k < 273) :
    ∃ e ∈ drawn, collectorIndex e.1 = k := by
  have inRange : k ∈ collectorList.map collectorIndex := by
    rw [collectorList_indices]
    exact List.mem_range.mpr hk
  rw [← complete, List.map_map] at inRange
  obtain ⟨e, member, same⟩ := List.mem_map.mp inRange
  exact ⟨e, member, same⟩

theorem drawn_distinct {drawn : List (BMR.Collector × ((Block × Block × Block) × Block))}
    (complete : drawn.map Prod.fst = collectorList) : (drawn.map fun e => collectorIndex e.1).Nodup := by
  have same : (drawn.map fun e => collectorIndex e.1) = collectorList.map collectorIndex := by
    rw [← complete, List.map_map]
    rfl
  rw [same, collectorList_indices]
  exact List.nodup_range

theorem collectorPoint_eq (K : Block) (k j : ℕ) :
    collectorPoint K k j = ((hashInput K (maskTag 0 k j) : ℕ) : BaseField) := rfl

theorem tagOfInput_collector (K : Block) {k j : ℕ} (hk : k < 273) (hj : j < 2) :
    tagOfInput (collectorPoint K k j) = collectorTag k j := by
  rw [collectorPoint_eq, tagOfInput_labelled (maskTag_labelled K (by norm_num) (by omega) (by omega)), hashInput_div]
  rfl

/-- The inputs of route M's replay are labelled and off the collectors' tags. -/
theorem viewReplay_off (H : HashN) (pub : Kriterion.CRT.Entry.Public) (labels : LamportSignature) :
    ∀ n ∈ asked H ((Instance.view).replayProgram pub u labels),
      Paths.SameVisible.Labelled n ∧ (tagFamily (n / 2 ^ 128) ≠ 7 ∨ tagStage (n / 2 ^ 128) ≠ 0) := by
  intro n inside
  rw [asked_viewReplay, List.mem_append, List.mem_cons] at inside
  rcases inside with inConv | inKey | inRest
  · obtain ⟨labelled, family, _⟩ := replayConv_facts pub u labels H n inConv
    exact ⟨labelled, Or.inl (by omega)⟩
  · subst inKey
    exact ⟨keyInput_labelled _, Or.inl (by rw [keyInput_family]; decide)⟩
  · obtain ⟨k, j, hk, hj, rfl⟩ := mem_nonCollector (H := H) inRest
    have fields := maskTag_fields (st := 1) (by norm_num) (show k < 65536 by omega) (show j < 64 by omega)
    refine ⟨maskTag_labelled _ (by norm_num) (by omega) (by omega), Or.inr ?_⟩
    rw [hashInput_div, fields.2.1]
    decide

/-- **The key agrees** on two hashes that agree on the conversion's value and at the key input. -/
theorem keyOf_congr (H H' : HashN) (pub : Kriterion.CRT.Entry.Public) (labels : LamportSignature)
    (conv : (Kriterion.CRT.Entry.replayConv pub u labels).eval H' =
      (Kriterion.CRT.Entry.replayConv pub u labels).eval H)
    (atKey : H' (maskKeyInput (Kriterion.CRT.Entry.curveOutput pub u
        ((Kriterion.CRT.Entry.replayConv pub u labels).eval H))) =
      H (maskKeyInput (Kriterion.CRT.Entry.curveOutput pub u ((Kriterion.CRT.Entry.replayConv pub u labels).eval H)))) :
    keyOf H' pub u labels = keyOf H pub u labels := by
  show (H' (maskKeyInput (Kriterion.CRT.Entry.curveOutput pub u
      ((Kriterion.CRT.Entry.replayConv pub u labels).eval H')))).1 =
    (H (maskKeyInput (Kriterion.CRT.Entry.curveOutput pub u ((Kriterion.CRT.Entry.replayConv pub u labels).eval H)))).1
  rw [conv, atKey]

/-- **The full replay's inputs** on `H'` are route M's on `H` and the collectors', when the two hashes give the same
conversion and key. -/
theorem mem_entryReplay (H H' : HashN) (pub : Kriterion.CRT.Entry.Public) (labels : LamportSignature)
    (convAsked : asked H' (Kriterion.CRT.Entry.replayConv pub u labels) =
      asked H (Kriterion.CRT.Entry.replayConv pub u labels))
    (convEval : (Kriterion.CRT.Entry.replayConv pub u labels).eval H' =
      (Kriterion.CRT.Entry.replayConv pub u labels).eval H)
    (keyAgree : keyOf H' pub u labels = keyOf H pub u labels) (n : ℕ) :
    n ∈ asked H' (Kriterion.CRT.Entry.replay pub u labels) ↔
      n ∈ asked H ((Instance.view).replayProgram pub u labels) ∨
        n ∈ asked H (collectorMasksM (keyOf H pub u labels) digitCount) := by
  rw [asked_entryReplay, asked_viewReplay, convAsked, convEval, keyAgree, asked_collectorMasksM,
    asked_nonCollectorMasksM, asked_collectorMasksM, asked_nonCollectorMasksM]
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((h | h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

/-- A collector point of a complete draw is programmed. -/
theorem collector_requested {K : Block} {drawn : List (BMR.Collector × ((Block × Block × Block) × Block))}
    (complete : drawn.map Prod.fst = collectorList) {k j : ℕ} (hk : k < 273) (hj : j < 2) :
    ∃ r ∈ programRequests K drawn, r.1 = collectorPoint K k j := by
  obtain ⟨e, member, idx⟩ := collector_drawn complete hk
  have two : j = 0 ∨ j = 1 := by omega
  rcases two with rfl | rfl
  · refine ⟨(collectorPoint K k 0, (e.2.1.1, e.2.1.2.1)), ?_, rfl⟩
    unfold programRequests
    refine List.mem_flatMap.mpr ⟨e, member, ?_⟩
    rw [idx]
    exact List.mem_cons_self
  · refine ⟨(collectorPoint K k 1, (e.2.1.2.2, e.2.2)), ?_, rfl⟩
    unfold programRequests
    refine List.mem_flatMap.mpr ⟨e, member, ?_⟩
    rw [idx]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A collector point is an input of the collector masks. -/
theorem collectorPoint_asked (H : HashN) (K : Block) {k j : ℕ} (hk : k < 273) (hj : j < 2) :
    collectorPoint K k j ∈ (asked H (collectorMasksM K digitCount)).map (fun n : ℕ => (n : BaseField)) := by
  refine List.mem_map.mpr ⟨hashInput K (maskTag 0 k j), ?_, rfl⟩
  rw [asked_collectorMasksM]
  exact List.mem_flatMap.mpr ⟨⟨k, hk⟩, List.mem_finRange _, List.mem_map.mpr ⟨⟨j, hj⟩, List.mem_finRange _, rfl⟩⟩

/-- **The containment, abstractly**: after route M's replay and the collector programs, a lookup is the full
replay's input set on the view's hash, answered by the view's table. -/
theorem lookup_core (pub : Kriterion.CRT.Entry.Public) (labels : LamportSignature) (table vt : TagTable)
    (Hv : HashN) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (fin installed : LazyOracle.State Empty Empty)
    (memA : ∀ n, n ∈ asked Hv (Kriterion.CRT.Entry.replay pub u labels) ↔
      n ∈ asked (tagHash table) ((Instance.view).replayProgram pub u labels) ∨
        n ∈ asked (tagHash table) (collectorMasksM (keyOf (tagHash table) pub u labels) digitCount))
    (finLookup : ∀ y, fin.hash.lookup y =
      if y ∈ runPoints crtLayout table ((Instance.view).replayProgram pub u labels)
      then some (Fintype.equivFin (Block × Block) (table (tagOfInput y))) else none)
    (complete : drawn.map Prod.fst = collectorList)
    (done : programHashAll (programRequests (keyOf (tagHash table) pub u labels) drawn) fin = some installed)
    (agreeRun : ∀ n ∈ asked (tagHash table) ((Instance.view).replayProgram pub u labels),
      vt (tagOfInput (n : BaseField)) = table (tagOfInput (n : BaseField)))
    (hit : ∀ e ∈ drawn, vt (collectorTag (collectorIndex e.1) 0) = (e.2.1.1, e.2.1.2.1) ∧
      vt (collectorTag (collectorIndex e.1) 1) = (e.2.1.2.2, e.2.2)) (y : BaseField) :
    installed.hash.lookup y =
      if y ∈ (asked Hv (Kriterion.CRT.Entry.replay pub u labels)).map (fun n : ℕ => (n : BaseField))
      then some (Fintype.equivFin (Block × Block) (vt (tagOfInput y))) else none := by
  obtain ⟨_, lookupInstalled⟩ := programHashAll_lookup _ _ _ done
  rw [lookupInstalled y]
  cases hreq : requestAnswer (programRequests (keyOf (tagHash table) pub u labels) drawn) y with
  | some a =>
    obtain ⟨e, member, which⟩ := mem_programRequests (requestAnswer_some hreq)
    have hk := collectorIndex_lt e.1
    have collIn : ∀ j, j < 2 → y = collectorPoint (keyOf (tagHash table) pub u labels) (collectorIndex e.1) j →
        y ∈ (asked Hv (Kriterion.CRT.Entry.replay pub u labels)).map (fun n : ℕ => (n : BaseField)) := by
      intro j hj hy
      obtain ⟨n, inside, same⟩ := List.mem_map.mp (collectorPoint_asked (tagHash table) _ hk hj)
      exact List.mem_map.mpr ⟨n, (memA n).mpr (Or.inr inside), same.trans hy.symm⟩
    dsimp only
    rcases which with ⟨hy, ha⟩ | ⟨hy, ha⟩
    · have hy' : y = collectorPoint (keyOf (tagHash table) pub u labels) (collectorIndex e.1) 0 := hy
      have ha' : a = (e.2.1.1, e.2.1.2.1) := ha
      rw [if_pos (collIn 0 (by norm_num) hy'), hy', tagOfInput_collector _ hk (by norm_num), (hit e member).1, ha']
    · have hy' : y = collectorPoint (keyOf (tagHash table) pub u labels) (collectorIndex e.1) 1 := hy
      have ha' : a = (e.2.1.2.2, e.2.2) := ha
      rw [if_pos (collIn 1 (by norm_num) hy'), hy', tagOfInput_collector _ hk (by norm_num), (hit e member).2, ha']
  | none =>
    rw [finLookup y]
    by_cases run : y ∈ runPoints crtLayout table ((Instance.view).replayProgram pub u labels)
    · rw [if_pos run]
      obtain ⟨n, inside, rfl⟩ := (runPoints_iff pub u labels table y).mp run
      rw [if_pos (List.mem_map.mpr ⟨n, (memA n).mpr (Or.inl inside), rfl⟩), agreeRun n inside]
    · rw [if_neg run, if_neg]
      intro inList
      obtain ⟨n, inside, rfl⟩ := List.mem_map.mp inList
      rcases (memA n).mp inside with inRun | inColl
      · exact run ((runPoints_iff pub u labels table _).mpr ⟨n, inRun, rfl⟩)
      · obtain ⟨k, j, hk, hj, rfl⟩ := mem_collector (H := tagHash table) inColl
        obtain ⟨r, inReq, hr⟩ := collector_requested (K := keyOf (tagHash table) pub u labels) complete hk hj
        exact requestAnswer_none hreq r inReq (hr.trans (collectorPoint_eq _ k j))

/-- Installing the entries of a function at a list on the empty state. -/
theorem install_empty_lookup (g : BaseField → Block × Block) (xs : List BaseField) (y : BaseField) :
    (Privacy.installEntries (xs.map fun x => (⟨.hash x, g x⟩ : Entry Empty Empty)) LazyOracle.empty).hash.lookup y =
      if y ∈ xs then some (Fintype.equivFin (Block × Block) (g y)) else none := by
  rw [installEntries_map_lookup]
  rfl

theorem replayEntries_eq (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    replayEntries source u table drawn =
      ((asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)))
        (Kriterion.CRT.Entry.replay (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u))).map
          (fun n : ℕ => (n : BaseField))).map
        (fun x => (⟨.hash x, vtOf source u table drawn (tagOfInput x)⟩ : Entry Empty Empty)) := by
  rw [replayEntries, List.map_map]
  rfl

/-- The inputs of route M's replay are visible on the curve. -/
theorem viewReplay_visible (valid : validate u = true) (H : HashN) (pub : Kriterion.CRT.Entry.Public)
    (labels : LamportSignature) :
    ∀ n ∈ asked H ((Instance.view).replayProgram pub u labels),
      visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true ∧ tagFamily (n / 2 ^ 128) ≠ 8 := by
  intro n inside
  rw [asked_viewReplay, List.mem_append, List.mem_cons] at inside
  rcases inside with inConv | inKey | inRest
  · obtain ⟨_, family, cold⟩ := replayConv_facts pub u labels H n inConv
    refine ⟨?_, by omega⟩
    rw [Paths.SameVisible.visTag_conv family, cold]
    rfl
  · subst inKey
    refine ⟨?_, by rw [keyInput_family]; decide⟩
    rw [Paths.SameVisible.visTag_keyMask (Or.inr (keyInput_family _)), valid]
  · obtain ⟨k, j, hk, hj, rfl⟩ := mem_nonCollector (H := H) inRest
    have fields := maskTag_fields (st := 1) (by norm_num) (show k < 65536 by omega) (show j < 64 by omega)
    refine ⟨?_, ?_⟩
    · rw [hashInput_div, Paths.SameVisible.visTag_keyMask (Or.inl fields.1), valid]
    · rw [hashInput_div, fields.1]
      decide

/-- **The containment**: after the replay and the collector programs, the private state has the lookups of the
view's entries off `ds` (the full replay's entries). -/
theorem containment (valid : validate u = true) (table : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State Empty Empty)
    (complete : drawn.map Prod.fst = collectorList)
    (done : programHashAll (programRequests (outOf Instance.crtEntry table source u).key drawn)
      (finOf Instance.crtEntry table source u) = some installed) (y : BaseField) :
    installed.hash.lookup y =
      (Privacy.installEntries (replayEntries source u table drawn) LazyOracle.empty).hash.lookup y := by
  have keyEq : (outOf Instance.crtEntry table source u).key =
      keyOf (tagHash table) (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u) :=
    viewReplay_key u (tagHash table) _ _
  rw [keyEq] at done
  obtain ⟨convAsked, convEval⟩ := Paths.SameVisible.asked_congr (tagHash table)
    (schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)))
    (Kriterion.CRT.Entry.replayConv (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u))
    (conv_agree source u table drawn _ _)
  have atKey := hash_agree source u table drawn (keyInput_labelled (Kriterion.CRT.Entry.curveOutput
      (Kriterion.CRT.Entry.publish source) u ((Kriterion.CRT.Entry.replayConv (Kriterion.CRT.Entry.publish source) u
        (Kriterion.CRT.Entry.labels source u)).eval (tagHash table))))
    (by rw [Paths.SameVisible.visTag_keyMask (Or.inr (keyInput_family _)), valid])
    (Or.inl (by rw [keyInput_family]; decide))
  have keyAgree := keyOf_congr u (tagHash table)
    (schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)))
    (Kriterion.CRT.Entry.publish source) (Kriterion.CRT.Entry.labels source u) convEval atKey
  have memA := mem_entryReplay u (tagHash table)
    (schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u table drawn)))
    (Kriterion.CRT.Entry.publish source) (Kriterion.CRT.Entry.labels source u) convAsked convEval keyAgree
  have agreeRun : ∀ n ∈ asked (tagHash table) ((Instance.view).replayProgram (Kriterion.CRT.Entry.publish source) u
      (Kriterion.CRT.Entry.labels source u)),
      vtOf source u table drawn (tagOfInput (n : BaseField)) = table (tagOfInput (n : BaseField)) := by
    intro n inside
    obtain ⟨labelled, off⟩ := viewReplay_off u (tagHash table) _ _ n inside
    have visible := (viewReplay_visible u valid (tagHash table) _ _ n inside).1
    have agree := hash_agree source u table drawn labelled visible off
    calc vtOf source u table drawn (tagOfInput (n : BaseField)) = tagHash table n := agree
      _ = table (tagPos (n / 2 ^ 128)) := rfl
      _ = table (tagOfInput (n : BaseField)) := by rw [tagOfInput_labelled labelled]
  have hit : ∀ e ∈ drawn, vtOf source u table drawn (collectorTag (collectorIndex e.1) 0) = (e.2.1.1, e.2.1.2.1) ∧
      vtOf source u table drawn (collectorTag (collectorIndex e.1) 1) = (e.2.1.2.2, e.2.2) := by
    intro e member
    have visible : ∀ j, j < 2 → visTag Kriterion.CRT.Entry.table u (collectorTag (collectorIndex e.1) j).val = true := by
      intro j hj
      have fields := collectorTag_fields (lt_trans (collectorIndex_lt e.1) (by norm_num)) (show j < 64 by omega)
      rw [Paths.SameVisible.visTag_keyMask (Or.inl fields.1), valid]
    have both := programmedTable_hit drawn table (drawn_distinct complete) e member
    rw [vtOf_apply, if_pos (visible 0 (by norm_num)), vtOf_apply, if_pos (visible 1 (by norm_num))]
    exact both
  rw [replayEntries_eq, install_empty_lookup]
  exact lookup_core u _ _ table _ _ drawn _ installed memA (finOf_lookup source u table) complete done agreeRun hit y

end Containment

end

end Kriterion.CRT.Privacy.Contain
