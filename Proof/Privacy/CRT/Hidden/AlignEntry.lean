/-
**The reach against the garbler for the configuration-E entry** (P2a; `Hidden/Align.lean` for the
coordinate).

For every hash `H`, scalar, coins and input `u`, with the honest labels and the published value of the garbling:

* `replayConv_aligned`: the conversion layer of both coordinates, both directions, at the cold predicate
  `hotTag table u τ = false`;
* `garble_designed_reached`: every input the garbler asks whose tag the designed rule shows at `u` is asked by the
  reach (`Entry.reachCM`), which is `DesignedReached` on the program level.
-/

import Proof.Privacy.CRT.Hidden.Align
import Proof.Correctness.CRT.EntryCorrect
import Proof.Privacy.CRT.Paths.Entry
import Proof.Privacy.CRT.Designed

namespace Kriterion.CRT.Privacy.Align

open Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.EntryCorrect Kriterion.CRT.EntryDelivery

/-! ### Keys of a tag run -/

/-- Every input a tag run asks is a labelled input at a key of the run, in range. -/
theorem asked_of_keyRun {α : Type} {S : Set Paths.TagKey} {Q : α → List (Paths.TagKey × Block) → Prop}
    {seen : List (Paths.TagKey × Block)} {program : CM α} (run : Paths.KeyRun S Q seen program) (H : HashN) :
    ∀ x ∈ asked H program, ∃ k ∈ S, k.InRange ∧ ∃ label, x = hashInput label k.code := by
  induction run with
  | pure seen value post => intro x inside; exact absurd inside List.not_mem_nil
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
      intro x inside
      rcases List.mem_cons.mp inside with first | later
      · exact ⟨key, member, range, label, by rw [first, coded]⟩
      · exact ih _ x later

theorem asked_of_tagged {α : Type} {S : Set Paths.TagKey} {program : CM α} (tagged : Paths.Tagged S program)
    (H : HashN) : ∀ x ∈ asked H program, ∃ k ∈ S, k.InRange ∧ ∃ label, x = hashInput label k.code :=
  asked_of_keyRun tagged H

/-- The fields of a key in range, as `TagInRange`. -/
theorem tagInRange_of_key {k : Paths.TagKey} (range : k.InRange) :
    TagInRange k.coord k.idx k.stage k.level k.slot k.part := by
  obtain ⟨_, coord, idx, stage, level, slot, part⟩ := range
  exact ⟨coord, idx, stage, level, slot, part⟩

theorem tagFamily_key {k : Paths.TagKey} (range : k.InRange) : tagFamily k.code = k.fam :=
  tagFamily_tagCode (tagInRange_of_key range)

/-! ### The conversion layer of the entry -/

theorem table_inputBits : table.inputBits = 254 := rfl

theorem coordValue_zero (u : BN254.AffineInput) : coordValue u 0 = u.x.val := by simp [coordValue]

theorem coordValue_one (u : BN254.AffineInput) : coordValue u 1 = u.y.val := by simp [coordValue]

/-- **The replay's conversion layer** asks every cold conversion input of the garbler and nothing else. -/
theorem replayConv_aligned (H : HashN) (scalar : BN254.NonZeroScalar) (coins : Coins) (u : BN254.AffineInput) :
    Aligned (ColdAt fun τ => hotTag table u τ = false)
      (asked H (coordGarbleM table xCount 0 (coins.inputDelta .x) (atNat (coins.inputZero .x) 0)) ++
        asked H (coordGarbleM table yCount 1 (coins.inputDelta .y) (atNat (coins.inputZero .y) 0)))
      (asked H (replayConv (pubOf H scalar coins) u (labelsFor coins u))) := by
  have progX : coordEvalM table xCount 0 (convOf (pubOf H scalar coins).crtX)
      (fun e => ((pubOf H scalar coins).recX.get e).val) u.x.val (labelX (labelsFor coins u)) =
      coordEvalM table xCount 0 (gxOf H coins).pub ((gxOf H coins).records fun e => (slXOf H scalar coins e).val)
        u.x.val (fun j => atNat (coins.inputZero .x) 0 j ^^^ (if u.x.val.testBit j then coins.inputDelta .x else 0)) := by
    unfold labelsFor
    rw [show (fun e => ((pubOf H scalar coins).recX.get e).val) =
        (gxOf H coins).records (fun e => (slXOf H scalar coins e).val) from funext (pubOf_recX H scalar coins),
      coordEvalM_labels_congr table xCount 0 _ _ u.x.val _ _
        (fun j low => labelX_honest _ _ _ (coins_key_x coins) u j low),
      pubOf_crtX, FlatLayout.coordEvalM_congr table xCount 0 _ _ _ u.x.val _ (convAgree_convOf _)]
  have progY : coordEvalM table yCount 1 (convOf (pubOf H scalar coins).crtY)
      (fun e => ((pubOf H scalar coins).recY.get e).val) u.y.val (labelY (labelsFor coins u)) =
      coordEvalM table yCount 1 (gyOf H coins).pub ((gyOf H coins).records fun e => (slYOf H scalar coins e).val)
        u.y.val (fun j => atNat (coins.inputZero .y) 0 j ^^^ (if u.y.val.testBit j then coins.inputDelta .y else 0)) := by
    unfold labelsFor
    rw [show (fun e => ((pubOf H scalar coins).recY.get e).val) =
        (gyOf H coins).records (fun e => (slYOf H scalar coins e).val) from funext (pubOf_recY H scalar coins),
      coordEvalM_labels_congr table yCount 1 _ _ u.y.val _ _
        (fun j low => labelY_honest _ _ _ (coins_key_y coins) u j low),
      pubOf_crtY, FlatLayout.coordEvalM_congr table yCount 1 _ _ _ u.y.val _ (convAgree_convOf _)]
  have tagsX := coordTags_cold table u xCount 0 (by norm_num) (Paths.bn254_ranges _ (by decide))
  have tagsY := coordTags_cold table u yCount 1 (by norm_num) (Paths.bn254_ranges _ (by decide))
  rw [coordValue_zero] at tagsX
  rw [coordValue_one] at tagsY
  unfold replayConv
  simp only [asked_bind, asked_pure, List.append_nil]
  rw [progX, progY]
  refine Aligned.append ?_ ?_
  · exact coord_aligned H table xCount 0 (coins.inputDelta .x) (atNat (coins.inputZero .x) 0) _ u.x.val
      SliceC.bn254_correctTable (by rw [table_inputBits]; exact val_lt_two_pow _) _ tagsX
  · exact coord_aligned H table yCount 1 (coins.inputDelta .y) (atNat (coins.inputZero .y) 0) _ u.y.val
      SliceC.bn254_correctTable (by rw [table_inputBits]; exact val_lt_two_pow _) _ tagsY

/-! ### The designed rule on tags -/

/-- The designed rule on a hash entry, read from its tag (`crtDesigned`'s hash branch). -/
def designTag (T : CrtTable) (exc : ℕ → Option BN254.AffineInput) (u : BN254.AffineInput) (τ : ℕ) : Bool :=
  match tagFamily τ with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => !hotTag T u τ
  | 7 | 10 => BN254.validate u
  | 8 => tagPart τ == inputBit u (tagCoord τ) (tagSlot τ)
  | 9 => exc (tagSlot τ) == some u
  | _ => false

theorem crtDesigned_hash {FI EI Coins Oracle : Type} (T : CrtTable) (view : TapeView Coins Oracle)
    (scalar : BN254.NonZeroScalar) (tape : Coins × Oracle) (u : BN254.AffineInput) (x : BN254.BaseField)
    (answer : Block × Block) :
    crtDesigned (FI := FI) (EI := EI) T view scalar tape u ⟨.hash x, answer⟩ =
      designTag T (view.exceptional scalar tape) u (x.val / 2 ^ 128) := rfl

theorem designTag_conv (T : CrtTable) (exc : ℕ → Option BN254.AffineInput) (u : BN254.AffineInput) {τ : ℕ}
    (small : tagFamily τ ≤ 6) : designTag T exc u τ = !hotTag T u τ := by
  unfold designTag
  generalize tagFamily τ = f at small
  interval_cases f <;> rfl

theorem designTag_of_family (T : CrtTable) (exc : ℕ → Option BN254.AffineInput) (u : BN254.AffineInput) {τ : ℕ}
    (fam : tagFamily τ = 7 ∨ tagFamily τ = 10) : designTag T exc u τ = BN254.validate u := by
  unfold designTag
  rcases fam with fam | fam <;> rw [fam] <;> rfl

theorem designTag_label (T : CrtTable) (exc : ℕ → Option BN254.AffineInput) (u : BN254.AffineInput) {τ : ℕ}
    (fam : tagFamily τ = 8) : designTag T exc u τ = (tagPart τ == inputBit u (tagCoord τ) (tagSlot τ)) := by
  unfold designTag
  rw [fam]
  rfl

theorem designTag_final (T : CrtTable) (exc : ℕ → Option BN254.AffineInput) (u : BN254.AffineInput) {τ : ℕ}
    (fam : tagFamily τ = 9) : designTag T exc u τ = (exc (tagSlot τ) == some u) := by
  unfold designTag
  rw [fam]
  rfl

/-! ### The digest's lists -/

section Digest

variable (H : HashN)

theorem asked_digestTableM (bits : ℕ) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block) :
    asked H (digestTableM bits zero delta) =
      (List.finRange 2).flatMap fun c => (List.finRange bits).flatMap fun p =>
        [hashInput (zero c p) (digestLabelTag c.val p.val 0),
          hashInput (zero c p ^^^ delta c) (digestLabelTag c.val p.val 1)] := by
  unfold digestTableM
  simp only [asked_bind, asked_tableM, asked_h128M, asked_pure, List.append_nil, List.singleton_append]

theorem asked_digestKeyM (bits : ℕ) (labels : Fin 2 → Fin bits → Block) (u : BN254.AffineInput) :
    asked H (digestKeyM bits labels u) =
      (List.finRange 2).flatMap fun c => (List.finRange bits).flatMap fun p =>
        [hashInput (labels c p) (digestLabelTag c.val p.val (coordBit u c p.val))] := by
  unfold digestKeyM
  simp only [asked_bind, asked_tableM, asked_h128M, asked_pure, List.append_nil]

theorem asked_garbleEntryM {bits : ℕ} (table : Fin 2 → Fin bits → Block × Block) (index : ℕ) (digit : Digit)
    (offset : BN254.AffineInput) (pad : Exception.Entry) :
    asked H (garbleEntryM table index digit offset pad) =
      match digitEndomorphismBase digit with
      | none => []
      | some phi => [hashInput (garblerKey table (Exception.exceptionalInput phi offset)) (digestFinalTag index)] := by
  unfold garbleEntryM
  cases digitEndomorphismBase digit with
  | none => rfl
  | some phi =>
      simp only [finalMaskM, asked_bind, asked_h128M, asked_pure, List.append_nil, List.singleton_append]

theorem asked_digestEvalM (bits digits : ℕ) (labels : Fin 2 → Fin bits → Block) (u : BN254.AffineInput)
    (entries : Fin digits → Exception.Entry) :
    asked H (digestEvalM bits digits labels u entries) =
      asked H (digestKeyM bits labels u) ++
        (List.finRange digits).flatMap fun o => [hashInput (digestKey H bits labels u) (digestFinalTag o.val)] := by
  unfold digestEvalM
  simp only [asked_bind, asked_tableM, asked_pure, List.append_nil, finalMaskM, asked_h128M, eval_digestKeyM]

end Digest

theorem inputBit_eq_coordBit (u : BN254.AffineInput) (c : Fin 2) (p : ℕ) :
    inputBit u c.val p = coordBit u c p := by
  unfold inputBit coordBit coordValue coordNat
  have hc : (c.val = 0) ↔ (c = 0) := by constructor <;> intro h <;> [exact Fin.ext h; exact congrArg Fin.val h]
  by_cases h0 : c = 0
  · rw [if_pos (hc.mpr h0), if_pos h0, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (u.x.val / 2 ^ p) with h | h <;> simp [h]
  · rw [if_neg (fun h => h0 (hc.mp h)), if_neg h0, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (u.y.val / 2 ^ p) with h | h <;> simp [h]

/-! ### Decoding the tags of the tail -/

theorem digestLabelTag_fields {c p b : ℕ} (hc : c < 2) (hp : p < 65536) (hb : b < 64) :
    tagFamily (digestLabelTag c p b) = 8 ∧ tagCoord (digestLabelTag c p b) = c ∧
      tagSlot (digestLabelTag c p b) = p ∧ tagPart (digestLabelTag c p b) = b := by
  have range : TagInRange c 0 0 0 p b := ⟨hc, by norm_num, by norm_num, by norm_num, hp, hb⟩
  unfold digestLabelTag
  exact ⟨tagFamily_tagCode range, tagCoord_tagCode range, tagSlot_tagCode range, tagPart_tagCode range⟩

theorem digestFinalTag_fields {o : ℕ} (ho : o < 65536) :
    tagFamily (digestFinalTag o) = 9 ∧ tagSlot (digestFinalTag o) = o := by
  have range : TagInRange 0 0 0 0 o 0 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, ho, by norm_num⟩
  unfold digestFinalTag
  exact ⟨tagFamily_tagCode range, tagSlot_tagCode range⟩

theorem maskKeyTag_family : tagFamily maskKeyTag = 10 := by
  have range : TagInRange 0 0 0 0 0 0 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  unfold maskKeyTag
  exact tagFamily_tagCode range

theorem exceptional_some (scalar : BN254.NonZeroScalar) (coins : Coins) (o : Fin digitCount)
    (phi : BN254.BaseField) (selected : digitEndomorphismBase ((outputKeysOf scalar coins).get o).digit = some phi) :
    exceptional scalar coins o.val =
      some (Exception.exceptionalInput phi ((outputKeysOf scalar coins).get o).offset.coordinates) := by
  have hget : ∀ h : o.val < digitCount, (outputKeysOf scalar coins).get ⟨o.val, h⟩ = (outputKeysOf scalar coins).get o :=
    fun _ => rfl
  unfold exceptional
  rw [dif_pos o.isLt]
  dsimp only
  rw [hget o.isLt, selected]

/-! ### The containment on the program level -/

/-- **Where the reach asks a designed garbler input**: in its conversion layer, on the curve in its key or masks, or
in its digest. -/
theorem garble_designed_parts (H : HashN) (scalar : BN254.NonZeroScalar) (coins : Coins) (u : BN254.AffineInput) :
    ∀ x ∈ asked H (garbleCM scalar coins), designTag table (exceptional scalar coins) u (x / 2 ^ 128) = true →
      x ∈ asked H (replayConv (pubOf H scalar coins) u (labelsFor coins u)) ∨
      (BN254.validate u = true ∧
        (x ∈ asked H (keyM (curveOutput (pubOf H scalar coins) u
            ((replayConv (pubOf H scalar coins) u (labelsFor coins u)).eval H))) ∨
          x ∈ asked H (maskAnswersM ((keyM (curveOutput (pubOf H scalar coins) u
            ((replayConv (pubOf H scalar coins) u (labelsFor coins u)).eval H))).eval H) digitCount))) ∨
      x ∈ asked H (digestEvalM coordinateBitCount digitCount (labelsOf (labelsFor coins u)) u
        (fun o => (pubOf H scalar coins).exception.get o)) := by
  intro x inside designed
  have conv := replayConv_aligned H scalar coins u
  unfold garbleCM at inside
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · -- the conversion layer of `x`
    obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table xCount 0 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) H _ inX
    rw [hashInput_div] at designed
    rw [designTag_conv _ _ _ (by rw [tagFamily_key range]; exact member.1)] at designed
    left
    exact conv.covers _ (List.mem_append_left _ inX) (by
      unfold ColdAt; rw [hashInput_div]; simpa using designed)
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table yCount 1 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) H _ inY
    rw [hashInput_div] at designed
    rw [designTag_conv _ _ _ (by rw [tagFamily_key range]; exact member.1)] at designed
    left
    exact conv.covers _ (List.mem_append_right _ inY) (by
      unfold ColdAt; rw [hashInput_div]; simpa using designed)
  · -- the key, on the curve
    simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inKey
    subst inKey
    have fam : tagFamily (maskKeyInput coins.bridgeKey / 2 ^ 128) = 10 := by
      unfold maskKeyInput; rw [hashInput_div]; exact maskKeyTag_family
    rw [designTag_of_family _ _ _ (Or.inr fam)] at designed
    have onCurve : BN254.OnCurve u := (BN254.validate_eq_true_iff u).mp designed
    right; left
    refine ⟨designed, Or.inl ?_⟩
    simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton]
    rw [curveOutput_eq H scalar coins u onCurve]
  · -- the masks, on the curve
    obtain ⟨k, member, range, label, same⟩ := asked_of_tagged
      (Paths.maskAnswersM_tagged _ digitCount (by decide) (by decide)) H _ inMask
    have fam : tagFamily (x / 2 ^ 128) = 7 := by
      rw [same, hashInput_div, tagFamily_key range]
      simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
        Set.mem_setOf_eq] at member
      omega
    rw [designTag_of_family _ _ _ (Or.inl fam)] at designed
    have onCurve : BN254.OnCurve u := (BN254.validate_eq_true_iff u).mp designed
    right; left
    refine ⟨designed, Or.inr ?_⟩
    rw [curveOutput_eq H scalar coins u onCurve]
    exact inMask
  · -- the digest
    right; right
    rw [asked_digestEvalM, List.mem_append]
    unfold digestGarbleM at inDigest
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inDigest
    rcases inDigest with inTable | inFinals
    · -- a digest label: designed only at `u`'s bit
      left
      rw [asked_digestTableM] at inTable
      rw [asked_digestKeyM]
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at inTable ⊢
      obtain ⟨c, p, same | same⟩ := inTable
      · subst same
        obtain ⟨hf, hcoord, hslot, hpart⟩ := digestLabelTag_fields (b := 0) c.isLt (lt_of_lt_of_le p.isLt (by decide))
          (by norm_num)
        rw [hashInput_div, designTag_label _ _ _ hf, hcoord, hslot, hpart, inputBit_eq_coordBit,
          beq_iff_eq] at designed
        refine ⟨c, p, ?_⟩
        rw [labelsOf_honest coins u c p, ← designed]
        simp
      · subst same
        obtain ⟨hf, hcoord, hslot, hpart⟩ := digestLabelTag_fields (b := 1) c.isLt (lt_of_lt_of_le p.isLt (by decide))
          (by norm_num)
        rw [hashInput_div, designTag_label _ _ _ hf, hcoord, hslot, hpart, inputBit_eq_coordBit,
          beq_iff_eq] at designed
        refine ⟨c, p, ?_⟩
        rw [labelsOf_honest coins u c p, ← designed]
        simp
    · -- a final: designed only at the digit's exceptional input
      right
      rw [asked_tableM] at inFinals
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_flatMap] at inFinals ⊢
      obtain ⟨o, inEntry⟩ := inFinals
      rw [asked_garbleEntryM] at inEntry
      refine ⟨o, ?_⟩
      split at inEntry
      · exact absurd inEntry List.not_mem_nil
      · rename_i phi selected
        rw [List.mem_singleton] at inEntry
        subst inEntry
        obtain ⟨hf, hslot⟩ := digestFinalTag_fields (o := o.val) (by have := o.isLt; simp [digitCount] at this; omega)
        rw [hashInput_div, designTag_final _ _ _ hf, hslot, beq_iff_eq, exceptional_some scalar coins o phi selected,
          Option.some.injEq] at designed
        rw [List.mem_singleton, eval_digestTableM,
          DigestUnlock.digestKey_honest H coordinateBitCount (zeroOf coins) (deltaOf coins) _ u
            (labelsOf_honest coins u), designed]

/-- **Every designed garbler input is the reach's** (`Entry.reachCM`, the reach on the curve; for every hash). -/
theorem garble_designed_reached (H : HashN) (scalar : BN254.NonZeroScalar) (coins : Coins) (u : BN254.AffineInput) :
    ∀ x ∈ asked H (garbleCM scalar coins), designTag table (exceptional scalar coins) u (x / 2 ^ 128) = true →
      x ∈ asked H (reachCM (pubOf H scalar coins) u (labelsFor coins u)) := by
  intro x inside designed
  unfold reachCM replay
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append]
  rcases garble_designed_parts H scalar coins u x inside designed with inConv | ⟨_, inKey | inMask⟩ | inDigest
  · exact Or.inl (Or.inl inConv)
  · exact Or.inl (Or.inr (Or.inl inKey))
  · exact Or.inl (Or.inr (Or.inr inMask))
  · exact Or.inr inDigest

end Kriterion.CRT.Privacy.Align
