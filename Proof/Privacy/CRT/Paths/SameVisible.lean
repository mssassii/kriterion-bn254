/-
**`sameVisible` of `viewEntriesPerm_of` for the concrete entry**.

At an input `u`, the garbler's entries at the visible tags are exactly the view's entries. On the tag table both are
determined by their inputs (the answer is the table at the input's tag), so the statement is about inputs:

* **invariance** (`asked_reachDecodedCM_invariant`): the reach asks the same inputs on the view's table as on the real
  table. The two hashes agree at every visible tag, and every input the reach asks before its digest finals is at a
  visible tag (`conv_visible`: the conversion blocks are cold; `replay_visible`: on the curve the key and the masks are
  visible; `digestKey_visible`: the digest labels are at `u`'s bits); the finals come last and their inputs depend only
  on the digest key, which the labels fix (`asked_congr`);
* **garbler to reach** (`garbler_to_reach`): a garbler input at a visible tag is designed (`designTag_of_visTag`), so
  the reach asks it (`Align.garble_designed_parts`; off the curve the key and masks are not visible);
* **reach to garbler** (`reach_to_garbler`): a reach input at a visible tag is a garbler input: the conversion blocks
  by `replayConv_aligned.sound`, the key and masks through `curveOutput_eq`, the digest labels through
  `labelsOf_honest`; the finals are never visible;
* `crtEntry_sameVisible`: the entries.
-/

import Proof.Privacy.CRT.Paths.ReachTranscript
import Proof.Privacy.CRT.Hidden.Reached

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_askN asked_digestKeyM asked_digestEvalM
  asked_digestTableM asked_of_tagged hashInput_div)

namespace SameVisible

/-! ### Congruence of the asked inputs -/

/-- **Two hashes that agree on every input a program asks give the same inputs and the same value.** -/
theorem asked_congr {α : Type} (H H' : HashN) :
    ∀ p : CM α, (∀ n ∈ asked H p, H n = H' n) → asked H' p = asked H p ∧ p.eval H' = p.eval H := by
  intro p
  induction p with
  | pure v => exact fun _ => ⟨rfl, rfl⟩
  | query n next ih =>
      intro agree
      have first : H n = H' n := agree n (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨askedSame, evalSame⟩ := ih (H n) fun m inside => agree m (List.mem_cons.mpr (Or.inr inside))
      refine ⟨?_, ?_⟩
      · show n :: asked H' (next (H' n)) = n :: asked H (next (H n))
        rw [← first, askedSame]
      · show (next (H' n)).eval H' = (next (H n)).eval H
        rw [← first, evalSame]

/-! ### Labelled inputs -/

/-- An input `hashInput label (tagCode …)` at a key in range. -/
def Labelled (n : ℕ) : Prop := ∃ k : TagKey, k.InRange ∧ ∃ label : Block, n = hashInput label k.code

theorem labelled_of_tagged {α : Type} {S : Set TagKey} {program : CM α} (tagged : Tagged S program) (H : HashN) :
    ∀ n ∈ asked H program, Labelled n := fun n inside => by
  obtain ⟨k, _, range, label, same⟩ := asked_of_tagged tagged H n inside
  exact ⟨k, range, label, same⟩

theorem Labelled.val {n : ℕ} (labelled : Labelled n) : ((n : BaseField)).val = n := by
  obtain ⟨k, range, label, rfl⟩ := labelled
  exact Align.val_natCast_of_lt (hashInput_lt range)

theorem Labelled.tag {n : ℕ} (labelled : Labelled n) : (tagOfInput (n : BaseField)).val = n / 2 ^ 128 := by
  obtain ⟨k, range, label, rfl⟩ := labelled
  rw [tagOfInput_hashInput range, hashInput_div]

/-! ### The visible tags by family -/

variable {T : CrtTable} {u : AffineInput} {τ : ℕ}

theorem visTag_conv (small : tagFamily τ ≤ 6) : H8.visTag T u τ = !hotTag T u τ := by
  unfold H8.visTag
  generalize tagFamily τ = f at small
  interval_cases f <;> rfl

theorem visTag_keyMask (fam : tagFamily τ = 7 ∨ tagFamily τ = 10) : H8.visTag T u τ = validate u := by
  unfold H8.visTag
  rcases fam with fam | fam <;> rw [fam] <;> rfl

theorem visTag_label (fam : tagFamily τ = 8) :
    H8.visTag T u τ = (tagPart τ == inputBit u (tagCoord τ) (tagSlot τ)) := by
  unfold H8.visTag
  rw [fam]
  rfl

theorem visTag_final (fam : tagFamily τ = 9) : H8.visTag T u τ = false := by
  unfold H8.visTag
  rw [fam]
  rfl

/-- A garbler tag the view shows is one the designed rule shows. -/
theorem designTag_of_visTag (exc : ℕ → Option AffineInput) (small : tagFamily τ ≤ 10)
    (vis : H8.visTag T u τ = true) : Align.designTag T exc u τ = true := by
  unfold H8.visTag at vis
  unfold Align.designTag
  generalize tagFamily τ = f at small vis ⊢
  interval_cases f <;> simp_all

/-! ### The reach's inputs before its finals are visible -/

section Visible

variable (H : HashN) (scalar : NonZeroScalar) (coins : Kriterion.CRT.Entry.Coins) (u : AffineInput)

/-- The conversion blocks of the reach are labelled and visible (they are cold). -/
theorem conv_visible :
    ∀ n ∈ asked H (Kriterion.CRT.Entry.replayConv (EntryCorrect.pubOf H scalar coins) u (EntryCorrect.labelsFor H coins u)),
      Labelled n ∧ H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true := by
  intro n inside
  obtain ⟨cold, _⟩ := (Align.replayConv_aligned H scalar coins u).sound n inside
  obtain ⟨k, member, range, label, same⟩ := asked_of_tagged (replayConv_tagged _ u _) H n inside
  refine ⟨⟨k, range, label, same⟩, ?_⟩
  have fam : tagFamily (n / 2 ^ 128) ≤ 6 := by
    rw [same, hashInput_div, Align.tagFamily_key range]
    exact replayConvKeys_fam k member
  rw [visTag_conv fam]
  unfold Align.ColdAt at cold
  rw [cold]
  rfl

/-- On the curve, the whole replay (conversion blocks, key, masks) is labelled and visible. -/
theorem replay_visible (valid : validate u = true) :
    ∀ n ∈ asked H (Kriterion.CRT.Entry.replay (EntryCorrect.pubOf H scalar coins) u (EntryCorrect.labelsFor H coins u)),
      Labelled n ∧ H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true := by
  intro n inside
  unfold Kriterion.CRT.Entry.replay at inside
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
  rcases inside with inConv | inKey | inMask
  · exact conv_visible H scalar coins u n inConv
  · simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inKey
    subst inKey
    refine ⟨⟨keyKey, keyKey_range, _, rfl⟩, ?_⟩
    have fam : tagFamily (maskKeyInput (Kriterion.CRT.Entry.curveOutput (EntryCorrect.pubOf H scalar coins) u
        ((Kriterion.CRT.Entry.replayConv (EntryCorrect.pubOf H scalar coins) u
          (EntryCorrect.labelsFor H coins u)).eval H)) / 2 ^ 128) = 10 := by
      unfold maskKeyInput
      rw [hashInput_div]
      exact Align.maskKeyTag_family
    rw [visTag_keyMask (Or.inr fam), valid]
  · obtain ⟨k, member, range, label, same⟩ :=
      asked_of_tagged (maskAnswersM_tagged _ digitCount (by decide) (by decide)) H n inMask
    refine ⟨⟨k, range, label, same⟩, ?_⟩
    have fam : tagFamily (n / 2 ^ 128) = 7 := by
      rw [same, hashInput_div, Align.tagFamily_key range]
      exact maskKeys_fam k member
    rw [visTag_keyMask (Or.inl fam), valid]

/-- The digest key's labels are labelled and visible (at `u`'s bits). -/
theorem digestKey_visible (labels : Fin 2 → Fin coordinateBitCount → Block) :
    ∀ n ∈ asked H (digestKeyM coordinateBitCount labels u),
      Labelled n ∧ H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true := by
  intro n inside
  rw [asked_digestKeyM] at inside
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at inside
  obtain ⟨c, p, rfl⟩ := inside
  have bit := coordBit_lt u c p.val
  have pSmall : p.val < 65536 := lt_of_lt_of_le p.isLt (by decide)
  refine ⟨⟨⟨8, c.val, 0, 0, 0, p.val, coordBit u c p.val⟩,
    ⟨by norm_num, c.isLt, by norm_num, by norm_num, by norm_num, pSmall, show coordBit u c p.val < 64 by omega⟩,
    _, rfl⟩, ?_⟩
  obtain ⟨hf, hcoord, hslot, hpart⟩ := Align.digestLabelTag_fields (b := coordBit u c p.val) c.isLt pSmall
    (by omega)
  rw [hashInput_div, visTag_label hf, hcoord, hslot, hpart, Align.inputBit_eq_coordBit]
  exact beq_self_eq_true _

end Visible

/-! ### Invariance of the reach -/

section Invariance

variable (H Hv : HashN) (scalar : NonZeroScalar) (coins : Kriterion.CRT.Entry.Coins) (u : AffineInput)
  (agree : ∀ n, Labelled n → H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true → Hv n = H n)

include agree in
theorem asked_digestEvalM_invariant (entries : Fin digitCount → Exception.Entry) :
    asked Hv (digestEvalM coordinateBitCount digitCount (Kriterion.CRT.Entry.labelsOf (EntryCorrect.labelsFor H coins u))
        u entries) =
      asked H (digestEvalM coordinateBitCount digitCount (Kriterion.CRT.Entry.labelsOf (EntryCorrect.labelsFor H coins u))
        u entries) := by
  have same := asked_congr H Hv (digestKeyM coordinateBitCount
    (Kriterion.CRT.Entry.labelsOf (EntryCorrect.labelsFor H coins u)) u) fun n inside => by
      obtain ⟨labelled, vis⟩ := digestKey_visible H u _ n inside
      exact (agree n labelled vis).symm
  rw [asked_digestEvalM, asked_digestEvalM, same.1, ← eval_digestKeyM Hv, ← eval_digestKeyM H, same.2]

include agree in
/-- **The reach asks the same inputs on the view's hash.** -/
theorem asked_reachDecodedCM_invariant [FieldCertificate] [GroupCertificate] :
    asked Hv (reachDecodedCM (EntryCorrect.pubOf H scalar coins) u (EntryCorrect.labelsFor H coins u)) =
      asked H (reachDecodedCM (EntryCorrect.pubOf H scalar coins) u (EntryCorrect.labelsFor H coins u)) := by
  unfold reachDecodedCM
  simp only [asked_bind, asked_pure, List.append_nil]
  by_cases valid : validate u = true
  · rw [if_pos valid]
    unfold Kriterion.CRT.Entry.reachCM
    simp only [asked_bind, asked_pure, List.append_nil]
    have replaySame := (asked_congr H Hv (Kriterion.CRT.Entry.replay (EntryCorrect.pubOf H scalar coins) u
      (EntryCorrect.labelsFor H coins u)) fun n inside => by
        obtain ⟨labelled, vis⟩ := replay_visible H scalar coins u valid n inside
        exact (agree n labelled vis).symm).1
    rw [replaySame, asked_digestEvalM_invariant H Hv coins u agree]
  · rw [if_neg valid]
    unfold EntryReading.reachOffCM
    simp only [asked_bind, asked_pure, List.append_nil]
    have convSame := (asked_congr H Hv (Kriterion.CRT.Entry.replayConv (EntryCorrect.pubOf H scalar coins) u
      (EntryCorrect.labelsFor H coins u)) fun n inside => by
        obtain ⟨labelled, vis⟩ := conv_visible H scalar coins u n inside
        exact (agree n labelled vis).symm).1
    rw [convSame, asked_digestEvalM_invariant H Hv coins u agree]

end Invariance

/-! ### Garbler and reach at the visible tags -/

section Both

variable (H : HashN) (scalar : NonZeroScalar) (coins : Kriterion.CRT.Entry.Coins) (u : AffineInput)

/-- **A garbler input at a visible tag is the reach's.** -/
theorem garbler_to_reach [FieldCertificate] [GroupCertificate] :
    ∀ n ∈ asked H (Kriterion.CRT.Entry.garbleCM scalar coins),
      H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true →
      n ∈ asked H (reachDecodedCM (EntryCorrect.pubOf H scalar coins) u (EntryCorrect.labelsFor H coins u)) := by
  intro n inside vis
  obtain ⟨k, member, range, label, same⟩ := asked_of_tagged (garbleCM_tagged scalar coins) H n inside
  have small : tagFamily (n / 2 ^ 128) ≤ 10 := by
    rw [same, hashInput_div, Align.tagFamily_key range]
    exact garblerKeys_fam k member
  have parts := Align.garble_designed_parts H scalar coins u n inside
    (designTag_of_visTag (Kriterion.CRT.Entry.exceptional scalar coins) small vis)
  unfold reachDecodedCM
  simp only [asked_bind, asked_pure, List.append_nil]
  by_cases valid : validate u = true
  · rw [if_pos valid]
    unfold Kriterion.CRT.Entry.reachCM Kriterion.CRT.Entry.replay
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append]
    rcases parts with inConv | ⟨_, inKey | inMask⟩ | inDigest
    · exact Or.inl (Or.inl inConv)
    · exact Or.inl (Or.inr (Or.inl inKey))
    · exact Or.inl (Or.inr (Or.inr inMask))
    · exact Or.inr inDigest
  · rw [if_neg valid]
    unfold EntryReading.reachOffCM
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append]
    rcases parts with inConv | ⟨on, _⟩ | inDigest
    · exact Or.inl inConv
    · exact absurd on valid
    · exact Or.inr inDigest

/-- The garbler's inputs, by block. -/
theorem garbler_of_mem {n : ℕ}
    (h : n ∈ asked H (coordGarbleM Kriterion.CRT.Entry.table Kriterion.CRT.Entry.xCount 0 (clip (coins.inputDelta .x))
          (fun j => clip (atNat (coins.inputZero .x) 0 j))) ∨
      n ∈ asked H (coordGarbleM Kriterion.CRT.Entry.table Kriterion.CRT.Entry.yCount 1 (clip (coins.inputDelta .y))
          (fun j => clip (atNat (coins.inputZero .y) 0 j))) ∨
      n ∈ asked H (keyM coins.bridgeKey) ∨
      n ∈ asked H (maskAnswersM ((keyM coins.bridgeKey).eval H) digitCount) ∨
      n ∈ asked H (digestTableM coordinateBitCount (EntryCorrect.keyZero H coins)
          (Kriterion.CRT.Entry.deltaOf coins))) :
    n ∈ asked H (Kriterion.CRT.Entry.garbleCM scalar coins) := by
  -- the garbler's digest table is at its actual zero labels `keyZero H coins` (the chunk joins absorbed)
  unfold EntryCorrect.keyZero EntryCorrect.gxOf EntryCorrect.gyOf at h
  unfold Kriterion.CRT.Entry.garbleCM digestGarbleM
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append]
  rcases h with h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- A digest label the reach asks at `u`'s bit is one of the garbler's digest table inputs. -/
theorem label_in_table (c : Fin 2) (p : Fin coordinateBitCount) :
    hashInput (Kriterion.CRT.Entry.labelsOf (EntryCorrect.labelsFor H coins u) c p)
        (digestLabelTag c.val p.val (coordBit u c p.val)) ∈
      asked H (digestTableM coordinateBitCount (EntryCorrect.keyZero H coins)
        (Kriterion.CRT.Entry.deltaOf coins)) := by
  rw [asked_digestTableM]
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false]
  refine ⟨c, p, ?_⟩
  rw [EntryCorrect.labelsOf_honest H coins u c p]
  have bit := coordBit_lt u c p.val
  rcases (show coordBit u c p.val = 0 ∨ coordBit u c p.val = 1 by omega) with zero | one
  · left
    rw [zero]
    simp
  · right
    rw [one]
    simp

/-- The reach's conversion blocks are garbler inputs. -/
theorem conv_to_garbler {n : ℕ}
    (inConv : n ∈ asked H (Kriterion.CRT.Entry.replayConv (EntryCorrect.pubOf H scalar coins) u
      (EntryCorrect.labelsFor H coins u))) :
    n ∈ asked H (Kriterion.CRT.Entry.garbleCM scalar coins) := by
  refine garbler_of_mem H scalar coins ?_
  rcases List.mem_append.mp ((Align.replayConv_aligned H scalar coins u).sound n inConv).2 with inX | inY
  · exact Or.inl inX
  · exact Or.inr (Or.inl inY)

/-- The reach's digest inputs at visible tags (its labels) are garbler inputs. -/
theorem digest_to_garbler {n : ℕ} (entries : Fin digitCount → Exception.Entry)
    (vis : H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true)
    (inDigest : n ∈ asked H (digestEvalM coordinateBitCount digitCount
      (Kriterion.CRT.Entry.labelsOf (EntryCorrect.labelsFor H coins u)) u entries)) :
    n ∈ asked H (Kriterion.CRT.Entry.garbleCM scalar coins) := by
  rw [asked_digestEvalM, List.mem_append] at inDigest
  rcases inDigest with inLabels | inFinals
  · rw [asked_digestKeyM] at inLabels
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at inLabels
    obtain ⟨c, p, rfl⟩ := inLabels
    exact garbler_of_mem H scalar coins (Or.inr (Or.inr (Or.inr (Or.inr (label_in_table H coins u c p)))))
  · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
      or_false] at inFinals
    obtain ⟨o, rfl | rfl⟩ := inFinals
    · obtain ⟨fam, _⟩ := Align.digestFinalTag_fields (o := 2 * o.val)
        (by have := o.isLt; simp only [digitCount] at this; omega)
      rw [hashInput_div, visTag_final fam] at vis
      cases vis
    · obtain ⟨fam, _⟩ := Align.digestFinalTag_fields (o := 2 * o.val + 1)
        (by have := o.isLt; simp only [digitCount] at this; omega)
      rw [hashInput_div, visTag_final fam] at vis
      cases vis

/-- **A reach input at a visible tag is the garbler's.** -/
theorem reach_to_garbler [FieldCertificate] [GroupCertificate] :
    ∀ n ∈ asked H (reachDecodedCM (EntryCorrect.pubOf H scalar coins) u (EntryCorrect.labelsFor H coins u)),
      H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true →
      n ∈ asked H (Kriterion.CRT.Entry.garbleCM scalar coins) := by
  intro n inside vis
  unfold reachDecodedCM at inside
  simp only [asked_bind, asked_pure, List.append_nil] at inside
  by_cases valid : validate u = true
  · rw [if_pos valid] at inside
    have onCurve : OnCurve u := (validate_eq_true_iff u).mp valid
    unfold Kriterion.CRT.Entry.reachCM Kriterion.CRT.Entry.replay at inside
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
    rcases inside with (inConv | inKey | inMask) | inDigest
    · exact conv_to_garbler H scalar coins u inConv
    · rw [EntryCorrect.curveOutput_eq H scalar coins u onCurve] at inKey
      exact garbler_of_mem H scalar coins (Or.inr (Or.inr (Or.inl inKey)))
    · rw [EntryCorrect.curveOutput_eq H scalar coins u onCurve] at inMask
      exact garbler_of_mem H scalar coins (Or.inr (Or.inr (Or.inr (Or.inl inMask))))
    · exact digest_to_garbler H scalar coins u _ vis inDigest
  · rw [if_neg valid] at inside
    unfold EntryReading.reachOffCM at inside
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
    rcases inside with inConv | inDigest
    · exact conv_to_garbler H scalar coins u inConv
    · exact digest_to_garbler H scalar coins u _ vis inDigest

end Both

end SameVisible

/-! ### The entries -/

open SameVisible in
/-- **The entries at the visible tags**, for any view table that agrees with the real table at the visible tags: the
garbler's visible entries are the reach's visible entries on the view table. -/
theorem SameVisible.assemble [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (coins : Kriterion.CRT.Entry.Coins) (u : AffineInput) (table X : TagTable)
    (hX : ∀ tag : Fin (2 ^ 40), H8.visTag Kriterion.CRT.Entry.table u tag.val = true → X tag = table tag)
    (p : Privacy.Entry Empty Empty → Bool)
    (hp : ∀ (x : BaseField) (a : Block × Block),
      p ⟨.hash x, a⟩ = H8.visTag Kriterion.CRT.Entry.table u (x.val / 2 ^ 128))
    (entry : Privacy.Entry Empty Empty) :
    (entry ∈ (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) table))
          (Kriterion.CRT.Entry.garbleCM scalar coins)).map
          (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) table).2.2 (n : BaseField)⟩ :
            Privacy.Entry Empty Empty)) ∧
        entryVisible Kriterion.CRT.Entry.table u entry = true) ↔
      entry ∈ ((asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) X))
          (reachDecodedCM (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar
            coins) u (EntryCorrect.labelsFor (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins u))).map
          (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) X).2.2 (n : BaseField)⟩ :
            Privacy.Entry Empty Empty))).filter p := by
  have answerSame : ∀ n, Labelled n → H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true →
      X (tagOfInput (n : BaseField)) = table (tagOfInput (n : BaseField)) := fun n labelled vis =>
    hX _ (by rw [labelled.tag]; exact vis)
  rw [asked_reachDecodedCM_invariant (schemeHash (tableOracle (FI := Empty) (EI := Empty) table))
    (schemeHash (tableOracle (FI := Empty) (EI := Empty) X)) scalar coins u answerSame]
  constructor
  · rintro ⟨inG, vis⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp inG
    have labelled := labelled_of_tagged (garbleCM_tagged scalar coins) _ n hn
    have vis' : H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true := by
      have shown : H8.visTag Kriterion.CRT.Entry.table u ((n : BaseField).val / 2 ^ 128) = true := vis
      rwa [labelled.val] at shown
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨n, garbler_to_reach _ scalar coins u n hn vis', ?_⟩, ?_⟩
    · exact congrArg (fun a => (⟨.hash (n : BaseField), a⟩ : Privacy.Entry Empty Empty))
        (answerSame n labelled vis')
    · rw [hp, labelled.val]
      exact vis'
  · intro inV
    obtain ⟨inMap, visP⟩ := List.mem_filter.mp inV
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp inMap
    have labelled := labelled_of_tagged (reachDecodedCM_tagged _ u _) _ n hn
    have vis' : H8.visTag Kriterion.CRT.Entry.table u (n / 2 ^ 128) = true := by
      rw [hp, labelled.val] at visP
      exact visP
    refine ⟨List.mem_map.mpr ⟨n, reach_to_garbler _ scalar coins u n hn vis', ?_⟩, ?_⟩
    · exact congrArg (fun a => (⟨.hash (n : BaseField), a⟩ : Privacy.Entry Empty Empty))
        (answerSame n labelled vis').symm
    · show H8.visTag Kriterion.CRT.Entry.table u ((n : BaseField).val / 2 ^ 128) = true
      rw [labelled.val]
      exact vis'

open SameVisible in
/-- **`sameVisible` of `viewEntriesPerm_of` for the concrete entry**: at every input, the garbler's entries at the
visible tags are the view's entries (the doubling hypothesis is not needed). -/
theorem crtEntry_sameVisible :
    ∀ [FieldCertificate] [GroupCertificate] [Fintype Empty] [Fintype Empty] [DecidableEq Empty] [DecidableEq Empty]
      (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) (u : AffineInput),
      ¬ H8.Doubling Instance.crtEntry scalar tape u → ∀ entry,
        (entry ∈ garblerEntries Instance.crtEntry parameter scalar tape ∧
            entryVisible Kriterion.CRT.Entry.table u entry = true) ↔
          entry ∈ H8.viewEntries Instance.crtEntry Kriterion.CRT.Entry.table u
            (H8.realView Instance.crtEntry Kriterion.CRT.Entry.table parameter scalar u tape) := by
  intro field group _ _ _ _ parameter scalar tape u _ entry
  obtain ⟨coins, table⟩ := tape
  have hgarble : (@Kriterion.CRT.Entry.scheme field group).garble parameter scalar (coins, tableOracle table) =
      (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins,
        EntryCorrect.keyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins) := by
    refine (entry_garble_eval field group parameter scalar coins (tableOracle table)).trans ?_
    unfold Kriterion.CRT.Entry.garbleProgram
    rw [FreeQuery.eval_toProgram]
    unfold Kriterion.CRT.Entry.garbleM
    rw [eval_liftHash]
    exact EntryCorrect.garbleCM_eval _ scalar coins
  have hencode : (@Kriterion.CRT.Entry.scheme field group).encode
      (EntryCorrect.keyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins) u =
      EntryCorrect.labelsFor (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins u := by
    unfold Kriterion.CRT.Entry.scheme EntryCorrect.labelsFor
    rfl
  have hview : H8.realView Instance.crtEntry Kriterion.CRT.Entry.table parameter scalar u (coins, table) =
      (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins,
        EntryCorrect.labelsFor (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins u, fun tag => table tag.1) := by
    unfold H8.realView H8.realGarbled
    dsimp only [Instance.crtEntry]
    rw [hgarble]
    dsimp only
    rw [hencode]
  have transcriptG := Align.transcript_toProgram (publicAnswer (tableOracle (FI := Empty) (EI := Empty) table))
    (liftHash (Kriterion.CRT.Entry.garbleCM scalar coins)) Kriterion.CRT.Entry.garbleBudget
    (Kriterion.CRT.Entry.bounded_garbleM scalar coins)
  rw [hview]
  unfold H8.viewEntries garblerEntries tapeOracle
  dsimp only [Instance.crtEntry]
  unfold Kriterion.CRT.Entry.garbleProgram Kriterion.CRT.Entry.garbleM EntryReading.reachProgram
  rw [transcriptG, Align.ftranscript_liftHash, Align.transcript_toProgram _
    (EntryReading.reachDecodedM (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table))
      scalar coins) u (EntryCorrect.labelsFor (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins u)) Kriterion.CRT.Entry.evaluateBudget
    (EntryReading.bounded_reachDecodedM _ u _), reachDecodedM_eq, Align.ftranscript_liftHash]
  refine assemble scalar coins u table _ ?_ _ ?_ entry
  · intro tag vis
    unfold H8.viewTable
    rw [dif_pos vis]
  · intro x a
    rfl

end Kriterion.CRT.Paths
