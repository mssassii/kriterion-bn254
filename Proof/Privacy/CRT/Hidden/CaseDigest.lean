/-
**H7's case `digestOther`** (`Hidden/StageTwo.lean`): a stage-2 query at a digest label (family 8) at
the bit `u` does not hold.

The garbler asks the digest label of coordinate `κ`, position `p` at both bits: at bit `b` its label is
`Z_{κ,p} ⊕ b · Δ_κ`. The evaluator's label is `E_{κ,p} = Z_{κ,p} ⊕ u_{κ,p} · Δ_κ`, which the stage-2 view holds.
At the other bit the garbler's label is `E_{κ,p} ⊕ Δ_κ`, so a query that meets it fixes
`Δ_κ = E_{κ,p} ⊕ label` (`digestOther_delta`). Given the view, `Δ_κ` is uniform (`Hidden/DeltaView.lean`), so this has conditional mass at most `2^-128`.
-/

import Proof.Privacy.CRT.Hidden.StageTwo
import Proof.Privacy.CRT.Paths.Reach

namespace Kriterion.CRT.Privacy.StageTwo

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Privacy.Align
open scoped ENNReal

namespace CaseDigest

/-- A labelled input's low 128 bits, as a block, are its label. -/
theorem ofNat_label (label : Block) (tag : ℕ) : BitVec.ofNat 128 (hashInput label tag % 2 ^ 128) = label := by
  rw [Paths.hashInput_label]
  exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt label.isLt])

/-- **A garbler input at a digest label at the other bit fixes the coordinate's `Δ`**: it is `E ⊕ label`, with `E`
the evaluator's label at that position. The coordinate and the position are read from the input's tag. -/
theorem digestOther_delta (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape Instance.crtEntry) (N : ℕ)
    (inG : N ∈ gAsked scalar tape) (other : digestOther u (N / 2 ^ 128)) :
    ∃ (c : Fin 2) (p : Fin coordinateBitCount), c.val = tagCoord (N / 2 ^ 128) ∧ p.val = tagSlot (N / 2 ^ 128) ∧
      Entry.deltaOf tape.1 c =
        Entry.labelsOf (EntryCorrect.labelsFor tape.1 u) c p ^^^ BitVec.ofNat 128 (N % 2 ^ 128) := by
  obtain ⟨coins, tab⟩ := tape
  obtain ⟨fam8, otherBit⟩ := other
  unfold gAsked at inG
  dsimp only at inG ⊢
  have notIn : ∀ {α : Type} {S : Set Paths.TagKey} {program : CM α}, Paths.Tagged S program →
      (∀ k ∈ S, k.fam ≠ 8) → N ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) tab)) program → False := by
    intro α S program tagged away inside
    obtain ⟨k, member, range, label, same⟩ := asked_of_tagged tagged _ N inside
    have fam : tagFamily (N / 2 ^ 128) = k.fam := by rw [same, hashInput_div, tagFamily_key range]
    exact away k member (fam ▸ fam8)
  unfold Entry.garbleCM digestGarbleM at inG
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inG
  rcases inG with inX | inY | inKey | inMask | inTable | inFinals
  · exact (notIn (Paths.coordGarbleM_tagged Entry.table Entry.xCount 0 (Paths.bn254_ranges _ (by decide))
      (by norm_num) _ _) (fun k member => by simp only [Paths.coordKeys, Set.mem_setOf_eq] at member; omega)
      inX).elim
  · exact (notIn (Paths.coordGarbleM_tagged Entry.table Entry.yCount 1 (Paths.bn254_ranges _ (by decide))
      (by norm_num) _ _) (fun k member => by simp only [Paths.coordKeys, Set.mem_setOf_eq] at member; omega)
      inY).elim
  · exact (notIn (Paths.keyM_tagged _) (fun k member => by rw [Set.mem_singleton_iff.mp member]; decide)
      inKey).elim
  · exact (notIn (Paths.maskAnswersM_tagged _ digitCount (by decide) (by decide))
      (fun k member => by have := Paths.maskKeys_fam k member; omega) inMask).elim
  · rw [asked_digestTableM] at inTable
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at inTable
    obtain ⟨c, p, same | same⟩ := inTable
    · subst same
      obtain ⟨_, hcoord, hslot, hpart⟩ := digestLabelTag_fields (b := 0) c.isLt
        (lt_of_lt_of_le p.isLt (by decide)) (by norm_num)
      rw [hashInput_div, hcoord, hslot, hpart, inputBit_eq_coordBit] at otherBit
      refine ⟨c, p, by rw [hashInput_div, hcoord], by rw [hashInput_div, hslot], ?_⟩
      rw [ofNat_label, EntryCorrect.labelsOf_honest coins u c p]
      have one : coordBit u c p.val = 1 := by have := Paths.coordBit_lt u c p.val; omega
      rw [if_pos one, BitVec.xor_comm (Entry.zeroOf coins c p), BitVec.xor_assoc, BitVec.xor_self,
        BitVec.xor_zero]
    · subst same
      obtain ⟨_, hcoord, hslot, hpart⟩ := digestLabelTag_fields (b := 1) c.isLt
        (lt_of_lt_of_le p.isLt (by decide)) (by norm_num)
      rw [hashInput_div, hcoord, hslot, hpart, inputBit_eq_coordBit] at otherBit
      refine ⟨c, p, by rw [hashInput_div, hcoord], by rw [hashInput_div, hslot], ?_⟩
      rw [ofNat_label, EntryCorrect.labelsOf_honest coins u c p]
      have zero : ¬ coordBit u c p.val = 1 := fun one => otherBit one.symm
      rw [if_neg zero, ← BitVec.xor_assoc]
      simp
  · rw [asked_tableM] at inFinals
    simp only [List.mem_flatMap, List.mem_finRange, true_and] at inFinals
    obtain ⟨o, inEntry⟩ := inFinals
    rw [asked_garbleEntryM] at inEntry
    split at inEntry
    · exact absurd inEntry List.not_mem_nil
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inEntry
      rcases inEntry with inEntry | inEntry
      · rw [inEntry, hashInput_div] at fam8
        have := (digestFinalTag_fields (o := 2 * o.val) (by have := o.isLt; simp only [digitCount] at this; omega)).1
        omega
      · rw [inEntry, hashInput_div] at fam8
        have := (digestFinalTag_fields (o := 2 * o.val + 1) (by have := o.isLt; simp only [digitCount] at this; omega)).1
        omega

/-- The evaluator's labels in the stage-2 view are the honest labels of the tape's coins at `u`. -/
theorem stageTwoView_labels [field : FieldCertificate] [group : GroupCertificate] (parameter : ℕ)
    (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape Instance.crtEntry) :
    (stageTwoView Instance.crtEntry Entry.table parameter scalar u tape).2.1 = EntryCorrect.labelsFor tape.1 u := by
  obtain ⟨coins, tab⟩ := tape
  have hgarble : (@Entry.scheme field group).garble parameter scalar (coins, tableOracle tab) =
      (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) tab)) scalar coins,
        coins.inputMacKey) := by
    refine (Paths.entry_garble_eval field group parameter scalar coins (tableOracle tab)).trans ?_
    unfold Entry.garbleProgram
    rw [FreeQuery.eval_toProgram]
    unfold Entry.garbleM
    rw [eval_liftHash]
    exact EntryCorrect.garbleCM_eval _ scalar coins
  unfold stageTwoView tapeOracle
  dsimp only [Instance.crtEntry]
  rw [hgarble]
  unfold Entry.scheme EntryCorrect.labelsFor
  rfl

/-- The coordinate and position of a digest label the garbler asks are in range. -/
theorem digestOther_ranges (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape Instance.crtEntry) (N : ℕ)
    (inG : N ∈ gAsked scalar tape) (other : digestOther u (N / 2 ^ 128)) :
    tagCoord (N / 2 ^ 128) < 2 ∧ tagSlot (N / 2 ^ 128) < coordinateBitCount := by
  obtain ⟨c, p, hc, hp, _⟩ := digestOther_delta scalar u tape N inG other
  exact ⟨hc ▸ c.isLt, hp ▸ p.isLt⟩

/-- **The event of `digestOther` fixes the coordinate's `Δ` given the view.** -/
theorem digestOther_subset [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (view : Instance.crtEntry.Public × LamportSignature × List (Entry Empty Empty)) (N : ℕ)
    (other : digestOther u (N / 2 ^ 128)) (c : Fin 2) (p : Fin coordinateBitCount)
    (hc : c.val = tagCoord (N / 2 ^ 128)) (hp : p.val = tagSlot (N / 2 ^ 128)) :
    {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧ N ∈ gAsked scalar tape ∧
        noExtra scalar u N tape} ⊆
      {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
        Entry.deltaOf tape.1 c = Entry.labelsOf view.2.1 c p ^^^ BitVec.ofNat 128 (N % 2 ^ 128)} := by
  rintro tape ⟨hv, inG, _⟩
  refine ⟨hv, ?_⟩
  obtain ⟨c', p', hc', hp', delta⟩ := digestOther_delta scalar u tape N inG other
  have sameC : c' = c := Fin.ext (hc'.trans hc.symm)
  have sameP : p' = p := Fin.ext (hp'.trans hp.symm)
  subst sameC sameP
  rw [← hv, stageTwoView_labels]
  exact delta

/-- **`Δ` given the stage-2 view**: the named fact the case needs from `Hidden/DeltaView.lean`, each
coordinate's `Δ` takes any value with conditional mass at most `2^-128` given the stage-2 view. -/
def DeltaGivenView : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (view : Instance.crtEntry.Public × LamportSignature × List (Entry Empty Empty)) (κ : Fin 2) (d : Block),
    (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
          Entry.deltaOf tape.1 κ = d} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ * (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view}

/-- The case's error is within the hidden charge. -/
theorem inv_le_charge : ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ ENNReal.ofReal crtHiddenCharge := by
  have real : (1 : ℝ) / 2 ^ 128 ≤ crtHiddenCharge := by
    rw [crtHiddenCharge_eq]
    have pos : 0 ≤ 1 / ((BN254.baseFieldModulus : ℝ) - 1) := by
      unfold BN254.baseFieldModulus
      norm_num
    have four : (1 : ℝ) / 2 ^ 128 ≤ 4 / 2 ^ 128 := by norm_num
    linarith
  calc ((2 : ℝ≥0∞) ^ 128)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal crtHiddenCharge := ENNReal.ofReal_le_ofReal real

end CaseDigest

open CaseDigest in
/-- **H7's case `digestOther`**, from `Δ` given the view. -/
theorem digestOther_case_of (deltaGivenView : DeltaGivenView) :
    GuessCase digestOther noExtra ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  intro field group parameter scalar u view N other
  by_cases ranges : tagCoord (N / 2 ^ 128) < 2 ∧ tagSlot (N / 2 ^ 128) < coordinateBitCount
  · refine le_trans (MeasureTheory.measure_mono (digestOther_subset parameter scalar u view N other
      ⟨_, ranges.1⟩ ⟨_, ranges.2⟩ rfl rfl)) ?_
    exact deltaGivenView parameter scalar u view _ _
  · have empty : {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
        N ∈ gAsked scalar tape ∧ noExtra scalar u N tape} = ∅ := by
      ext tape
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ inG _
      exact ranges (digestOther_ranges scalar u tape N inG other)
    rw [empty, MeasureTheory.measure_empty]
    exact zero_le


end Kriterion.CRT.Privacy.StageTwo
