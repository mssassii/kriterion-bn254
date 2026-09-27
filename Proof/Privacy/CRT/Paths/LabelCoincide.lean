/-
**P8's family-8 row: no hidden digest label is asked by the reach** (`Flags.CrtLabelCoincide`, `Flags/CoincidenceSplit.lean`).

The reach asks the digest labels only through its digest key (`digestKeyM`), one per position, at the part equal to
`u`'s bit (`reach_label_bit`); every other block of the reach has families other than 8 (`replay_tagged`,
`replayConv_tagged`, the finals). A garbler entry the reach asks is at a reach input (the inputs are below `p`), so a
family-8 one is at `u`'s bit, where the designed rule shows it.
-/

import Proof.Privacy.CRT.Paths.SameVisible
import Proof.Privacy.CRT.Flags.CoincidenceSplit
import Proof.Privacy.CRT.Hidden.StageTwo

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_digestKeyM asked_digestEvalM asked_of_tagged
  hashInput_div)

namespace LabelCoincide

theorem fullReplayKeys_fam : ∀ k ∈ fullReplayKeys, k.fam ≠ 8 := by
  rintro k (inC | inK | inM)
  · have := replayConvKeys_fam k inC
    omega
  · rw [Set.mem_singleton_iff.mp inK]
    decide
  · have := maskKeys_fam k inM
    omega

/-- **The reach asks a digest label only at `u`'s bit.** -/
theorem reach_label_bit [FieldCertificate] [GroupCertificate] (H : HashN) (pub : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    ∀ n ∈ asked H (reachDecodedCM pub u labels), tagFamily (n / 2 ^ 128) = 8 →
      tagPart (n / 2 ^ 128) = inputBit u (tagCoord (n / 2 ^ 128)) (tagSlot (n / 2 ^ 128)) := by
  intro n inside fam8
  have notIn : ∀ {α : Type} {S : Set TagKey} {program : CM α}, Tagged S program → (∀ k ∈ S, k.fam ≠ 8) →
      n ∈ asked H program → False := by
    intro α S program tagged away inAsked
    obtain ⟨k, member, range, label, same⟩ := asked_of_tagged tagged H n inAsked
    have fam : tagFamily (n / 2 ^ 128) = k.fam := by rw [same, hashInput_div, Align.tagFamily_key range]
    exact away k member (fam ▸ fam8)
  have fromDigest : n ∈ asked H (digestEvalM coordinateBitCount digitCount (Kriterion.CRT.Entry.labelsOf labels) u
      (fun o => pub.exception.get o)) →
      tagPart (n / 2 ^ 128) = inputBit u (tagCoord (n / 2 ^ 128)) (tagSlot (n / 2 ^ 128)) := by
    intro inDigest
    rw [asked_digestEvalM, List.mem_append] at inDigest
    rcases inDigest with inLabels | inFinals
    · rw [asked_digestKeyM] at inLabels
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at inLabels
      obtain ⟨c, p, rfl⟩ := inLabels
      have bit := coordBit_lt u c p.val
      obtain ⟨_, hcoord, hslot, hpart⟩ := Align.digestLabelTag_fields (b := coordBit u c p.val) c.isLt
        (lt_of_lt_of_le p.isLt (by decide)) (by omega)
      rw [hashInput_div, hcoord, hslot, hpart, Align.inputBit_eq_coordBit]
    · obtain ⟨s, hs, rfl⟩ := Align.mem_finals inFinals
      obtain ⟨fam9, _⟩ := Align.digestFinalTag_fields (o := s) (by simp only [digitCount] at hs; omega)
      rw [hashInput_div, fam9] at fam8
      cases fam8
  unfold reachDecodedCM at inside
  simp only [asked_bind, asked_pure, List.append_nil] at inside
  by_cases valid : validate u = true
  · rw [if_pos valid] at inside
    unfold Kriterion.CRT.Entry.reachCM at inside
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
    rcases inside with inReplay | inDigest
    · exact (notIn (replay_tagged pub u labels) fullReplayKeys_fam inReplay).elim
    · exact fromDigest inDigest
  · rw [if_neg valid] at inside
    unfold EntryReading.reachOffCM at inside
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
    rcases inside with inConv | inDigest
    · exact (notIn (replayConv_tagged pub u labels) (fun k member => by
        have := replayConvKeys_fam k member
        omega) inConv).elim
    · exact fromDigest inDigest

/-- The queries of the reach's transcript, on any oracle, are the reach's inputs. -/
theorem reachDecoded_queries [FieldCertificate] [GroupCertificate] (oracle : PublicOracle Empty Empty)
    (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : GarbledCircuit.LamportSignature)
    (bounded : (EntryReading.reachDecodedM pub u labels).Bounded Kriterion.CRT.Entry.evaluateBudget) :
    ∀ q ∈ (programTranscript (publicAnswer oracle) (FreeQuery.toProgram (EntryReading.reachDecodedM pub u labels)
        Kriterion.CRT.Entry.evaluateBudget bounded)).map Sigma.fst,
      ∃ n ∈ asked (schemeHash oracle) (reachDecodedCM pub u labels), q = .hash (n : BaseField) := by
  intro q inside
  rw [Align.transcript_toProgram (publicAnswer oracle) (EntryReading.reachDecodedM pub u labels)
    Kriterion.CRT.Entry.evaluateBudget bounded, reachDecodedM_eq, Align.ftranscript_liftHash, List.map_map] at inside
  obtain ⟨n, hn, same⟩ := List.mem_map.mp inside
  exact ⟨n, hn, same.symm⟩

end LabelCoincide

open LabelCoincide SameVisible in
/-- **P8's family-8 row for the concrete entry**: no hidden digest label is asked by the reach. -/
theorem crtEntry_labelCoincide : Flags.CrtLabelCoincide := by
  intro field group parameter scalar tape u e hidden
  obtain ⟨inG, inR, hiddenRule⟩ := hidden
  rw [StageTwo.garblerEntries_eq] at inG
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp inG
  unfold StageTwo.gAsked at hn
  have labelled := labelled_of_tagged (garbleCM_tagged scalar tape.1)
    (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) n hn
  intro fam8
  have fam : tagFamily (n / 2 ^ 128) = 8 := by
    have shown : tagFamily ((n : BaseField).val / 2 ^ 128) = 8 := fam8
    rwa [labelled.val] at shown
  unfold reachedEntries at inR
  dsimp only [Instance.crtEntry] at inR
  obtain ⟨n', hn', same⟩ := reachDecoded_queries _ _ _ _ _ _ inR
  have labelled' := labelled_of_tagged (reachDecodedCM_tagged _ u _) _ n' hn'
  have equal : n = n' := by
    have values := congrArg ZMod.val (PublicQuery.hash.inj same)
    rwa [labelled.val, labelled'.val] at values
  subst equal
  have bit := reach_label_bit _ _ u _ n hn' fam
  rw [Align.crtDesigned_hash, labelled.val, Align.designTag_label _ _ _ fam, bit] at hiddenRule
  simp at hiddenRule

end Kriterion.CRT.Paths
