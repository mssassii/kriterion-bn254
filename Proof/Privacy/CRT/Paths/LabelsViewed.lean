/-
**The family-8 containment of the touch guess: `CrtDigestLabelsViewed`** (for `Flags/TouchSplit.lean`).

At every view, each of `u`'s digest-label inputs is an input of the view's entries. The view's entries are the reach's
transcript on the view's table, at the visible tags. The reach runs the digest after the replay, on the curve and off
it (`reachCM`, `reachOffCM`). The digest key's inputs are a fixed list, whatever the answers
(`Align.asked_digestKeyM`), and at part `coordBit u c p` a digest label is visible (`SameVisible.digestKey_visible`).
-/

import Proof.Privacy.CRT.Flags.TouchSplit
import Proof.Privacy.CRT.Paths.SameVisible

set_option autoImplicit false

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_digestKeyM asked_digestEvalM)

namespace LabelsViewed

/-- A digest-key input of `u` is asked by the reach, on any hash, on and off the curve. -/
theorem digestKey_in_reach [FieldCertificate] [GroupCertificate] (H : HashN) (pub : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : GarbledCircuit.LamportSignature) (c : Fin 2) (p : Fin coordinateBitCount) :
    hashInput (Kriterion.CRT.Entry.labelsOf labels c p) (digestLabelTag c.val p.val (coordBit u c p.val)) ∈
      asked H (reachDecodedCM pub u labels) := by
  have inKey : hashInput (Kriterion.CRT.Entry.labelsOf labels c p)
      (digestLabelTag c.val p.val (coordBit u c p.val)) ∈
      asked H (digestKeyM coordinateBitCount (Kriterion.CRT.Entry.labelsOf labels) u) := by
    rw [asked_digestKeyM]
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton]
    exact ⟨c, p, rfl⟩
  have inDigest : hashInput (Kriterion.CRT.Entry.labelsOf labels c p)
      (digestLabelTag c.val p.val (coordBit u c p.val)) ∈
      asked H (digestEvalM coordinateBitCount digitCount (Kriterion.CRT.Entry.labelsOf labels) u
        (fun o => pub.exception.get o)) := by
    rw [asked_digestEvalM]
    exact List.mem_append_left _ inKey
  unfold reachDecodedCM
  simp only [asked_bind, asked_pure, List.append_nil]
  by_cases valid : validate u = true
  · rw [if_pos valid]
    unfold Kriterion.CRT.Entry.reachCM
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append]
    exact Or.inr inDigest
  · rw [if_neg valid]
    unfold EntryReading.reachOffCM
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append]
    exact Or.inr inDigest

/-- **The containment for any view table**: `u`'s digest-label inputs are inputs of the reach's visible entries. -/
theorem labelsViewed_of [FieldCertificate] [GroupCertificate] (X : TagTable) (pub : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : GarbledCircuit.LamportSignature) (c : Fin 2) (p : Fin coordinateBitCount)
    (vis : Privacy.Entry Empty Empty → Bool)
    (hvis : ∀ (x : BaseField) (a : Block × Block),
      vis ⟨.hash x, a⟩ = H8.visTag Kriterion.CRT.Entry.table u (x.val / 2 ^ 128)) :
    ((hashInput (Kriterion.CRT.Entry.labelsOf labels c p) (digestLabelTag c.val p.val (coordBit u c p.val)) : ℕ) :
        BaseField) ∈
      ((programTranscript (publicAnswer (tableOracle (FI := Empty) (EI := Empty) X))
        (EntryReading.reachProgram pub u labels)).filter vis).map entryInput := by
  unfold EntryReading.reachProgram
  rw [Align.transcript_toProgram _ (EntryReading.reachDecodedM pub u labels) Kriterion.CRT.Entry.evaluateBudget
    (EntryReading.bounded_reachDecodedM pub u labels), reachDecodedM_eq, Align.ftranscript_liftHash]
  have inKey : hashInput (Kriterion.CRT.Entry.labelsOf labels c p) (digestLabelTag c.val p.val (coordBit u c p.val)) ∈
      asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) X))
        (digestKeyM coordinateBitCount (Kriterion.CRT.Entry.labelsOf labels) u) := by
    rw [asked_digestKeyM]
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton]
    exact ⟨c, p, rfl⟩
  obtain ⟨labelled, visible⟩ := SameVisible.digestKey_visible _ u _ _ inKey
  refine List.mem_map.mpr ⟨⟨.hash _, _⟩, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_,
    digestKey_in_reach _ pub u labels c p, rfl⟩, ?_⟩, rfl⟩
  rw [hvis, labelled.val]
  exact visible

end LabelsViewed

open LabelsViewed in
/-- **`CrtDigestLabelsViewed` for the concrete entry**: `u`'s digest-label inputs are inputs of every view's entries. -/
theorem crtEntry_digestLabelsViewed : Flags.CrtDigestLabelsViewed := by
  intro field group u v c p
  unfold H8.viewEntries
  have reach : Instance.crtEntry.reachProgram field group v.1 u v.2.1 = EntryReading.reachProgram v.1 u v.2.1 := rfl
  rw [reach]
  exact labelsViewed_of _ v.1 u v.2.1 c p _ fun x a => rfl

end Kriterion.CRT.Paths
