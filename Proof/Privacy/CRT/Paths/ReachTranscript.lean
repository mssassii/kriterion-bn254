/-
**The reach's transcript on the concrete entry**: the evaluator's reach program (`EntryReading.reachProgram`: on the curve `Entry.reachCM`, then the decode) is the lift of one `Tagged` CM program (`reachDecodedM_eq`,
`reachDecodedCM_tagged`), so on any answers its transcript's entries are hashes of labelled inputs at distinct keys
(`reachProgram_transcript`), and the view's entries have no duplicates (`crtEntry_viewOnce`, the `viewOnce` of
`viewEntriesPerm_of`).
-/

import Proof.Privacy.CRT.Paths.Reach
import Proof.Privacy.CRT.Paths.Transcript

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws

namespace ReachTranscript

theorem liftHash_bind {α β : Type} (P : CM α) (f : α → CM β) :
    liftHash (FixedIndex := Empty) (EncIndex := Empty) (P >>= f) = liftHash P >>= fun a => liftHash (f a) := by
  induction P with
  | pure a => rfl
  | query n next ih => exact congrArg (FreeQuery.query _) (funext ih)

/-- Programs that are equal have equal transcripts, whatever their budget proofs. -/
theorem transcript_eq {α : Type} {P P' : FreeQuery Kriterion.CRT.Entry.Spec α} (same : P = P') {budget : ℕ}
    (bounded : P.Bounded budget) (bounded' : P'.Bounded budget)
    (answer : ∀ query : PublicQuery Empty Empty, query.Answer) :
    programTranscript answer (FreeQuery.toProgram P budget bounded) =
      programTranscript answer (FreeQuery.toProgram P' budget bounded') := by
  subst same
  rfl

end ReachTranscript

/-- **The reach as one CM program**: on the curve `Entry.reachCM`, off it `reachOffCM`, then the decode. -/
def reachDecodedCM [FieldCertificate] [GroupCertificate] (pub : Kriterion.CRT.Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) : CM (Option (Option Point)) :=
  (if validate input then Kriterion.CRT.Entry.reachCM pub input labels
    else EntryReading.reachOffCM pub input labels) >>= fun result => pure (some (Garbling.decodeResult result))

theorem reachDecodedM_eq [FieldCertificate] [GroupCertificate] (pub : Kriterion.CRT.Entry.Public)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    EntryReading.reachDecodedM pub input labels = liftHash (reachDecodedCM pub input labels) := by
  unfold EntryReading.reachDecodedM reachDecodedCM
  rw [ReachTranscript.liftHash_bind]
  by_cases valid : validate input = true
  · rw [if_pos valid, if_pos valid]
    rfl
  · rw [if_neg valid, if_neg valid]
    rfl

/-- **The reach is `Tagged`**, on and off the curve. -/
theorem reachDecodedCM_tagged [FieldCertificate] [GroupCertificate] (pub : Kriterion.CRT.Entry.Public)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Tagged (reachKeys ∪ reachOffKeys) (reachDecodedCM pub input labels) := by
  unfold reachDecodedCM
  exact Tagged.bind_pure (Tagged.ite (fun _ => (reachCM_tagged pub input labels).mono Set.subset_union_left)
    fun _ => (reachOffCM_tagged pub input labels).mono Set.subset_union_right) _

/-- **The reach's transcript**, on any answers: every entry is the hash of a labelled input at a key in range, and
the entries' inputs are pairwise distinct. -/
theorem reachProgram_transcript [FieldCertificate] [GroupCertificate]
    (answer : ∀ query : PublicQuery Empty Empty, query.Answer) (pub : Kriterion.CRT.Entry.Public)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    (∀ entry ∈ programTranscript answer (EntryReading.reachProgram pub input labels),
      ∃ key ∈ reachKeys ∪ reachOffKeys, key.InRange ∧ ∃ label : Block, entry.1 = .hash (inputOf (key, label))) ∧
    ((programTranscript answer (EntryReading.reachProgram pub input labels)).map entryInput).Nodup := by
  have boundedCM : (liftHash (FixedIndex := Empty) (EncIndex := Empty)
      (reachDecodedCM pub input labels)).Bounded Kriterion.CRT.Entry.evaluateBudget :=
    reachDecodedM_eq pub input labels ▸ EntryReading.bounded_reachDecodedM pub input labels
  have same : programTranscript answer (EntryReading.reachProgram pub input labels) =
      programTranscript answer (FreeQuery.toProgram (liftHash (reachDecodedCM pub input labels))
        Kriterion.CRT.Entry.evaluateBudget boundedCM) := by
    unfold EntryReading.reachProgram
    exact ReachTranscript.transcript_eq (reachDecodedM_eq pub input labels) _ _ answer
  rw [same]
  have facts := transcript_of_keyRun answer (reachDecodedCM_tagged pub input labels)
    (fun _ inside => absurd inside List.not_mem_nil) List.nodup_nil Kriterion.CRT.Entry.evaluateBudget boundedCM
  rw [List.map_nil, List.append_nil] at facts
  exact facts

/-- **`viewOnce` of `viewEntriesPerm_of` for the concrete entry**: the view's entries have no duplicates. -/
theorem crtEntry_viewOnce (T : CrtTable) :
    ∀ [FieldCertificate] [GroupCertificate] [Fintype Empty] [Fintype Empty] [DecidableEq Empty] [DecidableEq Empty]
      (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) (u : AffineInput),
      (H8.viewEntries Instance.crtEntry T u (H8.realView Instance.crtEntry T parameter scalar u tape)).Nodup := by
  intro _ _ _ _ _ _ parameter scalar tape u
  unfold H8.viewEntries
  refine List.Nodup.filter _ ?_
  dsimp only [Instance.crtEntry]
  exact (reachProgram_transcript _ _ _ _).2.of_map _

end Kriterion.CRT.Paths
