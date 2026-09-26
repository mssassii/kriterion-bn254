/-
**P8, the coincidence row for tag families 7 (masks) and 10 (the bridge key)** (`CrtKeyMaskHidden`).

A hidden entry the reach asks never has family 7 or 10, by cases on whether the input is on the curve:

* on the curve (`validate u = true`) the designed rule shows every family-7 and family-10 hash
  (`KeyMaskHidden.crtDesigned_keyMask`), so such an entry is not hidden;
* off the curve (`validate u = false`) the reach is `reachOffCM` followed by the decode, which is
  `Tagged reachOffKeys` (`KeyMaskHidden.reachDecodedCM_taggedOff`); so every entry it asks is the hash of a labelled
  input at a key of `replayConvKeys ∪ digestKeys` (`KeyMaskHidden.reachProgram_offKeys`), whose family is at most 6,
  or 8, or 9 (`replayConvKeys_fam`, `digestKeys_fam`, `tagFamily_inputOf`).

`crtKeyMaskHidden : CrtKeyMaskHidden`.
-/

import Proof.Privacy.CRT.Flags.CoincidenceSplit
import Proof.Privacy.CRT.Paths.ReachTranscript

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.Instance
open Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy.Laws Kriterion.CRT.Paths

namespace KeyMaskHidden

/-- An entry of family other than `11` is a hash, and its family is the tag family of the hashed value. -/
theorem entryFamily_hash {FI EI : Type} (e : Entry FI EI) (family : entryFamily e ≠ 11) :
    ∃ x, e.1 = .hash x ∧ entryFamily e = tagFamily (x.val / 2 ^ 128) := by
  rcases e with ⟨q, a⟩
  cases q
  all_goals first
    | exact ⟨_, rfl, rfl⟩
    | exact absurd rfl family

/-- The designed rule on a family-7 or family-10 hash is `validate u`. -/
theorem crtDesigned_keyMask {FI EI Coins Oracle : Type} (T : CrtTable) (view : TapeView Coins Oracle)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) (u : AffineInput) (e : Entry FI EI) (x : BaseField)
    (hx : e.1 = .hash x) (family : tagFamily (x.val / 2 ^ 128) = 7 ∨ tagFamily (x.val / 2 ^ 128) = 10) :
    crtDesigned T view scalar tape u e = validate u := by
  rcases e with ⟨q, a⟩
  dsimp only at hx
  subst hx
  unfold crtDesigned
  dsimp only
  generalize tagFamily (x.val / 2 ^ 128) = fam at family
  rcases family with rfl | rfl <;> rfl

/-- **The reach off the curve is `Tagged reachOffKeys`**: `reachOffCM`, then the decode. -/
theorem reachDecodedCM_taggedOff [FieldCertificate] [GroupCertificate] (pub : Kriterion.CRT.Entry.Public)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) (invalid : validate input = false) :
    Tagged reachOffKeys (reachDecodedCM pub input labels) := by
  unfold reachDecodedCM
  rw [if_neg (by rw [invalid]; exact Bool.false_ne_true)]
  exact Tagged.bind_pure (reachOffCM_tagged pub input labels) _

/-- **The reach's transcript off the curve**, on any answers: every entry is the hash of a labelled input at a key of
`reachOffKeys` in range. -/
theorem reachProgram_offKeys [FieldCertificate] [GroupCertificate]
    (answer : ∀ query : PublicQuery Empty Empty, query.Answer) (pub : Kriterion.CRT.Entry.Public)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) (invalid : validate input = false) :
    ∀ entry ∈ programTranscript answer (EntryReading.reachProgram pub input labels),
      ∃ key ∈ reachOffKeys, key.InRange ∧ ∃ label : Block, entry.1 = .hash (inputOf (key, label)) := by
  have boundedCM : (liftHash (FixedIndex := Empty) (EncIndex := Empty)
      (reachDecodedCM pub input labels)).Bounded Kriterion.CRT.Entry.evaluateBudget :=
    reachDecodedM_eq pub input labels ▸ EntryReading.bounded_reachDecodedM pub input labels
  have same : programTranscript answer (EntryReading.reachProgram pub input labels) =
      programTranscript answer (FreeQuery.toProgram (liftHash (reachDecodedCM pub input labels))
        Kriterion.CRT.Entry.evaluateBudget boundedCM) := by
    unfold EntryReading.reachProgram
    exact ReachTranscript.transcript_eq (reachDecodedM_eq pub input labels) _ _ answer
  rw [same]
  exact (transcript_of_keyRun answer (reachDecodedCM_taggedOff pub input labels invalid)
    (fun _ inside => absurd inside List.not_mem_nil) List.nodup_nil Kriterion.CRT.Entry.evaluateBudget boundedCM).1

/-- The keys the reach asks off the curve have family at most 6, or 8, or 9. -/
theorem reachOffKeys_fam : ∀ key ∈ reachOffKeys, key.fam ≠ 7 ∧ key.fam ≠ 10 := by
  intro key inside
  rcases inside with conv | digest
  · have := replayConvKeys_fam key conv
    omega
  · have := digestKeys_fam key digest
    omega

end KeyMaskHidden

open KeyMaskHidden in
/-- **`CrtKeyMaskHidden`**: a hidden entry the reach asks never has tag family 7 or 10. -/
theorem crtKeyMaskHidden : CrtKeyMaskHidden := by
  intro field group parameter scalar tape u e hidden
  suffices never : ¬ (entryFamily e = 7 ∨ entryFamily e = 10) by omega
  intro bad
  obtain ⟨x, hx, fx⟩ := entryFamily_hash e (by omega)
  cases valid : validate u
  · -- off the curve: the reach asks only keys of `reachOffKeys`
    obtain ⟨r, rin, req⟩ := List.mem_map.mp hidden.2.1
    unfold reachedEntries at rin
    dsimp only [Instance.crtEntry] at rin
    obtain ⟨key, kin, range, label, eq⟩ := reachProgram_offKeys _ _ u _ valid r rin
    have same := hx.symm.trans (req.symm.trans eq)
    injection same with xeq
    rw [fx, xeq, tagFamily_inputOf range] at bad
    have := reachOffKeys_fam key kin
    omega
  · -- on the curve: the designed rule shows families 7 and 10
    have shown := hidden.2.2
    rw [crtDesigned_keyMask _ _ _ _ _ e x hx (fx ▸ bad), valid] at shown
    exact Bool.noConfusion shown

end Kriterion.CRT.Privacy.Flags
