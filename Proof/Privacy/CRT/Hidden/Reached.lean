/-
**H5 for the CRT entry: `DesignedReached crtEntry table`** (P2a).

The garbler's and the reach's transcripts on the table oracle are their `asked` inputs with the oracle's answers
(`transcript_toProgram`, `ftranscript_liftHash`); a designed garbler entry is a garbler input whose tag the designed
rule shows (`crtDesigned_hash`, the inputs are below `p`), and `Align.garble_designed_reached` puts that input in the
reach.
-/

import Proof.Privacy.CRT.Hidden.AlignEntry
import Proof.Privacy.CRT.Hidden.Obligations
import Proof.Privacy.CRT.EntryInstance
import Proof.Privacy.CRT.Paths.TableFacts

namespace Kriterion.CRT.Privacy.Align

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT

/-! ### Transcripts of lifted programs -/

section Transcripts

variable {FI EI : Type}

/-- The (query, answer) pairs of a free program on a complete oracle, in order. -/
def ftranscript {α : Type} (answer : ∀ query : PublicQuery FI EI, query.Answer) :
    FreeQuery (publicOracleSpec FI EI) α → List (Entry FI EI)
  | .pure _ => []
  | .query request next => ⟨request, answer request⟩ :: ftranscript answer (next (answer request))

theorem transcript_toProgram {α : Type} (answer : ∀ query : PublicQuery FI EI, query.Answer) :
    ∀ (program : FreeQuery (publicOracleSpec FI EI) α) (budget : ℕ) (bounded : program.Bounded budget),
      programTranscript answer (FreeQuery.toProgram program budget bounded) = ftranscript answer program := by
  intro program
  induction program with
  | pure value => intro budget bounded; rfl
  | query request next ih =>
      intro budget bounded
      cases budget with
      | zero => exact absurd bounded FreeQuery.Bounded.not_zero
      | succ budget =>
          show ⟨request, answer request⟩ :: programTranscript answer
              (FreeQuery.toProgram (next (answer request)) budget (bounded.next (answer request))) = _
          rw [ih]
          rfl

theorem ftranscript_liftHash {α : Type} (oracle : PublicOracle FI EI) :
    ∀ program : CM α, ftranscript (publicAnswer oracle) (liftHash program) =
      (asked (schemeHash oracle) program).map fun n : ℕ => (⟨.hash (n : BaseField), oracle.2.2 (n : BaseField)⟩ :
        Entry FI EI) := by
  intro program
  induction program with
  | pure value => rfl
  | query input next ih =>
      show ⟨.hash (input : BaseField), oracle.2.2 (input : BaseField)⟩ ::
          ftranscript (publicAnswer oracle) (liftHash (next (oracle.2.2 (input : BaseField)))) = _
      rw [ih]
      rfl

theorem ftranscript_bind_pure {α β : Type} (answer : ∀ query : PublicQuery FI EI, query.Answer)
    (program : FreeQuery (publicOracleSpec FI EI) α) (f : α → β) :
    ftranscript answer (program >>= fun value => Pure.pure (f value)) = ftranscript answer program := by
  induction program with
  | pure value => rfl
  | query request next ih =>
      show ⟨request, answer request⟩ :: ftranscript answer (next (answer request) >>= fun value => Pure.pure (f value)) = _
      rw [ih]
      rfl

end Transcripts

/-! ### The inputs of the garbler are below `p` -/

theorem garbler_input_lt (H : HashN) (scalar : NonZeroScalar) (coins : Entry.Coins) :
    ∀ x ∈ asked H (Entry.garbleCM scalar coins), x < baseFieldModulus := by
  intro x inside
  obtain ⟨k, _, range, label, rfl⟩ := asked_of_tagged (Paths.garbleCM_tagged scalar coins) H x inside
  exact Paths.hashInput_lt range

theorem val_natCast_of_lt {x : ℕ} (small : x < baseFieldModulus) : ((x : BaseField)).val = x := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt small]

/-! ### H5 -/

/-- **H5 (`DesignedReached`) for the CRT entry at its table.** -/
theorem crtEntry_designedReached : DesignedReached Instance.crtEntry Entry.table := by
  intro field group parameter scalar tape u entry designed
  obtain ⟨coins, table⟩ := tape
  have transcriptG := transcript_toProgram (publicAnswer (tableOracle (FI := Empty) (EI := Empty) table))
    (liftHash (Entry.garbleCM scalar coins)) Entry.garbleBudget (Entry.bounded_garbleM scalar coins)
  unfold designedEntries garblerEntries tapeOracle at designed
  dsimp only [Instance.crtEntry] at designed
  rw [List.mem_filter] at designed
  obtain ⟨inGarbler, isDesigned⟩ := designed
  unfold Entry.garbleProgram Entry.garbleM at inGarbler
  rw [transcriptG, ftranscript_liftHash] at inGarbler
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp inGarbler
  rw [crtDesigned_hash,
    val_natCast_of_lt (garbler_input_lt (schemeHash (tableOracle table)) scalar coins x hx)] at isDesigned
  dsimp only at isDesigned
  have parts := garble_designed_parts (schemeHash (tableOracle table)) scalar coins u x hx isDesigned
  have onReach := garble_designed_reached (schemeHash (tableOracle table)) scalar coins u x hx isDesigned
  have transcriptR := transcript_toProgram (publicAnswer (tableOracle (FI := Empty) (EI := Empty) table))
    (EntryReading.reachDecodedM (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table))
      scalar coins) u (EntryCorrect.labelsFor coins u)) Entry.evaluateBudget
    (EntryReading.bounded_reachDecodedM (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty)
      table)) scalar coins) u (EntryCorrect.labelsFor coins u))
  have hgarble : (@Entry.scheme field group).garble parameter scalar (coins, tableOracle table) =
      (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins,
        coins.inputMacKey) := by
    refine (Paths.entry_garble_eval field group parameter scalar coins (tableOracle table)).trans ?_
    unfold Entry.garbleProgram
    rw [FreeQuery.eval_toProgram]
    unfold Entry.garbleM
    rw [eval_liftHash]
    exact EntryCorrect.garbleCM_eval _ scalar coins
  have hencode : (@Entry.scheme field group).encode coins.inputMacKey u = EntryCorrect.labelsFor coins u := by
    unfold Entry.scheme EntryCorrect.labelsFor
    rfl
  unfold reachedEntries tapeOracle
  dsimp only [Instance.crtEntry]
  rw [hgarble]
  dsimp only
  unfold EntryReading.reachProgram
  rw [hencode, transcriptR]
  unfold EntryReading.reachDecodedM
  rw [ftranscript_bind_pure]
  split
  · unfold Entry.reachM
    rw [ftranscript_liftHash]
    exact List.mem_map.mpr ⟨x, onReach, rfl⟩
  · rename_i offCurve
    rw [ftranscript_liftHash]
    refine List.mem_map.mpr ⟨x, ?_, rfl⟩
    unfold EntryReading.reachOffCM
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append]
    rcases parts with inConv | ⟨on, _⟩ | inDigest
    · exact Or.inl inConv
    · exact absurd on offCurve
    · exact Or.inr inDigest

end Kriterion.CRT.Privacy.Align
