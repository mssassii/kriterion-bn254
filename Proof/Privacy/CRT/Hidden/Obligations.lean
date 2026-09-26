/-
**The hidden hop's obligations**: the
views, the designed-visible and hidden entries, the two guess obligations (P2b) and the two structural facts (P2a).
-/

import Proof.Privacy.CRT.Hybrids

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

/-! ### The hidden hop `G0U → G1U` -/

section Hidden

variable [FieldCertificate] [GroupCertificate]

/-- The table oracle of a tape. -/
def tapeOracle (tape : TableTape E) : PublicOracle FI EI :=
  tableOracle tape.2

/-- The published value of a tape (hash-only: the whole stage-1 view). -/
def stageOneView (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) : E.Public :=
  ((E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, tapeOracle E tape)).1

/-- The garbler's entries on a tape. -/
def garblerEntries (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) : List (Entry FI EI) :=
  programTranscript (publicAnswer (tapeOracle E tape))
    (E.garbleProgram inferInstance inferInstance parameter scalar tape.1)

/-- The entries the evaluator's query path reaches at an input (`E.reachProgram`, no curve refusal). -/
def reachedEntries (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput) :
    List (Entry FI EI) :=
  let garbled := (E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, tapeOracle E tape)
  programTranscript (publicAnswer (tapeOracle E tape))
    (E.reachProgram inferInstance inferInstance garbled.1 u
      ((E.scheme inferInstance inferInstance).encode garbled.2 u))

/-- The designed-visible entries at an input (the tape the rule reads is `(coins, tapeOracle)`). -/
def designedEntries (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput) :
    List (Entry FI EI) :=
  (garblerEntries E parameter scalar tape).filter fun entry =>
    crtDesigned T ⟨fun scalar tape => E.exceptional scalar tape.1⟩ scalar
      (tape.1, tapeOracle E tape) u entry

/-- A query touches a list of entries when it asks one of their queries. -/
def Touches (entries : List (Entry FI EI)) (query : PublicQuery FI EI) : Prop :=
  query ∈ entries.map Sigma.fst

/-- The stage-2 view at an input: the published value, the labels, the designed-visible entries. -/
def stageTwoView (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape E) :
    E.Public × LamportSignature × List (Entry FI EI) :=
  let garbled := (E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, tapeOracle E tape)
  (garbled.1, (E.scheme inferInstance inferInstance).encode garbled.2 u, designedEntries E T parameter scalar tape u)

open Classical in
/-- The garbler entries the designed rule hides at `u`. -/
def hiddenEntries (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput) :
    List (Entry FI EI) :=
  (garblerEntries E parameter scalar tape).filter fun entry =>
    entry ∉ designedEntries E T parameter scalar tape u

end Hidden

/-- **Obligation (stage 1)** (P2b): given the published value, a query touches a garbler entry with conditional
mass at most `ε`, under the swapped tape. -/
def CrtStageOneGuess (ε : ℝ≥0∞) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (view : E.Public)
    (query : PublicQuery FI EI),
    (swappedTableTape E).toOuterMeasure
        {tape | stageOneView E parameter scalar tape = view ∧ Touches (garblerEntries E parameter scalar tape) query} ≤
      ε * (swappedTableTape E).toOuterMeasure {tape | stageOneView E parameter scalar tape = view}

/-- **Obligation (stage 2, per input)** (P2b): off an event `bad` of the tape of mass at most
`δ`, fixed before the input, given the stage-2 view at `u`, a query touches an entry the designed rule hides with
conditional mass at most `ε`. (For the CRT entry `bad` is a curve encoding's offset near the wrap window, whose
hint would otherwise pin the curve mask and with it the key's label.) -/
def CrtStageTwoGuess (T : CrtTable) (ε δ : ℝ≥0∞) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar),
    ∃ bad : TableTape E → Prop, (swappedTableTape E).toOuterMeasure {tape | bad tape} ≤ δ ∧
      ∀ (u : AffineInput) (view : E.Public × LamportSignature × List (Entry FI EI)) (query : PublicQuery FI EI),
        (swappedTableTape E).toOuterMeasure
            {tape | stageTwoView E T parameter scalar u tape = view ∧
              Touches (hiddenEntries E T parameter scalar tape u) query ∧ ¬ bad tape} ≤
          ε * (swappedTableTape E).toOuterMeasure {tape | stageTwoView E T parameter scalar u tape = view}

/-- **Structural fact** (P2a): the garbler asks each query once. -/
def GarblerDistinct : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E),
    ((garblerEntries E parameter scalar tape).map Sigma.fst).Nodup

/-- **Structural fact, the containment** (P2a): the honest evaluator reaches every designed-visible entry, at the
garbler's point. -/
def DesignedReached (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E)
    (u : AffineInput), ∀ entry ∈ designedEntries E T parameter scalar tape u,
      entry ∈ reachedEntries E parameter scalar tape u

end

end Kriterion.CRT.Privacy
