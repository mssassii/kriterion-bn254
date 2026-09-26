/-
**The hybrids of the CRT chain** `G0 → G0T → G0U → G1U → HW → H → I`.

All seven games are defined over `CrtEntry`, the entry as the privacy proof reads it (the `Solution` fields of
`EntrySig`, the evaluator program, the bridge input `t`, the digest's exceptional inputs, the site layout and the
route-M view). `EntryInstance.lean` supplies the concrete instance.

* `realHybrid` (`G0`): the tape-sampled real game.
* `tablePlantedHybrid` (`G0T`): the hash is an answer table indexed by tags (every hash input of the entry is
  labelled with a distinct tag, the bridge key included, so the tag reading answers every garbler input); the garbler's transcript on it is planted into the lazy oracle before stage 1.
* `padSwappedHybrid` (`G0U`): the same, with every pad and mask site drawn as a uniform target then a fibre sample.
* `hiddenDeletedHybrid` (`G1U`): stage 1 on an empty oracle; at the input choice the garbler entries the evaluator
  reaches are installed, the others (hidden) never.
* `publicFirstHybrid` (`HW`), `openedHybrid` (`H`), `idealHybrid` (`I`): the route-M simulator with (real rows,
  refill), (simulated rows, refill), (simulated rows, lazy).
-/

import Proof.Privacy.CRT.AbstractSimulator
import Proof.Privacy.CRT.Designed

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT

noncomputable section

/-! ### The entry as the privacy proof reads it -/

/-- **The CRT entry for the privacy chain.** -/
structure CrtEntry (FI EI : Type) extends EntrySig FI EI where
  /-- The evaluator program (the `Solution` field). -/
  evaluateBudget : ℕ
  evaluateProgram : (field : FieldCertificate) → @GroupCertificate field → Public → AffineInput →
    LamportSignature → QueryProgram (publicOracleSpec FI EI) (Option (Option (@Point field))) evaluateBudget
  /-- The evaluator's query path without the curve refusal (replay, rows, digest labels and finals), run at every
  input. `G1U`'s reach and `reachedEntries` read it: the evaluator refuses an off-curve input
  before any query, while the designed rule shows cold positions and the digest labels off the curve too. On the
  curve it asks the same queries as `evaluateProgram`. -/
  reachProgram : (field : FieldCertificate) → @GroupCertificate field → Public → AffineInput →
    LamportSignature → QueryProgram (publicOracleSpec FI EI) (Option (Option (@Point field))) evaluateBudget
  /-- The bridge input `t` of the curve check (so no game reads `t` directly). -/
  bridgeInput : Coins → BaseField
  /-- The exceptional input of digit `o` (a function of the scalar and the garbler's offsets). -/
  exceptional : NonZeroScalar → Coins → ℕ → Option AffineInput
  /-- The pad and mask sites. -/
  layout : SiteLayout
  /-- The route-M view. -/
  view : (field : FieldCertificate) → @GroupCertificate field → @RouteMView field Public

/-! ### Answer tables and transcripts -/

/-- A table of hash answers indexed by tags (tags are below `2^40`, D10). -/
abbrev TagTable := Fin (2 ^ 40) → Block × Block

/-- The tag of a field element read as a labelled input. -/
def tagOfInput (x : BaseField) : Fin (2 ^ 40) := ⟨x.val / 2 ^ 128 % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

variable {FI EI : Type}

/-- **The oracle of a table** (`G0T`): every hash input is answered by its tag. The permutation parts are
irrelevant (the CRT entry has no permutation index, D2). -/
def tableOracle (table : TagTable) : PublicOracle FI EI :=
  (Classical.arbitrary _, Classical.arbitrary _, fun x => table (tagOfInput x))

/-- The (query, answer) pairs of a program on a complete oracle, in order. -/
def programTranscript {α : Type} (answer : ∀ query : PublicQuery FI EI, query.Answer) :
    {budget : ℕ} → QueryProgram (publicOracleSpec FI EI) α budget → List (Entry FI EI)
  | _, .pure _ => []
  | _, .query request next => ⟨request, answer request⟩ :: programTranscript answer (next (answer request))

/-- Install entries into the lazy oracle, in order; a failed program is skipped. -/
def installEntries [DecidableEq FI] [DecidableEq EI] (entries : List (Entry FI EI))
    (oracle : LazyOracle.State FI EI) : LazyOracle.State FI EI :=
  entries.foldl (fun current entry => (LazyOracle.program entry.1 entry.2 current).getD current) oracle

/-- Overwrite a table at a site's tags with the site's answers. -/
def overwrite (table : TagTable) (tags : List ℕ) (answers : List (Block × Block)) : TagTable :=
  (tags.zip answers).foldl (fun current pair => Function.update current ⟨pair.1 % 2 ^ 40,
    Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ pair.2) table

/-- **The swapped table law** (`G0U`): uniform, then every site redrawn from its swapped law. -/
def swappedTableLaw (layout : SiteLayout) : PMF TagTable :=
  layout.sites.foldl (fun law site => law.bind fun table =>
    (layout.law site).map fun answers => overwrite table (siteTags layout site) answers)
    (PMF.uniformOfFintype TagTable)

/-! ### The games -/

section Games

variable (E : CrtEntry FI EI)

/-- The tape of `G0T` and later: coins and a tag table. -/
abbrev TableTape (E : CrtEntry FI EI) := E.Coins × TagTable

/-- **`G0`**: the tape-sampled real game. -/
def realHybrid : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  letI : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
  haveI : Nonempty E.Coins := ⟨E.coinWitness⟩
  realGame (E.scheme inferInstance inferInstance) (fun _ => PMF.uniformOfFintype (E.Coins × PublicOracle FI EI))
    (publicHandler Prod.snd) adversary parameter scalar ()

/-- The planted game on a tape law: garble on the table oracle, plant the whole transcript, run both stages. -/
def plantedGame [FieldCertificate] [GroupCertificate] [DecidableEq FI] [DecidableEq EI] (tapeLaw : PMF (TableTape E))
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) : PMF Bool :=
  tapeLaw.bind fun tape =>
    let oracle : PublicOracle FI EI := tableOracle tape.2
    let garbled := (E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, oracle)
    let planted := installEntries
      (programTranscript (publicAnswer oracle) (E.garbleProgram inferInstance inferInstance parameter scalar tape.1))
      LazyOracle.empty
    (LazyOracle.run (adversary.chooseInput parameter garbled.1 ()) planted).bind fun selected =>
      (LazyOracle.run (adversary.decide parameter garbled.1
        ((E.scheme inferInstance inferInstance).encode garbled.2 selected.1.1) () selected.1.2) selected.2).map Prod.fst

/-- The uniform table tape. -/
def uniformTableTape : PMF (TableTape E) :=
  letI : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
  haveI : Nonempty E.Coins := ⟨E.coinWitness⟩
  PMF.uniformOfFintype (TableTape E)

/-- The swapped table tape: coins uniform, the table from `swappedTableLaw`. -/
def swappedTableTape : PMF (TableTape E) :=
  letI : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
  haveI : Nonempty E.Coins := ⟨E.coinWitness⟩
  (PMF.uniformOfFintype E.Coins).bind fun coins => (swappedTableLaw E.layout).map fun table => (coins, table)

/-- **`G0T`**: the answer table planted before stage 1 (P6a1's table form). -/
def tablePlantedHybrid : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  plantedGame E (uniformTableTape E) adversary parameter scalar

/-- **`G0U`**: every pad and mask site swapped to a uniform target and a fibre sample. -/
def padSwappedHybrid : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  plantedGame E (swappedTableTape E) adversary parameter scalar

open Classical in
/-- **`G1U`**: `G0U`'s garbling; stage 1 on an empty oracle; at the input choice the garbler entries the evaluator
reaches at the selected input are installed, the hidden ones never. The reach is `E.reachProgram`'s transcript (the
query path without the curve refusal), so off the curve the reached entries are installed too. -/
def hiddenDeletedHybrid : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  (swappedTableTape E).bind fun tape =>
    let oracle : PublicOracle FI EI := tableOracle tape.2
    let scheme := E.scheme inferInstance inferInstance
    let garbled := scheme.garble parameter scalar (tape.1, oracle)
    let entries := programTranscript (publicAnswer oracle)
      (E.garbleProgram inferInstance inferInstance parameter scalar tape.1)
    (LazyOracle.run (adversary.chooseInput parameter garbled.1 ()) LazyOracle.empty).bind fun selected =>
      let labels := scheme.encode garbled.2 selected.1.1
      let reach := programTranscript (publicAnswer oracle)
        (E.reachProgram inferInstance inferInstance garbled.1 selected.1.1 labels)
      let visible := entries.filter fun entry => decide (entry.1 ∈ reach.map Sigma.fst)
      (LazyOracle.run (adversary.decide parameter garbled.1 labels () selected.1.2)
        (installEntries visible selected.2)).map Prod.fst

/-- **`HW`**: route M with the real rows and the refill reader. -/
def publicFirstHybrid : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  abstractIdealGame (E.scheme inferInstance inferInstance)
    (routeMSimulator (E.view inferInstance inferInstance)
      ((E.view inferInstance inferInstance).realRows scalar) (refillReader E.layout))
    adversary parameter scalar ()

/-- **`H`**: route M with the simulated rows and the refill reader. -/
def openedHybrid : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  abstractIdealGame (E.scheme inferInstance inferInstance)
    (routeMSimulator (E.view inferInstance inferInstance)
      ((E.view inferInstance inferInstance).simRows scalar) (refillReader E.layout))
    adversary parameter scalar ()

/-- **`I`**: route M with the simulated rows and the lazy reader; the machine realises exactly this. -/
def idealHybrid : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  abstractIdealGame (E.scheme inferInstance inferInstance)
    (routeMSimulator (E.view inferInstance inferInstance)
      ((E.view inferInstance inferInstance).simRows scalar) lazyReader)
    adversary parameter scalar ()

/-- **The chain of the CRT entry.** -/
def crtChain : CrtChain FI EI E.Public where
  real := realHybrid E
  tablePlanted := tablePlantedHybrid E
  padSwapped := padSwappedHybrid E
  hiddenDeleted := hiddenDeletedHybrid E
  publicFirst := publicFirstHybrid E
  opened := openedHybrid E
  ideal := idealHybrid E

end Games

end

end Kriterion.CRT.Privacy
