/-
**P7, the public-first hop `G1U → HW`, part 3: the middle games `M'` and `M`, and the lift from a per-input core**
(port of xinshu's `PublicFirst/Middle.lean`, `MiddleOff.lean` section 2 and `Lift.lean` section 3 to the route-M
simulator of `AbstractSimulator.lean`; hash-only, so the private run, the touch and the merge live on the hash table).

`M` is `HW` (`publicFirstHybrid`) with its stage 2 run on a **private** empty oracle and merged into the stage-1
state `σ₁` at the end (`mergeState`), flagged (`none`) when the private final state **meets** `σ₁` (a point both
store) or a reveal flag holds, and augmented by a **shadow** (`CrtShadow`): coins, and extra CRT programs whose
answers are discarded, run privately after the path (on the curve: the reach's digest, which `HW` does not replay,
F6; off the curve: the reach's on-curve branch).

On the curve, a private replay that already meets `σ₁` is flagged at once, and a rows, preimage or
fourth-block abort or a failed private collector program is flagged too (`HW` ends such a game with
`false`, F5, and a flag only lowers `M`).

Off the curve the shadow's program runs from the empty oracle through an `OffRun`: `M` reads it lazily
(`lazyRun`); `M'` draws one table from the swapped layout law and answers every query by its tag (`tableRun`,
`tableReader`), as `G1U°`'s table does. Both store exactly the asked points; their distance is the off-curve third
swap (xinshu's `MiddleOff` pattern, with the table in place of the tape).

* `middleStage2`, `middleGame`: the definitions.
* `CrtLiftCore`: the **per-input core** (the interface to the core H8 and the laws P6): at every input, stage-1
  state, adversary stage 2 and weight on the published value, `M'`'s flag-down stage-2 mass averaged over the source
  is below `G1U°`'s stage-2 mass averaged over the swapped tape.
* `below_of_core`: `Below G1U° M'` from the per-input core (xinshu's `flagMono_of_core`, one Fubini step).
-/

import Proof.Privacy.CRT.PublicFirst.Hop

namespace Kriterion.CRT.Privacy.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open scoped ENNReal

noncomputable section

variable {FI EI : Type}

/-! ### 1. Private states on the hash table -/

/-- The hash points a lazy state stores. -/
def storedPoints (state : LazyOracle.State FI EI) : List BaseField := state.hash.map Prod.fst

/-- **A private state meets a stage-1 state**: some hash point is stored by both. -/
def Meets (planted state : LazyOracle.State FI EI) : Prop :=
  ∃ x ∈ storedPoints state, x ∈ storedPoints planted

/-- **The merge**: the private hash pairs on top of the stage-1 state. -/
def mergeState (planted state : LazyOracle.State FI EI) : LazyOracle.State FI EI :=
  { planted with hash := state.hash ++ planted.hash }

/-! ### 2. The shadow and the middle games -/

/-- **The shadow of the middle game** (xinshu's `Shadow`, for the CRT): its own coins, extra CRT programs whose
answers are discarded (on the curve after the path and the collector programs; off the curve alone), and the reveal
flags (on the curve they may read the target rows, e.g. the doubling, and the coins, e.g. the wrap event pulled back
through the core's bijection). -/
structure CrtShadow (Source : Type) (FI EI : Type) where
  Coin : Type
  law : PMF Coin
  onCurve : Source → AffineInput → Coin → CM Unit
  offCurve : Source → AffineInput → Coin → CM Unit
  revealOn : Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → Coin →
    LazyOracle.State FI EI → Prop
  revealOff : Source → AffineInput → Coin → LazyOracle.State FI EI → Prop

/-! ### 3. The off-curve runs -/

section Runs

variable [DecidableEq FI] [DecidableEq EI]

/-- **The table reader** (`M'` off the curve): a stored point returns its answer; a fresh point is answered by the
table at its tag, and stored. -/
def tableReader (table : TagTable) : Reader FI EI := fun input state =>
  match (LazyOracle.lookup (.hash (input : BaseField)) state : Option (Block × Block)) with
  | some answer => PMF.pure (answer, state)
  | none => PMF.pure (table (tagOfInput (input : BaseField)),
      (LazyOracle.program (.hash (input : BaseField)) (table (tagOfInput (input : BaseField))) state).getD state)

/-- How a middle game runs the shadow's off-curve program from the empty oracle. -/
abbrev OffRun (FI EI : Type) := CM Unit → PMF (Unit × LazyOracle.State FI EI)

/-- **`M`'s off-curve run**: the program through the lazy reader. -/
def lazyRun : OffRun FI EI := fun program => runReader lazyReader program LazyOracle.empty

/-- **`M'`'s off-curve run**: a table from `law`, then the program through the table reader. -/
def tableRun (law : PMF TagTable) : OffRun FI EI := fun program =>
  law.bind fun table => runReader (tableReader table) program LazyOracle.empty

end Runs

variable (E : CrtEntry FI EI)

section Games

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The route-M view at the instances in scope. -/
abbrev viewHere : RouteMView E.Public := E.view inferInstance inferInstance

/-- The flagged ending of a private stage 2: flag (`none`) when the private state meets the stage-1 state or the
reveal holds, otherwise the labels and the merged state. -/
def finishPrivate (planted : LazyOracle.State FI EI) (labels : LamportSignature) (reveal : Prop)
    (state : LazyOracle.State FI EI) : Option (Option (LamportSignature × LazyOracle.State FI EI)) :=
  open Classical in
  if Meets planted state ∨ reveal then none else some (some (labels, mergeState planted state))

/-- The route-M collector draws of `HW` (preimages and fourth blocks, any abort aborts). -/
def collectorDraws (masks : BMR.Collector → BaseField) :
    PMF (Option (List (BMR.Collector × ((Block × Block × Block) × Block)))) :=
  drawAll (fun c => ((viewHere E).preimage (masks c)).bind fun limbs => match limbs with
      | none => PMF.pure none
      | some limbs => (viewHere E).fourth.map (Option.map fun fourth => (limbs, fourth)))
    collectorList

/-- **The middle game's stage 2** from the source, the input, its output and the stage-1 state (`none` a flag; an
abort is a flag too). -/
def middleStage2 (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (output : Option Point)
    (planted : LazyOracle.State FI EI) :
    PMF (Option (Option (LamportSignature × LazyOracle.State FI EI))) :=
  let labels := (viewHere E).labels source u
  let published := (viewHere E).publish source
  match output with
  | none => shadow.law.bind fun coin =>
      (offRun (shadow.offCurve source u coin)).map fun ran =>
        finishPrivate planted labels (shadow.revealOff source u coin ran.2) ran.2
  | some target =>
      (routeMReplay (viewHere E) (refillReader E.layout) published u labels LazyOracle.empty).bind fun ran =>
        open Classical in
        if Meets planted ran.2 then PMF.pure none else
        ((viewHere E).realRows scalar u target).bind fun drawnRows => match drawnRows with
          | none => PMF.pure none
          | some targets =>
            (collectorDraws E (collectorMasks u ran.1 ((viewHere E).gammaOf published) targets)).bind
              fun drawn => match drawn with
              | none => PMF.pure none
              | some drawn => match programHashAll (programRequests ran.1.key drawn) ran.2 with
                | none => PMF.pure none
                | some installed => shadow.law.bind fun coin =>
                  (runReader lazyReader (shadow.onCurve source u coin) installed).map fun shadowed =>
                    finishPrivate planted labels (shadow.revealOn source u targets coin shadowed.2) shadowed.2

/-- The adversary's stage 2 after a flagged stage 2 of a simulator (flag, abort, or the labels and a state). -/
def stageTwoCont {budget : ℕ} (decide : LamportSignature →
      OracleProgram (publicOracleSpec FI EI) Bool budget) :
    Option (Option (LamportSignature × LazyOracle.State FI EI)) → PMF (Option Bool)
  | none => PMF.pure none
  | some none => PMF.pure (some false)
  | some (some (labels, state)) => (LazyOracle.run (decide labels) state).map fun result => some result.1

/-- **The middle game** with a shadow and an off-curve reader. -/
def middleGame (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) : PMF (Option Bool) :=
  letI := (viewHere E).sourceFintype
  haveI := (viewHere E).sourceNonempty
  (PMF.uniformOfFintype (viewHere E).Source).bind fun source =>
    (LazyOracle.run (adversary.chooseInput parameter ((viewHere E).publish source) ()) LazyOracle.empty).bind
      fun selected =>
        (middleStage2 E shadow offRun scalar source selected.1.1
            ((E.scheme inferInstance inferInstance).function scalar selected.1.1) selected.2).bind
          (stageTwoCont fun labels =>
            adversary.decide parameter ((viewHere E).publish source) labels () selected.1.2)

/-! ### 3. The per-input core and the lift -/

/-- The weight of an adversary stage 2 after a flagged stage 2, at the bit `b` (a flag weighs `0`). -/
def stageTwoWeight {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (b : Bool) (outcome : Option (Option (LamportSignature × LazyOracle.State FI EI))) : ℝ≥0∞ :=
  stageTwoCont decide outcome (some b)

/-- **`M`'s flag-down stage-2 weight** at one source, input and stage-1 state. -/
def middleWeight (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI) (scalar : NonZeroScalar)
    (source : (viewHere E).Source) (u : AffineInput) (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) : ℝ≥0∞ :=
  ∑' outcome, middleStage2 E shadow offRun scalar source u
      ((E.scheme inferInstance inferInstance).function scalar u) planted outcome *
    stageTwoWeight (decide ((viewHere E).publish source)) b outcome

/-- **`G1U°`'s stage-2 weight** at one tape, input and stage-1 state. -/
def upperWeight (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput)
    (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) : ℝ≥0∞ :=
  let oracle : PublicOracle FI EI := tableOracle tape.2
  let scheme := E.scheme inferInstance inferInstance
  let garbled := scheme.garble parameter scalar (tape.1, oracle)
  ((LazyOracle.run (decide garbled.1 (scheme.encode garbled.2 u))
    (installEntries (designedRule E T parameter scalar tape u) planted)).map Prod.fst) b

end Games

/-- **The per-input core of the lift** (the interface to the core H8 and the laws P6): for every input, stage-1
state, adversary stage 2 and weight on the published value, `M`'s flag-down stage-2 mass, averaged over the uniform
source, is below `G1U°`'s, averaged over the swapped tape. -/
def CrtLiftCore (T : CrtTable) (shadow : ∀ [FieldCertificate] [GroupCertificate],
      CrtShadow (viewHere E).Source FI EI) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (planted : LazyOracle.State FI EI) (budget : ℕ)
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool),
    (letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        (weight ((viewHere E).publish source) *
          middleWeight E shadow (tableRun (swappedTableLaw E.layout)) scalar source u planted decide b))
      ≤ ∑' tape, swappedTableTape E tape *
        (weight ((E.scheme inferInstance inferInstance).garble parameter scalar
            (tape.1, tableOracle tape.2)).1 *
          upperWeight E T parameter scalar tape u planted decide b)

section Lift

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- `M`, flag-down, as a sum over the stage-1 outcomes. -/
theorem middleGame_some_eq (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) (b : Bool) :
    middleGame E shadow offRun adversary parameter scalar (some b) =
      (letI := (viewHere E).sourceFintype
       haveI := (viewHere E).sourceNonempty
       ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter ((viewHere E).publish source) ())
            LazyOracle.empty selected *
          middleWeight E shadow offRun scalar source selected.1.1 selected.2
            (fun table labels => adversary.decide parameter table labels () selected.1.2) b) := by
  unfold middleGame
  rw [PMF.bind_apply]
  refine tsum_congr fun source => ?_
  rw [PMF.bind_apply]
  congr 1

/-- `G1U°` as a sum over the stage-1 outcomes. -/
theorem hiddenDesigned_eq (T : CrtTable) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) (b : Bool) :
    hiddenDesignedHybrid E T adversary parameter scalar b =
      ∑' tape, swappedTableTape E tape *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter
            ((E.scheme inferInstance inferInstance).garble parameter scalar
              (tape.1, tableOracle tape.2)).1 ()) LazyOracle.empty selected *
          upperWeight E T parameter scalar tape selected.1.1 selected.2
            (fun table labels => adversary.decide parameter table labels () selected.1.2) b := by
  unfold hiddenDesignedHybrid hiddenDeletedWith stageOneLaw
  rw [PMF.bind_bind, PMF.bind_apply]
  refine tsum_congr fun tape => ?_
  rw [PMF.bind_map, PMF.bind_apply]
  rfl

/-- **The lift from its per-input core**: `M'` is below `G1U°`. -/
theorem below_of_core (T : CrtTable) (shadow : ∀ [FieldCertificate] [GroupCertificate],
      CrtShadow (viewHere E).Source FI EI)
    (core : CrtLiftCore E T shadow) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    Below (hiddenDesignedHybrid E T adversary parameter scalar)
      (middleGame E shadow (tableRun (swappedTableLaw E.layout)) adversary parameter scalar) := by
  intro b
  rw [middleGame_some_eq, hiddenDesigned_eq]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun selected => ?_
  have step := core parameter scalar selected.1.1 selected.2 _
    (fun table labels => adversary.decide parameter table labels () selected.1.2)
    (fun table => LazyOracle.run (adversary.chooseInput parameter table ()) LazyOracle.empty selected) b
  refine le_trans (le_of_eq (tsum_congr fun source => ?_)) (le_trans step (le_of_eq
    (tsum_congr fun tape => ?_)))
  · ring
  · ring

end Lift

end

end Kriterion.CRT.Privacy.PublicFirst
