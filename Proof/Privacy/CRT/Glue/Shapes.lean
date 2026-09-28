/-
**The shapes of the CRT privacy chain and its assembly**.

This file is xinshu's `Proof/Privacy/Phase3/Glue/Assembly.lean` made generic: the games, hop shapes and the final
assembly are stated over an abstract entry (`EntrySig`: index types, coins, public type, codec, scheme and garbler
program), so they elaborate before the CRT entry's signatures are frozen, and the conclusion
`chain_oracleAdaptivePrivacy` is literally the type of `Solution.adaptivePrivacy` at that entry.

* `ChainGame`, `atSolution`, `HopBound`, `UntilBad`, `CoreUntilBad`, `GameUntilBad`, `GameCoreUntilBad`: xinshu's shapes
  (`Assembly.lean:51-165`), over any index types and public type;
* `CrtChain`: the seven games `G0 … I`; `ChainHops`: the six hops with the error terms of `Glue/Budget.lean`;
* `chain_real_ideal_le`: the hops sum to `chainError` minus the cutoff;
* `chain_oracleAdaptivePrivacy`: from `G0` being the lazy real game, the hops and the machine law.

Every proof here is a port of xinshu's (verified to elaborate); nothing is `sorry`.
-/

import Proof.Privacy.CRT.Glue.Budget
import Solution
import Cryptography.Probability

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit
open Kriterion.Cryptography (Assumptions.advantage Assumptions.advantageTriangle Assumptions.WorkPerAdvantage)

noncomputable section

/-! ### Games -/

/-- The adversaries of the chain: public queries over `FI` and `EI`, affine input, the entry's public value, the
508 Lamport blocks, no auxiliary input. -/
abbrev ChainAdversary (FI EI Public : Type) :=
  AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Unit

/-- A game of the chain: one for every certificate pair and every choice of the index instances. -/
abbrev ChainGame (FI EI Public : Type) : Type 1 :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI],
    ChainAdversary FI EI Public → ℕ → NonZeroScalar → PMF Bool

variable {FI EI Public : Type}

/-- A chain game at the instances `Solution.adaptivePrivacy` installs. -/
def atSolution [Finite FI] [Finite EI] (game : ChainGame FI EI Public) (field : FieldCertificate)
    (group : @GroupCertificate field) : ChainAdversary FI EI Public → ℕ → NonZeroScalar → PMF Bool :=
  @game field group (Fintype.ofFinite FI) (Fintype.ofFinite EI) (Classical.decEq FI) (Classical.decEq EI)

/-- A hop: against every adversary with fewer than `2^100` queries the two games are within `error q₁ q₂`. -/
def HopBound [Finite FI] [Finite EI] (first second : ChainGame FI EI Public) (error : ℕ → ℕ → ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      Assumptions.advantage (atSolution first field group adversary parameter scalar)
        (atSolution second field group adversary parameter scalar) ≤
        error (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter)

/-! ### Identical until bad (xinshu's `Assembly.lean:84-165`, generic) -/

/-- The flag of a flagged outcome `(outcome, bad)`. -/
def badSet : Set (Bool × Bool) := {outcome | outcome.2 = true}

/-- Two games that are first marginals of flagged laws agreeing off the flag; the first raises it with mass at most
`error`. -/
def UntilBad (first second : PMF Bool) (error : ℝ) : Prop :=
  ∃ firstFlagged secondFlagged : PMF (Bool × Bool),
    firstFlagged.map Prod.fst = first ∧ secondFlagged.map Prod.fst = second ∧
    (∀ outcome, firstFlagged (outcome, false) = secondFlagged (outcome, false)) ∧
    (firstFlagged.toOuterMeasure badSet).toReal ≤ error

theorem map_fst_true (flagged : PMF (Bool × Bool)) :
    (flagged.map Prod.fst) true = flagged.toOuterMeasure {outcome | outcome.1 = true} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

theorem UntilBad.advantage_le {first second : PMF Bool} {error : ℝ}
    (bound : UntilBad first second error) : Assumptions.advantage first second ≤ error := by
  obtain ⟨firstFlagged, secondFlagged, firstEq, secondEq, agree, bad⟩ := bound
  have law := Kriterion.Cryptography.Probability.identical_until_bad secondFlagged firstFlagged
    badSet {outcome | outcome.1 = true} (by
      rintro ⟨outcome, flag⟩ notBad
      cases flag
      · exact (agree outcome).symm
      · exact (notBad rfl).elim)
  unfold Assumptions.advantage
  rw [← firstEq, ← secondEq, map_fst_true, map_fst_true, abs_sub_comm]
  exact law.trans bad

/-- Identical until bad, with the agreement off the flag given by an exact core law `realCore = simCore`. -/
def CoreUntilBad (first second : PMF Bool) (error : ℝ) : Prop :=
  ∃ (Core : Type) (realCore simCore : PMF Core) (continuation : Core → PMF (Bool × Bool))
    (firstFlagged : PMF (Bool × Bool)),
    realCore = simCore ∧ firstFlagged.map Prod.fst = first ∧
    (simCore.bind continuation).map Prod.fst = second ∧
    (∀ outcome, firstFlagged (outcome, false) = (realCore.bind continuation) (outcome, false)) ∧
    (firstFlagged.toOuterMeasure badSet).toReal ≤ error

theorem CoreUntilBad.untilBad {first second : PMF Bool} {error : ℝ}
    (bound : CoreUntilBad first second error) : UntilBad first second error := by
  obtain ⟨Core, realCore, simCore, continuation, firstFlagged, core, firstEq, secondEq, agree,
    bad⟩ := bound
  subst core
  exact ⟨firstFlagged, realCore.bind continuation, firstEq, secondEq, agree, bad⟩

/-- A hop in identical-until-bad form. -/
def GameUntilBad [Finite FI] [Finite EI] (first second : ChainGame FI EI Public) (error : ℕ → ℕ → ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      UntilBad (atSolution first field group adversary parameter scalar)
        (atSolution second field group adversary parameter scalar)
        (error (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter))

/-- A hop in exact-core identical-until-bad form. -/
def GameCoreUntilBad [Finite FI] [Finite EI] (first second : ChainGame FI EI Public)
    (error : ℕ → ℕ → ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      CoreUntilBad (atSolution first field group adversary parameter scalar)
        (atSolution second field group adversary parameter scalar)
        (error (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter))

theorem GameUntilBad.hopBound [Finite FI] [Finite EI] {first second : ChainGame FI EI Public}
    {error : ℕ → ℕ → ℝ} (bound : GameUntilBad first second error) : HopBound first second error :=
  fun field group adversary parameter scalar small =>
    (bound field group adversary parameter scalar small).advantage_le

theorem GameCoreUntilBad.hopBound [Finite FI] [Finite EI] {first second : ChainGame FI EI Public}
    {error : ℕ → ℕ → ℝ} (bound : GameCoreUntilBad first second error) : HopBound first second error :=
  fun field group adversary parameter scalar small =>
    (bound field group adversary parameter scalar small).untilBad.advantage_le

/-! ### The entry, abstractly -/

/-- What the chain needs from the entry: the fields of `Solution` that `Solution.adaptivePrivacy` mentions. The CRT
entry's instance has `FI = EI = Empty` (D2); `EntryInstance.lean` gives the concrete fields. -/
structure EntrySig (FI EI : Type) where
  /-- The private coins. -/
  Coins : Type
  coinsFinite : Finite Coins
  coinWitness : Coins
  /-- The public value and its codec. -/
  Public : Type
  Key : Type
  encoding : Encoding Public
  bytes : ℕ
  /-- The garbler's query bound. -/
  garbleBudget : ℕ
  /-- The scheme and the garbler program. -/
  scheme : (field : FieldCertificate) → @GroupCertificate field →
    GarbledCircuit NonZeroScalar AffineInput (Option (@Point field)) (Coins × PublicOracle FI EI) Public Key
      LamportSignature (PublicOracle FI EI)
  garbleProgram : (field : FieldCertificate) → @GroupCertificate field → ℕ → NonZeroScalar → Coins →
    QueryProgram (publicOracleSpec FI EI) (Public × Key) garbleBudget

/-- `M`: the library's ideal game with a closed machine, as a chain game. -/
def EntrySig.machineHybrid (E : EntrySig FI EI) (simulator : BoundedMachine.Simulator) :
    ChainGame FI EI E.Public :=
  fun adversary parameter scalar =>
    LazySimulatorProtocol.idealGame (E.scheme inferInstance inferInstance) E.encoding E.bytes simulator adversary
      parameter scalar ()

/-! ### The chain and its hops -/

/-- The seven games of the chain (the hybrids are defined in `Hybrids.lean` for the
CRT entry). -/
structure CrtChain (FI EI Public : Type) where
  /-- `G0`: the tape-sampled real game. -/
  real : ChainGame FI EI Public
  /-- `G0T`: the answer table planted before stage 1. -/
  tablePlanted : ChainGame FI EI Public
  /-- `G0U`: every pad and mask site swapped to a uniform target. -/
  padSwapped : ChainGame FI EI Public
  /-- `G1U`: hidden entries never installed. -/
  hiddenDeleted : ChainGame FI EI Public
  /-- `HW`: the route-M simulator with the real rows and the refill reader. -/
  publicFirst : ChainGame FI EI Public
  /-- `H`: the same with the simulated rows. -/
  opened : ChainGame FI EI Public
  /-- `I`: the abstract simulator, lazy reader: what the machine realises. -/
  ideal : ChainGame FI EI Public

/-- **The six hops from `G0` to `I`** with the error terms of `Glue/Budget.lean`. -/
structure ChainHops [Finite FI] [Finite EI] (C : CrtChain FI EI Public) : Prop where
  /-- `G0 → G0T`, P6a1: `1,759,967 / p`. -/
  table : HopBound C.real C.tablePlanted fun _ _ => tCollisionError
  /-- `G0T → G0U`, P1: one swap. -/
  swap : HopBound C.tablePlanted C.padSwapped fun _ _ => padSwapError
  /-- `G0U → G1U`, P2a and P2b: identical until a hidden entry is touched. -/
  hidden : GameUntilBad C.padSwapped C.hiddenDeleted fun first second =>
    hiddenPointError (first + second) + hiddenWindowError
  /-- `G1U → HW`, the core (P3, P45, P5a, P5b, P6, P7, P8). -/
  publicFirst : GameCoreUntilBad C.hiddenDeleted C.publicFirst fun first _ =>
    stageOneTouchError first + smudgeError + exceptionalError + coincidenceError + padSwapError
  /-- `HW → H`, P9: the output kernel. -/
  opening : HopBound C.publicFirst C.opened fun _ _ => outputKernelError
  /-- `H → I`, P10: the refill back, untouched sites only. -/
  refill : HopBound C.opened C.ideal fun _ _ => padSwapError

/-- **The machine law** (M7): against every adversary the machine's game is within `error` of `I`. -/
def MachineLaw [Finite FI] [Finite EI] (E : EntrySig FI EI) (ideal : ChainGame FI EI E.Public)
    (simulator : BoundedMachine.Simulator) (error : ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    Assumptions.advantage (atSolution ideal field group adversary parameter scalar)
      (atSolution (E.machineHybrid simulator) field group adversary parameter scalar) ≤ error

/-- **`G0` is the scored real game** (P1's `crt_lazy_real`, from xinshu's `lazy_real_uniform`): the library's lazy
real game of the entry, at the instances `Solution.adaptivePrivacy` installs, is `G0`. -/
def RealIsLazy [Finite FI] [Finite EI] (E : EntrySig FI EI) (real : ChainGame FI EI E.Public) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    @lazyRealGame FI EI E.Coins NonZeroScalar AffineInput E.Public E.Key LamportSignature Unit
        (Classical.decEq FI) (Classical.decEq EI)
        (@uniformRandomTape E.Coins (@Fintype.ofFinite E.Coins E.coinsFinite) E.coinWitness) E.garbleBudget
        (fun parameter scalar coins => (E.garbleProgram field group parameter scalar coins).toOracleProgram)
        (E.scheme field group).encode adversary parameter scalar () =
      atSolution real field group adversary parameter scalar

theorem advantage_le_one (first second : PMF Bool) : Assumptions.advantage first second ≤ 1 := by
  unfold Assumptions.advantage
  have bound (distribution : PMF Bool) : (distribution true).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one distribution true)
  have firstBound := bound first
  have secondBound := bound second
  have firstNonneg : 0 ≤ (first true).toReal := ENNReal.toReal_nonneg
  have secondNonneg : 0 ≤ (second true).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- The six hops from `G0` to `I` sum to all of `chainError` but the machine cutoff. -/
theorem chain_real_ideal_le [Finite FI] [Finite EI] (C : CrtChain FI EI Public) (hops : ChainHops C)
    (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI Public)
    (parameter : ℕ) (scalar : NonZeroScalar)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100) :
    Assumptions.advantage (atSolution C.real field group adversary parameter scalar)
        (atSolution C.ideal field group adversary parameter scalar) ≤
      chainError (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter) -
        machineCutoffError := by
  let game (hybrid : ChainGame FI EI Public) := atSolution hybrid field group adversary parameter scalar
  have s0 := hops.table field group adversary parameter scalar small
  have s1 := hops.swap field group adversary parameter scalar small
  have s2 := hops.hidden.hopBound field group adversary parameter scalar small
  have s3 := hops.publicFirst.hopBound field group adversary parameter scalar small
  have s4 := hops.opening field group adversary parameter scalar small
  have s5 := hops.refill field group adversary parameter scalar small
  have t0 := Assumptions.advantageTriangle (game C.real) (game C.tablePlanted) (game C.ideal)
  have t1 := Assumptions.advantageTriangle (game C.tablePlanted) (game C.padSwapped) (game C.ideal)
  have t2 := Assumptions.advantageTriangle (game C.padSwapped) (game C.hiddenDeleted) (game C.ideal)
  have t3 := Assumptions.advantageTriangle (game C.hiddenDeleted) (game C.publicFirst) (game C.ideal)
  have t4 := Assumptions.advantageTriangle (game C.publicFirst) (game C.opened) (game C.ideal)
  unfold chainError
  simp only at s0 s1 s2 s3 s4 s5
  linarith

/-- **The privacy field of `Solution`, from the chain.** The conclusion is literally the type of
`Solution.adaptivePrivacy` at an entry with these fields. -/
theorem chain_oracleAdaptivePrivacy [fixedFinite : Finite FI] [encFinite : Finite EI] (E : EntrySig FI EI)
    (C : CrtChain FI EI E.Public) (simulator : BoundedMachine.Simulator)
    (real : RealIsLazy E C.real) (hops : ChainHops C) (machine : MachineLaw E C.ideal simulator machineCutoffError) :
    ∀ (field : BN254.FieldCertificate) (group : @BN254.GroupCertificate field),
      letI := field
      letI := @Fintype.ofFinite FI fixedFinite
      letI := @Fintype.ofFinite EI encFinite
      letI := Classical.decEq FI
      letI := Classical.decEq EI
      GarbledCircuit.OracleAdaptivePrivacy (E.scheme field group) E.encoding E.bytes
        (@uniformRandomTape E.Coins (@Fintype.ofFinite E.Coins E.coinsFinite) E.coinWitness)
        (fun parameter scalar coins => (E.garbleProgram field group parameter scalar coins).toOracleProgram) := by
  intro field group
  letI : Fintype FI := Fintype.ofFinite _
  letI : Fintype EI := Fintype.ofFinite _
  letI : DecidableEq FI := Classical.decEq _
  letI : DecidableEq EI := Classical.decEq _
  letI : Fintype E.Coins := @Fintype.ofFinite E.Coins E.coinsFinite
  refine ⟨simulator, fun adversaryMachine parameter scalar => ?_⟩
  intro adversary
  have realEq : lazyRealGame (uniformRandomTape E.Coins E.coinWitness)
      (fun parameter scalar coins => (E.garbleProgram field group parameter scalar coins).toOracleProgram)
      (E.scheme field group).encode adversary parameter scalar () =
      atSolution C.real field group adversary parameter scalar :=
    real field group adversary parameter scalar
  have queries : adversary.firstQueryBudget parameter = adversaryMachine.firstFuel ∧
      adversary.secondQueryBudget parameter = adversaryMachine.secondFuel := ⟨rfl, rfl⟩
  -- `steps + 1 = size + 2 + firstFuel + secondFuel`: both the program size's `+ 1` and the challenge's `+ 1`.
  have steps : (adversaryMachine.firstFuel : ℝ) + (adversaryMachine.secondFuel : ℝ) + 2 ≤
      ((adversaryMachine.steps + 1 : ℕ) : ℝ) := by
    have work : adversaryMachine.firstFuel + adversaryMachine.secondFuel + 2 ≤ adversaryMachine.steps + 1 := by
      unfold BoundedMachine.Adversary.steps
      omega
    exact_mod_cast work
  show Assumptions.WorkPerAdvantage 100 (adversaryMachine.steps + 1)
    (Assumptions.advantage (lazyRealGame (uniformRandomTape E.Coins E.coinWitness)
      (fun parameter scalar coins => (E.garbleProgram field group parameter scalar coins).toOracleProgram)
      (E.scheme field group).encode adversary parameter scalar ())
      (atSolution (E.machineHybrid simulator) field group adversary parameter scalar))
  rw [realEq]
  by_cases small : adversaryMachine.firstFuel + adversaryMachine.secondFuel < 2 ^ 100
  · apply GarbledCircuit.adaptivePrivacyTransfer
      (ideal := atSolution C.ideal field group adversary parameter scalar)
    have smallBudget : adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter < 2 ^ 100 := by
      rw [queries.1, queries.2]
      exact small
    have hopsSum := chain_real_ideal_le C hops field group adversary parameter scalar smallBudget
    have cut := machine field group adversary parameter scalar
    have budget := chainError_budget adversaryMachine.firstFuel adversaryMachine.secondFuel small
    rw [queries.1, queries.2] at hopsSum
    unfold Assumptions.WorkPerAdvantage
    calc _ ≤ chainError adversaryMachine.firstFuel adversaryMachine.secondFuel * 2 ^ 100 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (adversaryMachine.firstFuel : ℝ) + (adversaryMachine.secondFuel : ℝ) + 2 := budget
      _ ≤ ((adversaryMachine.steps + 1 : ℕ) : ℝ) := steps
  · unfold Assumptions.WorkPerAdvantage
    have large : (2 : ℝ) ^ 100 ≤ (adversaryMachine.firstFuel : ℝ) + (adversaryMachine.secondFuel : ℝ) := by
      have : 2 ^ 100 ≤ adversaryMachine.firstFuel + adversaryMachine.secondFuel := Nat.le_of_not_gt small
      exact_mod_cast this
    calc _ ≤ 1 * (2 : ℝ) ^ 100 :=
          mul_le_mul_of_nonneg_right (advantage_le_one _ _) (by positivity)
      _ ≤ ((adversaryMachine.steps + 1 : ℕ) : ℝ) := by linarith

end

end Kriterion.CRT.Privacy
