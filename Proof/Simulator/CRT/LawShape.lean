/-
**The shape of the CRT machine law** (M7).

The chain's last game `I` (`idealHybrid`) runs `routeMSimulator` with the view's EXACT samplers: a uniform source,
`view.simRows` (xinshu's `simulatedRows`: `idealSamplers.tail`, `idealSamplers.lift`), `view.preimage`
(`idealPreimage`) and `view.fourth` (a uniform block). The machine draws by bounded rejection, so its law is exact only
against BOUNDED samplers. xinshu's split (`Proof/Simulator/Law.lean`) is carried over unchanged in form:

1. `Stage1Law`: the machine's stage-1 kernel equals `routeMWith`'s stage 1 at the bounded samplers, the retained
   memory read back by `extract` (exact `PMF` equality);
2. `Stage2Law`: from every stage-1 configuration in the support, the machine's stage-2 kernel equals `routeMWith`'s
   stage 2 on the extracted source, lazy reader (exact `PMF` equality);
3. `SamplerCutoff`: `I` against `B` (`boundedHybrid`: route M with the bounded samplers), within `machineCutoffError`
   (`2^-128`); a statement about samplers alone, no machine.

`machineLaw_of` proves `CrtMachineHop E simulator` from the three. No frozen statement changes: `routeMWith` is
`routeMSimulator` with a knob per sampler, and `routeMSimulator_eq_with` pins it to `routeMSimulator` at the exact
samplers (so a drift between the two definitions breaks this file's build).

The machine's bounded samplers for `crtEntry` (to be defined with M2): `source` the stage-1 law (field cells and
residue digits by bounded rejection, blocks and lanes as coin words, the mixed-radix digits of each record), `rows`
xinshu's `tailLaw` and `liftLaw` through `targetRows` (the `simulatedRows` shape), `preimage` xinshu's `preimageLaw`
(the verbatim `preimageOne`), `fourth` the view's own (a 128-bit coin word is exactly uniform).

The generic glue (`machineAbstract`, `idealGame_eq_machineAbstract`, `abstractIdealGame_eq_of_simulation`) is xinshu's
`Proof/Privacy/Phase3/Glue/LazyIdeal.lean` ported to the CRT copy of `LazyAbstractSimulator`.
-/

import Proof.Privacy.CRT.Named
import Proof.Simulator.Law

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC
open Kriterion.CRT.Privacy (RouteMView Reader lazyReader routeMReplay collectorMasks drawAll collectorList
  programHashAll programRequests)

noncomputable section

namespace LawShape

/-! ### Route M with sampler knobs -/

/-- The four sampler knobs of route M; `none` is a sampler abort. -/
structure RouteMSamplers [FieldCertificate] (Source : Type) where
  source : PMF (Option Source)
  rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))
  preimage : BaseField → PMF (Option (Block × Block × Block))
  fourth : PMF (Option Block)

variable {FI EI Public : Type}

/-- **Route M with sampler knobs**: `routeMSimulator` with `samplers` in place of the uniform source, the rows
kernel, `view.preimage` and `view.fourth`. -/
def routeMWith [FieldCertificate] [DecidableEq FI] [DecidableEq EI] (view : RouteMView Public)
    (samplers : RouteMSamplers view.Source) (reader : Reader FI EI) :
    Privacy.LazyAbstractSimulator FI EI Public where
  State := view.Source
  stage1 _ oracle := samplers.source.map (Option.map fun source => (view.publish source, source, oracle))
  stage2 source u output oracle :=
    let labels := view.labels source u
    let published := view.publish source
    match output with
    | none => PMF.pure (some (labels, oracle))
    | some target =>
      (routeMReplay view reader published u labels oracle).bind fun ran =>
        (samplers.rows u target).bind fun drawnRows => match drawnRows with
          | none => PMF.pure none
          | some targets =>
            let masks := collectorMasks u ran.1 (view.gammaOf published) targets
            (drawAll (fun c => (samplers.preimage (masks c)).bind fun limbs => match limbs with
                | none => PMF.pure none
                | some limbs => samplers.fourth.map (Option.map fun fourth => (limbs, fourth)))
              collectorList).map fun drawn => match drawn with
              | none => none
              | some drawn => (programHashAll (programRequests ran.1.key drawn) ran.2).map fun updated =>
                  (labels, updated)

/-- The exact samplers: a uniform source and the view's own samplers. -/
def exactSamplers [FieldCertificate] (view : RouteMView Public)
    (rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) :
    RouteMSamplers view.Source where
  source :=
    letI := view.sourceFintype
    letI := view.sourceNonempty
    (PMF.uniformOfFintype view.Source).map some
  rows := rows
  preimage := view.preimage
  fourth := view.fourth

/-- **`routeMSimulator` is `routeMWith` at the exact samplers.** -/
theorem routeMSimulator_eq_with [FieldCertificate] [DecidableEq FI] [DecidableEq EI] (view : RouteMView Public)
    (rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
    (reader : Reader FI EI) :
    Privacy.routeMSimulator view rows reader = routeMWith view (exactSamplers view rows) reader := by
  unfold Privacy.routeMSimulator routeMWith exactSamplers
  congr 1
  funext parameter oracle
  rw [PMF.map_comp]
  rfl

/-! ### A closed machine as an abstract simulator (xinshu's `LazyIdeal.lean`, ported) -/

/-- A closed machine read as an abstract simulator: each stage is the machine run from the protocol's request,
followed by the protocol's parse. -/
def machineAbstract [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (encoding : Encoding Public) (bytes : Nat) (machine : BoundedMachine.Simulator) :
    Privacy.LazyAbstractSimulator FI EI Public where
  State := BoundedMachine.Configuration (machine.size + 1)
  stage1 parameter oracle := OptionT.run (do
    let memory : BoundedMachine.Memory := { bits := fun stack =>
      if stack = 0 then [false, false] ++ SimulatorProtocol.natural parameter ++ SimulatorProtocol.natural bytes
      else [] }
    let (initial, oracle, _) ← OptionT.mk (machine.run machine.firstFuel ⟨0, memory⟩ oracle)
    let circuit ← OptionT.mk
      (PMF.pure (SimulatorProtocol.publicValue encoding bytes (initial.memory.bits 3)))
    pure (circuit, initial, oracle))
  stage2 initial input output oracle := OptionT.run (do
    let request := [false, true] ++ SimulatorProtocol.affine input ++ SimulatorProtocol.output output
    let memory := { initial.memory with
      bits := Function.update (Function.update initial.memory.bits 0 request) 3 [] }
    let (encoded, updated, _) ← OptionT.mk (machine.run machine.secondFuel ⟨0, memory⟩ oracle)
    let labels ← OptionT.mk (PMF.pure (SimulatorProtocol.words 128 508 (encoded.memory.bits 3)))
    pure (labels, updated))

/-- **The library's ideal game is the abstract game of the machine's kernels**, exactly. -/
theorem idealGame_eq_machineAbstract [FieldCertificate] {Randomness Key Oracle Aux : Type}
    [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (encoding : Encoding Public) (bytes : Nat) (machine : BoundedMachine.Simulator)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    LazySimulatorProtocol.idealGame scheme encoding bytes machine adversary parameter scalar auxiliary =
      Privacy.abstractIdealGame scheme (machineAbstract encoding bytes machine) adversary parameter scalar
        auxiliary := by
  unfold LazySimulatorProtocol.idealGame Privacy.abstractIdealGame machineAbstract
  simp only [Phase3.Glue.optionT_mk_run, bind_assoc, pure_bind]

/-- **Kernel-level comparison of abstract simulators** (xinshu's, for the CRT copy of the type). -/
theorem abstractIdealGame_eq_of_simulation [FieldCertificate] {Randomness Key Oracle Aux : Type}
    [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (first second : Privacy.LazyAbstractSimulator FI EI Public) (represent : first.State → second.State)
    (stage1 : ∀ parameter, second.stage1 parameter LazyOracle.empty =
      (first.stage1 parameter LazyOracle.empty).map
        (Option.map fun result => (result.1, represent result.2.1, result.2.2)))
    (stage2 : ∀ parameter result,
      some result ∈ (first.stage1 parameter LazyOracle.empty).support →
        ∀ input output oracle, second.stage2 (represent result.2.1) input output oracle =
          first.stage2 result.2.1 input output oracle)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    Privacy.abstractIdealGame scheme second adversary parameter scalar auxiliary =
      Privacy.abstractIdealGame scheme first adversary parameter scalar auxiliary := by
  unfold Privacy.abstractIdealGame
  rw [stage1, Phase3.Glue.optionT_mk_map]
  simp only [bind_assoc, pure_bind]
  congr 2
  apply Phase3.Glue.optionT_bind_congr
  intro result member
  simp only [stage2 parameter result member]

/-! ### The three statements, over a generic entry (instantiate at `crtEntry` by name, as `Named.lean` asks) -/

variable (E : Privacy.CrtEntry FI EI)

/-- The machine's bounded samplers, one family per certificate pair. -/
abbrev BoundedSamplers : Type :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field), @RouteMSamplers field (E.view field group).Source

/-- The retained memory read back as a source. -/
abbrev Extract : Type :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field), BoundedMachine.Memory → (E.view field group).Source

/-- **`B`**: route M with the machine's bounded samplers and the lazy reader. -/
def boundedHybrid (bounded : BoundedSamplers E) : Privacy.ChainGame FI EI E.Public := fun adversary parameter scalar =>
  Privacy.abstractIdealGame (E.scheme inferInstance inferInstance)
    (routeMWith (E.view inferInstance inferInstance) (bounded inferInstance inferInstance) lazyReader)
    adversary parameter scalar ()

/-- **Stage-1 law**: exact, at the instances `Solution.adaptivePrivacy` installs. -/
def Stage1Law [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers E)
    (extract : Extract E) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ),
    letI := Fintype.ofFinite FI
    letI := Fintype.ofFinite EI
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    (routeMWith (E.view field group) (bounded field group) lazyReader).stage1 parameter LazyOracle.empty =
      ((machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage1 parameter
          LazyOracle.empty).map
        (Option.map fun result => (result.1, extract field group result.2.1.memory, result.2.2))

/-- **Stage-2 law**: exact, from every stage-1 configuration in the support. -/
def Stage2Law [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers E)
    (extract : Extract E) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ),
    letI := Fintype.ofFinite FI
    letI := Fintype.ofFinite EI
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    ∀ result, some result ∈ ((machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage1 parameter
        LazyOracle.empty).support →
      ∀ input output oracle,
        (routeMWith (E.view field group) (bounded field group) lazyReader).stage2
            (extract field group result.2.1.memory) input output oracle =
          (machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage2 result.2.1 input output
            oracle

/-- **The sampler cutoff**: `I` against `B`, a statement about samplers alone. -/
def SamplerCutoff [Finite FI] [Finite EI] (bounded : BoundedSamplers E) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : Privacy.ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    Kriterion.Cryptography.Assumptions.advantage
        (Privacy.atSolution (Privacy.crtChain E).ideal field group adversary parameter scalar)
        (Privacy.atSolution (boundedHybrid E bounded) field group adversary parameter scalar) ≤
      Privacy.machineCutoffError

/-- **The split.** The two exact stage laws and the sampler cutoff give the machine row `H11`. -/
theorem machineLaw_of [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers E)
    (extract : Extract E) (stage1 : Stage1Law E simulator bounded extract)
    (stage2 : Stage2Law E simulator bounded extract) (cutoff : SamplerCutoff E bounded) :
    Privacy.CrtMachineHop E simulator := by
  intro field group adversary parameter scalar
  have exact : Privacy.atSolution (E.machineHybrid simulator) field group adversary parameter scalar =
      Privacy.atSolution (boundedHybrid E bounded) field group adversary parameter scalar := by
    letI := Fintype.ofFinite FI
    letI := Fintype.ofFinite EI
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    exact (idealGame_eq_machineAbstract _ _ _ _ _ _ _ _).trans
      (abstractIdealGame_eq_of_simulation _ _ _
        (fun configuration : BoundedMachine.Configuration (simulator.size + 1) =>
          extract field group configuration.memory)
        (stage1 field group) (stage2 field group) adversary parameter scalar ()).symm
  rw [exact]
  exact cutoff field group adversary parameter scalar

end LawShape

end

end Kriterion.CRT.SimMachine
