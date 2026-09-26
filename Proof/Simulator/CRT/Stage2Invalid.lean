/-
**Stage 2 of the CRT machine, the invalid arm**: on an undefined output (`f_k u = none`) the machine's
stage-2 kernel returns the selected labels and the incoming oracle state, exactly as route M's stage 2 does on the
extracted source (the `none` arm of `LawShape.routeMWith`).

The machine is `CrtTop.machine` (layout of `Design.lean`); its stage-2 prefix and invalid arm are
release-r1's `Request.prefixProgram` and `Stage2.invalid` (the label emission), so the port of xinshu's
`Proof/Simulator/Stage2Invalid.lean` reuses its lemmas (`memSem_prefix`, `memSem_emitLabels`, `labelRuns_words`):

* `stage2_run_none`: the machine's stage-2 run on an undefined output pops the tag, runs the prefix, branches to the
  invalid arm, emits the labels and halts, with the oracle state unchanged;
* `labels_extract`: the emitted labels are `Entry.labels (CrtSource.extract ram) u` whenever the key cells hold
  `Z_j` and `Z_j ⊕ Δ` (`KeyCellsHold`, written by stage 1's tail);
* `stage2_none`: the machine's stage 2 on an undefined output, as a law;
* `stage2NoneArm_of_keys`: `Stage2Law` restricted to `output = none`,
  given that every stage-1 result holds its key cells.
-/

import Proof.Simulator.CRT.Runs
import Proof.Simulator.CRT.LawShape
import Proof.Simulator.CRT.Stage1Source
import Proof.Simulator.Stage2Invalid
import Proof.Simulator.OracleUse
import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.SimMachine

namespace CrtStage2Invalid

open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit Kriterion.ArgoMAC
  Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.CRT.Privacy (lazyReader)

noncomputable section

/-! ### The key cells stage 1 leaves -/

/-- **The key cells**: the label of bit `1` of input bit `j` is the label of bit `0` xor its coordinate's `Δ`. -/
def KeyCellsHold (ram : Word → Word) : Prop :=
  ∀ j, j < labelCount → ram (word (keyBase + 2 * j + 1)) =
    ram (word (keyBase + 2 * j)) ^^^ ram (word (Layout.deltaCell (j / 254)))

/-- Truncating a word to a block commutes with xor. -/
theorem block_of_xor (first second : Word) :
    BitVec.ofNat 128 (first ^^^ second).toNat =
      BitVec.ofNat 128 first.toNat ^^^ BitVec.ofNat 128 second.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_xor]

/-- The `(x >>> i) % 2` of the prefix is the bit `x.testBit i`. -/
theorem shift_bit (value index : Nat) :
    (value >>> index) % 2 = if value.testBit index then 1 else 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ index) with h | h <;> simp [h]

/-- A zero label of the extracted source is the even key cell. -/
theorem zeros_extract (ram : Word → Word) (κ : Fin 2) (i : Fin coordinateBitCount) :
    (CrtSource.extract ram).zeros κ i =
      BitVec.ofNat 128 (ram (word (keyBase + 2 * (254 * κ.val + i.val)))).toNat := by
  have inside : 254 * κ.val + i.val < labelCount := by
    have := κ.isLt
    have := i.isLt
    unfold labelCount
    simp only [coordinateBitCount] at *
    omega
  simp only [CrtSource.extract, CrtSource.sourceOf, total, dif_pos inside]
  rfl

/-- A `Δ` of the extracted source is its cell. -/
theorem deltas_extract (ram : Word → Word) (κ : Fin 2) :
    (CrtSource.extract ram).deltas κ = BitVec.ofNat 128 (ram (word (Layout.deltaCell κ.val))).toNat := by
  simp only [CrtSource.extract, CrtSource.sourceOf, total, dif_pos κ.isLt]
  rfl

/-- **The selected labels, read through `CrtSource.extract`**: the label the prefix copies for input bit `index` is
`Entry.labels` of the extracted source. -/
theorem label_extract (ram : Word → Word) (keys : KeyCellsHold ram) (input : AffineInput) (index : Nat)
    (bound : index < 508) :
    BitVec.ofNat 128 (ram (word (keyBase + 2 * index + inputBit input.x.val input.y.val index))).toNat =
      (Kriterion.CRT.Entry.labels (CrtSource.extract ram) input)[index] := by
  unfold Kriterion.CRT.Entry.labels
  rw [Vector.getElem_ofFn]
  unfold inputBit
  by_cases low : index < 254
  · have lowCount : index < coordinateBitCount := low
    rw [dif_pos lowCount, if_pos low, shift_bit]
    dsimp only
    rw [zeros_extract, deltas_extract]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
    by_cases bit : input.x.val.testBit index
    · rw [if_pos bit, if_pos bit, keys index (by unfold labelCount; omega), block_of_xor,
        Nat.div_eq_of_lt low]
    · rw [if_neg bit, if_neg bit, Nat.add_zero]
  · have highCount : ¬ index < coordinateBitCount := low
    rw [dif_neg highCount, if_neg low, shift_bit]
    dsimp only
    rw [zeros_extract, deltas_extract]
    have flat : 254 * (1 : Fin 2).val + (index - coordinateBitCount) = index := by
      show 254 * 1 + (index - 254) = index
      omega
    have modEq : index % 254 = index - coordinateBitCount := by
      show index % 254 = index - 254
      omega
    rw [flat, modEq]
    by_cases bit : input.y.val.testBit (index - coordinateBitCount)
    · rw [if_pos bit, if_pos bit, keys index (by unfold labelCount; omega), block_of_xor,
        show index / 254 = (1 : Fin 2).val by show index / 254 = 1; omega]
    · rw [if_neg bit, if_neg bit, Nat.add_zero]

/-- **The emitted label vector is `Entry.labels` of the extracted source.** -/
theorem labels_extract (ram : Word → Word) (keys : KeyCellsHold ram) (input : AffineInput) :
    (Vector.ofFn fun index : Fin 508 => BitVec.ofNat 128 (ram (word (keyBase + 2 * index.val +
      inputBit input.x.val input.y.val index.val))).toNat) =
        Kriterion.CRT.Entry.labels (CrtSource.extract ram) input := by
  apply Vector.ext
  intro index bound
  rw [Vector.getElem_ofFn]
  exact label_extract ram keys input index bound

/-! ### The stage-2 run on an undefined output -/

section Run

variable [FieldCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
variable (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)

/-- **The machine's stage-2 run on an undefined output**: tag, prefix, branch to the invalid arm, label emission,
halt; the oracle state is returned unchanged and the response stack holds the label runs of the selected labels. -/
theorem stage2_run_none (memory : Memory) (input : AffineInput) (oracle : OState FI EI) :
    ∃ (last : Memory) (used : Nat),
      (CrtTop.machine s1 r replay within).run (CrtTop.machine s1 r replay within).secondFuel
          ⟨0, stage2Memory memory input none⟩ oracle =
        PMF.pure (some (atPc (CrtTop.machine s1 r replay within) (Design.invalidHalt (CrtTop.blocks s1 r)) last,
          oracle, used)) ∧
      SimulatorProtocol.words 128 508 (last.bits 3) =
        some (Vector.ofFn fun index : Fin 508 => BitVec.ofNat 128 (memory.ram (word (keyBase + 2 * index.val +
          inputBit input.x.val input.y.val index.val))).toNat) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := CrtTop.layout s1 r
  have sizeP := CrtTop.prefix_size s1 r
  have costP := CrtTop.prefix_cost s1 r
  have sizeI := CrtTop.invalid_size s1 r
  have costI := CrtTop.invalid_cost s1 r
  have small := CrtTop.invalid_le_valid s1 r
  set machine := CrtTop.machine s1 r replay within with machineDef
  have sizeIs : machine.size = Design.size (CrtTop.blocks s1 r) := rfl
  set start := Top.afterTag (stage2Memory memory input none) (stage2Rest input none) with startDef
  obtain ⟨middle, runPrefix, bitsPrefix, labels, _, flag⟩ := memSem_prefix start
    input.x.val input.y.val (coord_small _) (coord_small _) [false, false] false false 0 0
    (by simp [OutBits]) (afterTag_request memory input none)
  obtain ⟨last, runEmit, _, bitsEmit, _⟩ := memSem_emitLabels middle
  have flagZero : middle.registers rFlag = 0 := by rw [flag]; rfl
  have response : last.bits 3 = labelRuns middle.ram := by
    rw [bitsEmit, bitsPrefix, Function.update_of_ne (by decide), startDef, afterTag_response,
      List.append_nil]
  refine ⟨last, 1 + (CrtTop.blocks s1 r).invalid.cost + 1 + (CrtTop.blocks s1 r).prefixBlock.cost + 1 + 1, ?_, ?_⟩
  · have fuelIs : machine.secondFuel = ((CrtTop.blocks s1 r).prefixBlock.cost +
        (Design.validCost (CrtTop.blocks s1 r) + 1 + 1)) + 1 + 1 := by
      rw [machineDef, CrtTop.machine_secondFuel]
      simp only [Design.secondFuel, Nat.max_eq_left small]
      omega
    set base := stage2Memory memory input none with baseDef
    have request : base.bits 0 = false :: true :: stage2Rest input none := stage2Memory_request memory input none
    rw [Top.atPc_zero, fuelIs]
    rewrite [run_pop_bit machine (pc := 0) (by rw [sizeIs]; omega) (CrtTop.code_zero s1 r replay within) _
      base false (true :: stage2Rest input none) request oracle]
    simp only [Bool.false_eq_true, if_false]
    have second : ({ base with bits := Function.update base.bits 0 (true :: stage2Rest input none) } :
        Memory).bits 0 = true :: stage2Rest input none := by simp only [Function.update_self]
    rewrite [run_pop_bit machine (pc := 1) (by rw [sizeIs]; omega) (CrtTop.code_one s1 r replay within) _ _ true
      (stage2Rest input none) second oracle]
    simp only [if_true]
    set rest := stage2Rest input none with restDef
    have memoryEq : ({ ({ base with bits := Function.update base.bits 0 (true :: rest) } : Memory) with
        bits := Function.update (Function.update base.bits 0 (true :: rest)) 0 rest } : Memory) = start := by
      simp only [startDef, baseDef, restDef, Top.afterTag, Function.update_idem]
    have block := run_placed (FixedIndex := FI) (EncIndex := EI) machine Request.prefixProgram
      (Design.stage2Base (CrtTop.blocks s1 r)) (CrtTop.placed_prefix s1 r replay within)
    rw [← sizeP, ← costP, show Design.stage2Base (CrtTop.blocks s1 r) + (CrtTop.blocks s1 r).prefixBlock.size =
      Design.branchAt (CrtTop.blocks s1 r) by omega] at block
    rewrite [memoryEq, block, sem_noOracle _ prefix_noOracle, runPrefix, PMF.pure_map, Option.map_some,
      PMF.pure_bind]
    simp only [_root_.Kriterion.ArgoMAC.PlanB.SimMachine.after, if_pos (show (CrtTop.blocks s1 r).prefixBlock.cost ≤ (CrtTop.blocks s1 r).prefixBlock.cost +
      (Design.validCost (CrtTop.blocks s1 r) + 1 + 1) by omega), Nat.add_sub_cancel_left]
    rewrite [run_branch machine (by rw [sizeIs]; omega) rFlag (Design.invalidBase (CrtTop.blocks s1 r))
      (Design.validBase (CrtTop.blocks s1 r)) (CrtTop.code_branch s1 r replay within)]
    simp only [flagZero, if_true]
    have arm := run_placed (FixedIndex := FI) (EncIndex := EI) machine Stage2.invalid
      (Design.invalidBase (CrtTop.blocks s1 r)) (CrtTop.placed_invalid s1 r replay within)
    rw [← sizeI, ← costI, show Design.invalidBase (CrtTop.blocks s1 r) + (CrtTop.blocks s1 r).invalid.size =
      Design.invalidHalt (CrtTop.blocks s1 r) by omega] at arm
    have emit : Stage2.invalid.memSem middle = PMF.pure (some last) := runEmit
    rewrite [arm, sem_noOracle _ invalid_noOracle, emit, PMF.pure_map, Option.map_some, PMF.pure_bind]
    simp only [_root_.Kriterion.ArgoMAC.PlanB.SimMachine.after, if_pos (show (CrtTop.blocks s1 r).invalid.cost ≤ Design.validCost (CrtTop.blocks s1 r) + 1
      by omega)]
    rw [show Design.validCost (CrtTop.blocks s1 r) + 1 - (CrtTop.blocks s1 r).invalid.cost =
      (Design.validCost (CrtTop.blocks s1 r) - (CrtTop.blocks s1 r).invalid.cost) + 1 by omega]
    rewrite [run_halt machine (by rw [sizeIs]; omega) (CrtTop.code_invalidHalt s1 r replay within)]
    simp only [PMF.pure_map, Option.map_some]
  · rw [response, labelRuns_words]
    unfold labelVector
    refine congrArg some (congrArg Vector.ofFn (funext fun index => ?_))
    rw [labels index.val index.isLt, startDef, afterTag_ram]

/-- **Stage 2 on an undefined output**, as a law: the labels the key cells select, and the incoming oracle state. -/
theorem stage2_none (initial : Configuration ((CrtTop.machine s1 r replay within).size + 1)) (input : AffineInput)
    (oracle : OState FI EI) (keys : KeyCellsHold initial.memory.ram)
    {Public : Type} (encoding : Encoding Public) (bytes : Nat) :
    (LawShape.machineAbstract (FI := FI) (EI := EI) encoding bytes (CrtTop.machine s1 r replay within)).stage2
        initial input none oracle =
      PMF.pure (some (Kriterion.CRT.Entry.labels (CrtSource.extract initial.memory.ram) input, oracle)) := by
  obtain ⟨last, used, run, words⟩ := stage2_run_none s1 r replay within initial.memory input oracle
  unfold LawShape.machineAbstract
  dsimp only
  rw [show (⟨Function.update (Function.update initial.memory.bits 0
      ([false, true] ++ SimulatorProtocol.affine input ++ SimulatorProtocol.output none)) 3 [],
      initial.memory.registers, initial.memory.ram⟩ : Memory) =
      stage2Memory initial.memory input none from rfl, run]
  simp only [optionT_mk_pure_some, pure_bind, atPc_memory, words, labels_extract _ keys]
  rfl

end Run

/-! ### The invalid arm of `Stage2Law` -/

section Arm

/-- **`Stage2Law` restricted to `output = none`**: `Stage2NoneArm` (`Glue/Machine.lean`), stated
verbatim over a generic entry under a name of this file, so that it unfolds to exactly the same term. -/
def NoneArm {FI EI : Type} (E : Privacy.CrtEntry FI EI) [Finite FI] [Finite EI]
    (simulator : BoundedMachine.Simulator) (bounded : LawShape.BoundedSamplers E) (extract : LawShape.Extract E) :
    Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ),
    letI := Fintype.ofFinite FI
    letI := Fintype.ofFinite EI
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    ∀ result, some result ∈ ((LawShape.machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage1
        parameter LazyOracle.empty).support →
      ∀ input oracle,
        (LawShape.routeMWith (E.view field group) (bounded field group) lazyReader).stage2
            (extract field group result.2.1.memory) input none oracle =
          (LawShape.machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage2 result.2.1 input none
            oracle

/-- **Every stage-1 result's memory satisfies `holds`**, at the instances of `Stage2Law`. -/
def Stage1Holds {FI EI : Type} (E : Privacy.CrtEntry FI EI) [Finite FI] [Finite EI]
    (simulator : BoundedMachine.Simulator) (holds : Memory → Prop) : Prop :=
  ∀ (field : FieldCertificate) (_group : @GroupCertificate field) (parameter : ℕ),
    letI := Fintype.ofFinite FI
    letI := Fintype.ofFinite EI
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    ∀ result, some result ∈ ((LawShape.machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage1
        parameter LazyOracle.empty).support → holds result.2.1.memory

variable (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)

/-- **The invalid arm of `Stage2Law`**: at the machine, any bounded samplers and the extract `CrtSource.extract`, on
an undefined output route M's stage 2 on the extracted source equals the machine's stage 2, for every stage-1 result
whose key cells hold (`keysOf`). -/
theorem stage2NoneArm_of_keys (bounded : LawShape.BoundedSamplers Privacy.Instance.crtEntry)
    (keysOf : Stage1Holds Privacy.Instance.crtEntry (CrtTop.machine s1 r replay within)
      (fun memory => KeyCellsHold memory.ram)) :
    NoneArm Privacy.Instance.crtEntry (CrtTop.machine s1 r replay within) bounded
      (fun _ _ memory => CrtSource.extract memory.ram) := by
  intro field group parameter result member input oracle
  have keys : KeyCellsHold result.2.1.memory.ram := keysOf field group parameter result member
  have machineSide := @stage2_none field Empty Empty (Fintype.ofFinite Empty) (Fintype.ofFinite Empty)
    (Classical.decEq Empty) (Classical.decEq Empty) s1 r replay within result.2.1 input oracle keys _
    Privacy.Instance.crtEntry.encoding Privacy.Instance.crtEntry.bytes
  rw [machineSide]
  rfl

end Arm

end

end CrtStage2Invalid

end Kriterion.CRT.SimMachine
