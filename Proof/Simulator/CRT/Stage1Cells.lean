/-
**Stage 1's cells and their laws** (M2): release-r1's bounded field cell with the width and bound as parameters
(`memSem_boundedCell`), for the records' digits (`digitCell`).
-/

import Proof.Simulator.CRT.Stage1Serial
import Proof.Simulator.Stage1Cells

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.ArgoMAC.Phase3.Glue (optionProduct)
open CrtStage1

namespace CrtCells

variable [FieldCertificate]

/-- **A bounded cell**: bounded rejection below `bound` over `width` coins, stored at `address`, scratch
cleared (release-r1's `memSem_fieldCell` with the width and bound as parameters). -/
theorem memSem_boundedCell (width bound address : Nat) (widthSmall : width ≤ 256) (boundSmall : bound < 2 ^ 256)
    (memory : Memory) :
    (Prog.seq (bounded width (testBelow bound) attempts (storeAt address rOut)) (zeroRegs samplerScratch)).memSem
        memory =
      (rejectLaw width (fun value => decide (value < bound)) attempts).map fun kept =>
        kept.map fun value =>
          clearRegs (storeRam memory (word address) (BitVec.ofNat 256 value)) samplerScratch := by
  have scratchJunk : attemptScratch [rAddr] = [rAcc, rBit, rAddr, rSel, rAddr] := rfl
  have outOut : rOut ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  have flagOut : rFlag ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  set start := setReg (setReg memory rOut (word 0)) rFlag (word 0) with startDef
  have startFlag : start.registers rFlag = bitWord false := by
    rw [startDef, setReg_registers, if_pos rfl]; rfl
  have shape : (Prog.seq (bounded width (testBelow bound) attempts (storeAt address rOut)) (zeroRegs samplerScratch)).memSem
        memory =
      ((Prog.rep attempts fun _ => attempt width (testBelow bound)).memSem start).bind
        (kleisli (cellTail address)) := by
    unfold bounded rejection
    rw [memSem_seq, memSem_seq, PMF.bind_bind]
    simp only [cst, Prog.memSem, Op.memSem, PMF.pure_bind]
    rw [startDef]
    have tailIs : cellTail address =
        (Prog.seq (.ite rFlag (storeAt address rOut) (.abort rSel)) (zeroRegs samplerScratch)).memSem :=
      funext fun final => (memSem_cellContinuation address final).symm
    rw [tailIs]
    congr 1
    funext result
    rw [kleisli_bind]
    congr 1
  rw [shape]
  have tailClear : ((Prog.rep attempts fun _ => attempt width (testBelow bound)).memSem start).bind
      (kleisli (cellTail address)) =
      (((Prog.rep attempts fun _ => attempt width (testBelow bound)).memSem start).map
        (Option.map fun final => clearRegs final (attemptScratch [rAddr]))).bind
        (kleisli (cellTail address)) := by
    rw [PMF.bind_map]
    congr 1
    funext result
    cases result with
    | none => rfl
    | some final => exact (cellTail_clear address final).symm
  rw [tailClear, rep_attempt_law width widthSmall (testBelow bound)
      (fun value => decide (value < bound)) [rAddr] (isTest_testBelow bound boundSmall)
      (by decide) (by decide) (by decide) attempts start ⟨false, startFlag⟩,
    attemptsLaw_eq_rejectLaw width _ (attemptScratch [rAddr]) outOut flagOut attempts _
      (clearRegs_idem _ _) (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl),
    PMF.bind_map]
  rw [PMF.map]
  congr 1
  funext kept
  cases kept with
  | none =>
      simp only [Function.comp_apply, kleisli, keptMem, cellTail]
      rw [if_pos (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl)]
      rfl
  | some value =>
      simp only [Function.comp_apply, kleisli, keptMem, cellTail]
      have flagOne : (clearRegs (setReg (setReg (clearRegs start (attemptScratch [rAddr])) rOut
          (BitVec.ofNat 256 value)) rFlag 1) (attemptScratch [rAddr])).registers rFlag = 1 := by
        rw [clearRegs_registers, if_neg flagOut, setReg_registers, if_pos rfl]
      rw [if_neg (by rw [flagOne]; decide)]
      simp only [Option.map_some]
      refine congrArg (fun final => PMF.pure (some final)) ?_
      rw [clearRegs_eq_iff]
      refine ⟨?_, ?_, fun index outside => ?_⟩
      · simp only [storeRam, setReg, (clearRegs_other _ _).1, clearRegs_registers, if_neg outOut,
          Function.update_of_ne (show rOut ≠ rFlag by decide), Function.update_self]
        rw [startDef]
        rfl
      · simp only [storeRam, setReg, (clearRegs_other _ _).2]
        rw [startDef]
        rfl
      · have notOut : index ≠ rOut := fun same => outside (by rw [same]; decide)
        have notFlag : index ≠ rFlag := fun same => outside (by rw [same]; decide)
        have notScratch : index ∉ attemptScratch [rAddr] := by
          intro inside
          apply outside
          rw [scratchJunk] at inside
          simp only [samplerScratch, List.mem_cons] at inside ⊢
          rcases inside with h | h | h | h | h | h <;> simp [h]
        have notAddr : index ≠ rAddr := fun same => notScratch (by rw [same, scratchJunk]; decide)
        simp only [storeRam, setReg_registers, clearRegs_registers, notAddr, notOut, notFlag,
          notScratch, if_false, startDef]


end CrtCells

end Kriterion.CRT.SimMachine
