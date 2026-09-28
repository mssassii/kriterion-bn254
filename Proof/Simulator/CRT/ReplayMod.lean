/-
**The modulus-256 path agrees with the evaluator** (`agree_mod256Block`): the machine's
`mod256Block` against `liftHash (modEvalM T S coord pub joins v chunks i)` for a modulus of kind
`chunkZero`, with chunk 0's leaves in RAM (the chunk loop's saved leaves, `agree_chunkLoop`).
-/

import Proof.Simulator.CRT.ReplayBody
import Proof.Simulator.CRT.ReplayChunks
import Construction.Simulator.CRT.ReplayMod
import Construction.CRT.Coord

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC

/-- `modEvalM` at a modulus of kind `chunkZero` is the body on chunk 0's leaves at hot index
`v mod m`. -/
theorem modEvalM_chunkZero (T : CrtTable) (S coord : Nat) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → Nat) (v : Nat) (chunks : Nat → ChunkEval T.castWidth)
    (i : Fin T.count) (kind : T.kind i = .chunkZero) :
    modEvalM T S coord pub joins v chunks i =
      bodyEvalM (T.modulus i) S (T.padAnswers S i) coord i.val
        (fun residue => (chunks 0).leaves residue.val) (v % T.modulus i) (joins i) := by
  simp only [modEvalM, kind, stored_eq]

section Mod256

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The modulus-256 path**: the same questions as `modEvalM` at a `chunkZero` modulus, the
residues `L_e` at `outBase + e`, and the frame of the body plus the hot cell. -/
theorem agree_mod256Block (T : CrtTable) (S coord : Nat) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → Nat) (v : Nat) (vSmall : v < 2 ^ 256)
    (chunks : Nat → ChunkEval T.castWidth) (i : Fin T.count) (kind : T.kind i = .chunkZero)
    (width : Nat) (modulus : T.modulus i = 2 ^ width) (widthSmall : width < 256)
    (coordCell : Nat) (bc : BodyCells) (chain : BodyChain bc (T.modulus i) S (T.padAnswers S i))
    (memory : Memory) (coordVal : memory.ram (word coordCell) = word v)
    (leafCells : ∀ ρ, ρ < T.modulus i →
      memory.ram (word (bc.vecBase + ρ)) = labelWord ((chunks 0).leaves ρ))
    (joinCells : ∀ e : Fin S, memory.ram (word (bc.joinBase + e.val)) = word (joins i e))
    (joinsLt : ∀ e, joins i e < T.modulus i)
    (tagSmall : ∀ ρ j, ρ < T.modulus i → j < T.padAnswers S i → bodyTag coord i.val ρ j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (residues : Fin S → Nat) after =>
        (∀ e : Fin S, after.ram (word (bc.outBase + e.val)) = word (residues e)) ∧
          (∀ e : Fin S, residues e < T.modulus i) ∧
          Frame (mod256Writes bc S (T.padAnswers S i)) bodyClobbers memory after)
      ((mod256Block coordCell bc (T.modulus i) width S (T.padAnswers S i) (bodyTag coord i.val)).tree
        memory)
      (liftHash (modEvalM T S coord pub joins v chunks i)) := by
  have := chain.mPos; have := chain.mSmall; have := chain.joinBelow; have := chain.vecBelow
  have := chain.hotBelow; have := chain.ansBelow; have := chain.digBelow; have := chain.accABelow
  have := chain.accBBelow; have := chain.outFits
  obtain ⟨m1, run1, ram1, bits1, regs1⟩ :=
    exec_chunkPrefix coordCell bc.hot 0 width memory v coordVal vSmall (by norm_num) widthSmall
  have keep : ∀ x, x < bc.hot → m1.ram (word x) = memory.ram (word x) := fun x xb => by
    rw [ram1, Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
  have prefixFrame : Frame (Writes.cell bc.hot) (Clobbers.ofList [rA, rB, rAddr]) memory m1 :=
    ⟨fun address off => by rw [ram1, Function.update_of_ne off], bits1,
      fun register outside => regs1 register (fun h => outside (by simp [Clobbers.ofList, h]))
        (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))⟩
  unfold mod256Block
  rw [tree_seq_exec _ _ (det_chunkPrefix _ _ _ _) memory m1 run1,
    modEvalM_chunkZero T S coord pub joins v chunks i kind]
  refine (agree_bodyBlock bc (T.modulus i) S (T.padAnswers S i) coord i.val chain
    (fun residue => (chunks 0).leaves residue.val) (v % T.modulus i) (Nat.mod_lt _ (by omega))
    (joins i) joinsLt m1
    (by rw [ram1, Function.update_self, modulus, Nat.shiftRight_zero])
    (fun ρ => by
      rw [keep _ (by have := ρ.isLt; omega)]
      exact leafCells ρ.val ρ.isLt)
    (fun e => by
      rw [keep _ (by have := e.isLt; omega)]
      exact joinCells e)
    tagSmall).mono fun residues after post => ⟨post.1, post.2.1, ?_⟩
  refine (Frame.trans prefixFrame post.2.2).mono (fun address inside => inside.symm) ?_
  rintro register (inside | inside)
  · simp only [Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false] at inside
    simp only [bodyClobbers, Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false]
    rcases inside with h | h | h <;> simp [h]
  · exact inside

end Mod256

end Kriterion.CRT.SimMachine
