/-
**What stage 1 retains** (`CrtStage2Invalid.Stage1Holds crtEntry CrtTop.crtSimulator CrtValidStart.Retained`).

Every stage-1 result of the CRT machine holds `CrtStage1Final.finalOf (stage1Start parameter) d` for a draw `d` in
the support of the draw law (`CrtStage1Law.mem_support_stage1_final`). On that memory:

* the source cells are in range: the stores leave them in range (`cellsValid_stored`) and the tail, which writes only
  the record limbs and the true labels, leaves them alone (`cells_keep`);
* the hint cells are zero: the start memory's RAM is zero, the stores and the tail never write a hint cell
  (`stored_off`, `final_off`);
* the odd key cell `j` is the even key cell `j` XOR `Δ` of its coordinate: the tail writes it so (`finalOf_spec`) from
  the stored even cell and the stored `Δ`, which it leaves alone;
* the even key cells and the two `Δ` cells are below `2^128`: they hold the drawn zeros and deltas (`stored_zeros`,
  `stored_deltas`), which are below `2^128` on the support (`DrawValid`).

`retained_finalOf` is stated for any start memory whose hint cells are zero (the machine stays generic in its blocks).
-/

import Proof.Simulator.CRT.Stage1LawFinal
import Proof.Simulator.CRT.ValidStart
import Proof.Simulator.CRT.Machine

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit
open Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open CrtStage1 CrtDraws CrtStored CrtRecord CrtSource CrtTail CrtStage1Final
open Kriterion.ArgoMAC.PlanB.SimMachine.Top (afterTag)

noncomputable section

namespace CrtStage1Retained

variable [FieldCertificate]

/-- **The tail keeps the source cells in range**: it writes only the record limbs and the true labels. -/
theorem cells_keep {final stored : Memory}
    (off : ∀ address, ¬ LimbCell address → ¬ TrueCell address → final.ram address = stored.ram address)
    (valid : CellsValid stored.ram) : CellsValid final.ram where
  fields index inside := by
    rw [CrtStage1Law.off_far off (fieldBase + index)
      (by unfold fieldCount curveCellCount rowCellCount fieldBase at *; omega)
      (Or.inl (by unfold fieldCount curveCellCount rowCellCount fieldBase tmpBase at *; omega))
      (Or.inl (by unfold fieldCount curveCellCount rowCellCount fieldBase keyBase at *; omega))]
    exact valid.fields index inside
  bytes n inside := by
    rw [CrtStage1Law.off_far off (exceptionBase + n) (by unfold exceptionByteCount exceptionBase at *; omega)
      (Or.inl (by unfold exceptionByteCount exceptionBase tmpBase at *; omega))
      (Or.inl (by unfold exceptionByteCount exceptionBase keyBase at *; omega))]
    exact valid.bytes n inside
  joins n inside := by
    have := joinAddr_range n inside
    rw [CrtStage1Law.off_far off (joinAddr n) (by omega) (Or.inr (by unfold tmpBase; omega))
      (Or.inr (by unfold keyBase; omega))]
    exact valid.joins n inside
  pins n inside := by
    have := pinAddr_range n inside
    rw [CrtStage1Law.off_far off (pinAddr n) (by omega) (Or.inr (by unfold tmpBase; omega))
      (Or.inr (by unfold keyBase; omega))]
    exact valid.pins n inside
  digits n inside := by
    have := digitAddr_range n inside
    rw [CrtStage1Law.off_far off (digitAddr n) (by omega) (Or.inr (by unfold tmpBase; omega))
      (Or.inr (by unfold keyBase; omega))]
    exact valid.digits n inside

omit [FieldCertificate] in
/-- The encodings of a coordinate number at most `367`. -/
theorem encCount_le (κ : Nat) : CrtStage1.encCount κ ≤ 367 := by
  unfold CrtStage1.encCount Entry.xCount Entry.yCount
  split <;> omega

/-- **What stage 1 retains**, from a start memory whose hint cells are zero, for a draw in the support. -/
theorem retained_finalOf (start : Memory)
    (hintsZero : ∀ κ, κ < 2 → ∀ e, e < CrtStage1.encCount κ → start.ram (word (Layout.hintCell κ e)) = word 0)
    (d : Draw) (member : some d ∈ drawLaw.support) : CrtValidStart.Retained (finalOf start d) := by
  have valid := drawValid_of_support d member
  have spec := finalOf_spec start d (cellsValid_stored start d valid)
  have off := spec.2.2.2.2.2.2
  have trueCells := spec.2.2.2.2.2.1
  have evenKeep : ∀ j, j < labelCount → (finalOf start d).ram (word (keyBase + 2 * j)) =
      (storedMem start d).ram (word (keyBase + 2 * j)) :=
    fun j hj => off _ (even_not_limb j hj) (CrtStage1Law.notTrue_even j hj)
  have deltaKeep : ∀ κ, κ < 2 → (finalOf start d).ram (word (Layout.deltaCell κ)) =
      (storedMem start d).ram (word (Layout.deltaCell κ)) :=
    fun κ hκ => final_off _ _ off _ (by unfold Layout.deltaCell; omega)
      (Or.inr (by unfold Layout.deltaCell tmpBase; omega))
      (Or.inr (Or.inl (by unfold Layout.deltaCell keyBase labelCount; omega)))
  refine ⟨cells_keep off (cellsValid_stored start d valid), ?_, ?_, ?_, ?_⟩
  · intro κ hκ e he
    have eb := lt_of_lt_of_le he (encCount_le κ)
    rw [final_off _ _ off (Layout.hintCell κ e) (by unfold Layout.hintCell; omega)
      (Or.inr (by unfold Layout.hintCell tmpBase; omega))
      (Or.inr (Or.inl (by unfold Layout.hintCell keyBase labelCount; omega)))]
    rw [stored_off start d (Layout.hintCell κ e) (by unfold Layout.hintCell; omega)
      (Or.inl (by unfold Layout.hintCell; omega))
      (Or.inr (by unfold Layout.hintCell keyBase labelCount; omega))
      (Or.inr (by unfold Layout.hintCell; omega))
      (Or.inr (by unfold Layout.hintCell; omega))
      (Or.inr (by unfold Layout.hintCell; omega))
      (Or.inr (by unfold Layout.hintCell exceptionBase exceptionByteCount; omega))
      (Or.inr (by unfold Layout.hintCell fieldBase fieldCount curveCellCount rowCellCount; omega))]
    exact hintsZero κ hκ e he
  · intro j hj
    rw [evenKeep j hj, deltaKeep (j / 254) (by unfold labelCount at hj; omega)]
    exact trueCells j hj
  · intro j hj
    have hz : (storedMem start d).ram (word (keyBase + 2 * j)) = BitVec.ofNat 256 (d.zeros ⟨j, hj⟩) :=
      stored_zeros start d ⟨j, hj⟩
    rw [evenKeep j hj, hz, toNat_ofNat_small _ (valid.small.zeros _)]
    exact valid.zeros _
  · intro κ hκ
    have hd : (storedMem start d).ram (word (Layout.deltaCell κ)) = BitVec.ofNat 256 (d.deltas ⟨κ, hκ⟩) :=
      stored_deltas start d ⟨κ, hκ⟩
    rw [deltaKeep κ hκ, hd, toNat_ofNat_small _ (valid.small.deltas _)]
    exact valid.deltas _

omit [FieldCertificate] in
/-- The stage-1 start memory's RAM is zero. -/
theorem stage1Start_ram (parameter : Nat) (address : Word) :
    (CrtStage1Law.stage1Start parameter).ram address = word 0 := rfl

end CrtStage1Retained

/-- **Every stage-1 result of the CRT simulator retains the valid arm's facts.** -/
theorem CrtStage1Retained.retained :
    CrtStage2Invalid.Stage1Holds Privacy.Instance.crtEntry CrtTop.crtSimulator CrtValidStart.Retained := by
  rw [CrtTop.crtSimulator_eq]
  intro field _group parameter result member
  obtain ⟨d, dm, rfl⟩ := @CrtStage1Law.mem_support_stage1_final field Empty Empty (Fintype.ofFinite Empty)
    (Fintype.ofFinite Empty) (Classical.decEq Empty) (Classical.decEq Empty) _ _ _ CrtTop.crt_within
    (CrtTop.ofProg_size _) (CrtTop.ofProg_cost _) parameter _ result member
  exact CrtStage1Retained.retained_finalOf (CrtStage1Law.stage1Start parameter)
    (fun _ _ _ _ => CrtStage1Retained.stage1Start_ram parameter _) d dm

end

end Kriterion.CRT.SimMachine
