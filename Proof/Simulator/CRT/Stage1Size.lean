/-
**The size of stage 1** (M7): `CrtStage1.program.size ≤ 2 ^ 55` and its cost likewise, by per-block bounds
(`CostFacts.size_rep_le`, `cost_le_size`); nothing is evaluated.

The one trap: the kernel reduces `Nat.add` to a literal whenever it compares two sums that are not
syntactically equal, and it unfolds `rep` although the elaborator treats it as irreducible. So the sum of the
block sizes is built by a chain of generic `rfl` lemmas (`size_program_eq`), and the arithmetic runs over free
variables (`bound_arith`).
-/

import Proof.Simulator.CRT.Stage1Serial
import Proof.Simulator.CRT.Stage1Stored
import Proof.Simulator.CRT.ReplayCost

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open CrtStage1

namespace CrtSize

theorem digitWidth_le_fin : ∀ i : Fin 85, digitWidth (modulusAt i) ≤ 9 := by decide +kernel

theorem digitWidth_le (n : Nat) : digitWidth (modulusAt (n % moduliCount)) ≤ 9 :=
  digitWidth_le_fin ⟨n % moduliCount, Nat.mod_lt _ (by decide)⟩

theorem size_digitCell (m address : Nat) (small : digitWidth m ≤ 9) : (digitCell m address).size ≤ 20000 := by
  unfold digitCell
  rw [Prog.size_seq, size_bounded _ _ _ _ (by rw [cost_storeAt]; norm_num), size_zeroRegs, size_storeAt,
    cost_storeAt]
  simp only [testBelow, Prog.size_seq, size_cst, ar, Prog.size, attempts, samplerScratch, List.length_cons,
    List.length_nil]
  omega

theorem size_recordProg (κ e : Nat) : (recordProg κ e).size ≤ 6000 := by
  unfold recordProg
  simp only [Prog.seqList, Prog.size_seq, Prog.size]
  have clear : clearLimbs.size = recordLimbCount * 3 :=
    Prog.size_rep _ _ _ fun _ _ => by simp only [Prog.size_seq, size_cst, size_storeAt]
  have horner : (Prog.rep moduliCount fun n => CrtStage1.hornerStep κ e (moduliCount - 1 - n)).size =
      moduliCount * 40 :=
    Prog.size_rep _ _ _ fun _ _ => by
      simp only [CrtStage1.hornerStep, Prog.seqList, Prog.size_seq, size_loadAt, size_setupConsts, size_mulSmallAdd,
        recordLimbCount, Prog.size]
  have emit : emitRecord.size = (2 + 3 * 112) + 4 * (2 + 3 * 128) := by
    simp only [emitRecord, Prog.seqList, Prog.size_seq, size_emitWord, Prog.size]
  rw [clear, horner, emit]
  simp only [recordLimbCount, moduliCount]
  omega

theorem size_pieceProg (p : Piece) (safe : CrtSerial.PieceSafe p) : (pieceProg p).size ≤ 6000 := by
  cases p with
  | word address width =>
      simp only [pieceProg, size_emitWord]
      have := safe.2.2
      omega
  | record κ e => exact size_recordProg κ e

-- CHECK: Recheck this closed list-length certificate under the fallback selector;
-- the inherited kernel recursion limit has not been tested with the new table.
set_option maxRecDepth 200000 in
theorem pieces_length : pieces.length = 56144 := by decide +kernel

theorem size_serializeList (list : List Piece) (safeAll : ∀ p ∈ list, CrtSerial.PieceSafe p) :
    (Prog.rep list.length fun n => pieceProg (list.getD (list.length - 1 - n) default)).size ≤
      list.length * 6000 := by
  refine CostFacts.size_rep_le _ _ _ fun n bound => ?_
  have index : list.length - 1 - n < list.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index, Option.getD_some]
  exact size_pieceProg _ (safeAll _ (List.getElem_mem index))

theorem size_serialize : serialize.size ≤ pieces.length * 6000 :=
  size_serializeList pieces CrtSerial.pieces_safe

/-- One block off the front of a `seqList` (generic, so its kernel check never sees a big program). -/
theorem size_cons (first : Prog) (rest : List Prog) :
    (Prog.seqList (first :: rest)).size = first.size + (Prog.seqList rest).size := rfl

/-- The program as its list of blocks (one delta step). -/
theorem program_eq : CrtStage1.program = Prog.seqList [CrtStage1.fields, CrtStage1.bytes, CrtStage1.joins,
    CrtStage1.pins, CrtStage1.digits, CrtStage1.zeros, CrtStage1.deltas, CrtStage1.serialize, CrtStage1.keyTrue,
    CrtStage1.clearLimbs, zeroRegs allRegisters] := rfl

/-- **The size of stage 1 is the sum of its blocks.** The proof term is a chain of `size_cons` and `congrArg`
whose types match syntactically. Any other route (`simp`, `rw`, `rfl` on differing sums) makes the kernel
reduce `Nat.add` of block sizes to literals, which unfolds the whole program: the kernel ignores `rep`'s
irreducibility. -/
theorem size_program_eq : CrtStage1.program.size =
    CrtStage1.fields.size + (CrtStage1.bytes.size + (CrtStage1.joins.size + (CrtStage1.pins.size +
        (CrtStage1.digits.size + (CrtStage1.zeros.size + (CrtStage1.deltas.size + (CrtStage1.serialize.size +
        (CrtStage1.keyTrue.size + (CrtStage1.clearLimbs.size + ((zeroRegs allRegisters).size +
        ((Prog.seqList []).size))))))))))) :=
  (congrArg Prog.size program_eq).trans
    ((size_cons CrtStage1.fields [CrtStage1.bytes, CrtStage1.joins, CrtStage1.pins, CrtStage1.digits,
        CrtStage1.zeros, CrtStage1.deltas, CrtStage1.serialize, CrtStage1.keyTrue, CrtStage1.clearLimbs,
        zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.fields.size) ((size_cons CrtStage1.bytes [CrtStage1.joins, CrtStage1.pins,
          CrtStage1.digits, CrtStage1.zeros, CrtStage1.deltas, CrtStage1.serialize, CrtStage1.keyTrue,
          CrtStage1.clearLimbs, zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.bytes.size) ((size_cons CrtStage1.joins [CrtStage1.pins, CrtStage1.digits,
          CrtStage1.zeros, CrtStage1.deltas, CrtStage1.serialize, CrtStage1.keyTrue, CrtStage1.clearLimbs,
          zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.joins.size) ((size_cons CrtStage1.pins [CrtStage1.digits, CrtStage1.zeros,
          CrtStage1.deltas, CrtStage1.serialize, CrtStage1.keyTrue, CrtStage1.clearLimbs,
          zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.pins.size) ((size_cons CrtStage1.digits [CrtStage1.zeros, CrtStage1.deltas,
          CrtStage1.serialize, CrtStage1.keyTrue, CrtStage1.clearLimbs, zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.digits.size) ((size_cons CrtStage1.zeros [CrtStage1.deltas,
          CrtStage1.serialize, CrtStage1.keyTrue, CrtStage1.clearLimbs, zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.zeros.size) ((size_cons CrtStage1.deltas [CrtStage1.serialize,
          CrtStage1.keyTrue, CrtStage1.clearLimbs, zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.deltas.size) ((size_cons CrtStage1.serialize [CrtStage1.keyTrue,
          CrtStage1.clearLimbs, zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.serialize.size) ((size_cons CrtStage1.keyTrue [CrtStage1.clearLimbs,
          zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.keyTrue.size) ((size_cons CrtStage1.clearLimbs [zeroRegs allRegisters]).trans
      (congrArg (HAdd.hAdd CrtStage1.clearLimbs.size) (size_cons (zeroRegs allRegisters) [])))))))))))))))))))))

theorem size_nil : (Prog.seqList []).size = 0 := rfl

/-- The arithmetic of the stage-1 bound, over free variables (no program is in sight). -/
theorem bound_arith (total a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Nat)
    (eq : total = a0 + (a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + (a8 + (a9 + (a10 + a11)))))))))))
    (h0 : a0 ≤ fieldCount * 457231) (h1 : a1 ≤ exceptionByteCount * 62) (h2 : a2 ≤ 2 * Entry.joinCount * 902)
    (h3 : a3 ≤ 2 * (Entry.pinCount * 128) * 104) (h4 : a4 ≤ recordCount * moduliCount * 20000)
    (h5 : a5 ≤ labelCount * 902) (h6 : a6 ≤ 2 * 902) (h7 : a7 ≤ 56144 * 6000) (h8 : a8 ≤ labelCount * 7)
    (h9 : a9 ≤ recordLimbCount * 3) (h10 : a10 ≤ 16) (h11 : a11 = 0) : total ≤ 2 ^ 55 := by
  rewrite [CrtStored.joinCount_eq] at h2
  rewrite [CrtConv.pinCount_eq] at h3
  simp only [fieldCount, curveCellCount, rowCellCount, exceptionByteCount, recordCount, moduliCount, labelCount,
    recordLimbCount, Entry.xCount, Entry.yCount] at h0 h1 h4 h5 h8 h9
  omega

/-- **Stage 1 fits.** -/
theorem size_program : CrtStage1.program.size ≤ 2 ^ 55 := by
  have fieldsSize : CrtStage1.fields.size = fieldCount * 457231 :=
    Prog.size_rep _ _ _ fun _ _ => Stage1.size_fieldCell _
  have bytesSize : CrtStage1.bytes.size = exceptionByteCount * 62 := Stage1.size_bytes
  have joinsSize : CrtStage1.joins.size ≤ 2 * Entry.joinCount * 902 :=
    CostFacts.size_rep_le _ _ _ fun _ _ => by rw [Stage1.size_wordCell]
  have pinsSize : CrtStage1.pins.size ≤ 2 * (Entry.pinCount * 128) * 104 :=
    CostFacts.size_rep_le _ _ _ fun n _ => by
      rw [Stage1.size_wordCell]
      have := CrtSerial.pinWidthAt_le (pinOf n)
      omega
  have digitsSize : CrtStage1.digits.size ≤ recordCount * moduliCount * 20000 :=
    CostFacts.size_rep_le _ _ _ fun n _ => size_digitCell _ _ (digitWidth_le n)
  have zerosSize : CrtStage1.zeros.size ≤ labelCount * 902 :=
    CostFacts.size_rep_le _ _ _ fun _ _ => by rw [Stage1.size_wordCell]
  have deltasSize : CrtStage1.deltas.size ≤ 2 * 902 :=
    CostFacts.size_rep_le _ _ _ fun _ _ => by rw [Stage1.size_wordCell]
  have keySize : CrtStage1.keyTrue.size ≤ labelCount * 7 :=
    CostFacts.size_rep_le _ _ _ fun _ _ => by
      simp only [keyXor, Prog.seqList, Prog.size_seq, size_loadAt, size_storeAt, ar, Prog.size]; omega
  have clearSize : CrtStage1.clearLimbs.size = recordLimbCount * 3 :=
    Prog.size_rep _ _ _ fun _ _ => by simp only [Prog.size_seq, size_cst, size_storeAt]
  have serialSize : CrtStage1.serialize.size ≤ 56144 * 6000 := by
    have bound := size_serialize
    rewrite [pieces_length] at bound
    exact bound
  have regs : (zeroRegs allRegisters).size = 16 := by
    rewrite [size_zeroRegs]; rfl
  exact bound_arith _ _ _ _ _ _ _ _ _ _ _ _ _ size_program_eq fieldsSize.le bytesSize.le joinsSize pinsSize
    digitsSize zerosSize deltasSize serialSize keySize clearSize.le regs.le size_nil

theorem cost_program : CrtStage1.program.cost ≤ 2 ^ 55 :=
  le_trans (CostFacts.cost_le_size _) size_program

end CrtSize

end Kriterion.CRT.SimMachine
