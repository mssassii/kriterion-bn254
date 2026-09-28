/-
**Route M's collector solve, as an execution** (M6).

The blocks of `Construction/Simulator/CRT/Solve.lean` are deterministic; each lemma gives the block's execution
(`Prog.exec`) in field terms: the accumulator register, the stored mask, the registers it keeps. `exec_solveDigit`
composes them: the three masks of digit `d` are written to `openTarget d c`, nothing else in RAM changes.
-/

import Proof.Simulator.ReplayElement
import Proof.Simulator.CRT.Exec
import Construction.Simulator.CRT.Solve
import Construction.CRT.Rows

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.ArgoMAC.PlanB (NormRow)

noncomputable section

namespace Solve

variable [FieldCertificate]

/-! ### Field words -/

theorem fieldSub_words (first second : BaseField) :
    Arithmetic.fieldSub.eval (fieldWord first) (fieldWord second) = fieldWord (first - second) := by
  rw [eval_fieldSub, fieldWord_cast, fieldWord_cast]

theorem fieldInv_word (value : BaseField) (other : Word) :
    Arithmetic.fieldInv.eval (fieldWord value) other = fieldWord value⁻¹ := by
  show BitVec.ofNat 256 ((((fieldWord value).toNat : Nat) : BaseField)⁻¹).val = _
  rw [fieldWord_cast]
  rfl

omit [FieldCertificate] in
theorem exec_seqList_cons (first : Prog) (rest : List Prog) (memory middle : Memory)
    (runs : first.exec memory = some middle) :
    (Prog.seqList (first :: rest)).exec memory = (Prog.seqList rest).exec middle := by
  show (first.exec memory).bind (Prog.seqList rest).exec = _
  rw [runs]
  rfl

omit [FieldCertificate] in
theorem exec_seqList_nil (memory : Memory) : (Prog.seqList []).exec memory = some memory := rfl

/-! ### The accumulating blocks -/

/-- **`rAcc += (v − π) · f`.** -/
theorem exec_addRowScaled (dec mask : Nat) (factor : Register) (memory : Memory) (acc v p f : BaseField)
    (hSel : factor ≠ rSel) (hD : factor ≠ rD) (hAddr : factor ≠ rAddr) (hAcc : factor ≠ rAcc)
    (decCell : memory.ram (word dec) = fieldWord v) (maskCell : memory.ram (word mask) = fieldWord p)
    (factorReg : memory.registers factor = fieldWord f) (accReg : memory.registers rAcc = fieldWord acc) :
    ∃ after, (addRowScaled dec mask factor).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rAcc = fieldWord (acc + (v - p) * f) ∧
      ∀ register, register ≠ rAcc → register ≠ rAddr → register ≠ rSel → register ≠ rD →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false,
      if_neg hSel, if_neg hD, if_neg hAddr, if_neg hAcc]
    rw [decCell, maskCell, factorReg, accReg, fieldSub_words, fieldMul_words, fieldAdd_words]
  · simp only [setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-- **`rAcc += v − π`.** -/
theorem exec_addRow (dec mask : Nat) (memory : Memory) (acc v p : BaseField)
    (decCell : memory.ram (word dec) = fieldWord v) (maskCell : memory.ram (word mask) = fieldWord p)
    (accReg : memory.registers rAcc = fieldWord acc) :
    ∃ after, (addRow dec mask).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rAcc = fieldWord (acc + (v - p)) ∧
      ∀ register, register ≠ rAcc → register ≠ rAddr → register ≠ rSel → register ≠ rD →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false]
    rw [decCell, maskCell, accReg, fieldSub_words, fieldAdd_words]
  · simp only [setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-- **`rAcc += c · f`.** -/
theorem exec_addConstScaled (cell : Nat) (factor : Register) (memory : Memory) (acc c f : BaseField)
    (hSel : factor ≠ rSel) (hAddr : factor ≠ rAddr) (hAcc : factor ≠ rAcc)
    (constCell : memory.ram (word cell) = fieldWord c)
    (factorReg : memory.registers factor = fieldWord f) (accReg : memory.registers rAcc = fieldWord acc) :
    ∃ after, (addConstScaled cell factor).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rAcc = fieldWord (acc + c * f) ∧
      ∀ register, register ≠ rAcc → register ≠ rAddr → register ≠ rSel →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 => ?_⟩
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false,
      if_neg hSel, if_neg hAddr, if_neg hAcc]
    rw [constCell, factorReg, accReg, fieldMul_words, fieldAdd_words]
  · simp only [setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3]

/-! ### The finishing blocks -/

/-- **`RAM[out] = v − (w − acc)`.** -/
theorem exec_finishMask (row dec out : Nat) (memory : Memory) (acc w v : BaseField)
    (rowCell : memory.ram (word row) = fieldWord w) (decCell : memory.ram (word dec) = fieldWord v)
    (accReg : memory.registers rAcc = fieldWord acc) :
    ∃ after, (finishMask row dec out).exec memory = some after ∧
      after.ram = Function.update memory.ram (word out) (fieldWord (v - (w - acc))) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAddr → register ≠ rSel → register ≠ rD →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register n1 n2 n3 => ?_⟩
  · simp (config := {decide := true}) only [storeRam, setReg, Function.update_apply, if_true, if_false]
    rw [rowCell, decCell, accReg, fieldSub_words, fieldSub_words]
  · simp only [storeRam, setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3]

/-- **`RAM[out] = v − (w − acc) · z⁻¹`**, `z` in `rC`. -/
theorem exec_finishMaskOver (row dec out : Nat) (memory : Memory) (acc w v z : BaseField)
    (rowCell : memory.ram (word row) = fieldWord w) (decCell : memory.ram (word dec) = fieldWord v)
    (accReg : memory.registers rAcc = fieldWord acc) (zReg : memory.registers rC = fieldWord z) :
    ∃ after, (finishMaskOver rC row dec out).exec memory = some after ∧
      after.ram = Function.update memory.ram (word out) (fieldWord (v - (w - acc) * z⁻¹)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAddr → register ≠ rSel → register ≠ rD → register ≠ rAcc →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := {decide := true}) only [storeRam, setReg, Function.update_apply, if_true, if_false]
    rw [rowCell, decCell, accReg, zReg, fieldSub_words, fieldInv_word, fieldMul_words, fieldSub_words]
  · simp only [storeRam, setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-- `(−1)^ν w = w − ν w − ν w`, `ν` as `0` or `1`. -/
theorem signed_eq (sign : Bool) (w : BaseField) :
    w - Rows.flagValue sign * w - Rows.flagValue sign * w = Rows.signed sign w := by
  cases sign
  · simp [Rows.flagValue, Rows.signed]
  · simp only [Rows.flagValue, Rows.signed, if_true]
    ring

set_option maxHeartbeats 1000000 in
/-- **`RAM[out] = v − ((−1)^ν w − acc) · z⁻¹`**, `z` in `rC`, `ν` in `RAM[sign]`. -/
theorem exec_finishMaskSigned (sign row dec out : Nat) (memory : Memory) (acc w v z : BaseField) (ν : Bool)
    (signCell : memory.ram (word sign) = fieldWord (Rows.flagValue ν))
    (rowCell : memory.ram (word row) = fieldWord w) (decCell : memory.ram (word dec) = fieldWord v)
    (accReg : memory.registers rAcc = fieldWord acc) (zReg : memory.registers rC = fieldWord z) :
    ∃ after, (finishMaskSigned sign rC row dec out).exec memory = some after ∧
      after.ram = Function.update memory.ram (word out) (fieldWord (v - (Rows.signed ν w - acc) * z⁻¹)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAddr → register ≠ rSel → register ≠ rD → register ≠ rAcc →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := {decide := true}) only [storeRam, setReg, Function.update_apply, if_true, if_false]
    rw [rowCell, signCell, decCell, accReg, zReg]
    simp only [fieldMul_words, fieldSub_words, fieldInv_word]
    rw [signed_eq]
  · simp only [storeRam, setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-! ### The rows -/

omit [FieldCertificate] in
theorem exec_loadAt (target : Register) (address : Nat) (memory : Memory) :
    (loadAt target address).exec memory =
      some (setReg (setReg memory rAddr (word address)) target (memory.ram (word address))) := rfl

/-- The registers the rows keep: `rA = x`, `rB = y`, `rC = x²`. -/
def RowRegs (memory : Memory) (x y : BaseField) : Prop :=
  memory.registers rA = fieldWord x ∧ memory.registers rB = fieldWord y ∧
    memory.registers rC = fieldWord (x * x)

theorem RowRegs.keep {memory after : Memory} {x y : BaseField} (holds : RowRegs memory x y)
    (keep : ∀ register, register ≠ rAcc → register ≠ rAddr → register ≠ rSel → register ≠ rD →
      after.registers register = memory.registers register) : RowRegs after x y :=
  ⟨(keep rA (by decide) (by decide) (by decide) (by decide)).trans holds.1,
    (keep rB (by decide) (by decide) (by decide) (by decide)).trans holds.2.1,
    (keep rC (by decide) (by decide) (by decide) (by decide)).trans holds.2.2⟩

/-- A block keeps every register but `rAcc`, `rAddr`, `rSel`, `rD`. -/
def Keeps4 (memory after : Memory) : Prop :=
  ∀ register, register ≠ rAcc → register ≠ rAddr → register ≠ rSel → register ≠ rD →
    after.registers register = memory.registers register

/-- **The `X` row**: `π = v(x9) − (W.x − (xC0 + r(x7)·x + r(y10)))`. -/
theorem exec_rowX (d : Nat) (memory : Memory) (x y c0 v7 p7 v10 p10 w v9 : BaseField)
    (regs : RowRegs memory x y)
    (hc : memory.ram (word (Opening.rowCell d 0)) = fieldWord c0)
    (hv7 : memory.ram (word (decX (4 * d))) = fieldWord v7)
    (hp7 : memory.ram (word (maskX (4 * d))) = fieldWord p7)
    (hv10 : memory.ram (word (decY (3 * d))) = fieldWord v10)
    (hp10 : memory.ram (word (maskY (3 * d))) = fieldWord p10)
    (hw : memory.ram (word (openRow d)) = fieldWord w)
    (hv9 : memory.ram (word (decX (4 * d + 1))) = fieldWord v9) :
    ∃ after, (rowX d).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (openTarget d 0))
        (fieldWord (v9 - (w - (c0 + (v7 - p7) * x + (v10 - p10))))) ∧
      after.bits = memory.bits ∧ RowRegs after x y ∧ Keeps4 memory after := by
  set m1 := setReg (setReg memory rAddr (word (Opening.rowCell d 0))) rAcc
    (memory.ram (word (Opening.rowCell d 0))) with m1Def
  have acc1 : m1.registers rAcc = fieldWord c0 := by
    rw [m1Def]; simp only [setReg, Function.update_self]; exact hc
  have regs1 : RowRegs m1 x y := RowRegs.keep regs fun register n1 n2 _ _ => by
    rw [m1Def]; simp only [setReg, Function.update_apply, if_neg n1, if_neg n2]
  obtain ⟨m2, run2, ram2, bits2, acc2, keep2⟩ := exec_addRowScaled _ _ rA m1 c0 v7 p7 x (by decide)
    (by decide) (by decide) (by decide) hv7 hp7 regs1.1 acc1
  obtain ⟨m3, run3, ram3, bits3, acc3, keep3⟩ := exec_addRow _ _ m2 _ v10 p10
    (by rw [ram2]; exact hv10) (by rw [ram2]; exact hp10) acc2
  obtain ⟨m4, run4, ram4, bits4, keep4⟩ := exec_finishMask _ _ (openTarget d 0) m3 _ w v9
    (by rw [ram3, ram2]; exact hw) (by rw [ram3, ram2]; exact hv9) acc3
  refine ⟨m4, ?_, ?_, ?_, ?_, fun register n1 n2 n3 n4 => ?_⟩
  · unfold rowX
    rw [exec_seqList_cons _ _ _ m1 (exec_loadAt _ _ _), exec_seqList_cons _ _ _ m2 run2,
      exec_seqList_cons _ _ _ m3 run3, exec_seqList_cons _ _ _ m4 run4, exec_seqList_nil]
  · rw [ram4, ram3, ram2]; rfl
  · rw [bits4, bits3, bits2]; rfl
  · exact RowRegs.keep (RowRegs.keep (RowRegs.keep regs1 keep2) keep3)
      fun register n1 n2 n3 n4 => keep4 register n2 n3 n4
  · rw [keep4 register n2 n3 n4, keep3 register n1 n2 n3 n4, keep2 register n1 n2 n3 n4, m1Def]
    simp only [setReg, Function.update_apply, if_neg n1, if_neg n2]

omit [FieldCertificate] in
theorem exec_cst (target : Register) (value : Nat) (memory : Memory) :
    (cst target value).exec memory = some (setReg memory target (word value)) := rfl

theorem fieldWord_zero : fieldWord (0 : BaseField) = word 0 := rfl

/-- **The sign row**: `π = v(cubic) − ((−1)^ν W.y − (r(y8)·y + r(y10')))·(x·x)⁻¹`. -/
theorem exec_rowY (d : Nat) (memory : Memory) (x y v8 p8 v10 p10 w vc : BaseField) (ν : Bool)
    (regs : RowRegs memory x y)
    (hs : memory.ram (word (Layout.signCell d)) = fieldWord (Rows.flagValue ν))
    (hv8 : memory.ram (word (decY (3 * d + 1))) = fieldWord v8)
    (hp8 : memory.ram (word (maskY (3 * d + 1))) = fieldWord p8)
    (hv10 : memory.ram (word (decY (3 * d + 2))) = fieldWord v10)
    (hp10 : memory.ram (word (maskY (3 * d + 2))) = fieldWord p10)
    (hw : memory.ram (word (openRow d + 1)) = fieldWord w)
    (hvc : memory.ram (word (decX (4 * d + 2))) = fieldWord vc) :
    ∃ after, (rowY d).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (openTarget d 1))
        (fieldWord (vc - (Rows.signed ν w - (0 + (v8 - p8) * y + (v10 - p10))) * (x * x)⁻¹)) ∧
      after.bits = memory.bits ∧ RowRegs after x y ∧ Keeps4 memory after := by
  set m1 := setReg memory rAcc (word 0) with m1Def
  have acc1 : m1.registers rAcc = fieldWord 0 := by
    rw [m1Def, fieldWord_zero]; simp only [setReg, Function.update_self]
  have regs1 : RowRegs m1 x y := RowRegs.keep regs fun register n1 _ _ _ => by
    rw [m1Def]; simp only [setReg, Function.update_apply, if_neg n1]
  obtain ⟨m3, run3, ram3, bits3, acc3, keep3⟩ := exec_addRowScaled _ _ rB m1 _ v8 p8 y (by decide)
    (by decide) (by decide) (by decide) hv8 hp8 regs1.2.1 acc1
  have regs3 : RowRegs m3 x y := RowRegs.keep regs1 keep3
  obtain ⟨m4, run4, ram4, bits4, acc4, keep4⟩ := exec_addRow _ _ m3 _ v10 p10
    (by rw [ram3]; exact hv10) (by rw [ram3]; exact hp10) acc3
  have regs4 : RowRegs m4 x y := RowRegs.keep regs3 keep4
  obtain ⟨m5, run5, ram5, bits5, keep5⟩ := exec_finishMaskSigned _ _ _ (openTarget d 1) m4 _ w vc (x * x) ν
    (by rw [ram4, ram3]; exact hs) (by rw [ram4, ram3]; exact hw) (by rw [ram4, ram3]; exact hvc) acc4 regs4.2.2
  refine ⟨m5, ?_, ?_, ?_, RowRegs.keep regs4 fun register n1 n2 n3 n4 => keep5 register n2 n3 n4 n1,
    fun register n1 n2 n3 n4 => ?_⟩
  · unfold rowY
    rw [exec_seqList_cons _ _ _ m1 (exec_cst _ _ _), exec_seqList_cons _ _ _ m3 run3,
      exec_seqList_cons _ _ _ m4 run4, exec_seqList_cons _ _ _ m5 run5, exec_seqList_nil]
  · rw [ram5, ram4, ram3]; rfl
  · rw [bits5, bits4, bits3]; rfl
  · rw [keep5 register n2 n3 n4 n1, keep4 register n1 n2 n3 n4, keep3 register n1 n2 n3 n4, m1Def]
    simp only [setReg, Function.update_apply, if_neg n1]

/-- **The `Z` row**: `π = v(x9'') − (W.z − 0)`. -/
theorem exec_rowZ (d : Nat) (memory : Memory) (x y w v9 : BaseField) (regs : RowRegs memory x y)
    (hw : memory.ram (word (openRow d + 2)) = fieldWord w)
    (hv9 : memory.ram (word (decX (4 * d + 3))) = fieldWord v9) :
    ∃ after, (rowZ d).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (openTarget d 2)) (fieldWord (v9 - (w - 0))) ∧
      after.bits = memory.bits ∧ RowRegs after x y ∧ Keeps4 memory after := by
  set m1 := setReg memory rAcc (word 0) with m1Def
  have acc1 : m1.registers rAcc = fieldWord 0 := by
    rw [m1Def, fieldWord_zero]; simp only [setReg, Function.update_self]
  have regs1 : RowRegs m1 x y := RowRegs.keep regs fun register n1 _ _ _ => by
    rw [m1Def]; simp only [setReg, Function.update_apply, if_neg n1]
  obtain ⟨m2, run2, ram2, bits2, keep2⟩ := exec_finishMask _ _ (openTarget d 2) m1 0 w v9 hw hv9 acc1
  refine ⟨m2, ?_, ?_, ?_, RowRegs.keep regs1 fun register n1 n2 n3 n4 => keep2 register n2 n3 n4,
    fun register n1 n2 n3 n4 => ?_⟩
  · unfold rowZ
    rw [exec_seqList_cons _ _ _ m1 (exec_cst _ _ _), exec_seqList_cons _ _ _ m2 run2, exec_seqList_nil]
  · rw [ram2]; rfl
  · rw [bits2]; rfl
  · rw [keep2 register n2 n3 n4, m1Def]
    simp only [setReg, Function.update_apply, if_neg n1]

/-- **The prefix**: `x`, `y`, `x²` from the request cells. -/
theorem exec_solvePrefix (memory : Memory) (x y : BaseField)
    (hx : memory.ram (word reqX) = fieldWord x) (hy : memory.ram (word reqY) = fieldWord y) :
    ∃ after, solvePrefix.exec memory = some after ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      RowRegs after x y ∧
      ∀ register, register ≠ rAddr → register ≠ rA → register ≠ rB → register ≠ rC →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ⟨?_, ?_, ?_⟩, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false]
    exact hx
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false]
    exact hy
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false]
    rw [hx, fieldMul_words]
  · simp only [setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-! ### One digit -/

/-- **The three masks of digit `d`**, from the request `x, y`, the published row (its `X` constant and sign bit;
the normalization flags clear), the target row `W` and the cell contents `dx, px` (delivered values and masks of the
`x` encodings), `dy, py` (of the `y` encodings). -/
def maskFormula (x y : BaseField) (gamma : NormRow) (w : FieldMacToECMac.HomogeneousValue)
    (dx px dy py : Nat → BaseField) (d : Nat) : Fin 3 → BaseField
  | 0 => dx (4 * d + 1) - (w.x - (gamma.xC0 + (dx (4 * d) - px (4 * d)) * x + (dy (3 * d) - py (3 * d))))
  | 1 => dx (4 * d + 2) - (Rows.signed gamma.sign w.y - (0 + (dy (3 * d + 1) - py (3 * d + 1)) * y +
      (dy (3 * d + 2) - py (3 * d + 2)))) * (x * x)⁻¹
  | 2 => dx (4 * d + 3) - (w.z - 0)

omit [FieldCertificate] in
theorem cellNe {first second : Nat} (firstSmall : first < 2 ^ 256) (secondSmall : second < 2 ^ 256)
    (different : first ≠ second) : word first ≠ word second := fun same =>
  different (by
    have := congrArg BitVec.toNat same
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstSmall, Nat.mod_eq_of_lt secondSmall] at this
    exact this)

/-- What the solve of digit `d` reads, in field terms. -/
structure DigitCells (memory : Memory) (x y : BaseField) (gamma : NormRow)
    (w : FieldMacToECMac.HomogeneousValue) (dx px dy py : Nat → BaseField) (d : Nat) : Prop where
  reqXCell : memory.ram (word reqX) = fieldWord x
  reqYCell : memory.ram (word reqY) = fieldWord y
  row0 : memory.ram (word (Opening.rowCell d 0)) = fieldWord gamma.xC0
  sign : memory.ram (word (Layout.signCell d)) = fieldWord (Rows.flagValue gamma.sign)
  decXCell : ∀ k, k < 4 → memory.ram (word (decX (4 * d + k))) = fieldWord (dx (4 * d + k))
  maskX0 : memory.ram (word (maskX (4 * d))) = fieldWord (px (4 * d))
  decYCell : ∀ k, k < 3 → memory.ram (word (decY (3 * d + k))) = fieldWord (dy (3 * d + k))
  maskYCell : ∀ k, k < 3 → memory.ram (word (maskY (3 * d + k))) = fieldWord (py (3 * d + k))
  targetX : memory.ram (word (openRow d)) = fieldWord w.x
  targetY : memory.ram (word (openRow d + 1)) = fieldWord w.y
  targetZ : memory.ram (word (openRow d + 2)) = fieldWord w.z

/-- **One digit**: the three masks are written to `openTarget d c`, nothing else in RAM changes. -/
theorem exec_solveDigit (d : Nat) (small : d < 91) (memory : Memory) (x y : BaseField) (gamma : NormRow)
    (w : FieldMacToECMac.HomogeneousValue) (dx px dy py : Nat → BaseField)
    (cells : DigitCells memory x y gamma w dx px dy py d) :
    ∃ after, (solveDigit d).exec memory = some after ∧
      after.ram = Function.update (Function.update (Function.update memory.ram
        (word (openTarget d 0)) (fieldWord (maskFormula x y gamma w dx px dy py d 0)))
        (word (openTarget d 1)) (fieldWord (maskFormula x y gamma w dx px dy py d 1)))
        (word (openTarget d 2)) (fieldWord (maskFormula x y gamma w dx px dy py d 2)) ∧
      after.bits = memory.bits ∧
      ∀ register, ¬ solveClobbers register → after.registers register = memory.registers register := by
  have t0 : ∀ address, address < openBase + 1000 ∨ openBase + 2000 ≤ address → address < 2 ^ 256 →
      word address ≠ word (openTarget d 0) := fun address range fits =>
    cellNe fits (by unfold openTarget openBase; omega) (by unfold openTarget; omega)
  have t1 : ∀ address, address < openBase + 1000 ∨ openBase + 2000 ≤ address → address < 2 ^ 256 →
      word address ≠ word (openTarget d 1) := fun address range fits =>
    cellNe fits (by unfold openTarget openBase; omega) (by unfold openTarget; omega)
  obtain ⟨m1, run1, ram1, bits1, regs1, keep1⟩ :=
    exec_solvePrefix memory x y cells.reqXCell cells.reqYCell
  have dx0 := cells.decXCell 0 (by omega)
  have dx1 := cells.decXCell 1 (by omega)
  have dx2 := cells.decXCell 2 (by omega)
  have dx3 := cells.decXCell 3 (by omega)
  have dy0 := cells.decYCell 0 (by omega)
  have dy1 := cells.decYCell 1 (by omega)
  have dy2 := cells.decYCell 2 (by omega)
  have py0 := cells.maskYCell 0 (by omega)
  have py1 := cells.maskYCell 1 (by omega)
  have py2 := cells.maskYCell 2 (by omega)
  simp only [Nat.add_zero] at dx0 dy0 py0
  obtain ⟨m2, run2, ram2, bits2, regs2, keep2⟩ := exec_rowX d m1 x y gamma.xC0 (dx (4 * d)) (px (4 * d))
    (dy (3 * d)) (py (3 * d)) w.x (dx (4 * d + 1)) regs1 (by rw [ram1]; exact cells.row0)
    (by rw [ram1]; exact dx0) (by rw [ram1]; exact cells.maskX0) (by rw [ram1]; exact dy0)
    (by rw [ram1]; exact py0) (by rw [ram1]; exact cells.targetX) (by rw [ram1]; exact dx1)
  have read2 : ∀ address, address < openBase + 1000 ∨ openBase + 2000 ≤ address → address < 2 ^ 256 →
      m2.ram (word address) = memory.ram (word address) := fun address range fits => by
    rw [ram2, Function.update_of_ne (t0 address range fits), ram1]
  obtain ⟨m3, run3, ram3, bits3, regs3, keep3⟩ := exec_rowY d m2 x y
    (dy (3 * d + 1)) (py (3 * d + 1)) (dy (3 * d + 2)) (py (3 * d + 2)) w.y (dx (4 * d + 2)) gamma.sign regs2
    (by rw [read2 _ (by unfold Layout.signCell fieldBase openBase; omega)
      (by unfold Layout.signCell fieldBase; omega)]; exact cells.sign)
    (by rw [read2 _ (by unfold decY Layout.decodedCell openBase; omega)
      (by unfold decY Layout.decodedCell; omega)]; exact dy1)
    (by rw [read2 _ (by unfold maskY Layout.maskCell openBase; omega)
      (by unfold maskY Layout.maskCell; omega)]; exact py1)
    (by rw [read2 _ (by unfold decY Layout.decodedCell openBase; omega)
      (by unfold decY Layout.decodedCell; omega)]; exact dy2)
    (by rw [read2 _ (by unfold maskY Layout.maskCell openBase; omega)
      (by unfold maskY Layout.maskCell; omega)]; exact py2)
    ((read2 _ (by unfold openRow openBase; omega) (by unfold openRow openBase; omega)).trans cells.targetY)
    (by rw [read2 _ (by unfold decX Layout.decodedCell openBase; omega)
      (by unfold decX Layout.decodedCell; omega)]; exact dx2)
  have read3 : ∀ address, address < openBase + 1000 ∨ openBase + 2000 ≤ address → address < 2 ^ 256 →
      m3.ram (word address) = memory.ram (word address) := fun address range fits => by
    rw [ram3, Function.update_of_ne (t1 address range fits), read2 address range fits]
  obtain ⟨m4, run4, ram4, bits4, regs4, keep4⟩ := exec_rowZ d m3 x y w.z (dx (4 * d + 3)) regs3
    ((read3 _ (by unfold openRow openBase; omega) (by unfold openRow openBase; omega)).trans cells.targetZ)
    (by rw [read3 _ (by unfold decX Layout.decodedCell openBase; omega)
      (by unfold decX Layout.decodedCell; omega)]; exact dx3)
  refine ⟨m4, ?_, ?_, ?_, ?_⟩
  · unfold solveDigit
    rw [exec_seqList_cons _ _ _ m1 run1, exec_seqList_cons _ _ _ m2 run2, exec_seqList_cons _ _ _ m3 run3,
      exec_seqList_cons _ _ _ m4 run4, exec_seqList_nil]
  · rw [ram4, ram3, ram2, ram1]
    rfl
  · rw [bits4, bits3, bits2, bits1]
  · intro register outside
    simp only [solveClobbers, Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := outside
    rw [keep4 register n1 n2 n3 n7, keep3 register n1 n2 n3 n7, keep2 register n1 n2 n3 n7,
      keep1 register n2 n4 n5 n6]

/-! ### The 91 digits -/

/-- The solve reads nothing in the target region `[openBase + 1000, openBase + 2000)`. -/
def OutsideTargets (address : Nat) : Prop := address < openBase + 1000 ∨ openBase + 2000 ≤ address

omit [FieldCertificate] in
/-- **The cells of a digit transfer** to any memory that agrees outside the target region. -/
theorem DigitCells.transfer {memory memory' : Memory} {x y : BaseField} {gamma : NormRow}
    {w : FieldMacToECMac.HomogeneousValue} {dx px dy py : Nat → BaseField} {d : Nat} (small : d < 91)
    (cells : DigitCells memory x y gamma w dx px dy py d)
    (same : ∀ address, OutsideTargets address → address < 2 ^ 256 →
      memory'.ram (word address) = memory.ram (word address)) :
    DigitCells memory' x y gamma w dx px dy py d where
  reqXCell := (same _ (by unfold OutsideTargets reqX requestBase openBase; omega)
    (by unfold reqX requestBase; omega)).trans cells.reqXCell
  reqYCell := (same _ (by unfold OutsideTargets reqY requestBase openBase; omega)
    (by unfold reqY requestBase; omega)).trans cells.reqYCell
  row0 := (same _ (by unfold OutsideTargets Opening.rowCell fieldBase curveCellCount openBase; omega)
    (by unfold Opening.rowCell fieldBase curveCellCount; omega)).trans cells.row0
  sign := (same _ (by unfold OutsideTargets Layout.signCell fieldBase openBase; omega)
    (by unfold Layout.signCell fieldBase; omega)).trans cells.sign
  decXCell k bound := (same _ (by unfold OutsideTargets decX Layout.decodedCell openBase; omega)
    (by unfold decX Layout.decodedCell; omega)).trans (cells.decXCell k bound)
  maskX0 := (same _ (by unfold OutsideTargets maskX Layout.maskCell openBase; omega)
    (by unfold maskX Layout.maskCell; omega)).trans cells.maskX0
  decYCell k bound := (same _ (by unfold OutsideTargets decY Layout.decodedCell openBase; omega)
    (by unfold decY Layout.decodedCell; omega)).trans (cells.decYCell k bound)
  maskYCell k bound := (same _ (by unfold OutsideTargets maskY Layout.maskCell openBase; omega)
    (by unfold maskY Layout.maskCell; omega)).trans (cells.maskYCell k bound)
  targetX := (same _ (by unfold OutsideTargets openRow openBase; omega)
    (by unfold openRow openBase; omega)).trans cells.targetX
  targetY := (same _ (by unfold OutsideTargets openRow openBase; omega)
    (by unfold openRow openBase; omega)).trans cells.targetY
  targetZ := (same _ (by unfold OutsideTargets openRow openBase; omega)
    (by unfold openRow openBase; omega)).trans cells.targetZ

omit [FieldCertificate] in
theorem openTarget_ne {d c d' c' : Nat} (small : d < 91) (cSmall : c < 3) (small' : d' < 91) (cSmall' : c' < 3)
    (different : d ≠ d' ∨ c ≠ c') : word (openTarget d c) ≠ word (openTarget d' c') :=
  cellNe (by unfold openTarget openBase; omega) (by unfold openTarget openBase; omega)
    (by unfold openTarget; omega)

/-- The solve's invariant after `count` digits. -/
def SolveInv (start : Memory) (x y : BaseField) (gammas : Nat → NormRow)
    (targets : Nat → FieldMacToECMac.HomogeneousValue) (dx px dy py : Nat → BaseField) (count : Nat)
    (memory : Memory) : Prop :=
  (∀ d (c : Fin 3), d < count →
      memory.ram (word (openTarget d c.val)) = fieldWord (maskFormula x y (gammas d) (targets d) dx px dy py d c)) ∧
    (∀ address, (∀ d c, d < count → c < 3 → address ≠ word (openTarget d c)) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ solveClobbers register → memory.registers register = start.registers register

/-- **The 273 collector masks**: `openTarget d c` holds `maskFormula … d c`; nothing else in RAM changes. -/
theorem exec_solve (memory : Memory) (x y : BaseField) (gammas : Nat → NormRow)
    (targets : Nat → FieldMacToECMac.HomogeneousValue) (dx px dy py : Nat → BaseField)
    (cells : ∀ d, d < 91 → DigitCells memory x y (gammas d) (targets d) dx px dy py d) :
    ∃ after, solve.exec memory = some after ∧ SolveInv memory x y gammas targets dx px dy py 91 after := by
  refine Prog.exec_rep solveDigit (SolveInv memory x y gammas targets dx px dy py) 91
    (fun index bound current inv => ?_) memory
    ⟨fun _ _ small => absurd small (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨written, frame, bits, regs⟩ := inv
  have outside : ∀ address, OutsideTargets address → address < 2 ^ 256 →
      current.ram (word address) = memory.ram (word address) := fun address range fits =>
    frame _ fun d c small cSmall => cellNe fits (by unfold openTarget openBase; omega)
      (by unfold OutsideTargets openTarget at *; omega)
  obtain ⟨after, run, ram, bitsAfter, regsAfter⟩ := exec_solveDigit index bound current x y (gammas index)
    (targets index) dx px dy py ((cells index bound).transfer bound outside)
  refine ⟨after, run, fun d c small => ?_, fun address away => ?_, bitsAfter.trans bits,
    fun register out => (regsAfter register out).trans (regs register out)⟩
  · rw [ram]
    by_cases last : d = index
    · subst last
      fin_cases c
      · rw [Function.update_of_ne (openTarget_ne bound (by omega) bound (by omega) (Or.inr (by decide))),
          Function.update_of_ne (openTarget_ne bound (by omega) bound (by omega) (Or.inr (by decide))),
          Function.update_self]
        rfl
      · rw [Function.update_of_ne (openTarget_ne bound (by omega) bound (by omega) (Or.inr (by decide))),
          Function.update_self]
        rfl
      · rw [Function.update_self]
        rfl
    · have earlier : d < index := by omega
      rw [Function.update_of_ne (openTarget_ne (by omega) c.isLt bound (by omega) (Or.inl last)),
        Function.update_of_ne (openTarget_ne (by omega) c.isLt bound (by omega) (Or.inl last)),
        Function.update_of_ne (openTarget_ne (by omega) c.isLt bound (by omega) (Or.inl last))]
      exact written d c earlier
  · rw [ram, Function.update_of_ne (away index 2 (by omega) (by omega)),
      Function.update_of_ne (away index 1 (by omega) (by omega)),
      Function.update_of_ne (away index 0 (by omega) (by omega))]
    exact frame address fun d c small cSmall => away d c (by omega) cSmall

end Solve

end

end Kriterion.CRT.SimMachine
