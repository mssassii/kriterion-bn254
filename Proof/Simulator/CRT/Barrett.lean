/-
**Barrett reduction by a small constant modulus**.

`barrett src dst m width` computes `x mod m` for `x < 2 ^ width` with `R = ⌊2 ^ width / m⌋`:
`q = ⌊x · R / 2 ^ width⌋` is `⌊x / m⌋` or one less (`barrett_quot_le`, `barrett_quot_ge`), so
`r = x - q · m` lies in `[0, 2m)` and one constant-time subtraction of `m` finishes
(`barrett_result`). With `2 · width ≤ 256` every product fits a word (`exec_barrett`).

Frame: the block writes `dst`, `rD`, `rE`, `rF` and nothing else (RAM and stacks unchanged).
-/

import Proof.Simulator.CRT.Exec

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! ### Straight-line steps of `exec` -/

theorem exec_cst_seq (target : Register) (value : Nat) (rest : Prog) (memory : Memory) :
    (Prog.seq (cst target value) rest).exec memory = rest.exec (setReg memory target (word value)) :=
  rfl

theorem exec_ar_val (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) (first second : Word) (hfirst : memory.registers left = first)
    (hsecond : memory.registers right = second) :
    (Prog.seq (ar operation target left right) rest).exec memory =
      rest.exec (setReg memory target (operation.eval first second)) := by
  show rest.exec (setReg memory target
    (operation.eval (memory.registers left) (memory.registers right))) = _
  rw [hfirst, hsecond]

theorem exec_ar_last (operation : Arithmetic) (target left right : Register) (memory : Memory)
    (first second : Word) (hfirst : memory.registers left = first)
    (hsecond : memory.registers right = second) :
    (ar operation target left right).exec memory =
      some (setReg memory target (operation.eval first second)) := by
  show some (setReg memory target
    (operation.eval (memory.registers left) (memory.registers right))) = _
  rw [hfirst, hsecond]

/-! ### The quotient estimate -/

/-- The estimate is not too large. -/
theorem barrett_quot_le (x m width : Nat) (mPos : 0 < m) :
    x * (2 ^ width / m) / 2 ^ width * m ≤ x := by
  have key : x * (2 ^ width / m) / 2 ^ width * 2 ^ width ≤ x * (2 ^ width / m) :=
    Nat.div_mul_le_self _ _
  have rm : 2 ^ width / m * m ≤ 2 ^ width := Nat.div_mul_le_self _ _
  have scaled : x * (2 ^ width / m) / 2 ^ width * m * 2 ^ width ≤ x * 2 ^ width :=
    calc x * (2 ^ width / m) / 2 ^ width * m * 2 ^ width
        = x * (2 ^ width / m) / 2 ^ width * 2 ^ width * m := by ring
      _ ≤ x * (2 ^ width / m) * m := Nat.mul_le_mul_right _ key
      _ = x * (2 ^ width / m * m) := by ring
      _ ≤ x * 2 ^ width := Nat.mul_le_mul_left _ rm
  exact Nat.le_of_mul_le_mul_right scaled (by positivity)

/-- The estimate is at most one too small. -/
theorem barrett_quot_ge (x m width : Nat) (mPos : 0 < m) (small : x < 2 ^ width) :
    x / m ≤ x * (2 ^ width / m) / 2 ^ width + 1 := by
  set R := 2 ^ width / m with RDef
  set q := x * R / 2 ^ width with qDef
  set Q := x / m with QDef
  have above : 2 ^ width ≤ m * (R + 1) := by
    have := Nat.div_add_mod (2 ^ width) m
    have := Nat.mod_lt (2 ^ width) mPos
    rw [RDef]; nlinarith
  have Qm : Q * m ≤ x := Nat.div_mul_le_self x m
  have next : x * R < 2 ^ width * (q + 1) := Nat.lt_mul_div_succ _ (by positivity)
  have chain : Q * 2 ^ width < (q + 2) * 2 ^ width :=
    calc Q * 2 ^ width ≤ Q * (m * (R + 1)) := Nat.mul_le_mul_left _ above
      _ = Q * m * R + Q * m := by ring
      _ ≤ x * R + Q * m := Nat.add_le_add_right (Nat.mul_le_mul_right _ Qm) _
      _ < 2 ^ width * (q + 1) + 2 ^ width := by omega
      _ = (q + 2) * 2 ^ width := by ring
  have := Nat.lt_of_mul_lt_mul_right chain
  omega

/-- **Barrett's result**: `r = x - q m` corrected once is `x mod m`. -/
theorem barrett_result (x m width : Nat) (mPos : 0 < m) (small : x < 2 ^ width) :
    let q := x * (2 ^ width / m) / 2 ^ width
    let r := x - q * m
    r - (1 - (if r < m then 1 else 0)) * m = x % m ∧ r < 2 * m := by
  intro q r
  have le := barrett_quot_le x m width mPos
  have ge := barrett_quot_ge x m width mPos small
  have split := Nat.div_add_mod x m
  have modLt := Nat.mod_lt x mPos
  have qle : q ≤ x / m := (Nat.le_div_iff_mul_le mPos).mpr le
  rcases Nat.lt_or_ge q (x / m) with lt | ge'
  · have qEq : x / m = q + 1 := by omega
    have rEq : r = x % m + m := by
      show x - q * m = _
      have : x = q * m + m + x % m := by rw [qEq] at split; nlinarith [split]
      omega
    refine ⟨?_, by omega⟩
    rw [if_neg (by omega)]
    omega
  · have qEq : x / m = q := by omega
    have rEq : r = x % m := by
      show x - q * m = _
      have : x = q * m + x % m := by rw [qEq] at split; nlinarith [split]
      omega
    refine ⟨?_, by omega⟩
    rw [if_pos (by omega)]
    omega

/-! ### The block -/

/-- **Barrett reduction on the machine.** -/
theorem exec_barrett (src dst : Register) (m width x : Nat) (memory : Memory)
    (srcE : src ≠ rE) (srcF : src ≠ rF) (dstD : dst ≠ rD) (dstE : dst ≠ rE) (dstF : dst ≠ rF)
    (srcVal : memory.registers src = word x) (small : x < 2 ^ width) (mPos : 0 < m)
    (mSmall : m < 2 ^ 256) (wide : 2 * width ≤ 256) :
    ∃ after, (barrett src dst m width).exec memory = some after ∧
      after.registers dst = word (x % m) ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ dst → register ≠ rD → register ≠ rE → register ≠ rF →
        after.registers register = memory.registers register := by
  obtain ⟨result, rSmall⟩ := barrett_result x m width mPos small
  set R := 2 ^ width / m with RDef
  set q := x * R / 2 ^ width with qDef
  set r := x - q * m with rDef
  have widthPow : 2 ^ width * 2 ^ width ≤ 2 ^ 256 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have widthSmall : 2 ^ width < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have RLe : R ≤ 2 ^ width := Nat.div_le_self _ _
  have xR : x * R < 2 ^ 256 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le small RLe (by positivity)) widthPow
  have qLe : q ≤ x := by
    rw [qDef]
    calc x * R / 2 ^ width ≤ x * 2 ^ width / 2 ^ width :=
          Nat.div_le_div_right (Nat.mul_le_mul_left _ RLe)
      _ = x := Nat.mul_div_cancel _ (by positivity)
  have xSmall : x < 2 ^ 256 := lt_trans small widthSmall
  have qm : q * m ≤ x := barrett_quot_le x m width mPos
  have bit : (if r < m then 1 else 0) ≤ 1 := by split <;> omega
  have corr : (1 - (if r < m then 1 else 0)) * m ≤ r := by
    by_cases lt : r < m
    · rw [if_pos lt]; simp
    · rw [if_neg lt]; omega
  have corrSmall : (1 - (if r < m then 1 else 0)) * m < 2 ^ 256 := by
    by_cases lt : r < m
    · rw [if_pos lt]; simp
    · rw [if_neg lt]; omega
  unfold barrett
  rw [exec_cst_seq,
    exec_ar_val _ _ _ _ _ _ (word x) (word R) (by rw [reg_setReg, if_neg srcE, srcVal])
      (by rw [reg_setReg, if_pos rfl]),
    eval_mul_word _ _ xR, exec_cst_seq,
    exec_ar_val _ _ _ _ _ _ (word (x * R)) (word width)
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte])
      (by rw [reg_setReg, if_pos rfl]),
    eval_shr_word _ _ xR (by omega), exec_cst_seq,
    exec_ar_val _ _ _ _ _ _ (word q) (word m)
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte] <;> rfl)
      (by rw [reg_setReg, if_pos rfl]),
    eval_mul_word _ _ (by omega),
    exec_ar_val _ _ _ _ _ _ (word x) (word (q * m))
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte, srcE, srcF, srcVal,
        if_false])
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte]),
    eval_sub_word _ _ qm xSmall,
    exec_ar_val _ _ _ _ _ _ (word r) (word m)
      (by rw [reg_setReg, if_pos rfl])
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte, Ne.symm dstF, dstF,
        if_false]),
    eval_less_word _ _ (by omega) mSmall, exec_cst_seq,
    exec_ar_val _ _ _ _ _ _ (word 1) (word (if r < m then 1 else 0))
      (by rw [reg_setReg, if_pos rfl])
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte]),
    eval_sub_word _ _ bit (by norm_num),
    exec_ar_val _ _ _ _ _ _ (word (1 - (if r < m then 1 else 0))) (word m)
      (by rw [reg_setReg, if_pos rfl])
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte, Ne.symm dstF, dstF,
        if_false]),
    eval_mul_word _ _ corrSmall,
    exec_ar_last _ _ _ _ _ (word r) (word ((1 - (if r < m then 1 else 0)) * m))
      (by simp (config := { decide := true }) only [reg_setReg, reduceIte, Ne.symm dstE, Ne.symm dstD, dstE, dstD,
        if_false] <;> rfl)
      (by rw [reg_setReg, if_pos rfl]),
    eval_sub_word _ _ corr (by omega), result]
  refine ⟨_, rfl, by rw [reg_setReg, if_pos rfl], rfl, rfl, fun register notDst notD notE notF => ?_⟩
  simp only [reg_setReg, if_neg notDst, if_neg notD, if_neg notE, if_neg notF]

/-- `exec_barrett`'s frame in the schema. -/
theorem frame_barrett (dst : Register) (memory after : Memory) (ram : after.ram = memory.ram)
    (bitsSame : after.bits = memory.bits)
    (regs : ∀ register, register ≠ dst → register ≠ rD → register ≠ rE → register ≠ rF →
      after.registers register = memory.registers register) :
    Frame barrettWrites (barrettClobbers dst) memory after where
  ram address _ := by rw [ram]
  bits := bitsSame
  registers register outside := regs register
    (fun h => outside (by simp [barrettClobbers, Clobbers.ofList, h]))
    (fun h => outside (by simp [barrettClobbers, Clobbers.ofList, h]))
    (fun h => outside (by simp [barrettClobbers, Clobbers.ofList, h]))
    (fun h => outside (by simp [barrettClobbers, Clobbers.ofList, h]))

theorem det_barrett (src dst : Register) (m width : Nat) :
    (barrett src dst m width).OpsSatisfy Op.Det :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial⟩

end Kriterion.CRT.SimMachine
