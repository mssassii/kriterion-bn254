/-
**The replay of one fused extraction stage agrees with the evaluator's `extStageEvalM`** (package
M4a; `Construction/Simulator/CRT/ReplayExtract.lean`).

Part 1 (this section): the straight-line pieces of an expansion and the agreement of one subtree
with `subtreeM`.
-/

import Proof.Simulator.CRT.ReplayCast
import Construction.Simulator.CRT.ReplayExtract
import Construction.CRT.Extract
import Proof.Correctness.CRT.TreeSteps

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### Straight-line pieces -/

theorem exec_absSlot (cells : StageCells) (start t : Nat) (memory : Memory) (slot : Nat)
    (slotCell : memory.ram (word cells.slot) = word slot)
    (small : slot + 2 ^ start * t < 2 ^ 256) :
    ∃ after, (absSlot cells start t).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rF = word (slot + 2 ^ start * t) ∧
      ∀ register, register ≠ rF → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notF notB notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, slotCell]
    rw [eval_add_word _ _ small]
  · simp only [reg_setReg, if_neg notF, if_neg notB, if_neg notAddr]

theorem det_absSlot (cells : StageCells) (start t : Nat) : (absSlot cells start t).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, trivial⟩

theorem exec_nodeInput (cells : StageCells) (base stride : Nat) (memory : Memory) (x : Nat)
    (label : Block) (xReg : memory.registers rF = word x)
    (nodeCell : memory.ram (word (cells.nodeBase + x)) = blockWord label)
    (addrSmall : cells.nodeBase + x < 2 ^ 256) (strideSmall : stride < 2 ^ 64)
    (tagSmall : base + stride * x < 2 ^ 127) :
    ∃ after, (nodeInput cells base stride).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      after.registers rInput = word (hashInput label (base + stride * x)) ∧
      ∀ register, register ≠ rInput → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have xSmall : x < 2 ^ 256 := by omega
  have prodSmall : x * (2 ^ 128 * stride) < 2 ^ 256 := by
    have : stride * x < 2 ^ 127 := by omega
    calc x * (2 ^ 128 * stride) = 2 ^ 128 * (stride * x) := by ring
      _ < 2 ^ 128 * 2 ^ 127 := Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ < 2 ^ 256 := by norm_num
  have labelSmall := label.isLt
  have sum1 : label.toNat + x * (2 ^ 128 * stride) < 2 ^ 256 := by
    have : stride * x < 2 ^ 127 := by omega
    have : x * (2 ^ 128 * stride) = 2 ^ 128 * (stride * x) := by ring
    omega
  have sum2 : label.toNat + x * (2 ^ 128 * stride) + 2 ^ 128 * base < 2 ^ 256 := by
    have : x * (2 ^ 128 * stride) + 2 ^ 128 * base = 2 ^ 128 * (base + stride * x) := by ring
    omega
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notI notB notC notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, xReg]
    rw [eval_add_word x cells.nodeBase (by omega), Nat.add_comm x cells.nodeBase, nodeCell,
      blockWord_eq_word, eval_mul_word x (2 ^ 128 * stride) prodSmall, eval_add_word _ _ sum1,
      eval_add_word _ _ sum2]
    congr 1
    unfold hashInput
    ring
  · simp only [reg_setReg, if_neg notI, if_neg notB, if_neg notC, if_neg notAddr]

theorem det_nodeInput (cells : StageCells) (base stride : Nat) :
    (nodeInput cells base stride).OpsSatisfy Op.Det :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem exec_matStore (cells : StageCells) (level t : Nat) (memory : Memory)
    (apart : word (cells.matBase + t) ≠ word (cells.levelSumBase + level)) :
    ∃ after, (matStore cells level t).exec memory = some after ∧
      after.ram = Function.update (Function.update memory.ram (word (cells.matBase + t))
        (memory.registers rFirst)) (word (cells.levelSumBase + level))
          (memory.ram (word (cells.levelSumBase + level)) ^^^ memory.registers rFirst) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register notE notAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reg_storeRam,
      reduceIte]
    rw [Function.update_of_ne (Ne.symm apart), eval_xor]
  · simp only [reg_setReg, reg_storeRam, if_neg notE, if_neg notAddr]

theorem det_matStore (cells : StageCells) (level t : Nat) : (matStore cells level t).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩

/-- The tail of `extendEntry` after the absolute slot. -/
def extendRest (cells : StageCells) (level t : Nat) : Prog :=
  .seq (cst rB cells.nodeBase)
    (.seq (ar .add rF rF rB)
    (.seq (loadAt rC (cells.matBase + t))
    (.seq (.op (.load rE rF))
    (.seq (ar .xor rE rE rC)
    (.seq (.op (.store rF rE))
    (.seq (cst rB (2 ^ level))
    (.seq (ar .add rF rF rB) (.op (.store rF rC)))))))))

theorem extendEntry_eq (cells : StageCells) (start level t : Nat) :
    extendEntry cells start level t = .seq (absSlot cells start t) (extendRest cells level t) := rfl

theorem exec_extendRest (cells : StageCells) (level t : Nat) (memory : Memory) (x : Nat)
    (xReg : memory.registers rF = word x) (small : cells.nodeBase + x + 2 ^ level < 2 ^ 256)
    (apart : word (cells.nodeBase + x) ≠ word (cells.nodeBase + x + 2 ^ level)) :
    ∃ after, (extendRest cells level t).exec memory = some after ∧
      after.ram = Function.update (Function.update memory.ram (word (cells.nodeBase + x))
        (memory.ram (word (cells.nodeBase + x)) ^^^ memory.ram (word (cells.matBase + t))))
          (word (cells.nodeBase + x + 2 ^ level)) (memory.ram (word (cells.matBase + t))) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rF → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have hp := Nat.two_pow_pos level
  have s1 : x + cells.nodeBase < 2 ^ 256 := by omega
  have s2 : x + cells.nodeBase + 2 ^ level < 2 ^ 256 := by omega
  refine ⟨_, rfl, ?_, rfl, fun register notB notC notE notF notAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reg_storeRam,
      reduceIte, xReg]
    rw [eval_add_word _ _ s1, eval_add_word _ _ s2, eval_xor, Nat.add_comm x cells.nodeBase]
  · simp only [reg_setReg, reg_storeRam, if_neg notB, if_neg notC, if_neg notE, if_neg notF,
      if_neg notAddr]

theorem det_extendEntry (cells : StageCells) (start level t : Nat) :
    (extendEntry cells start level t).OpsSatisfy Op.Det :=
  ⟨det_absSlot cells start t, trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial, trivial,
    trivial, trivial, trivial⟩

/-! ### Absolute slots -/

theorem slotPos_lt (slot start d t : Nat) (slotLt : slot < 2 ^ start) (tLt : t < 2 ^ d) :
    slot + 2 ^ start * t < 2 ^ (start + d) := by
  have : 2 ^ start * t + 2 ^ start ≤ 2 ^ start * 2 ^ d := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ tLt
  rw [pow_add]
  omega

theorem slotPos_inj (slot start t t' : Nat) (same : slot + 2 ^ start * t = slot + 2 ^ start * t') :
    t = t' :=
  Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos start) (by omega)

theorem slotPos_high (slot start d t : Nat) :
    slot + 2 ^ start * t + 2 ^ (start + d) = slot + 2 ^ start * (t + 2 ^ d) := by
  rw [pow_add]; ring

/-! ### The layout of a stage -/

/-- **The layout of a stage**: the input cells (read only, in any order, possibly shared with
other data) lie below the scratch and output chain, and the chain is ascending and in range. Every
disjointness fact is one `omega` on these inequalities. -/
structure StageLayout (cells : StageCells) (w rb : Nat) : Prop where
  c1 : cells.value < cells.subBase
  c2 : cells.remBase + 128 ≤ cells.subBase
  c3 : cells.joinBase + w ≤ cells.subBase
  c4 : cells.pinBase + 128 ≤ cells.subBase
  c5 : cells.subBase + 128 ≤ cells.nodeBase
  c6 : cells.nodeBase + 2 ^ w ≤ cells.matBase
  c7 : cells.matBase + 2 ^ w ≤ cells.levelSumBase
  c8 : cells.levelSumBase + w ≤ cells.classBase
  c9 : cells.classBase + 128 * (w + 1) ≤ cells.castSumBase
  c10 : cells.castSumBase + 128 * (w + 1) ≤ cells.ansBase
  c11 : cells.ansBase + 2 * castAnswers rb ≤ cells.laneBase
  c12 : cells.laneBase + 128 ≤ cells.active
  c13 : cells.active < cells.slot
  c14 : cells.slot < cells.bitBase
  c15 : cells.bitBase + w ≤ cells.nextBase
  c16 : cells.nextBase + 128 < 2 ^ 256

/-- The registers a stage may change are none of these. -/
theorem ne_of_not_stage {register : Register} (outside : ¬ stageClobbers register)
    (other : Register) (inside : other ∈ [rA, rB, rC, rD, rE, rF, rAddr, rInput, rFirst, rSecond]) :
    register ≠ other := fun same => outside (by rw [same]; exact inside)

/-! ### The XOR of a vector -/

/-- The XOR of the entries of a vector. -/
def xorOf {count : Nat} (values : Vector Block count) : Block := xorFold values.get

theorem xorOf_push {count : Nat} (values : Vector Block count) (value : Block) :
    xorOf (values.push value) = xorOf values ^^^ value := by
  unfold xorOf xorFold
  rw [Fin.foldl_succ_last]
  simp only [Vector.get_eq_getElem, Fin.val_last, Fin.val_castSucc, Vector.getElem_push_eq]
  congr 1
  congr 1
  funext acc i
  rw [Vector.getElem_push_lt i.isLt]

theorem xorOf_zero (values : Vector Block 0) : xorOf values = 0 := rfl

theorem word_xor_zero' (a : Word) : a ^^^ (0 : Word) = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp

theorem xor_blockWord_zero (a : Word) : a ^^^ blockWord 0 = a := by
  rw [blockWord_zero, word_xor_zero']

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The invariant of the hash loop of one level after `count` relative slots. -/
def HashInv (cells : StageCells) (w level : Nat) (start : Memory) (count : Nat)
    (values : Vector Block count) (memory : Memory) : Prop :=
  (∀ t (bound : t < count), memory.ram (word (cells.matBase + t)) = blockWord (values[t]'bound)) ∧
    memory.ram (word (cells.levelSumBase + level)) =
      start.ram (word (cells.levelSumBase + level)) ^^^ blockWord (xorOf values) ∧
    (∀ address, address ≠ word (cells.levelSumBase + level) →
      (∀ t, t < 2 ^ w → address ≠ word (cells.matBase + t)) → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ stageClobbers register → memory.registers register = start.registers register

/-- **One hashed node of a subtree level.** -/
theorem agree_hashEntry (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (start d base stride : Nat) (strideSmall : stride < 2 ^ 64) (slot : Nat) (slotLt : slot < 2 ^ start)
    (levelLt : start + d < w) (parent : Fin (2 ^ d) → Block) (m0 : Memory)
    (slotCell : m0.ram (word cells.slot) = word slot)
    (nodeCells : ∀ t : Fin (2 ^ d),
      m0.ram (word (cells.nodeBase + (slot + 2 ^ start * t.val))) = blockWord (parent t))
    (tagSmall : ∀ t, t < 2 ^ d → base + stride * (slot + 2 ^ start * t) < 2 ^ 127)
    (index : Fin (2 ^ d)) (values : Vector Block index.val) (memory : Memory)
    (holds : HashInv cells w (start + d) m0 index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : Block) after =>
        HashInv cells w (start + d) m0 (index.val + 1) (values.push result) after)
      ((hashEntry cells start (start + d) base stride index.val).tree memory)
      (liftHash (h128M (parent index) (base + stride * (slot + 2 ^ start * index.val)))) := by
  obtain ⟨mats, sumCell, frame, bitsSame, regs⟩ := holds
  have c5 := layout.c5; have c6 := layout.c6; have c7 := layout.c7; have c8 := layout.c8
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c9 := layout.c9; have c10 := layout.c10; have c11 := layout.c11; have c12 := layout.c12
  have powd : 2 ^ start * 2 ^ d = 2 ^ (start + d) := by rw [pow_add]
  have powLe : 2 ^ (start + d) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have tLt := index.isLt
  have xLt : slot + 2 ^ start * index.val < 2 ^ (start + d) := by
    have : 2 ^ start * index.val + 2 ^ start ≤ 2 ^ start * 2 ^ d := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ tLt
    omega
  have tLtw : index.val < 2 ^ w := by
    have : 2 ^ d ≤ 2 ^ (start + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have slotNow : memory.ram (word cells.slot) = word slot := by
    rw [frame _ (word_ne (by omega) (by omega) (by omega))
      (fun t tb => word_ne (by omega) (by omega) (by omega))]
    exact slotCell
  have nodeNow : memory.ram (word (cells.nodeBase + (slot + 2 ^ start * index.val))) =
      blockWord (parent index) := by
    rw [frame _ (word_ne (by omega) (by omega) (by omega))
      (fun t tb => word_ne (by omega) (by omega) (by omega))]
    exact nodeCells index
  obtain ⟨m1, run1, ram1, bits1, rF1, regs1⟩ :=
    exec_absSlot cells start index.val memory slot slotNow (by omega)
  obtain ⟨m2, run2, ram2, bits2, input2, regs2⟩ :=
    exec_nodeInput cells base stride m1 _ (parent index) rF1 (by rw [ram1]; exact nodeNow)
      (by omega) strideSmall (tagSmall _ tLt)
  have hashSmall : hashInput (parent index) (base + stride * (slot + 2 ^ start * index.val)) <
      2 ^ 256 := by
    unfold hashInput
    have := (parent index).isLt
    have := tagSmall _ tLt
    omega
  unfold hashEntry
  rw [tree_seq_exec _ _ (det_absSlot cells start index.val) memory m1 run1,
    tree_seq_exec _ _ (det_nodeInput cells base stride) m1 m2 run2,
    tree_query_hash _ m2 _ hashSmall input2, liftHash_h128M]
  refine .node _ fun answer => ?_
  rw [tree_eq_exec _ (det_matStore cells (start + d) index.val)]
  set m3 := writePair m2 rFirst rSecond (blockWord answer.1, blockWord answer.2) with m3Def
  have first3 : m3.registers rFirst = blockWord answer.1 := by
    rw [m3Def, writePair_reg, if_neg (by decide), if_pos rfl]
  obtain ⟨m4, run4, ram4, bits4, regs4⟩ := exec_matStore cells (start + d) index.val m3
    (word_ne (by omega) (by omega) (by omega))
  rw [run4]
  have matSmall : cells.matBase + index.val < 2 ^ 256 := by omega
  refine .leaf ⟨fun t bound => ?_, ?_, fun address offSum offMat => ?_, ?_, fun register outside => ?_⟩
  · rw [ram4, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), first3]
    by_cases last : t = index.val
    · subst last
      rw [Function.update_self, Vector.getElem_push_eq]
    · have tSmall : t < index.val := by omega
      rw [Function.update_of_ne (word_ne (by omega) matSmall (by omega)), m3Def, writePair_ram, ram2,
        ram1, Vector.getElem_push_lt tSmall]
      exact mats t tSmall
  · rw [ram4, Function.update_self, first3, m3Def, writePair_ram, ram2, ram1, sumCell,
      xorOf_push, BitVec.xor_assoc, blockWord_xor]
  · rw [ram4, Function.update_of_ne offSum, Function.update_of_ne (offMat index.val tLtw), m3Def,
      writePair_ram, ram2, ram1]
    exact frame address offSum offMat
  · rw [bits4, m3Def, writePair_bits, bits2, bits1]
    exact bitsSame
  · rw [regs4 register (ne_of_not_stage outside rE (by simp)) (ne_of_not_stage outside rAddr (by simp)),
      m3Def, writePair_reg, if_neg (ne_of_not_stage outside rSecond (by simp)),
      if_neg (ne_of_not_stage outside rFirst (by simp)),
      regs2 register (ne_of_not_stage outside rInput (by simp)) (ne_of_not_stage outside rB (by simp))
        (ne_of_not_stage outside rC (by simp)) (ne_of_not_stage outside rAddr (by simp)),
      regs1 register (ne_of_not_stage outside rF (by simp)) (ne_of_not_stage outside rB (by simp))
        (ne_of_not_stage outside rAddr (by simp))]
    exact regs register outside

/-- **The extension of one level, in place**: after `count` relative slots, node `x_t` holds
`node x_t ⊕ mat t` and node `x_t + 2 ^ level` holds `mat t`. -/
theorem exec_extendLoop (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (start d slot : Nat) (slotLt : slot < 2 ^ start) (levelLt : start + d < w) (m0 : Memory)
    (slotCell : m0.ram (word cells.slot) = word slot) :
    ∀ count, count ≤ 2 ^ d → ∃ after,
      (Prog.rep count (extendEntry cells start (start + d))).exec m0 = some after ∧
      (∀ t, t < count →
        after.ram (word (cells.nodeBase + (slot + 2 ^ start * t))) =
            m0.ram (word (cells.nodeBase + (slot + 2 ^ start * t))) ^^^
              m0.ram (word (cells.matBase + t)) ∧
          after.ram (word (cells.nodeBase + (slot + 2 ^ start * t) + 2 ^ (start + d))) =
            m0.ram (word (cells.matBase + t))) ∧
      (∀ address, (∀ t, t < count → address ≠ word (cells.nodeBase + (slot + 2 ^ start * t)) ∧
          address ≠ word (cells.nodeBase + (slot + 2 ^ start * t) + 2 ^ (start + d))) →
        after.ram address = m0.ram address) ∧
      after.bits = m0.bits ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rF → register ≠ rAddr →
        after.registers register = m0.registers register
  | 0, _ => ⟨m0, Prog.exec_rep_zero _ _, fun t bound => absurd bound (by omega), fun _ _ => rfl, rfl,
      fun _ _ _ _ _ _ => rfl⟩
  | count + 1, bound => by
      obtain ⟨middle, run, cells', frame, bitsSame, regs⟩ :=
        exec_extendLoop cells w rb layout start d slot slotLt levelLt m0 slotCell count (by omega)
      have c5 := layout.c5; have c6 := layout.c6; have c7 := layout.c7; have c8 := layout.c8
      have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
      have c9 := layout.c9; have c10 := layout.c10; have c11 := layout.c11; have c12 := layout.c12
      have hL := Nat.two_pow_pos (start + d)
      have powLe : 2 ^ (start + d + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
      have twice : 2 ^ (start + d + 1) = 2 ^ (start + d) + 2 ^ (start + d) := by rw [pow_succ]; omega
      have dLe : 2 ^ d ≤ 2 ^ (start + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have posLt : ∀ t, t < 2 ^ d → slot + 2 ^ start * t < 2 ^ (start + d) :=
        fun t tb => slotPos_lt slot start d t slotLt tb
      have xc := posLt count (by omega)
      have wne : ∀ a b : Nat, a < 2 ^ 256 → b < 2 ^ 256 → a ≠ b → word a ≠ word b :=
        fun a b ha hb hne => word_ne ha hb hne
      have nb : ∀ t, t < 2 ^ d →
          cells.nodeBase + (slot + 2 ^ start * t) + 2 ^ (start + d) < cells.matBase := by
        intro t tb; have := posLt t tb; omega
      have nodeNow : middle.ram (word (cells.nodeBase + (slot + 2 ^ start * count))) =
          m0.ram (word (cells.nodeBase + (slot + 2 ^ start * count))) := by
        refine frame _ fun t tb => ⟨?_, ?_⟩
        · have := nb t (by omega)
          refine wne _ _ (by omega) (by omega) fun same => ?_
          have := slotPos_inj slot start count t (by omega)
          omega
        · have := nb t (by omega)
          have := posLt t (by omega)
          exact wne _ _ (by omega) (by omega) (by omega)
      have matNow : middle.ram (word (cells.matBase + count)) = m0.ram (word (cells.matBase + count)) := by
        refine frame _ fun t tb => ⟨?_, ?_⟩
        · have := nb t (by omega); exact wne _ _ (by omega) (by omega) (by omega)
        · have := nb t (by omega); exact wne _ _ (by omega) (by omega) (by omega)
      have slotNow : middle.ram (word cells.slot) = word slot := by
        rw [frame _ fun t tb => ⟨by have := nb t (by omega); exact wne _ _ (by omega) (by omega) (by omega),
          by have := nb t (by omega); exact wne _ _ (by omega) (by omega) (by omega)⟩]
        exact slotCell
      obtain ⟨m1, run1, ram1, bits1, rF1, regs1⟩ :=
        exec_absSlot cells start count middle slot slotNow (by omega)
      obtain ⟨m2, run2, ram2, bits2, regs2⟩ := exec_extendRest cells (start + d) count m1 _ rF1
        (by omega) (wne _ _ (by omega) (by omega) (by omega))
      refine ⟨m2, ?_, fun t tb => ?_, fun address off => ?_, ?_, fun register nB nC nE nF nAddr => ?_⟩
      · rw [Prog.exec_rep_succ, run, Option.bind_some, extendEntry_eq,
          Prog.exec_seq_some _ _ _ _ run1, run2]
      · rw [ram2, ram1]
        have nbc := nb count (by omega)
        by_cases last : t = count
        · subst last
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)), Function.update_self,
              nodeNow, matNow]
          · rw [Function.update_self, matNow]
        · have tSmall : t < count := by omega
          have nbt := nb t (by omega)
          have ne1 : cells.nodeBase + (slot + 2 ^ start * t) ≠ cells.nodeBase + (slot + 2 ^ start * count) := by
            intro same; have := slotPos_inj slot start t count (by omega); omega
          have ne2 : cells.nodeBase + (slot + 2 ^ start * t) + 2 ^ (start + d) ≠
              cells.nodeBase + (slot + 2 ^ start * count) + 2 ^ (start + d) := by
            intro same; have := slotPos_inj slot start t count (by omega); omega
          have xt := posLt t (by omega)
          obtain ⟨cell1, cell2⟩ := cells' t tSmall
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)),
              Function.update_of_ne (wne _ _ (by omega) (by omega) ne1), cell1]
          · rw [Function.update_of_ne (wne _ _ (by omega) (by omega) ne2),
              Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)), cell2]
      · rw [ram2, ram1, Function.update_of_ne (off count (by omega)).2,
          Function.update_of_ne (off count (by omega)).1, frame address fun t tb => off t (by omega)]
      · rw [bits2, bits1, bitsSame]
      · rw [regs2 register nB nC nE nF nAddr, regs1 register nF nB nAddr, regs register nB nC nE nF nAddr]

/-- What the machine holds after `d` levels of the subtree below `(start, slot)`, against the
program's `subtreeM` result `r`: the level-`start + d` labels at their absolute slots, the level
XORs added into `Y_L`, and the frame (only nodes of the subtree's class, the materials and the level
XORs written). `m0` is the memory at the subtree's start. -/
def SubtreePost (cells : StageCells) (w start slot : Nat) (m0 : Memory) (d : Nat)
    (r : (Fin (2 ^ d) → Block) × (Nat → Block)) (m : Memory) : Prop :=
  (∀ t : Fin (2 ^ d), m.ram (word (cells.nodeBase + (slot + 2 ^ start * t.val))) = blockWord (r.1 t)) ∧
    (∀ L, L < w → m.ram (word (cells.levelSumBase + L)) =
      m0.ram (word (cells.levelSumBase + L)) ^^^ blockWord (r.2 L)) ∧
    (∀ L, start + d ≤ L → r.2 L = 0) ∧
    (∀ address, (∀ x, x < 2 ^ w → x % 2 ^ start = slot → address ≠ word (cells.nodeBase + x)) →
      (∀ t, t < 2 ^ w → address ≠ word (cells.matBase + t)) →
      (∀ L, L < w → address ≠ word (cells.levelSumBase + L)) → m.ram address = m0.ram address) ∧
    m.bits = m0.bits ∧
    ∀ register, ¬ stageClobbers register → m.registers register = m0.registers register

theorem slotPos_mod (slot start t : Nat) (slotLt : slot < 2 ^ start) :
    (slot + 2 ^ start * t) % 2 ^ start = slot := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt slotLt]

/-- **One level of a subtree** against `garbleStepM` and the level bookkeeping of `subtreeM`. -/
theorem agree_subtreeLevel (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (start d base stride : Nat) (strideSmall : stride < 2 ^ 64) (slot : Nat)
    (slotLt : slot < 2 ^ start) (levelLt : start + d < w) (treeTag : Nat → Nat → Nat)
    (hTag : ∀ x, treeTag (start + d) x = base + stride * x)
    (tagSmall : ∀ t, t < 2 ^ d → base + stride * (slot + 2 ^ start * t) < 2 ^ 127)
    (m0 : Memory) (slotCell : m0.ram (word cells.slot) = word slot)
    (prev : (Fin (2 ^ d) → Block) × (Nat → Block)) (m : Memory)
    (post : SubtreePost cells w start slot m0 d prev m) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (SubtreePost cells w start slot m0 (d + 1))
      ((subtreeLevel cells start d base stride).tree m)
      (liftHash (garbleStepM d (fun t => treeTag (start + d) (slot + 2 ^ start * t)) prev.1 >>=
        fun step => pure (step.1, fun level => if level = start + d then step.2 else prev.2 level))) := by
  obtain ⟨nodes, sums, zero, frame, bitsSame, regs⟩ := post
  have c5 := layout.c5; have c6 := layout.c6; have c7 := layout.c7; have c8 := layout.c8
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c9 := layout.c9; have c10 := layout.c10; have c11 := layout.c11; have c12 := layout.c12
  have hL := Nat.two_pow_pos (start + d)
  have powLe : 2 ^ (start + d + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have twice : 2 ^ (start + d + 1) = 2 ^ (start + d) + 2 ^ (start + d) := by rw [pow_succ]; omega
  have dLe : 2 ^ d ≤ 2 ^ (start + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have posLt : ∀ t, t < 2 ^ d → slot + 2 ^ start * t < 2 ^ (start + d) :=
    fun t tb => slotPos_lt slot start d t slotLt tb
  have slotNow : m.ram (word cells.slot) = word slot := by
    rw [frame _ (fun x xb _ => word_ne (by omega) (by omega) (by omega))
      (fun t tb => word_ne (by omega) (by omega) (by omega))
      (fun L Lb => word_ne (by omega) (by omega) (by omega))]
    exact slotCell
  have tagsEq : (fun t => treeTag (start + d) (slot + 2 ^ start * t)) =
      fun t => base + stride * (slot + 2 ^ start * t) := funext fun t => hTag _
  rw [tagsEq]
  unfold subtreeLevel garbleStepM tableM
  rw [tree_seq]
  simp only [TreeLaws.monad_bind, liftHash_bind, liftHash_vector, TreeLaws.bind_assoc]
  refine Agree.bindOpt (fun materials after inv => ?_)
    (agree_rep_vector_plain (hashEntry cells start (start + d) base stride)
      (HashInv cells w (start + d) m) (2 ^ d) _
      (fun index values current holds =>
        agree_hashEntry cells w rb layout start d base stride strideSmall slot slotLt levelLt prev.1 m
          slotNow nodes tagSmall index values current holds)
      m ⟨fun t bound => absurd bound (Nat.not_lt_zero _), by rw [xorOf_zero, xor_blockWord_zero],
        fun _ _ _ => rfl, rfl, fun _ _ => rfl⟩)
  obtain ⟨mats, sumCell, frameH, bitsH, regsH⟩ := inv
  have slotAfter : after.ram (word cells.slot) = word slot := by
    rw [frameH _ (word_ne (by omega) (by omega) (by omega))
      (fun t tb => word_ne (by omega) (by omega) (by omega))]
    exact slotNow
  rw [tree_eq_exec _ (det_rep _ _ fun t _ => det_extendEntry cells start (start + d) t)]
  obtain ⟨m2, run2, cells2, frame2, bits2, regs2⟩ :=
    exec_extendLoop cells w rb layout start d slot slotLt levelLt after slotAfter (2 ^ d) le_rfl
  rw [run2]
  have nodeClass : ∀ t, t < 2 ^ d →
      (slot + 2 ^ start * t) % 2 ^ start = slot ∧ (slot + 2 ^ start * t + 2 ^ (start + d)) % 2 ^ start = slot := by
    intro t tb
    refine ⟨slotPos_mod slot start t slotLt, ?_⟩
    rw [slotPos_high]; exact slotPos_mod slot start _ slotLt
  refine .leaf ⟨fun t' => ?_, fun L Lw => ?_, fun L hL => ?_, fun address offNode offMat offSum => ?_,
    ?_, fun register outside => ?_⟩
  · have rLt := Nat.mod_lt t'.val (Nat.two_pow_pos d)
    have hsplit := Kriterion.CRT.SliceC.val_split t'
    obtain ⟨c1, c2⟩ := cells2 (t'.val % 2 ^ d) rLt
    have xr := posLt _ rLt
    have nodePrev : after.ram (word (cells.nodeBase + (slot + 2 ^ start * (t'.val % 2 ^ d)))) =
        blockWord (prev.1 ⟨t'.val % 2 ^ d, rLt⟩) := by
      rw [frameH _ (word_ne (by omega) (by omega) (by omega))
        (fun t tb => word_ne (by omega) (by omega) (by omega))]
      exact nodes ⟨_, rLt⟩
    have matR : after.ram (word (cells.matBase + t'.val % 2 ^ d)) =
        blockWord (materials.get ⟨t'.val % 2 ^ d, rLt⟩) := by
      rw [mats _ rLt]; rfl
    simp only [stored_eq]
    rw [Kriterion.CRT.SliceC.extendLevel_eq]
    by_cases hb : t'.val.testBit d
    · rw [if_pos hb]
      rw [if_pos hb] at hsplit
      have hpos : slot + 2 ^ start * t'.val = slot + 2 ^ start * (t'.val % 2 ^ d) + 2 ^ (start + d) := by
        rw [slotPos_high, ← hsplit]
      rw [hpos, ← Nat.add_assoc cells.nodeBase (slot + 2 ^ start * (t'.val % 2 ^ d)) (2 ^ (start + d)),
        c2, matR]
    · rw [if_neg hb]
      simp only [hb, Bool.false_eq_true, if_false] at hsplit
      have hpos : slot + 2 ^ start * t'.val = slot + 2 ^ start * (t'.val % 2 ^ d) := by
        congr 2
      rw [hpos, c1, nodePrev, matR, blockWord_xor]
  · have xAll : ∀ t, t < 2 ^ d → cells.nodeBase + (slot + 2 ^ start * t) + 2 ^ (start + d) < cells.matBase :=
      fun t tb => by have := posLt t tb; omega
    rw [frame2 _ fun t tb => ⟨word_ne (by omega) (by have := xAll t tb; omega)
      (by have := xAll t tb; omega), word_ne (by omega) (by have := xAll t tb; omega)
      (by have := xAll t tb; omega)⟩]
    dsimp only
    by_cases hLd : L = start + d
    · subst hLd
      rw [sumCell, if_pos rfl, sums _ Lw, zero _ le_rfl, xor_blockWord_zero]
      rfl
    · rw [if_neg hLd, frameH _ (word_ne (by omega) (by omega) (by omega))
        (fun t tb => word_ne (by omega) (by omega) (by omega)), sums L Lw]
  · simp only
    rw [if_neg (by omega)]
    exact zero L (by omega)
  · rw [frame2 address fun t tb => ⟨offNode _ (by have := posLt t tb; omega) (nodeClass t tb).1,
        by rw [Nat.add_assoc]; exact offNode _ (by have := posLt t tb; omega) (nodeClass t tb).2⟩,
      frameH address (offSum _ (by omega)) offMat]
    exact frame address offNode offMat offSum
  · rw [bits2, bitsH, bitsSame]
  · rw [regs2 register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rC (by simp))
      (ne_of_not_stage outside rE (by simp)) (ne_of_not_stage outside rF (by simp))
      (ne_of_not_stage outside rAddr (by simp)), regsH register outside, regs register outside]

/-- **A whole subtree** against `subtreeM`: `depth` levels from the closed node at `(start, slot)`
whose label is at `node[slot]`, with affine tags `treeBase L + stride · x`. -/
theorem agree_subtreeReplay (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (start stride : Nat) (strideSmall : stride < 2 ^ 64) (treeBase : Nat → Nat) (slot : Nat)
    (slotLt : slot < 2 ^ start) (treeTag : Nat → Nat → Nat)
    (hTag : ∀ L x, L < w → treeTag L x = treeBase L + stride * x)
    (tagSmall : ∀ L x, L < w → x < 2 ^ w → treeBase L + stride * x < 2 ^ 127)
    (m0 : Memory) (slotCell : m0.ram (word cells.slot) = word slot) (label : Block)
    (nodeCell : m0.ram (word (cells.nodeBase + slot)) = blockWord label) :
    ∀ depth, start + depth ≤ w →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
        (SubtreePost cells w start slot m0 depth)
        ((subtreeReplay cells start depth treeBase stride).tree m0)
        (liftHash (subtreeM treeTag start slot label depth))
  | 0, _ => by
      unfold subtreeReplay
      rw [Prog.rep, subtreeM]
      refine .leaf ⟨fun t => ?_, fun L _ => (xor_blockWord_zero _).symm, fun _ _ => rfl,
        fun _ _ _ _ => rfl, rfl, fun _ _ => rfl⟩
      have t0 : t.val = 0 := Nat.lt_one_iff.mp (lt_of_lt_of_eq t.isLt (pow_zero 2))
      rw [t0, Nat.mul_zero, Nat.add_zero]
      exact nodeCell
  | d + 1, le => by
      have powLe : 2 ^ (start + d) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold subtreeReplay
      rw [Prog.rep, tree_seq, subtreeM, TreeLaws.monad_bind, liftHash_bind]
      refine Agree.bindOpt (fun prev m post => ?_)
        (agree_subtreeReplay cells w rb layout start stride strideSmall treeBase slot slotLt treeTag
          hTag tagSmall m0 slotCell label nodeCell d (by omega))
      exact agree_subtreeLevel cells w rb layout start d (treeBase (start + d)) stride strideSmall slot
        slotLt (by omega) treeTag (fun x => hTag _ x (by omega))
        (fun t tb => tagSmall _ _ (by omega) (by have := slotPos_lt slot start d t slotLt tb; omega))
        m0 slotCell prev m post

end Agreement

end Kriterion.CRT.SimMachine
