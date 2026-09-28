/-
**The replay of one cast agrees with the evaluator's `castM`** (`agree_castBlock`).

The answers are asked in order and stored as 128-bit halves; the lanes are then read from the
stored halves by a shift and a mask. The link between the two readings is arithmetic on the
concatenated answers: `packAnswers` is the limb value of the halves (`packAnswers_eq_limbValue`),
and a block-aligned lane of a limb value is read from its own limb (`lane_of_limbValue`).
-/

import Proof.Simulator.CRT.ReplayTree
import Proof.Simulator.CRT.Garner
import Construction.Simulator.CRT.ReplayCast
import Construction.CRT.Chunk

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### The arithmetic of the reading -/

/-- The concatenation of answers as 128-bit halves, little-endian. -/
theorem sum_answers_eq_limbValue (h : Nat → Nat) :
    ∀ count, ∑ j ∈ range count, 2 ^ (256 * j) * (h (2 * j) + 2 ^ 128 * h (2 * j + 1)) =
      limbValue h (2 * count)
  | 0 => by simp [limbValue]
  | count + 1 => by
      rw [sum_range_succ, sum_answers_eq_limbValue h count,
        show 2 * (count + 1) = 2 * count + 1 + 1 by ring, limbValue_succ, limbValue_succ]
      have first : (2 : Nat) ^ (256 * count) = 2 ^ (128 * (2 * count)) := by ring_nf
      have second : (2 : Nat) ^ (256 * count) * 2 ^ 128 = 2 ^ (128 * (2 * count + 1)) := by
        rw [← pow_add]; ring_nf
      calc limbValue h (2 * count) + 2 ^ (256 * count) * (h (2 * count) + 2 ^ 128 * h (2 * count + 1))
          = limbValue h (2 * count) + h (2 * count) * 2 ^ (256 * count) +
              h (2 * count + 1) * (2 ^ (256 * count) * 2 ^ 128) := by ring
        _ = _ := by rw [second, first]

/-- The halves of a vector of answers (`0` off range). -/
def halvesOf {count : Nat} (values : Vector (Block × Block) count) (b : Nat) : Nat :=
  if inRange : b / 2 < count then
    (if b % 2 = 0 then (values[b / 2]'inRange).1.toNat else (values[b / 2]'inRange).2.toNat)
  else 0

theorem halvesOf_lt {count : Nat} (values : Vector (Block × Block) count) (b : Nat) :
    halvesOf values b < 2 ^ 128 := by
  unfold halvesOf
  split
  · split
    · exact BitVec.isLt _
    · exact BitVec.isLt _
  · positivity

theorem packAnswers_eq_limbValue {count : Nat} (values : Vector (Block × Block) count) :
    packAnswers count values.get = limbValue (halvesOf values) (2 * count) := by
  rw [← sum_answers_eq_limbValue]
  unfold packAnswers
  rw [← Fin.sum_univ_eq_sum_range (fun j => 2 ^ (256 * j) *
    (halvesOf values (2 * j) + 2 ^ 128 * halvesOf values (2 * j + 1)))]
  refine sum_congr rfl fun j _ => ?_
  have even : (2 * j.val) / 2 = j.val := by omega
  have odd : (2 * j.val + 1) / 2 = j.val := by omega
  unfold halvesOf answerNat
  rw [dif_pos (by rw [even]; exact j.isLt), dif_pos (by rw [odd]; exact j.isLt),
    if_pos (by omega), if_neg (by omega)]
  simp only [even, odd, Vector.get_eq_getElem]

/-- The limbs of a limb value are the limbs. -/
theorem limbOf_limbValue (x : Nat → Nat) (small : ∀ k, x k < 2 ^ 128) :
    ∀ n k, k < n → limbOf (limbValue x n) k = x k
  | 0, k, bound => absurd bound (by omega)
  | n + 1, k, bound => by
      rw [limbValue_succ]
      by_cases last : k = n
      · subst last
        unfold limbOf
        rw [carry_step, Nat.div_eq_of_lt (limbValue_lt x small k), zero_add,
          Nat.mod_eq_of_lt (small k)]
      · rw [limbOf_add_high _ _ _ _ (by omega), limbOf_limbValue x small n k (by omega)]

/-- **A block-aligned lane of a limb value** is read from its own limb. -/
theorem lane_of_limbValue (x : Nat → Nat) (small : ∀ k, x k < 2 ^ 128) (n b s l : Nat)
    (bBound : b < n) (fits : s + l ≤ 128) :
    (limbValue x n >>> (128 * b + s)) % 2 ^ l = (x b >>> s) % 2 ^ l := by
  set V := limbValue x n
  have split := div_limb_split V b
  rw [limbOf_limbValue x small n b bBound] at split
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, pow_add, ← Nat.div_div_eq_div_mul, split]
  set q := V / 2 ^ (128 * (b + 1))
  have powSplit : (2 : Nat) ^ 128 = 2 ^ (128 - s - l) * 2 ^ l * 2 ^ s := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [powSplit, show q * (2 ^ (128 - s - l) * 2 ^ l * 2 ^ s) + x b =
      x b + (q * 2 ^ (128 - s - l) * 2 ^ l) * 2 ^ s by ring,
    Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]

/-- Lane `i` of a cast reads `l` bits at `l · (i mod per)` of block `i / per`. -/
theorem castLanes_val (l : Nat) (lPos : 0 < l) (lSmall : l ≤ 128) {count : Nat}
    (values : Vector (Block × Block) count) (i : Fin laneCount)
    (blockBound : i.val / lanesPerBlock l < 2 * count) :
    (castLanes l (packAnswers count values.get) i).val =
      (halvesOf values (i.val / lanesPerBlock l) >>> (l * (i.val % lanesPerBlock l))) % 2 ^ l := by
  unfold castLanes laneOffset
  rw [ZMod.val_natCast, packAnswers_eq_limbValue]
  have perPos : 0 < lanesPerBlock l := Nat.div_pos lSmall lPos
  have fits : l * (i.val % lanesPerBlock l) + l ≤ 128 := by
    have lt := Nat.mod_lt i.val perPos
    have le : l * lanesPerBlock l ≤ 128 := by
      unfold lanesPerBlock; rw [Nat.mul_comm]; exact Nat.div_mul_le_self 128 l
    calc l * (i.val % lanesPerBlock l) + l = l * (i.val % lanesPerBlock l + 1) := by ring
      _ ≤ l * lanesPerBlock l := Nat.mul_le_mul_left _ lt
      _ ≤ 128 := le
  exact lane_of_limbValue _ (halvesOf_lt values) _ _ _ _ blockBound fits

/-- Every lane's block is among the answers' halves. -/
theorem laneBlock_lt (l : Nat) (lPos : 0 < l) (lSmall : l ≤ 128) (i : Nat) (iBound : i < laneCount) :
    i / lanesPerBlock l < 2 * castAnswers l := by
  have perPos : 0 < lanesPerBlock l := Nat.div_pos lSmall lPos
  have blocks : i / lanesPerBlock l < castBlocks l := by
    unfold castBlocks
    simp only [labelBits]
    rw [Nat.lt_div_iff_mul_lt perPos]
    have := Nat.div_mul_le_self i (lanesPerBlock l)
    have := Nat.lt_div_mul_add (a := i) perPos
    simp only [laneCount, labelBits] at iBound
    omega
  unfold castAnswers
  omega

/-! ### The machine -/

theorem exec_loadAt (target : Register) (address : Nat) (memory : Memory) :
    (loadAt target address).exec memory =
      some (setReg (setReg memory rAddr (word address)) target (memory.ram (word address))) := by
  show some (setReg (setReg memory rAddr (word address)) target
    ((setReg memory rAddr (word address)).ram
      ((setReg memory rAddr (word address)).registers rAddr))) = _
  rw [reg_setReg, if_pos rfl]
  rfl

/-- The layout facts one cast needs. -/
structure CastLayout (cells : CastCells) (l : Nat) : Prop where
  ansFits : cells.ansBase + 2 * castAnswers l < 2 ^ 256
  laneFits : cells.laneBase + laneCount < 2 ^ 256
  apart : ∀ b, b < 2 * castAnswers l → ∀ i, i < laneCount → cells.ansBase + b ≠ cells.laneBase + i
  labelSmall : cells.label < 2 ^ 256
  labelOff : ∀ b, b < 2 * castAnswers l → cells.label ≠ cells.ansBase + b

theorem ne_of_not_cast {register : Register} (outside : ¬ castClobbers register)
    (other : Register) (inside : other ∈ [rA, rB, rAddr, rInput, rFirst, rSecond]) :
    register ≠ other := fun same => outside (by rw [same]; exact inside)

/-- The invariant of the query loop after `count` answers. -/
def CastInv (cells : CastCells) (total : Nat) (start : Memory) (count : Nat)
    (values : Vector (Block × Block) count) (memory : Memory) : Prop :=
  (∀ j (bound : j < count),
      memory.ram (word (cells.ansBase + 2 * j)) = blockWord (values[j]'bound).1 ∧
        memory.ram (word (cells.ansBase + (2 * j + 1))) = blockWord (values[j]'bound).2) ∧
    (∀ address, (∀ b, b < 2 * total → address ≠ word (cells.ansBase + b)) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ castClobbers register → memory.registers register = start.registers register

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **One answer of a cast.** -/
theorem agree_castQuery (cells : CastCells) (l : Nat) (layout : CastLayout cells l)
    (tagOf : Nat → Nat) (label : Block) (start : Memory)
    (labelCell : start.ram (word cells.label) = blockWord label)
    (tagSmall : ∀ j, j < castAnswers l → tagOf j < 2 ^ 127)
    (index : Fin (castAnswers l)) (values : Vector (Block × Block) index.val) (memory : Memory)
    (holds : CastInv cells (castAnswers l) start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : Block × Block) after =>
        CastInv cells (castAnswers l) start (index.val + 1) (values.push result) after)
      ((castQuery cells (tagOf index.val) index.val).tree memory)
      (liftHash (askN (hashInput label (tagOf index.val)))) := by
  obtain ⟨done, frame, bitsSame, regs⟩ := holds
  have ansFits := layout.ansFits
  have indexBound := index.isLt
  have labelNow : memory.ram (word cells.label) = blockWord label := by
    rw [frame _ fun b bound => word_ne layout.labelSmall (by omega) (layout.labelOff b bound)]
    exact labelCell
  have hashSmall : hashInput label (tagOf index.val) < 2 ^ 256 := by
    unfold hashInput
    have := label.isLt
    have := tagSmall _ index.isLt
    omega
  set m1 := setReg (setReg memory rAddr (word cells.label)) rInput (blockWord label) with m1Def
  set m2 := setReg m1 rB (word (2 ^ 128 * tagOf index.val)) with m2Def
  set m3 := setReg m2 rInput (word (hashInput label (tagOf index.val))) with m3Def
  have run1 : (loadAt rInput cells.label).exec memory = some m1 := by
    rw [exec_loadAt, labelNow]
  have run3 : (ar .add rInput rInput rB).exec m2 = some m3 := by
    rw [exec_ar_last _ _ _ _ m2 (word label.toNat) (word (2 ^ 128 * tagOf index.val))
      (by rw [m2Def, reg_setReg, if_neg (by decide), m1Def, reg_setReg, if_pos rfl]; rfl)
      (by rw [m2Def, reg_setReg, if_pos rfl]), eval_add_word _ _ hashSmall]
    rfl
  unfold castQuery
  rw [tree_seq_exec _ _ (show (loadAt rInput cells.label).OpsSatisfy Op.Det from ⟨trivial, trivial⟩)
      memory m1 run1,
    tree_seq_exec _ _ (show (cst rB (2 ^ 128 * tagOf index.val)).OpsSatisfy Op.Det from trivial) m1 m2 rfl,
    tree_seq_exec _ _ (show (ar .add rInput rInput rB).OpsSatisfy Op.Det from trivial) m2 m3 run3,
    tree_query_hash _ m3 _ hashSmall (by rw [m3Def, reg_setReg, if_pos rfl])]
  refine .node _ fun (answer : Block × Block) => ?_
  rw [tree_eq_exec _ (show (Prog.seq (storeAt (cells.ansBase + 2 * index.val) rFirst)
      (storeAt (cells.ansBase + (2 * index.val + 1)) rSecond)).OpsSatisfy Op.Det from
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩)]
  set m4 := writePair m3 rFirst rSecond (blockWord answer.1, blockWord answer.2) with m4Def
  have first4 : m4.registers rFirst = blockWord answer.1 := by
    rw [m4Def, writePair_reg, if_neg (by decide), if_pos rfl]
  have second4 : m4.registers rSecond = blockWord answer.2 := by
    rw [m4Def, writePair_reg, if_pos rfl]
  rw [exec_storeAt_seq _ _ _ m4 (by decide), exec_storeAt _ _ _ (by decide)]
  have cellNe : ∀ b c, b < 2 * castAnswers l → c < 2 * castAnswers l → b ≠ c →
      word (cells.ansBase + b) ≠ word (cells.ansBase + c) :=
    fun b c bb cb ne => word_ne (by omega) (by omega) (by omega)
  refine .leaf ⟨fun j bound => ?_, fun address off => ?_, ?_, fun register outside => ?_⟩
  · simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg]
    simp (config := { decide := true }) only [reduceIte]
    rw [second4, first4]
    by_cases last : j = index.val
    · subst last
      simp only [Vector.getElem_push_eq]
      refine ⟨?_, Function.update_self ..⟩
      rw [Function.update_of_ne (cellNe (2 * index.val) (2 * index.val + 1) (by omega) (by omega)
        (by omega)), Function.update_self]
    · have jSmall : j < index.val := by omega
      simp only [Vector.getElem_push_lt jSmall]
      rw [Function.update_of_ne (cellNe (2 * j) (2 * index.val + 1) (by omega) (by omega) (by omega)),
        Function.update_of_ne (cellNe (2 * j) (2 * index.val) (by omega) (by omega) (by omega)),
        Function.update_of_ne (cellNe (2 * j + 1) (2 * index.val + 1) (by omega) (by omega) (by omega)),
        Function.update_of_ne (cellNe (2 * j + 1) (2 * index.val) (by omega) (by omega) (by omega))]
      exact done j jSmall
  · simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg]
    simp (config := { decide := true }) only [reduceIte]
    rw [Function.update_of_ne (off (2 * index.val + 1) (by omega)),
      Function.update_of_ne (off (2 * index.val) (by omega))]
    exact frame address off
  · simp only [bits_storeRam, bits_setReg]
    exact bitsSame
  · simp only [reg_storeRam, reg_setReg, if_neg (ne_of_not_cast outside rAddr (by simp))]
    rw [m4Def, writePair_reg, if_neg (ne_of_not_cast outside rSecond (by simp)),
      if_neg (ne_of_not_cast outside rFirst (by simp)), m3Def, reg_setReg,
      if_neg (ne_of_not_cast outside rInput (by simp)), m2Def, reg_setReg,
      if_neg (ne_of_not_cast outside rB (by simp)), m1Def, reg_setReg,
      if_neg (ne_of_not_cast outside rInput (by simp)), reg_setReg,
      if_neg (ne_of_not_cast outside rAddr (by simp))]
    exact regs register outside

/-- The stored halves, read back by index. -/
theorem ansCell_halves (cells : CastCells) (total : Nat) (start memory : Memory)
    (values : Vector (Block × Block) total) (holds : CastInv cells total start total values memory)
    (b : Nat) (bBound : b < 2 * total) :
    memory.ram (word (cells.ansBase + b)) = word (halvesOf values b) := by
  obtain ⟨done, _, _, _⟩ := holds
  rcases Nat.even_or_odd' b with ⟨j, rfl | rfl⟩
  · have jb : j < total := by omega
    have half : 2 * j / 2 = j := by omega
    have evenMod : 2 * j % 2 = 0 := by omega
    simp only [halvesOf, half, evenMod, jb, dif_pos, if_pos]
    exact (done j jb).1
  · have jb : j < total := by omega
    have half : (2 * j + 1) / 2 = j := by omega
    have oddMod : (2 * j + 1) % 2 = 1 := by omega
    simp only [halvesOf, half, oddMod, jb, dif_pos, one_ne_zero, if_false]
    exact (done j jb).2

/-! ### The parity lane -/

/-- Bit `i` read by `/ 2 ^ i % 2`: two naturals with the same bit `i` agree. -/
theorem div_pow_mod_two_of_testBit {a b i : Nat} (same : a.testBit i = b.testBit i) :
    a / 2 ^ i % 2 = b / 2 ^ i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at same
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ i) with hb | hb <;> simp_all

/-- The low 128 bits of a word carry the label: bit `i < 104` of `S` is bit `i` of the label. -/
theorem label_bit_of_low (label : Label) (S i : Nat) (low : S % 2 ^ 128 = label.toNat) (iSmall : i < 128) :
    S / 2 ^ i % 2 = label.toNat / 2 ^ i % 2 := by
  apply div_pow_mod_two_of_testBit
  rw [← low, Nat.testBit_mod_two_pow]
  simp [iSmall]

/-- The parity bit of a lane as a natural. -/
theorem getLsbD_ite_eq (label : Label) (i : Nat) :
    (if label.getLsbD i then 1 else 0) = label.toNat / 2 ^ i % 2 := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (label.toNat / 2 ^ i) with h | h <;> simp [h]

theorem half_lane_arith (h s w : Nat) :
    (h >>> s) % 2 ^ (w + 1) / 2 = h / 2 ^ (s + 1) % 2 ^ (w + 1 - 1) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.add_sub_cancel, pow_succ' 2 w, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← pow_succ]

/-- **A parity lane of a limb value**: twice the upper `l - 1` bits of the block-aligned lane, plus bit `i`
of the label. -/
theorem parityCastLanes_val (l : Nat) (lPos : 0 < l) (lSmall : l ≤ 128) {count : Nat}
    (values : Vector (Block × Block) count) (label : Label) (i : Fin laneCount)
    (blockBound : i.val / lanesPerBlock l < 2 * count) :
    (Parity.parityCastLanes l label (packAnswers count values.get) i).val =
      2 * (halvesOf values (i.val / lanesPerBlock l) / 2 ^ (l * (i.val % lanesPerBlock l) + 1) %
        2 ^ (l - 1)) + label.toNat / 2 ^ i.val % 2 := by
  obtain ⟨w, rfl⟩ : ∃ w, l = w + 1 := ⟨l - 1, by omega⟩
  have base := castLanes_val (w + 1) lPos lSmall values i blockBound
  set X := castLanes (w + 1) (packAnswers count values.get) with XDef
  show (Parity.parityLift (Parity.halfLanes X) label i).val = _
  rw [Parity.parityLift_val, getLsbD_ite_eq]
  have half : (Parity.halfLanes X i).val = (X i).val / 2 := by
    simp only [Parity.halfLanes, ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    have := ZMod.val_lt (X i)
    have e : (2 : Nat) ^ (w + 1) = 2 ^ w * 2 := pow_succ 2 w
    omega
  rw [half, base, half_lane_arith]

theorem exec_laneBitProg (i : Nat) (memory : Memory) (S : Nat) (dReg : memory.registers rD = word S)
    (SSmall : S < 2 ^ 256) (iSmall : i < 256) :
    ∃ after, (laneBitProg i).exec memory = some after ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rSecond = word (S / 2 ^ i % 2) ∧
      ∀ register, register ≠ rB → register ≠ rSecond → after.registers register = memory.registers register := by
  have bitDivSmall : S / 2 ^ i < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) SSmall
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notB notSecond => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, reduceIte, dReg]
    rw [eval_shr_word S i SSmall (by omega),
      show Arithmetic.and.eval (word (S / 2 ^ i)) (word 1) = word (S / 2 ^ i % 2 ^ 1) from
        eval_and_pow _ 1 bitDivSmall (by norm_num), pow_one]
  · simp only [reg_setReg, if_neg notB, if_neg notSecond]

set_option maxHeartbeats 800000 in
theorem exec_laneUpperProg (cells : CastCells) (l i : Nat) (memory : Memory) (half b : Nat)
    (blockCell : memory.ram (word (cells.ansBase + i / lanesPerBlock l)) = word half)
    (secondReg : memory.registers rSecond = word b)
    (halfSmall : half < 2 ^ 256) (bSmall : b < 2) (lPos : 0 < l) (lLe : l ≤ 128) :
    ∃ after, (laneUpperProg cells l i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.laneBase + i))
        (word (2 * (half / 2 ^ (l * (i % lanesPerBlock l) + 1) % 2 ^ (l - 1)) + b)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have shiftSmall : l * (i % lanesPerBlock l) + 1 < 2 ^ 256 := by
    have : l * (i % lanesPerBlock l) ≤ l * lanesPerBlock l :=
      Nat.mul_le_mul_left _ (Nat.mod_lt _ (Nat.div_pos lLe lPos)).le
    have : l * lanesPerBlock l ≤ 128 := by
      unfold lanesPerBlock; rw [Nat.mul_comm]; exact Nat.div_mul_le_self 128 l
    omega
  have divSmall : half / 2 ^ (l * (i % lanesPerBlock l) + 1) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) halfSmall
  set u := half / 2 ^ (l * (i % lanesPerBlock l) + 1) % 2 ^ (l - 1) with uDef
  have uSmall : u < 2 ^ 128 := by
    have : 2 ^ (l - 1) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.mod_lt (half / 2 ^ (l * (i % lanesPerBlock l) + 1)) (Nat.two_pow_pos (l - 1))
    omega
  refine ⟨_, rfl, ?_, rfl, fun register notA notB notAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte,
      blockCell, secondReg]
    rw [eval_shr_word half _ halfSmall shiftSmall, eval_and_pow _ (l - 1) divSmall (by omega),
      eval_add_word u u (by omega), eval_add_word (u + u) b (by omega)]
    congr 2
    omega
  · simp only [reg_storeRam, reg_setReg, if_neg notA, if_neg notB, if_neg notAddr]

theorem exec_laneExtract (cells : CastCells) (l i : Nat) (memory : Memory) (half S : Nat)
    (blockCell : memory.ram (word (cells.ansBase + i / lanesPerBlock l)) = word half)
    (dReg : memory.registers rD = word S)
    (halfSmall : half < 2 ^ 256) (SSmall : S < 2 ^ 256) (lPos : 0 < l) (lLe : l ≤ 128) (iSmall : i < 256) :
    ∃ after, (laneExtract cells l i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.laneBase + i))
        (word (2 * (half / 2 ^ (l * (i % lanesPerBlock l) + 1) % 2 ^ (l - 1)) + S / 2 ^ i % 2)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr → register ≠ rSecond →
        after.registers register = memory.registers register := by
  obtain ⟨m1, run1, ram1, bits1, second1, regs1⟩ := exec_laneBitProg i memory S dReg SSmall iSmall
  obtain ⟨m2, run2, ram2, bits2, regs2⟩ := exec_laneUpperProg cells l i m1 half (S / 2 ^ i % 2)
    (by rw [ram1]; exact blockCell) second1 halfSmall (Nat.mod_lt _ (by norm_num)) lPos lLe
  refine ⟨m2, by rw [laneExtract, Prog.exec_seq_some _ _ memory m1 run1, run2], by rw [ram2, ram1],
    by rw [bits2, bits1], fun register notA notB notAddr notSecond => ?_⟩
  rw [regs2 register notA notB notAddr, regs1 register notB notSecond]

theorem det_castLanesProg (cells : CastCells) (l : Nat) : (castLanesProg cells l).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ =>
    ⟨⟨trivial, trivial, trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial,
      trivial, ⟨trivial, trivial⟩⟩

/-- **The lane loop of a cast**: with the answers' halves in the answer region and a word whose low
128 bits are the label in `rD`, the 104 parity lanes land in the lane region. -/
theorem exec_castLanesProg (cells : CastCells) (l : Nat) (lPos : 0 < l) (lSmall : l ≤ 128)
    (values : Vector (Block × Block) (castAnswers l)) (label : Label) (S : Nat) (memory : Memory)
    (halves : ∀ b, b < 2 * castAnswers l → memory.ram (word (cells.ansBase + b)) = word (halvesOf values b))
    (dReg : memory.registers rD = word S) (SSmall : S < 2 ^ 256) (low : S % 2 ^ 128 = label.toNat)
    (ansFits : cells.ansBase + 2 * castAnswers l < 2 ^ 256) (laneFits : cells.laneBase + laneCount < 2 ^ 256)
    (apart : ∀ b, b < 2 * castAnswers l → ∀ i, i < laneCount → cells.ansBase + b ≠ cells.laneBase + i) :
    ∃ after, (castLanesProg cells l).exec memory = some after ∧
      (∀ i : Fin laneCount, after.ram (word (cells.laneBase + i.val)) =
        word (Parity.parityCastLanes l label (packAnswers (castAnswers l) values.get) i).val) ∧
      (∀ address, (∀ i', i' < laneCount → address ≠ word (cells.laneBase + i')) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr → register ≠ rSecond →
        after.registers register = memory.registers register := by
  have lc : laneCount = 104 := rfl
  obtain ⟨final, run, lanes, frameL, bitsL, regsL⟩ := Prog.exec_rep (laneExtract cells l)
    (fun i current =>
      (∀ i', i' < i → current.ram (word (cells.laneBase + i')) =
          word (2 * (halvesOf values (i' / lanesPerBlock l) / 2 ^ (l * (i' % lanesPerBlock l) + 1) %
            2 ^ (l - 1)) + S / 2 ^ i' % 2)) ∧
        (∀ address, (∀ i', i' < laneCount → address ≠ word (cells.laneBase + i')) →
          current.ram address = memory.ram address) ∧
        current.bits = memory.bits ∧
        ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr → register ≠ rSecond →
          current.registers register = memory.registers register)
    laneCount (fun i bound current holds => by
      obtain ⟨done, frame, bits, regs⟩ := holds
      have blockBound := laneBlock_lt l lPos lSmall i bound
      have blockNow : current.ram (word (cells.ansBase + i / lanesPerBlock l)) =
          word (halvesOf values (i / lanesPerBlock l)) := by
        rw [frame _ fun i' ib => word_ne (by omega) (by omega) (apart _ blockBound i' ib)]
        exact halves _ blockBound
      have dNow : current.registers rD = word S := by
        rw [regs rD (by decide) (by decide) (by decide) (by decide)]
        exact dReg
      obtain ⟨next, step, ram, bitsN, regsN⟩ := exec_laneExtract cells l i current _ S blockNow dNow
        (lt_trans (halvesOf_lt values _) (by norm_num)) SSmall lPos lSmall (by omega)
      have laneSmall : cells.laneBase + i < 2 ^ 256 := by omega
      refine ⟨next, step, fun i' ib => ?_, fun address off => ?_, by rw [bitsN, bits],
        fun register notA notB notAddr notSecond => by rw [regsN register notA notB notAddr notSecond,
          regs register notA notB notAddr notSecond]⟩
      · rw [ram]
        by_cases last : i' = i
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) laneSmall (by omega)), done i' (by omega)]
      · rw [ram, Function.update_of_ne (off i bound)]
        exact frame address off)
    memory ⟨fun i' ib => absurd ib (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ _ _ _ => rfl⟩
  refine ⟨final, run, fun i => ?_, frameL, bitsL, regsL⟩
  rw [lanes i.val i.isLt, parityCastLanes_val l lPos lSmall values label i
    (laneBlock_lt l lPos lSmall i.val i.isLt), label_bit_of_low label S i.val low (by omega)]

/-- **One cast** against the evaluator's parity `castM`: the same answers in the same order, the 104
parity lanes in the lane region, and the frame of the schema. -/
theorem agree_castBlock (cells : CastCells) (l : Nat) (lPos : 0 < l) (lSmall : l ≤ 128)
    (layout : CastLayout cells l) (tagOf : Nat → Nat) (label : Label) (memory : Memory)
    (labelCell : memory.ram (word cells.label) = labelWord label)
    (tagSmall : ∀ j, j < castAnswers l → tagOf j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (lanes : Lanes l) after =>
        (∀ i : Fin laneCount, after.ram (word (cells.laneBase + i.val)) = word (lanes i).val) ∧
          Frame (castWrites cells l) castBlockClobbers memory after)
      ((castBlock cells l tagOf).tree memory) (liftHash (castM l label tagOf)) := by
  have ansFits := layout.ansFits
  have laneFits : cells.laneBase + 104 < 2 ^ 256 := layout.laneFits
  unfold castBlock castM hlongM
  rw [tree_seq, TreeLaws.monad_bind, TreeLaws.monad_bind, liftHash_bind, liftHash_bind,
    liftHash_vector, TreeLaws.bind_assoc]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_rep_vector_plain (fun j => castQuery cells (tagOf j) j)
      (CastInv cells (castAnswers l) memory) (castAnswers l) _
      (fun index values current holds =>
        agree_castQuery cells l layout tagOf (embed label) memory (by simpa only [labelWord_embed] using labelCell) tagSmall index values current holds)
      memory ⟨fun j bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ => rfl⟩)
  have halves := ansCell_halves cells (castAnswers l) memory after values inv
  obtain ⟨_, frameQ, bitsQ, regsQ⟩ := inv
  have labelNow : after.ram (word cells.label) = labelWord label := by
    rw [frameQ _ fun b bound => word_ne layout.labelSmall (by omega) (layout.labelOff b bound)]
    exact labelCell
  set m0 := setReg (setReg after rAddr (word cells.label)) rD (labelWord label) with m0Def
  have load : (loadAt rD cells.label).exec after = some m0 := by rw [exec_loadAt, labelNow]
  have labelSmall : label.toNat < 2 ^ 256 := lt_trans label.isLt (by norm_num)
  obtain ⟨final, run, lanes, frameL, bitsL, regsL⟩ := exec_castLanesProg cells l lPos lSmall values label
    label.toNat m0 (fun b bb => by rw [m0Def, ram_setReg, ram_setReg]; exact halves b bb)
    (by rw [m0Def, reg_setReg, if_pos rfl, labelWord_eq_word])
    labelSmall (Nat.mod_eq_of_lt (lt_trans label.isLt (by norm_num))) ansFits layout.laneFits layout.apart
  rw [tree_eq_exec _ (show (Prog.seq (loadAt rD cells.label) (castLanesProg cells l)).OpsSatisfy Op.Det from
      ⟨⟨trivial, trivial⟩, det_castLanesProg cells l⟩),
    Prog.exec_seq_some _ _ after m0 load, run]
  refine .leaf ⟨fun i => ?_, ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩
  · rw [lanes i, materialize_eq]
  · have offAns : ∀ b, b < 2 * castAnswers l → address ≠ word (cells.ansBase + b) :=
      fun b bb same => outside (Or.inl ⟨b, bb, same⟩)
    have offLane : ∀ i', i' < laneCount → address ≠ word (cells.laneBase + i') :=
      fun i' ib same => outside (Or.inr ⟨i', ib, same⟩)
    rw [frameL address offLane, m0Def, ram_setReg, ram_setReg, frameQ address offAns]
  · rw [bitsL, m0Def, bits_setReg, bits_setReg, bitsQ]
  · have notIn : ∀ r, r ∈ [rA, rB, rD, rAddr, rInput, rFirst, rSecond] → register ≠ r :=
      fun r inside same => outside (by rw [same]; exact inside)
    rw [regsL register (notIn rA (by simp)) (notIn rB (by simp)) (notIn rAddr (by simp))
      (notIn rSecond (by simp)), m0Def, reg_setReg, if_neg (notIn rD (by simp)), reg_setReg,
      if_neg (notIn rAddr (by simp))]
    exact regsQ register fun inside => outside (by
      unfold castClobbers Clobbers.ofList at inside
      unfold castBlockClobbers Clobbers.ofList
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
      rcases inside with h | h | h | h | h | h <;> simp [h])

end Agreement

/-! ### The cast phase of one chunk -/

/-- The evaluator's cast phase of one chunk after its tree (the tail of `chunkEvalM`). -/
def castPhaseM (l width : Nat) (tagOf : Nat → Nat → Nat) (tree : Fin (2 ^ width) → Label)
    (value : Nat) (pin : Lanes l) : CM (ChunkEval l) :=
  tableM (2 ^ width) (fun leaf =>
      if leaf.val = value then pure 0 else castM l (tree leaf) (tagOf leaf.val)) >>= fun casts =>
    let cold := sumLanes fun leaf : Fin (2 ^ width) => if leaf.val = value then 0 else casts leaf
    let hot := materialize (pin - cold)
    pure { leaves := atNat tree 0, casts := fun leaf => if leaf = value then hot else atNat casts 0 leaf }

/-- `chunkEvalM` is its tree followed by its cast phase. -/
theorem chunkEvalM_split (T : CrtTable) (coord : Nat) (labels : Nat → Label) (v : Nat)
    (joins : Nat → Label) (pin : Lanes T.castWidth) (c : Nat) :
    chunkEvalM T coord labels v joins pin c =
      (treeEvalM (chunkTreeTag coord c) (T.chunkValue v c) (fun n => labels (T.chunkOffset c + n))
        joins (T.chunkWidth c) >>= fun tree =>
          castPhaseM T.castWidth (T.chunkWidth c) (chunkCastTag coord c) tree (T.chunkValue v c) pin) :=
  rfl

/-- ZMod subtraction of small naturals as the machine computes it. -/
theorem zmod_sub_val (N a c : Nat) (NPos : 0 < N) (cSmall : c < N) :
    (((a : ZMod N) - (c : ZMod N)).val) = (a % N + N - c) % N := by
  haveI : NeZero N := ⟨NPos.ne'⟩
  have le : c ≤ a % N + N := by omega
  have cast : ((a % N + N - c : Nat) : ZMod N) = (a : ZMod N) - (c : ZMod N) := by
    rw [Nat.cast_sub le, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_self, add_zero]
  rw [← cast, ZMod.val_natCast]

/-- The same for two residues, read through their values. -/
theorem zmod_sub_val' (N : Nat) (NPos : 0 < N) (x y : ZMod N) :
    (x - y).val = (x.val + N - y.val) % N := by
  haveI : NeZero N := ⟨NPos.ne'⟩
  have := zmod_sub_val N x.val y.val NPos (ZMod.val_lt y)
  rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Nat.mod_eq_of_lt (ZMod.val_lt x)] at this

/-- The layout facts one chunk's cast phase needs. -/
structure ChunkCastLayout (cc : ChunkCastCells) (width l : Nat) : Prop where
  ansFits : cc.ansBase + 2 * castAnswers l < 2 ^ 256
  castFits : cc.castBase + 128 * 2 ^ width < 2 ^ 256
  levelFits : cc.levelBase + 2 ^ width < 2 ^ 256
  pinFits : cc.pinBase + 128 < 2 ^ 256
  alphaSmall : cc.alpha < 2 ^ 256
  ansCast : ∀ b, b < 2 * castAnswers l → ∀ x, x < 128 * 2 ^ width → cc.ansBase + b ≠ cc.castBase + x
  levelAns : ∀ leaf, leaf < 2 ^ width → ∀ b, b < 2 * castAnswers l → cc.levelBase + leaf ≠ cc.ansBase + b
  levelCast : ∀ leaf, leaf < 2 ^ width → ∀ x, x < 128 * 2 ^ width →
    cc.levelBase + leaf ≠ cc.castBase + x
  alphaAns : ∀ b, b < 2 * castAnswers l → cc.alpha ≠ cc.ansBase + b
  alphaCast : ∀ x, x < 128 * 2 ^ width → cc.alpha ≠ cc.castBase + x
  pinAns : ∀ i, i < 128 → ∀ b, b < 2 * castAnswers l → cc.pinBase + i ≠ cc.ansBase + b
  pinCast : ∀ i, i < 128 → ∀ x, x < 128 * 2 ^ width → cc.pinBase + i ≠ cc.castBase + x

/-- A cell outside both regions of the cast phase is not written. -/
theorem not_chunkCastWrites (cc : ChunkCastCells) (width l address : Nat)
    (layout : ChunkCastLayout cc width l) (small : address < 2 ^ 256)
    (offAns : ∀ b, b < 2 * castAnswers l → address ≠ cc.ansBase + b)
    (offCast : ∀ x, x < 128 * 2 ^ width → address ≠ cc.castBase + x) :
    ¬ chunkCastWrites cc width l (word address) := by
  have ansFits := layout.ansFits
  have castFits := layout.castFits
  rintro (⟨b, bb, same⟩ | ⟨x, xb, same⟩)
  · have bb' : b < 2 * castAnswers l := bb
    exact offAns b bb' (word_inj small (by omega) same)
  · have xb' : x < 128 * 2 ^ width := xb
    exact offCast x xb' (word_inj small (by omega) same)

/-- The cast layout of one leaf. -/
theorem leafLayout (cc : ChunkCastCells) (width l : Nat) (layout : ChunkCastLayout cc width l)
    (leaf : Nat) (leafBound : leaf < 2 ^ width) : CastLayout (leafCells cc leaf) l where
  ansFits := layout.ansFits
  laneFits := by
    have := layout.castFits
    show cc.castBase + 128 * leaf + laneCount < 2 ^ 256
    have : 128 * leaf + 128 ≤ 128 * 2 ^ width := by omega
    simp only [laneCount, labelBits]; omega
  apart := fun b bb i ib => by
    show cc.ansBase + b ≠ cc.castBase + 128 * leaf + i
    rw [Nat.add_assoc]
    exact layout.ansCast b bb _ (by simp only [laneCount, labelBits] at ib; omega)
  labelSmall := by have := layout.levelFits; show cc.levelBase + leaf < 2 ^ 256; omega
  labelOff := fun b bb => layout.levelAns leaf leafBound b bb

/-- The invariant of the cast loop after `count` leaves. -/
def CastLoopInv (cc : ChunkCastCells) (width l value : Nat) (start : Memory) (count : Nat)
    (values : Vector (Lanes l) count) (memory : Memory) : Prop :=
  (∀ leaf (bound : leaf < count), leaf ≠ value → ∀ i (ib : i < laneCount),
      memory.ram (word (cc.castBase + 128 * leaf + i)) = word (((values[leaf]'bound) ⟨i, ib⟩).val)) ∧
    (∀ address, ¬ chunkCastWrites cc width l address → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ chunkCastClobbers register → memory.registers register = start.registers register

theorem ne_of_not_chunkCast {register : Register} (outside : ¬ chunkCastClobbers register)
    (other : Register) (inside : other ∈ [rA, rB, rC, rD, rAddr, rInput, rFirst, rSecond]) :
    register ≠ other := fun same => outside (by rw [same]; exact inside)

theorem castClobbers_sub (register : Register) (inside : castBlockClobbers register) :
    chunkCastClobbers register := by
  revert register inside
  simp only [castBlockClobbers, chunkCastClobbers, Clobbers.ofList]
  decide

/-- A cell of an earlier leaf is outside a later leaf's cast writes. -/
theorem earlier_not_castWrites (cc : ChunkCastCells) (width l : Nat)
    (layout : ChunkCastLayout cc width l) (leaf index i : Nat) (lt : leaf < index)
    (indexBound : index < 2 ^ width) (ib : i < laneCount) :
    ¬ castWrites (leafCells cc index) l (word (cc.castBase + 128 * leaf + i)) := by
  have castFits := layout.castFits
  have ansFits := layout.ansFits
  simp only [laneCount, labelBits] at ib
  rintro (⟨b, bb, same⟩ | ⟨k, kb, same⟩)
  · have bb' : b < 2 * castAnswers l := bb
    dsimp only [leafCells] at same
    have eq := word_inj (by omega) (by omega) same
    exact layout.ansCast b bb' (128 * leaf + i) (by omega) (by omega)
  · have kb' : k < laneCount := kb
    simp only [laneCount, labelBits] at kb'
    dsimp only [leafCells] at same
    have eq := word_inj (by omega) (by omega) same
    omega

/-- An address outside the phase's writes is outside one leaf's cast writes. -/
theorem not_castWrites_of (cc : ChunkCastCells) (width l : Nat) (layout : ChunkCastLayout cc width l)
    (index : Nat) (indexBound : index < 2 ^ width) (address : Word)
    (off : ¬ chunkCastWrites cc width l address) :
    ¬ castWrites (leafCells cc index) l address := by
  rintro (inside | ⟨k, kb, same⟩)
  · exact off (Or.inl inside)
  · have kb' : k < laneCount := kb
    simp only [laneCount, labelBits] at kb'
    refine off (Or.inr ⟨128 * index + k, show 128 * index + k < 128 * 2 ^ width by omega, ?_⟩)
    rw [same]
    show word (cc.castBase + 128 * index + k) = word (cc.castBase + (128 * index + k))
    rw [Nat.add_assoc]

/-! ### The pin solve -/

theorem exec_ite (source : Register) (whenSet whenClear : Prog) (memory : Memory) :
    (Prog.ite source whenSet whenClear).exec memory =
      if memory.registers source = 0 then whenClear.exec memory else whenSet.exec memory := rfl

/-- One term of the solve: subtract a cold cast lane modulo `2 ^ l`, or skip the hot leaf. -/
theorem exec_solveTerm (cc : ChunkCastCells) (width l i leaf : Nat) (memory : Memory)
    (value acc c : Nat) (widthSmall : width < 20) (lSmall : l ≤ 128)
    (alphaCell : memory.ram (word cc.alpha) = word value) (valueLt : value < 2 ^ width)
    (leafSmall : leaf < 2 ^ width)
    (accReg : memory.registers rD = word acc) (accLt : acc < 2 ^ l)
    (castCell : leaf ≠ value → memory.ram (word (cc.castBase + 128 * leaf + i)) = word c)
    (cLt : c < 2 ^ l) :
    ∃ after, (solveTerm cc width l i leaf).exec memory = some after ∧
      after.registers rD = word (if leaf = value then acc else (acc + 2 ^ l - c) % 2 ^ l) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rD →
        register ≠ rAddr → after.registers register = memory.registers register := by
  have powSmall : 2 ^ width < 2 ^ 20 := Nat.pow_lt_pow_right (by norm_num) widthSmall
  have lPow : 2 ^ l ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) lSmall
  have valueSmall : value < 2 ^ 256 := by omega
  have leafSmall' : leaf < 2 ^ 256 := by omega
  obtain ⟨m1, run1, ram1, bits1, rA1, regs1⟩ :=
    exec_entryTest (alphaCells cc) width leaf memory value alphaCell valueSmall (by omega)
  rw [Nat.mod_eq_of_lt valueLt] at rA1
  have accNow : m1.registers rD = word acc := by
    rw [regs1 rD (by decide) (by decide) (by decide), accReg]
  unfold solveTerm
  rw [Prog.exec_seq_some _ _ memory m1 run1, exec_ite]
  by_cases same : leaf = value
  · rw [if_pos (by rw [rA1]; exact (word_xor_eq_zero valueSmall leafSmall').mpr same.symm)]
    refine ⟨m1, rfl, by rw [if_pos same, accNow], ram1, bits1, fun register n1 n2 _ _ n5 =>
      regs1 register n1 n2 n5⟩
  · rw [if_neg (by rw [rA1]; exact fun zero => same ((word_xor_eq_zero valueSmall leafSmall').mp zero).symm)]
    have cellNow : m1.ram (word (cc.castBase + 128 * leaf + i)) = word c := by rw [ram1]; exact castCell same
    have sum : acc + 2 ^ l < 2 ^ 256 := by
      have : 2 ^ l + 2 ^ l ≤ 2 ^ 129 := by rw [pow_succ]; omega
      have : (2 : Nat) ^ 129 < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      omega
    have diffSmall : acc + 2 ^ l - c < 2 ^ 256 := by omega
    refine ⟨_, rfl, ?_, by simp only [ram_setReg]; exact ram1, by simp only [bits_setReg]; exact bits1,
      fun register n1 n2 n3 n4 n5 => ?_⟩
    · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, cellNow, accNow]
      rw [eval_add_word _ _ sum, eval_sub_word _ _ (by omega) sum,
        eval_and_pow _ _ diffSmall (by omega), if_neg same]
    · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5]
      exact regs1 register n1 n2 n5

/-- The running difference of the solve for lane `i`: the pin lane minus the cold cast lanes of the
first `k` leaves. -/
def coldTerm {l width : Nat} (values : Vector (Lanes l) (2 ^ width)) (value : Nat)
    (lane : Fin laneCount) (leaf : Nat) : ZMod (2 ^ l) :=
  if inRange : leaf < 2 ^ width then (if leaf = value then 0 else (values[leaf]'inRange) lane) else 0

theorem coldTerm_sum {l width : Nat} (values : Vector (Lanes l) (2 ^ width)) (value : Nat)
    (lane : Fin laneCount) :
    (sumLanes fun leaf : Fin (2 ^ width) =>
        if leaf.val = value then (0 : Lanes l) else values.get leaf) lane =
      ∑ k ∈ range (2 ^ width), coldTerm values value lane k := by
  unfold sumLanes
  rw [materialize_eq, Finset.sum_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun k => coldTerm values value lane k)]
  refine sum_congr rfl fun leaf _ => ?_
  unfold coldTerm
  rw [dif_pos leaf.isLt]
  split
  · rfl
  · rfl

/-- **One lane of the solve**: the hot cast's lane `i` is the pin lane (twice the stored half-pin cell)
minus the cold cast lanes, stored at `castBase + 128 · α + i`. -/
theorem exec_solveLane (cc : ChunkCastCells) (width l i : Nat) (memory : Memory) (value : Nat)
    (values : Vector (Lanes l) (2 ^ width)) (pin : Lanes l) (widthSmall : width < 20)
    (lPos : 0 < l) (lSmall : l ≤ 128) (layout : ChunkCastLayout cc width l)
    (valueLt : value < 2 ^ width) (iBound : i < laneCount)
    (alphaCell : memory.ram (word cc.alpha) = word value)
    (pinCell : memory.ram (word (cc.pinBase + i)) = word ((pin ⟨i, iBound⟩).val / 2))
    (pinEven : (pin ⟨i, iBound⟩).val % 2 = 0)
    (castCells : ∀ leaf (bound : leaf < 2 ^ width), leaf ≠ value →
      memory.ram (word (cc.castBase + 128 * leaf + i)) = word ((values[leaf]'bound) ⟨i, iBound⟩).val) :
    ∃ after, (solveLane cc width l i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cc.castBase + 128 * value + i))
        (word ((pin ⟨i, iBound⟩ - ∑ k ∈ range (2 ^ width), coldTerm values value ⟨i, iBound⟩ k).val)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rD →
        register ≠ rAddr → after.registers register = memory.registers register := by
  have NPos : 0 < 2 ^ l := by positivity
  have castFits := layout.castFits
  set lane : Fin laneCount := ⟨i, iBound⟩ with laneDef
  set m0 := setReg (setReg (setReg memory rAddr (word (cc.pinBase + i))) rD (word ((pin lane).val / 2))) rD
    (word (pin lane).val) with m0Def
  obtain ⟨m1, run1, acc1, ram1, bits1, regs1⟩ := Prog.exec_rep (solveTerm cc width l i)
    (fun k current =>
      current.registers rD = word ((pin lane - ∑ j ∈ range k, coldTerm values value lane j).val) ∧
        current.ram = memory.ram ∧ current.bits = memory.bits ∧
        ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rD →
          register ≠ rAddr → current.registers register = memory.registers register)
    (2 ^ width) (fun k bound current holds => by
      obtain ⟨acc, ram, bits, regs⟩ := holds
      set X := pin lane - ∑ j ∈ range k, coldTerm values value lane j with XDef
      obtain ⟨next, step, accNext, ramNext, bitsNext, regsNext⟩ :=
        exec_solveTerm cc width l i k current value X.val ((values[k]'bound) lane).val widthSmall lSmall
          (by rw [ram]; exact alphaCell) valueLt bound acc (ZMod.val_lt X)
          (fun notHot => by rw [ram]; exact castCells k bound notHot) (ZMod.val_lt _)
      refine ⟨next, step, ?_, by rw [ramNext, ram], by rw [bitsNext, bits],
        fun register n1 n2 n3 n4 n5 => by rw [regsNext register n1 n2 n3 n4 n5,
          regs register n1 n2 n3 n4 n5]⟩
      rw [accNext, sum_range_succ, ← sub_sub, ← XDef]
      unfold coldTerm
      rw [dif_pos bound]
      by_cases hot : k = value
      · rw [if_pos hot, if_pos hot, sub_zero]
      · rw [if_neg hot, if_neg hot]
        conv_rhs => rw [zmod_sub_val' _ NPos])
    m0 ⟨by rw [m0Def, reg_setReg, if_pos rfl, sum_range_zero, sub_zero], rfl, rfl,
      fun register n1 n2 n3 n4 n5 => by rw [m0Def, reg_setReg, if_neg n4, reg_setReg, if_neg n4, reg_setReg,
        if_neg n5]⟩
  have prodSmall : value * 128 < 2 ^ 256 := by omega
  have addrSmall : value * 128 + (cc.castBase + i) < 2 ^ 256 := by
    simp only [laneCount, labelBits] at iBound; omega
  have runAll : (solveLane cc width l i).exec memory =
      (Prog.seq (loadAt rA cc.alpha) (.seq (cst rB 128) (.seq (ar .mul rA rA rB)
        (.seq (cst rB (cc.castBase + i)) (.seq (ar .add rA rA rB) (.op (.store rA rD))))))).exec m1 := by
    have pinSmall : (pin lane).val < 2 ^ 256 := by
      have := ZMod.val_lt (pin lane)
      have : 2 ^ l ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    unfold solveLane
    rw [exec_loadAt_seq, pinCell,
      exec_ar_val _ _ _ _ _ _ (word ((pin lane).val / 2)) (word ((pin lane).val / 2))
        (by rw [reg_setReg, if_pos rfl]) (by rw [reg_setReg, if_pos rfl]),
      eval_add_word _ _ (by omega),
      show (pin lane).val / 2 + (pin lane).val / 2 = (pin lane).val by omega, ← m0Def,
      Prog.exec_seq_some _ _ m0 m1 run1]
  rw [runAll]
  refine ⟨_, rfl, ?_, ?_, fun register n1 n2 n3 n4 n5 => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte, ram1,
      alphaCell, acc1]
    rw [eval_mul_word _ _ prodSmall, eval_add_word _ _ addrSmall,
      show value * 128 + (cc.castBase + i) = cc.castBase + 128 * value + i by ring]
  · simp only [bits_storeRam, bits_setReg]
    exact bits1
  · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2, if_neg n5]
    exact regs1 register n1 n2 n3 n4 n5

theorem det_solveTerm (cc : ChunkCastCells) (width l i leaf : Nat) :
    (solveTerm cc width l i leaf).OpsSatisfy Op.Det :=
  ⟨det_entryTest _ _ _, ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial⟩, trivial⟩

theorem det_pinSolve (cc : ChunkCastCells) (width l : Nat) : (pinSolve cc width l).OpsSatisfy Op.Det :=
  det_rep _ _ fun i _ => ⟨⟨trivial, trivial⟩, trivial, det_rep _ _ (fun leaf _ => det_solveTerm cc width l i leaf),
    ⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial⟩

/-- **The pin solve**: all 104 lanes of the hot cast. -/
theorem exec_pinSolve (cc : ChunkCastCells) (width l : Nat) (memory : Memory) (value : Nat)
    (values : Vector (Lanes l) (2 ^ width)) (pin : Lanes l) (widthSmall : width < 20)
    (lPos : 0 < l) (lSmall : l ≤ 128) (layout : ChunkCastLayout cc width l)
    (valueLt : value < 2 ^ width)
    (alphaCell : memory.ram (word cc.alpha) = word value)
    (pinCells : ∀ i (ib : i < laneCount), memory.ram (word (cc.pinBase + i)) = word ((pin ⟨i, ib⟩).val / 2))
    (pinEven : Parity.EvenLanes pin)
    (castCells : ∀ leaf (bound : leaf < 2 ^ width), leaf ≠ value → ∀ i (ib : i < laneCount),
      memory.ram (word (cc.castBase + 128 * leaf + i)) = word ((values[leaf]'bound) ⟨i, ib⟩).val) :
    ∃ after, (pinSolve cc width l).exec memory = some after ∧
      (∀ i (ib : i < laneCount), after.ram (word (cc.castBase + 128 * value + i)) =
        word ((pin ⟨i, ib⟩ - ∑ k ∈ range (2 ^ width), coldTerm values value ⟨i, ib⟩ k).val)) ∧
      (∀ address, (∀ i, i < laneCount → address ≠ word (cc.castBase + 128 * value + i)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rD →
        register ≠ rAddr → after.registers register = memory.registers register := by
  have castFits := layout.castFits
  have pinFits := layout.pinFits
  have hotSmall : ∀ i, i < laneCount → cc.castBase + 128 * value + i < 2 ^ 256 := fun i ib => by
    simp only [laneCount, labelBits] at ib; omega
  obtain ⟨after, run, done, frame, bits, regs⟩ := Prog.exec_rep (solveLane cc width l)
    (fun i current =>
      (∀ i' (ib : i' < laneCount), i' < i → current.ram (word (cc.castBase + 128 * value + i')) =
          word ((pin ⟨i', ib⟩ - ∑ k ∈ range (2 ^ width), coldTerm values value ⟨i', ib⟩ k).val)) ∧
        (∀ address, (∀ i', i' < laneCount → address ≠ word (cc.castBase + 128 * value + i')) →
          current.ram address = memory.ram address) ∧
        current.bits = memory.bits ∧
        ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rD →
          register ≠ rAddr → current.registers register = memory.registers register)
    laneCount (fun i bound current holds => by
      obtain ⟨done, frame, bits, regs⟩ := holds
      have offHot : ∀ address, address < 2 ^ 256 →
          (∀ i', i' < laneCount → address ≠ cc.castBase + 128 * value + i') →
          current.ram (word address) = memory.ram (word address) := fun address small off =>
        frame _ fun i' ib => word_ne small (hotSmall i' ib) (off i' ib)
      obtain ⟨next, step, ram, bitsN, regsN⟩ := exec_solveLane cc width l i current value values pin
        widthSmall lPos lSmall layout valueLt bound
        (by rw [offHot _ layout.alphaSmall fun i' ib => by
              rw [Nat.add_assoc]; exact layout.alphaCast _ (by simp only [laneCount, labelBits] at ib; omega)]
            exact alphaCell)
        (by rw [offHot _ (by simp only [laneCount, labelBits] at bound; omega) fun i' ib => by
              rw [Nat.add_assoc]; exact layout.pinCast i (by simp only [laneCount, labelBits] at bound; omega) _
                (by simp only [laneCount, labelBits] at ib; omega)]
            exact pinCells i bound)
        (pinEven ⟨i, bound⟩)
        (fun leaf lb notHot => by
          rw [offHot _ (by simp only [laneCount, labelBits] at bound; omega) fun i' ib same => by
            simp only [laneCount, labelBits] at bound ib
            have : 128 * leaf + i = 128 * value + i' := by omega
            omega]
          exact castCells leaf lb notHot i bound)
      refine ⟨next, step, fun i' ib lt => ?_, fun address off => ?_, by rw [bitsN, bits],
        fun register n1 n2 n3 n4 n5 => by rw [regsN register n1 n2 n3 n4 n5,
          regs register n1 n2 n3 n4 n5]⟩
      · rw [ram]
        by_cases last : i' = i
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (hotSmall i' ib) (hotSmall i bound) (by omega))]
          exact done i' ib (by omega)
      · rw [ram, Function.update_of_ne (off i bound)]
        exact frame address off)
    memory ⟨fun i' ib lt => absurd lt (Nat.not_lt_zero _), fun _ _ => rfl, rfl,
      fun _ _ _ _ _ _ => rfl⟩
  exact ⟨after, run, fun i ib => done i ib ib, frame, bits, regs⟩

section Phase

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **One leaf of the cast loop**: the hot leaf is skipped, every other leaf is cast. -/
theorem agree_castEntry (cc : ChunkCastCells) (width l : Nat) (widthSmall : width < 20)
    (lPos : 0 < l) (lSmall : l ≤ 128) (layout : ChunkCastLayout cc width l)
    (tagOf : Nat → Nat → Nat) (tree : Fin (2 ^ width) → Label) (value : Nat)
    (valueLt : value < 2 ^ width) (start : Memory)
    (alphaCell : start.ram (word cc.alpha) = word value)
    (leafCellsHold : ∀ leaf : Fin (2 ^ width),
      start.ram (word (cc.levelBase + leaf.val)) = labelWord (tree leaf))
    (tagSmall : ∀ leaf j, leaf < 2 ^ width → j < castAnswers l → tagOf leaf j < 2 ^ 127)
    (index : Fin (2 ^ width)) (values : Vector (Lanes l) index.val) (memory : Memory)
    (holds : CastLoopInv cc width l value start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : Lanes l) after =>
        CastLoopInv cc width l value start (index.val + 1) (values.push result) after)
      ((castEntry cc width l tagOf index.val).tree memory)
      (liftHash (if index.val = value then pure 0 else castM l (tree index) (tagOf index.val))) := by
  obtain ⟨done, frame, bitsSame, regs⟩ := holds
  have castFits := layout.castFits
  have levelFits := layout.levelFits
  have powSmall : 2 ^ width < 2 ^ 20 := Nat.pow_lt_pow_right (by norm_num) widthSmall
  have valueSmall : value < 2 ^ 256 := by omega
  have indexSmall : index.val < 2 ^ 256 := by have := index.isLt; omega
  have alphaNow : memory.ram (word cc.alpha) = word value := by
    rw [frame _ (not_chunkCastWrites cc width l _ layout layout.alphaSmall layout.alphaAns
      layout.alphaCast)]
    exact alphaCell
  obtain ⟨m1, run1, ram1, bits1, rA1, regs1⟩ :=
    exec_entryTest (alphaCells cc) width index.val memory value alphaNow valueSmall (by omega)
  rw [Nat.mod_eq_of_lt valueLt] at rA1
  unfold castEntry
  rw [tree_seq_exec _ _ (det_entryTest (alphaCells cc) width index.val) memory m1 run1, tree_ite, rA1,
    liftHash_ite]
  have regsBack : ∀ register, ¬ chunkCastClobbers register →
      m1.registers register = start.registers register := fun register outside => by
    rw [regs1 register (ne_of_not_chunkCast outside rA (by simp))
      (ne_of_not_chunkCast outside rB (by simp)) (ne_of_not_chunkCast outside rAddr (by simp))]
    exact regs register outside
  by_cases same : index.val = value
  · rw [if_pos ((word_xor_eq_zero valueSmall indexSmall).mpr same.symm), if_pos same]
    refine .leaf ⟨fun leaf bound notHot i ib => ?_, fun address off => ?_, ?_, regsBack⟩
    · have lt : leaf < index.val := by omega
      simp only [Vector.getElem_push_lt lt]
      rw [ram1]
      exact done leaf lt notHot i ib
    · rw [ram1]
      exact frame address off
    · rw [bits1]
      exact bitsSame
  · rw [if_neg (fun zero => same ((word_xor_eq_zero valueSmall indexSmall).mp zero).symm),
      if_neg same]
    have labelNow : m1.ram (word (leafCells cc index.val).label) = labelWord (tree index) := by
      show m1.ram (word (cc.levelBase + index.val)) = _
      rw [ram1, frame _ (not_chunkCastWrites cc width l _ layout (by have := index.isLt; omega)
        (layout.levelAns _ index.isLt) (layout.levelCast _ index.isLt))]
      exact leafCellsHold index
    refine (agree_castBlock (leafCells cc index.val) l lPos lSmall
      (leafLayout cc width l layout index.val index.isLt) (tagOf index.val) (tree index) m1 labelNow
      (fun j jb => tagSmall _ _ index.isLt jb)).mono fun lanes after post => ?_
    obtain ⟨lanesCells, frameC⟩ := post
    refine ⟨fun leaf bound notHot i ib => ?_, fun address off => ?_, ?_,
      fun register outside => ?_⟩
    · by_cases last : leaf = index.val
      · subst last
        simp only [Vector.getElem_push_eq]
        exact lanesCells ⟨i, ib⟩
      · have lt : leaf < index.val := by omega
        simp only [Vector.getElem_push_lt lt]
        rw [frameC.ram _ (earlier_not_castWrites cc width l layout leaf index.val i lt index.isLt ib),
          ram1]
        exact done leaf lt notHot i ib
    · rw [frameC.ram _ (not_castWrites_of cc width l layout index.val index.isLt address off), ram1]
      exact frame address off
    · rw [frameC.bits, bits1]
      exact bitsSame
    · rw [frameC.registers register (fun inside => outside (castClobbers_sub register inside))]
      exact regsBack register outside

/-- **The cast phase of one chunk** against the tail of `chunkEvalM` (`castPhaseM`): the cold
leaves' casts in ascending order with the hot leaf skipped, then the hot cast solved from the pin
lanes in RAM; every leaf's lanes end in the cast region, under the frame of the schema. -/
theorem agree_castPhase (cc : ChunkCastCells) (width l : Nat) (widthSmall : width < 20)
    (lPos : 0 < l) (lSmall : l ≤ 128) (layout : ChunkCastLayout cc width l)
    (tagOf : Nat → Nat → Nat) (tree : Fin (2 ^ width) → Label) (value : Nat)
    (valueLt : value < 2 ^ width) (pin : Lanes l) (memory : Memory)
    (alphaCell : memory.ram (word cc.alpha) = word value)
    (leafCellsHold : ∀ leaf : Fin (2 ^ width),
      memory.ram (word (cc.levelBase + leaf.val)) = labelWord (tree leaf))
    (pinCells : ∀ i (ib : i < laneCount), memory.ram (word (cc.pinBase + i)) = word ((pin ⟨i, ib⟩).val / 2))
    (pinEven : Parity.EvenLanes pin)
    (tagSmall : ∀ leaf j, leaf < 2 ^ width → j < castAnswers l → tagOf leaf j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : ChunkEval l) after =>
        (∀ leaf (lb : leaf < 2 ^ width), result.leaves leaf = tree ⟨leaf, lb⟩) ∧
        (∀ leaf (lb : leaf < 2 ^ width) i (ib : i < laneCount),
          after.ram (word (cc.castBase + 128 * leaf + i)) = word ((result.casts leaf) ⟨i, ib⟩).val) ∧
          Frame (chunkCastWrites cc width l) chunkCastClobbers memory after)
      ((chunkCastPhase cc width l tagOf).tree memory)
      (liftHash (castPhaseM l width tagOf tree value pin)) := by
  have castFits := layout.castFits
  have pinFits := layout.pinFits
  unfold chunkCastPhase castPhaseM tableM
  rw [tree_seq, TreeLaws.monad_bind, TreeLaws.monad_bind, liftHash_bind, liftHash_bind,
    liftHash_vector, TreeLaws.bind_assoc]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_rep_vector_plain (castEntry cc width l tagOf) (CastLoopInv cc width l value memory)
      (2 ^ width) _
      (fun index values current holds =>
        agree_castEntry cc width l widthSmall lPos lSmall layout tagOf tree value valueLt memory
          alphaCell leafCellsHold tagSmall index values current holds)
      memory ⟨fun leaf bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ => rfl⟩)
  obtain ⟨casts, frameL, bitsL, regsL⟩ := inv
  have alphaNow : after.ram (word cc.alpha) = word value := by
    rw [frameL _ (not_chunkCastWrites cc width l _ layout layout.alphaSmall layout.alphaAns
      layout.alphaCast)]
    exact alphaCell
  have pinNow : ∀ i (ib : i < laneCount), after.ram (word (cc.pinBase + i)) = word ((pin ⟨i, ib⟩).val / 2) :=
    fun i ib => by
      simp only [laneCount, labelBits] at ib
      rw [frameL _ (not_chunkCastWrites cc width l _ layout (by omega) (layout.pinAns i (by omega))
        (layout.pinCast i (by omega)))]
      exact pinCells i ib
  rw [tree_eq_exec _ (det_pinSolve cc width l)]
  obtain ⟨final, run, hot, frameP, bitsP, regsP⟩ := exec_pinSolve cc width l after value values pin
    widthSmall lPos lSmall layout valueLt alphaNow pinNow pinEven casts
  rw [run]
  refine .leaf ⟨fun leaf lb => ?_, fun leaf lb i ib => ?_,
    ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩
  · show atNat tree 0 leaf = _
    unfold atNat
    rw [dif_pos lb]
  · show final.ram _ = word ((if leaf = value then materialize (pin - sumLanes fun leaf : Fin (2 ^ width) =>
        if leaf.val = value then (0 : Lanes l) else values.get leaf) else atNat values.get 0 leaf)
          ⟨i, ib⟩).val
    by_cases same : leaf = value
    · subst same
      rw [if_pos rfl, materialize_eq, Pi.sub_apply, coldTerm_sum]
      exact hot i ib
    · rw [if_neg same]
      unfold atNat
      rw [dif_pos lb, Vector.get_eq_getElem]
      have hotSmall : ∀ i', i' < laneCount → cc.castBase + 128 * value + i' < 2 ^ 256 := fun i' ib' => by
        simp only [laneCount, labelBits] at ib'; omega
      rw [frameP _ fun i' ib' => word_ne (by simp only [laneCount, labelBits] at ib; omega) (hotSmall i' ib') (by
        simp only [laneCount, labelBits] at ib ib'
        intro eq
        have : 128 * leaf + i = 128 * value + i' := by omega
        omega)]
      exact casts leaf lb same i ib
  · rw [frameP address fun i' ib' same => outside (Or.inr ⟨128 * value + i',
      by simp only [laneCount, labelBits] at ib'; show 128 * value + i' < 128 * 2 ^ width; omega,
      by rw [same, Nat.add_assoc]⟩)]
    exact frameL address outside
  · rw [bitsP, bitsL]
  · rw [regsP register (ne_of_not_chunkCast outside rA (by simp)) (ne_of_not_chunkCast outside rB (by simp))
      (ne_of_not_chunkCast outside rC (by simp)) (ne_of_not_chunkCast outside rD (by simp))
      (ne_of_not_chunkCast outside rAddr (by simp))]
    exact regsL register outside

/-- **One chunk** against the
evaluator's `chunkEvalM`, split by `chunkEvalM_split` into its tree and its cast phase: every leaf
label and every leaf's cast lanes end in RAM, under the union of the two frames. The chunk value
`α` must already be at `cells.alpha`. -/
theorem agree_chunkReplay (cells : TreeCells) (cc : ChunkCastCells) (tagTree tagCast : Nat → Nat → Nat)
    (width l : Nat) (widthPos : 1 ≤ width) (widthSmall : width < 20) (lPos : 0 < l) (lSmall : l ≤ 128)
    (sameLevel : cc.levelBase = cells.levelBase) (sameAlpha : cc.alpha = cells.alpha)
    (treeLayouts : ∀ k, k < width → TreeLayout cells k) (castLayout : ChunkCastLayout cc width l)
    (alphaOffTree : ¬ treeEvalWrites cells width (word cells.alpha))
    (pinOffTree : ∀ i, i < laneCount → ¬ treeEvalWrites cells width (word (cc.pinBase + i)))
    (value : Nat) (valueLt : value < 2 ^ width) (bitLabel : Nat → Block) (join : Nat → Label) (pin : Lanes l)
    (memory : Memory)
    (alphaCell : memory.ram (word cells.alpha) = word value)
    (joinCells : ∀ k, 1 ≤ k → k < width → memory.ram (word (cells.join k)) = labelWord (join k))
    (bitCells : ∀ k, k < width → memory.ram (word (cells.bit k)) = blockWord (bitLabel k))
    (pinCells : ∀ i (ib : i < laneCount), memory.ram (word (cc.pinBase + i)) = word ((pin ⟨i, ib⟩).val / 2))
    (pinEven : Parity.EvenLanes pin)
    (tagTreeSmall : ∀ k s, k < width → s < 2 ^ k → tagTree k s < 2 ^ 127)
    (tagCastSmall : ∀ leaf j, leaf < 2 ^ width → j < castAnswers l → tagCast leaf j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : ChunkEval l) after =>
        (∀ leaf (lb : leaf < 2 ^ width),
          after.ram (word (cells.levelBase + leaf)) = labelWord (result.leaves leaf)) ∧
        (∀ leaf (lb : leaf < 2 ^ width) i (ib : i < laneCount),
          after.ram (word (cc.castBase + 128 * leaf + i)) = word ((result.casts leaf) ⟨i, ib⟩).val) ∧
          Frame ((treeEvalWrites cells width).union (chunkCastWrites cc width l))
            (treeStepClobbers.union chunkCastClobbers) memory after)
      ((chunkReplay cells cc tagTree tagCast width l).tree memory)
      (liftHash (treeEvalM tagTree value (fun k => clip (bitLabel k)) join width >>= fun tree =>
        castPhaseM l width tagCast tree value pin)) := by
  have powSmall : 2 ^ width < 2 ^ 20 := Nat.pow_lt_pow_right (by norm_num) widthSmall
  unfold chunkReplay
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun tree after post => ?_)
    (agree_treeEvalBlock cells tagTree width widthPos (by omega) value (by omega) bitLabel join memory
      treeLayouts alphaCell joinCells bitCells tagTreeSmall)
  obtain ⟨levels, frameT⟩ := post
  have alphaNow : after.ram (word cc.alpha) = word value := by
    rw [sameAlpha, frameT.ram _ alphaOffTree]
    exact alphaCell
  have pinNow : ∀ i (ib : i < laneCount), after.ram (word (cc.pinBase + i)) = word ((pin ⟨i, ib⟩).val / 2) :=
    fun i ib => by rw [frameT.ram _ (pinOffTree i ib)]; exact pinCells i ib
  have leavesNow : ∀ leaf : Fin (2 ^ width),
      after.ram (word (cc.levelBase + leaf.val)) = labelWord (tree leaf) := fun leaf => by
    rw [sameLevel]; exact levels leaf
  refine (agree_castPhase cc width l widthSmall lPos lSmall castLayout tagCast tree value valueLt pin
    after alphaNow leavesNow pinNow pinEven tagCastSmall).mono fun result final post => ?_
  obtain ⟨leavesEq, casts, frameC⟩ := post
  refine ⟨fun leaf lb => ?_, casts, frameT.trans frameC⟩
  have levelFits := castLayout.levelFits
  rw [← sameLevel, frameC.ram _ (not_chunkCastWrites cc width l _ castLayout (by omega)
    (castLayout.levelAns leaf lb) (castLayout.levelCast leaf lb)), sameLevel, leavesEq leaf lb]
  exact levels ⟨leaf, lb⟩

end Phase

end Kriterion.CRT.SimMachine
