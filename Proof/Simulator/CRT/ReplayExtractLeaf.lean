/-
**The leaves of an expansion** (package M4a, part 2): the cast of one relative leaf at a
data-dependent slot (`castDyn`) against `castM`, and its terms of the class and cast sums
(`accLevel`).
-/

import Proof.Simulator.CRT.ReplayExtract

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### The cast input -/

theorem exec_castInputBase (cells : StageCells) (start t base stride : Nat) (memory : Memory)
    (slot : Nat) (label : Label) (slotCell : memory.ram (word cells.slot) = word slot)
    (nodeCell : memory.ram (word (cells.nodeBase + (slot + 2 ^ start * t))) = labelWord label)
    (addrSmall : cells.nodeBase + (slot + 2 ^ start * t) < 2 ^ 256) (strideSmall : stride < 2 ^ 64)
    (tagSmall : base + stride * (slot + 2 ^ start * t) < 2 ^ 127) :
    ∃ after, (castInputBase cells start t base stride).exec memory = some after ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rD = word (hashInput (embed label) (base + stride * (slot + 2 ^ start * t))) ∧
      ∀ register, register ≠ rD → register ≠ rB → register ≠ rC → register ≠ rF → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨m1, run1, ram1, bits1, rF1, regs1⟩ :=
    exec_absSlot cells start t memory slot slotCell (by omega)
  set x := slot + 2 ^ start * t with xDef
  have xSmall : x < 2 ^ 256 := by omega
  have prodSmall : x * (2 ^ 128 * stride) < 2 ^ 256 := by
    have : stride * x < 2 ^ 127 := by omega
    calc x * (2 ^ 128 * stride) = 2 ^ 128 * (stride * x) := by ring
      _ < 2 ^ 128 * 2 ^ 127 := Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ < 2 ^ 256 := by norm_num
  have labelSmall : label.toNat < 2 ^ 101 := label.isLt
  have sum1 : label.toNat + x * (2 ^ 128 * stride) < 2 ^ 256 := by
    have : stride * x < 2 ^ 127 := by omega
    have : x * (2 ^ 128 * stride) = 2 ^ 128 * (stride * x) := by ring
    omega
  have sum2 : label.toNat + x * (2 ^ 128 * stride) + 2 ^ 128 * base < 2 ^ 256 := by
    have : x * (2 ^ 128 * stride) + 2 ^ 128 * base = 2 ^ 128 * (base + stride * x) := by ring
    omega
  have nodeCell1 : m1.ram (word (cells.nodeBase + x)) = labelWord label := by rw [ram1]; exact nodeCell
  unfold castInputBase
  rw [Prog.exec_seq_some _ _ memory m1 run1]
  refine ⟨_, rfl, ?_, ?_, ?_, fun register notD notB notC notF notAddr => ?_⟩
  · simp only [ram_setReg, ram1]
  · simp only [bits_setReg, bits1]
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, rF1]
    rw [eval_add_word x cells.nodeBase (by omega), Nat.add_comm x cells.nodeBase, nodeCell1,
      labelWord_eq_word, eval_mul_word x (2 ^ 128 * stride) prodSmall, eval_add_word _ _ sum1,
      eval_add_word _ _ sum2]
    congr 1
    unfold hashInput
    simp only [show ∀ l : Label, (embed l).toNat = l.toNat from Narrow.embed_toNat]
    ring
  · simp only [reg_setReg, if_neg notD, if_neg notB, if_neg notC, if_neg notAddr]
    exact regs1 register notF notB notAddr

theorem det_castInputBase (cells : StageCells) (start t base stride : Nat) :
    (castInputBase cells start t base stride).OpsSatisfy Op.Det :=
  ⟨det_absSlot cells start t, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **One answer of a cast at a run-time tag**: the input `label + 2 ^ 128 · tag0` is in `rD`. -/
theorem agree_castQueryDyn (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (label : Label) (tag0 : Nat) (start : Memory)
    (inputReg : start.registers rD = word (hashInput (embed label) tag0))
    (tagSmall : tag0 + castAnswers rb < 2 ^ 127)
    (index : Fin (castAnswers rb)) (values : Vector (Block × Block) index.val) (memory : Memory)
    (holds : CastInv cells.castCells (castAnswers rb) start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : Block × Block) after =>
        CastInv cells.castCells (castAnswers rb) start (index.val + 1) (values.push result) after)
      ((castQueryDyn cells index.val).tree memory)
      (liftHash (askN (hashInput (embed label) (tag0 + index.val)))) := by
  obtain ⟨done, frame, bitsSame, regs⟩ := holds
  simp only [StageCells.castCells] at done frame
  have c11 := layout.c11; have c12 := layout.c12; have c13 := layout.c13; have c14 := layout.c14
  have c15 := layout.c15; have c16 := layout.c16
  have indexBound := index.isLt
  have inputNow : memory.registers rD = word (hashInput (embed label) tag0) := by
    rw [regs rD (by unfold castClobbers Clobbers.ofList; decide)]; exact inputReg
  have hashSmall : hashInput (embed label) (tag0 + index.val) < 2 ^ 256 := by
    unfold hashInput
    simp only [show ∀ l : Label, (embed l).toNat = l.toNat from Narrow.embed_toNat]
    have : label.toNat < 2 ^ 101 := label.isLt
    omega
  have eq : hashInput (embed label) tag0 + 2 ^ 128 * index.val = hashInput (embed label) (tag0 + index.val) := by
    unfold hashInput; ring
  set m2 := setReg memory rB (word (2 ^ 128 * index.val)) with m2Def
  set m3 := setReg m2 rInput (word (hashInput (embed label) (tag0 + index.val))) with m3Def
  have run3 : (ar .add rInput rD rB).exec m2 = some m3 := by
    rw [exec_ar_last _ _ _ _ m2 (word (hashInput (embed label) tag0)) (word (2 ^ 128 * index.val))
      (by rw [m2Def, reg_setReg, if_neg (by decide)]; exact inputNow)
      (by rw [m2Def, reg_setReg, if_pos rfl]), eval_add_word _ _ (by rw [eq]; exact hashSmall), eq]
  unfold castQueryDyn
  rw [tree_seq_exec _ _ (show (cst rB (2 ^ 128 * index.val)).OpsSatisfy Op.Det from trivial) memory m2 rfl,
    tree_seq_exec _ _ (show (ar .add rInput rD rB).OpsSatisfy Op.Det from trivial) m2 m3 run3,
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
  have cellNe : ∀ b c, b < 2 * castAnswers rb → c < 2 * castAnswers rb → b ≠ c →
      word (cells.ansBase + b) ≠ word (cells.ansBase + c) :=
    fun b c bb cb ne => word_ne (by omega) (by omega) (by omega)
  refine .leaf ⟨fun j bound => ?_, fun address off => ?_, ?_, fun register outside => ?_⟩
  · simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg, StageCells.castCells]
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
  · simp only [StageCells.castCells] at off
    simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg]
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
      if_neg (ne_of_not_cast outside rB (by simp))]
    exact regs register outside

/-- **The cast of relative leaf `t`** against `castM` at the tags `base + stride · α + part`
(`α = slot + 2 ^ start · t`): the lanes in the lane region; only the answer and lane cells change. -/
theorem agree_castDyn (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (rbPos : 0 < rb) (rbLe : rb ≤ 128) (start t base stride : Nat) (strideSmall : stride < 2 ^ 64)
    (memory : Memory) (slot : Nat) (label : Label) (slotCell : memory.ram (word cells.slot) = word slot)
    (nodeCell : memory.ram (word (cells.nodeBase + (slot + 2 ^ start * t))) = labelWord label)
    (xLt : slot + 2 ^ start * t < 2 ^ w)
    (tagSmall : base + stride * (slot + 2 ^ start * t) + castAnswers rb < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (lanes : Lanes rb) after =>
        (∀ i : Fin laneCount, after.ram (word (cells.laneBase + i.val)) = word (lanes i).val) ∧
        (∀ address, (∀ b, b < 2 * castAnswers rb → address ≠ word (cells.ansBase + b)) →
          (∀ i, i < laneCount → address ≠ word (cells.laneBase + i)) → after.ram address = memory.ram address) ∧
        after.bits = memory.bits ∧
        ∀ register, ¬ stageClobbers register → after.registers register = memory.registers register)
      ((castDyn cells rb start t base stride).tree memory)
      (liftHash (castM rb label fun part => base + stride * (slot + 2 ^ start * t) + part)) := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have lc : laneCount = 101 := rfl
  obtain ⟨m1, run1, ram1, bits1, rD1, regs1⟩ := exec_castInputBase cells start t base stride memory slot
    label slotCell nodeCell (by omega) strideSmall (by omega)
  unfold castDyn castM hlongM
  rw [tree_seq_exec _ _ (det_castInputBase cells start t base stride) memory m1 run1, tree_seq,
    TreeLaws.monad_bind, TreeLaws.monad_bind, liftHash_bind, liftHash_bind, liftHash_vector,
    TreeLaws.bind_assoc]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_rep_vector_plain (castQueryDyn cells)
      (CastInv cells.castCells (castAnswers rb) m1) (castAnswers rb) _
      (fun index values current holds =>
        agree_castQueryDyn cells w rb layout label _ m1 rD1 tagSmall index values current holds)
      m1 ⟨fun j bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ => rfl⟩)
  have halves := ansCell_halves cells.castCells (castAnswers rb) m1 after values inv
  simp only [StageCells.castCells] at halves
  obtain ⟨_, frameQ, bitsQ, regsQ⟩ := inv
  simp only [StageCells.castCells] at frameQ
  set S := hashInput (embed label) (base + stride * (slot + 2 ^ start * t)) with SDef
  have SSmall : S < 2 ^ 256 := by
    rw [SDef]
    unfold hashInput
    simp only [show ∀ l : Label, (embed l).toNat = l.toNat from Narrow.embed_toNat]
    have : label.toNat < 2 ^ 101 := label.isLt
    omega
  have low : S % 2 ^ 128 = label.toNat := by
    rw [SDef]
    unfold hashInput
    simp only [show ∀ l : Label, (embed l).toNat = l.toNat from Narrow.embed_toNat]
    have : label.toNat < 2 ^ 101 := label.isLt
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have dNow : after.registers rD = word S := by
    rw [regsQ rD (by unfold castClobbers Clobbers.ofList; decide)]
    exact rD1
  rw [tree_eq_exec _ (det_castLanesProg cells.castCells rb)]
  obtain ⟨final, run, lanes, frameL, bitsL, regsL⟩ := exec_castLanesProg cells.castCells rb rbPos rbLe values
    label S after (fun b bb => halves b bb) dNow SSmall low (by simp only [StageCells.castCells]; omega)
    (by simp only [StageCells.castCells]; omega)
    (fun b bb i ib => by simp only [StageCells.castCells]; omega)
  rw [run]
  refine .leaf ⟨fun i => ?_, fun address offAns offLane => ?_, ?_, fun register outside => ?_⟩
  · have lane := lanes i
    simp only [StageCells.castCells] at lane
    rw [lane, materialize_eq]
  · have frameL' := frameL address
    simp only [StageCells.castCells] at frameL'
    rw [frameL' offLane, frameQ address offAns, ram1]
  · rw [bitsL, bitsQ, bits1]
  · rw [regsL register (ne_of_not_stage outside rA (by simp)) (ne_of_not_stage outside rB (by simp))
      (ne_of_not_stage outside rAddr (by simp)) (ne_of_not_stage outside rSecond (by simp)),
      regsQ register (fun inside => outside (by
        unfold castClobbers Clobbers.ofList at inside
        unfold stageClobbers Clobbers.ofList
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
        rcases inside with h | h | h | h | h | h <;> simp [h])),
      regs1 register (ne_of_not_stage outside rD (by simp)) (ne_of_not_stage outside rB (by simp))
        (ne_of_not_stage outside rC (by simp)) (ne_of_not_stage outside rF (by simp))
        (ne_of_not_stage outside rAddr (by simp))]

end Agreement

/-! ### The terms of one leaf in the sums -/

theorem lane_add_scale_val {rb : Nat} (C L : ZMod (2 ^ rb)) (q : Nat) :
    (C + (q : ZMod (2 ^ rb)) * L).val = (C.val + q * L.val) % 2 ^ rb := by
  haveI : NeZero (2 ^ rb) := ⟨by positivity⟩
  have h : ((C.val + q * L.val : Nat) : ZMod (2 ^ rb)) = C + (q : ZMod (2 ^ rb)) * L := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [← h, ZMod.val_natCast]

theorem lane_add_val {rb : Nat} (C L : ZMod (2 ^ rb)) : (C + L).val = (C.val + L.val) % 2 ^ rb := by
  haveI : NeZero (2 ^ rb) := ⟨by positivity⟩
  exact ZMod.val_add C L

theorem exec_accClass (cells : StageCells) (rb j i : Nat) (memory : Memory) (q lane old : Nat)
    (fReg : memory.registers rF = word q)
    (laneCell : memory.ram (word (cells.laneBase + i)) = word lane)
    (oldCell : memory.ram (word (cells.classBase + 128 * j + i)) = word old)
    (prodSmall : q * lane < 2 ^ 255) (oldSmall : old < 2 ^ 255) (rbSmall : rb < 256) :
    ∃ after, (accClass cells rb j i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.classBase + 128 * j + i))
        (word ((old + q * lane) % 2 ^ rb)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register notA notB notC notE notAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reg_storeRam,
      reduceIte, fReg, laneCell, oldCell]
    rw [eval_mul_word q lane (by omega), eval_add_word old (q * lane) (by omega),
      eval_and_pow _ rb (by omega) rbSmall]
  · simp only [reg_setReg, reg_storeRam, if_neg notA, if_neg notB, if_neg notC, if_neg notE,
      if_neg notAddr]

theorem exec_accCast (cells : StageCells) (rb j i : Nat) (memory : Memory) (lane old : Nat)
    (laneCell : memory.ram (word (cells.laneBase + i)) = word lane)
    (oldCell : memory.ram (word (cells.castSumBase + 128 * j + i)) = word old)
    (laneSmall : lane < 2 ^ 255) (oldSmall : old < 2 ^ 255) (rbSmall : rb < 256) :
    ∃ after, (accCast cells rb j i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.castSumBase + 128 * j + i))
        (word ((old + lane) % 2 ^ rb)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register notB notC notE notAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reg_storeRam,
      reduceIte, laneCell, oldCell]
    rw [eval_add_word old lane (by omega), eval_and_pow _ rb (by omega) rbSmall]
  · simp only [reg_setReg, reg_storeRam, if_neg notB, if_neg notC, if_neg notE, if_neg notAddr]

/-- The class and cast sums of the levels `j ≤ w`, one lane per cell. -/
def SumCells (cells : StageCells) (w rb : Nat) (cls cst : Nat → Lanes rb) (m : Memory) : Prop :=
  ∀ j, j ≤ w → ∀ i : Fin laneCount,
    m.ram (word (cells.classBase + 128 * j + i.val)) = word ((cls j) i).val ∧
      m.ram (word (cells.castSumBase + 128 * j + i.val)) = word ((cst j) i).val

/-- **The terms of the current leaf in the sums of level `j`**: `R_j += (α mod 2 ^ j) · lanes`,
`T_j += lanes`, lane by lane. -/
theorem exec_accLevel (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (rbLe : rb ≤ 128) (wSmall : w ≤ 64) (start t j : Nat) (jLe : j ≤ w) (slot : Nat) (memory : Memory)
    (slotCell : memory.ram (word cells.slot) = word slot) (xLt : slot + 2 ^ start * t < 2 ^ w)
    (L C T : Lanes rb)
    (laneCells : ∀ i : Fin laneCount, memory.ram (word (cells.laneBase + i.val)) = word (L i).val)
    (classCells : ∀ i : Fin laneCount,
      memory.ram (word (cells.classBase + 128 * j + i.val)) = word (C i).val)
    (castCells : ∀ i : Fin laneCount,
      memory.ram (word (cells.castSumBase + 128 * j + i.val)) = word (T i).val) :
    ∃ after, (accLevel cells rb start t j).exec memory = some after ∧
      (∀ i : Fin laneCount,
        after.ram (word (cells.classBase + 128 * j + i.val)) =
          word ((C + scaleLanes ((slot + 2 ^ start * t) % 2 ^ j) L) i).val ∧
        after.ram (word (cells.castSumBase + 128 * j + i.val)) = word ((T + L) i).val) ∧
      (∀ address, (∀ i, i < laneCount → address ≠ word (cells.classBase + 128 * j + i)) →
        (∀ i, i < laneCount → address ≠ word (cells.castSumBase + 128 * j + i)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rF →
        register ≠ rAddr → after.registers register = memory.registers register := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have lc : laneCount = 101 := rfl
  haveI : NeZero (2 ^ rb) := ⟨by positivity⟩
  have powj : 2 ^ j ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have powW : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) wSmall
  have powRb : 2 ^ rb ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) rbLe
  set α := slot + 2 ^ start * t with αDef
  set q := α % 2 ^ j with qDef
  have qLt : q < 2 ^ 64 := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos j)) powj
  have laneLt : ∀ i : Fin laneCount, (L i).val < 2 ^ 128 := fun i => lt_of_lt_of_le (ZMod.val_lt _) powRb
  have prodLt : ∀ i : Fin laneCount, q * (L i).val < 2 ^ 255 := fun i =>
    calc q * (L i).val < 2 ^ 64 * 2 ^ 128 := Nat.mul_lt_mul'' qLt (laneLt i)
      _ < 2 ^ 255 := by norm_num
  have classLt : ∀ i : Fin laneCount, (C i).val < 2 ^ 255 :=
    fun i => lt_of_lt_of_le (ZMod.val_lt _) (le_trans powRb (by norm_num))
  have castLt : ∀ i : Fin laneCount, (T i).val < 2 ^ 255 :=
    fun i => lt_of_lt_of_le (ZMod.val_lt _) (le_trans powRb (by norm_num))
  obtain ⟨m1, run1, ram1, bits1, rF1, regs1⟩ :=
    exec_absSlot cells start t memory slot slotCell (by omega)
  set m3 := setReg (setReg m1 rB (word (2 ^ j - 1))) rF (word q) with m3Def
  have m3ram : m3.ram = memory.ram := by rw [m3Def, ram_setReg, ram_setReg, ram1]
  obtain ⟨final, runL, _, cellsL, frameL, bitsL, regsL⟩ := Prog.exec_rep
    (fun i => Prog.seq (accClass cells rb j i) (accCast cells rb j i))
    (fun i current =>
      current.registers rF = word q ∧
      (∀ i' (b : i' < laneCount), current.ram (word (cells.classBase + 128 * j + i')) =
          word ((if i' < i then (C + scaleLanes q L) ⟨i', b⟩ else C ⟨i', b⟩).val) ∧
        current.ram (word (cells.castSumBase + 128 * j + i')) =
          word ((if i' < i then (T + L) ⟨i', b⟩ else T ⟨i', b⟩).val)) ∧
      (∀ address, (∀ i', i' < laneCount → address ≠ word (cells.classBase + 128 * j + i')) →
        (∀ i', i' < laneCount → address ≠ word (cells.castSumBase + 128 * j + i')) →
        current.ram address = m3.ram address) ∧
      current.bits = m3.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        current.registers register = m3.registers register)
    laneCount (fun i bound current holds => by
      obtain ⟨fReg, sums, frame, bits, regs⟩ := holds
      have laneNow : current.ram (word (cells.laneBase + i)) = word (L ⟨i, bound⟩).val := by
        rw [frame _ (fun i' ib => word_ne (by omega) (by omega) (by omega))
          (fun i' ib => word_ne (by omega) (by omega) (by omega)), m3ram]
        exact laneCells ⟨i, bound⟩
      obtain ⟨clsNow, cstNow⟩ := sums i bound
      rw [if_neg (lt_irrefl i)] at clsNow cstNow
      obtain ⟨m4, run4, ram4, bits4, regs4⟩ := exec_accClass cells rb j i current q _ _ fReg laneNow
        clsNow (prodLt _) (classLt _) (by omega)
      have laneNow4 : m4.ram (word (cells.laneBase + i)) = word (L ⟨i, bound⟩).val := by
        rw [ram4, Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]; exact laneNow
      have cstNow4 : m4.ram (word (cells.castSumBase + 128 * j + i)) = word (T ⟨i, bound⟩).val := by
        rw [ram4, Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]; exact cstNow
      obtain ⟨m5, run5, ram5, bits5, regs5⟩ := exec_accCast cells rb j i m4 _ _ laneNow4 cstNow4
        (lt_trans (laneLt _) (by norm_num)) (castLt _) (by omega)
      refine ⟨m5, by rw [Prog.exec_seq_some _ _ current m4 run4, run5], ?_, fun i' b => ?_,
        fun address offC offT => ?_, by rw [bits5, bits4, bits],
        fun register nA nB nC nE nAddr => by
          rw [regs5 register nB nC nE nAddr, regs4 register nA nB nC nE nAddr,
            regs register nA nB nC nE nAddr]⟩
      · rw [regs5 rF (by decide) (by decide) (by decide) (by decide),
          regs4 rF (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact fReg
      · by_cases last : i' = i
        · subst last
          rw [if_pos (Nat.lt_succ_self _), if_pos (Nat.lt_succ_self _)]
          refine ⟨?_, ?_⟩
          · rw [ram5, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), ram4,
              Function.update_self,
              show (C + scaleLanes q L) ⟨i', b⟩ = C ⟨i', b⟩ + (q : ZMod (2 ^ rb)) * L ⟨i', b⟩ from rfl,
              lane_add_scale_val]
          · rw [ram5, Function.update_self, show (T + L) ⟨i', b⟩ = T ⟨i', b⟩ + L ⟨i', b⟩ from rfl,
              lane_add_val]
        · obtain ⟨cls', cst'⟩ := sums i' b
          simp only [show (i' < i + 1) ↔ (i' < i) by omega]
          refine ⟨?_, ?_⟩
          · rw [ram5, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), ram4,
              Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
            exact cls'
          · rw [ram5, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), ram4,
              Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
            exact cst'
      · rw [ram5, Function.update_of_ne (offT i bound), ram4, Function.update_of_ne (offC i bound)]
        exact frame address offC offT)
    m3 ⟨by rw [m3Def, reg_setReg, if_pos rfl],
      fun i' b => ⟨by rw [if_neg (Nat.not_lt_zero _), m3ram]; exact classCells ⟨i', b⟩,
        by rw [if_neg (Nat.not_lt_zero _), m3ram]; exact castCells ⟨i', b⟩⟩,
      fun _ _ _ => rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
  refine ⟨final, ?_, fun i => ?_, fun address offC offT => ?_, ?_,
    fun register nA nB nC nE nF nAddr => ?_⟩
  · unfold accLevel
    rw [Prog.exec_seq_some _ _ memory m1 run1, exec_cst_seq,
      exec_ar_val _ _ _ _ _ _ (word α) (word (2 ^ j - 1))
        (by rw [reg_setReg, if_neg (by decide)]; exact rF1) (by rw [reg_setReg, if_pos rfl]),
      eval_and_pow α j (by omega) (by omega)]
    exact runL
  · obtain ⟨h1, h2⟩ := cellsL i.val i.isLt
    rw [if_pos i.isLt] at h1 h2
    exact ⟨h1, h2⟩
  · rw [frameL address offC offT, m3ram]
  · rw [bitsL, m3Def, bits_setReg, bits_setReg, bits1]
  · rw [regsL register nA nB nC nE nAddr, m3Def, reg_setReg, if_neg nF, reg_setReg, if_neg nB,
      regs1 register nF nB nAddr]

/-- **All the terms of the current leaf**: the levels `start .. w`. -/
theorem exec_leafSums (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (rbLe : rb ≤ 128) (wSmall : w ≤ 64) (start t : Nat) (startLe : start ≤ w) (slot : Nat)
    (memory : Memory) (slotCell : memory.ram (word cells.slot) = word slot)
    (xLt : slot + 2 ^ start * t < 2 ^ w) (L : Lanes rb) (cls cst : Nat → Lanes rb)
    (laneCells : ∀ i : Fin laneCount, memory.ram (word (cells.laneBase + i.val)) = word (L i).val)
    (sums : SumCells cells w rb cls cst memory) :
    ∃ after, (Prog.rep (w - start + 1) fun k => accLevel cells rb start t (start + k)).exec memory =
        some after ∧
      SumCells cells w rb
        (fun j => if start ≤ j then cls j + scaleLanes ((slot + 2 ^ start * t) % 2 ^ j) L else cls j)
        (fun j => if start ≤ j then cst j + L else cst j) after ∧
      (∀ address, (∀ j, j ≤ w → ∀ i, i < laneCount →
          address ≠ word (cells.classBase + 128 * j + i) ∧
            address ≠ word (cells.castSumBase + 128 * j + i)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rF →
        register ≠ rAddr → after.registers register = memory.registers register := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have lc : laneCount = 101 := rfl
  obtain ⟨final, run, sumsF, frameF, bitsF, regsF⟩ := Prog.exec_rep
    (fun k => accLevel cells rb start t (start + k))
    (fun k current =>
      SumCells cells w rb
        (fun j => if start ≤ j ∧ j < start + k then
          cls j + scaleLanes ((slot + 2 ^ start * t) % 2 ^ j) L else cls j)
        (fun j => if start ≤ j ∧ j < start + k then cst j + L else cst j) current ∧
      (∀ address, (∀ j, j ≤ w → ∀ i, i < laneCount →
          address ≠ word (cells.classBase + 128 * j + i) ∧
            address ≠ word (cells.castSumBase + 128 * j + i)) →
        current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rF →
        register ≠ rAddr → current.registers register = memory.registers register)
    (w - start + 1) (fun k bound current holds => by
      obtain ⟨sumsC, frame, bits, regs⟩ := holds
      have offAll : ∀ n, n < cells.classBase ∨ cells.castSumBase + 128 * (w + 1) ≤ n →
          n < 2 ^ 256 → current.ram (word n) = memory.ram (word n) := fun n hn nb =>
        frame _ fun j jb i ib => ⟨word_ne nb (by omega) (by omega), word_ne nb (by omega) (by omega)⟩
      have slotNow : current.ram (word cells.slot) = word slot := by
        rw [offAll _ (Or.inr (by omega)) (by omega)]; exact slotCell
      have lanesNow : ∀ i : Fin laneCount, current.ram (word (cells.laneBase + i.val)) = word (L i).val :=
        fun i => by rw [offAll _ (Or.inr (by have := i.isLt; omega)) (by have := i.isLt; omega)]; exact laneCells i
      have jOld : ¬ (start ≤ start + k ∧ start + k < start + k) := by omega
      obtain ⟨next, step, cellsN, frameN, bitsN, regsN⟩ := exec_accLevel cells w rb layout rbLe wSmall
        start t (start + k) (by omega) slot current slotNow xLt L (cls (start + k)) (cst (start + k))
        lanesNow (fun i => by simpa only [if_neg jOld] using (sumsC (start + k) (by omega) i).1)
        (fun i => by simpa only [if_neg jOld] using (sumsC (start + k) (by omega) i).2)
      refine ⟨next, step, fun j jb i => ?_, fun address off => ?_, by rw [bitsN, bits],
        fun register nA nB nC nE nF nAddr => by
          rw [regsN register nA nB nC nE nF nAddr, regs register nA nB nC nE nF nAddr]⟩
      · by_cases here : j = start + k
        · subst here
          have cond : start ≤ start + k ∧ start + k < start + (k + 1) := by omega
          simp only [if_pos cond]
          exact cellsN i
        · have iff : (start ≤ j ∧ j < start + (k + 1)) = (start ≤ j ∧ j < start + k) :=
            propext (by omega)
          simp only [iff]
          have iLt := i.isLt
          rw [frameN _ (fun i' ib => word_ne (by omega) (by omega) (by omega))
            (fun i' ib => word_ne (by omega) (by omega) (by omega)),
            frameN _ (fun i' ib => word_ne (by omega) (by omega) (by omega))
            (fun i' ib => word_ne (by omega) (by omega) (by omega))]
          exact sumsC j jb i
      · rw [frameN address (fun i ib => (off (start + k) (by omega) i ib).1)
          (fun i ib => (off (start + k) (by omega) i ib).2)]
        exact frame address off)
    memory ⟨fun j jb i => by
        have cond : ¬ (start ≤ j ∧ j < start + 0) := by omega
        simp only [if_neg cond]
        exact sums j jb i,
      fun _ _ => rfl, rfl, fun _ _ _ _ _ _ _ => rfl⟩
  refine ⟨final, run, fun j jb i => ?_, frameF, bitsF, regsF⟩
  have iff : (start ≤ j ∧ j < start + (w - start + 1)) = (start ≤ j) := propext (by omega)
  have := sumsF j jb i
  simp only [iff] at this
  exact this

/-- The invariant of the leaf loop of an expansion after `count` relative leaves: the partial
class and cast sums of the levels `start .. w`, and the frame. -/
def LeafInv (cells : StageCells) (w rb start slot : Nat) (cls cst : Nat → Lanes rb) (m0 : Memory)
    (count : Nat) (values : Vector (Lanes rb) count) (m : Memory) : Prop :=
  SumCells cells w rb
      (fun j => if start ≤ j then
        cls j + ∑ t : Fin count, scaleLanes ((slot + 2 ^ start * t.val) % 2 ^ j) (values.get t)
        else cls j)
      (fun j => if start ≤ j then cst j + ∑ t : Fin count, values.get t else cst j) m ∧
    (∀ address, (∀ j, j ≤ w → ∀ i, i < laneCount →
        address ≠ word (cells.classBase + 128 * j + i) ∧
          address ≠ word (cells.castSumBase + 128 * j + i)) →
      (∀ b, b < 2 * castAnswers rb → address ≠ word (cells.ansBase + b)) →
      (∀ i, i < laneCount → address ≠ word (cells.laneBase + i)) → m.ram address = m0.ram address) ∧
    m.bits = m0.bits ∧
    ∀ register, ¬ stageClobbers register → m.registers register = m0.registers register

theorem SumCells.transfer {cells : StageCells} {w rb : Nat} {cls cst : Nat → Lanes rb} {m m' : Memory}
    (holds : SumCells cells w rb cls cst m)
    (same : ∀ j, j ≤ w → ∀ i, i < laneCount →
      m'.ram (word (cells.classBase + 128 * j + i)) = m.ram (word (cells.classBase + 128 * j + i)) ∧
        m'.ram (word (cells.castSumBase + 128 * j + i)) = m.ram (word (cells.castSumBase + 128 * j + i))) :
    SumCells cells w rb cls cst m' := fun j jb i => by
  rw [(same j jb i.val i.isLt).1, (same j jb i.val i.isLt).2]
  exact holds j jb i

theorem det_accClass (cells : StageCells) (rb j i : Nat) : (accClass cells rb j i).OpsSatisfy Op.Det := by
  unfold accClass
  exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩

theorem det_accCast (cells : StageCells) (rb j i : Nat) : (accCast cells rb j i).OpsSatisfy Op.Det := by
  unfold accCast
  exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩

theorem det_accLevel (cells : StageCells) (rb start t j : Nat) :
    (accLevel cells rb start t j).OpsSatisfy Op.Det := by
  unfold accLevel
  exact ⟨det_absSlot cells start t, trivial, trivial,
    det_rep _ _ fun i _ => ⟨det_accClass cells rb j i, det_accCast cells rb j i⟩⟩

theorem sum_push {X M : Type} [AddCommMonoid M] {count : Nat} (values : Vector X count) (x : X)
    (f : Nat → X → M) :
    ∑ t : Fin (count + 1), f t.val ((values.push x).get t) =
      (∑ t : Fin count, f t.val (values.get t)) + f count x := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Vector.get_eq_getElem, Vector.getElem_push_eq]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Vector.getElem_push_lt t.isLt]

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **One relative leaf of an expansion**: its cast against `castM`, then its terms in the sums. -/
theorem agree_leafEntry (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (rbPos : 0 < rb) (rbLe : rb ≤ 128) (wSmall : w ≤ 64) (start : Nat) (startLe : start ≤ w)
    (castBase stride : Nat) (strideSmall : stride < 2 ^ 64) (castTag : Nat → Nat → Nat)
    (hCast : ∀ x part, castTag x part = castBase + stride * x + part)
    (castSmall : ∀ x, x < 2 ^ w → castBase + stride * x + castAnswers rb < 2 ^ 127)
    (slot : Nat) (slotLt : slot < 2 ^ start) (labels : Fin (2 ^ (w - start)) → Label)
    (cls cst : Nat → Lanes rb) (m0 : Memory) (slotCell : m0.ram (word cells.slot) = word slot)
    (nodeCells : ∀ t : Fin (2 ^ (w - start)),
      m0.ram (word (cells.nodeBase + (slot + 2 ^ start * t.val))) = labelWord (labels t))
    (index : Fin (2 ^ (w - start))) (values : Vector (Lanes rb) index.val) (memory : Memory)
    (holds : LeafInv cells w rb start slot cls cst m0 index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (lanes : Lanes rb) after =>
        LeafInv cells w rb start slot cls cst m0 (index.val + 1) (values.push lanes) after)
      ((leafEntry cells w rb start castBase stride index.val).tree memory)
      (liftHash (castM rb (labels index) (castTag (slot + 2 ^ start * index.val)))) := by
  obtain ⟨sums, frame, bitsSame, regs⟩ := holds
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have lc : laneCount = 101 := rfl
  have xLt : slot + 2 ^ start * index.val < 2 ^ w := by
    have := slotPos_lt slot start (w - start) index.val slotLt index.isLt
    rwa [Nat.add_sub_cancel' startLe] at this
  have offLeaf : ∀ n, n < cells.classBase ∨ cells.laneBase + 128 ≤ n → n < 2 ^ 256 →
      memory.ram (word n) = m0.ram (word n) := fun n hn nb =>
    frame _ (fun j jb i ib => ⟨word_ne nb (by omega) (by omega), word_ne nb (by omega) (by omega)⟩)
      (fun b bb => word_ne nb (by omega) (by omega)) (fun i ib => word_ne nb (by omega) (by omega))
  have slotNow : memory.ram (word cells.slot) = word slot := by
    rw [offLeaf _ (Or.inr (by omega)) (by omega)]; exact slotCell
  have nodeNow : memory.ram (word (cells.nodeBase + (slot + 2 ^ start * index.val))) =
      labelWord (labels index) := by
    rw [offLeaf _ (Or.inl (by omega)) (by omega)]; exact nodeCells index
  rw [show castTag (slot + 2 ^ start * index.val) =
      fun part => castBase + stride * (slot + 2 ^ start * index.val) + part from
    funext fun part => hCast _ part,
    ← TreeLaws.bind_pure_right (liftHash (castM rb (labels index) fun part =>
      castBase + stride * (slot + 2 ^ start * index.val) + part))]
  unfold leafEntry
  rw [tree_seq]
  refine Agree.bindOpt (fun lanes m1 post1 => ?_)
    (agree_castDyn cells w rb layout rbPos rbLe start index.val castBase stride strideSmall memory slot
      (labels index) slotNow nodeNow xLt (castSmall _ xLt))
  obtain ⟨lanesCell, frame1, bits1, regs1⟩ := post1
  have slot1 : m1.ram (word cells.slot) = word slot := by
    rw [frame1 _ (fun b bb => word_ne (by omega) (by omega) (by omega))
      (fun i ib => word_ne (by omega) (by omega) (by omega))]
    exact slotNow
  have sums1 := sums.transfer (m' := m1) fun j jb i ib =>
    ⟨frame1 _ (fun b bb => word_ne (by omega) (by omega) (by omega))
        (fun i' ib' => word_ne (by omega) (by omega) (by omega)),
      frame1 _ (fun b bb => word_ne (by omega) (by omega) (by omega))
        (fun i' ib' => word_ne (by omega) (by omega) (by omega))⟩
  obtain ⟨m2, run2, sums2, frame2, bits2, regs2⟩ := exec_leafSums cells w rb layout rbLe wSmall start
    index.val startLe slot m1 slot1 xLt lanes _ _ lanesCell sums1
  rw [tree_eq_exec _ (det_rep _ _ fun k _ => det_accLevel cells rb start index.val (start + k)), run2]
  refine .leaf ⟨fun j jb i => ?_, fun address offSums offAns offLane => ?_, ?_, fun register outside => ?_⟩
  · obtain ⟨h1, h2⟩ := sums2 j jb i
    by_cases hj : start ≤ j
    · simp only [if_pos hj] at h1 h2 ⊢
      rw [sum_push values lanes (fun t v => scaleLanes ((slot + 2 ^ start * t) % 2 ^ j) v),
        sum_push values lanes (fun _ v => v), ← add_assoc, ← add_assoc]
      exact ⟨h1, h2⟩
    · simp only [if_neg hj] at h1 h2 ⊢
      exact ⟨h1, h2⟩
  · rw [frame2 address offSums, frame1 address offAns offLane]
    exact frame address offSums offAns offLane
  · rw [bits2, bits1, bitsSame]
  · rw [regs2 register (ne_of_not_stage outside rA (by simp)) (ne_of_not_stage outside rB (by simp))
      (ne_of_not_stage outside rC (by simp)) (ne_of_not_stage outside rE (by simp))
      (ne_of_not_stage outside rF (by simp)) (ne_of_not_stage outside rAddr (by simp)),
      regs1 register outside, regs register outside]

end Agreement

end Kriterion.CRT.SimMachine
