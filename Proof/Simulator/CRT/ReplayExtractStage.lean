/-
**The whole stage** (package M4a, part 5): one round against `stageRoundM`, the rounds against
`stageRoundsM`, the prefix and the final block, and the replay of a fused extraction stage against
`extStageEvalM`.
-/

import Proof.Simulator.CRT.ReplayExtractRound

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-- The rounds in snoc form: the last round after the others. -/
theorem stageRoundsM_snoc {rb : Nat} (w : Nat) (treeTag castTag : Nat → Nat → Nat) (sub : Lanes w)
    (value : Nat) (joins : Nat → Label) (pin : Lanes rb) :
    ∀ (r n : Nat) (state : StageState rb),
      stageRoundsM w treeTag castTag sub value joins pin (r + 1) n state =
        FreeQuery.bind (stageRoundsM w treeTag castTag sub value joins pin r n state)
          (stageRoundM w treeTag castTag sub value joins pin (n + r))
  | 0, n, state => by
      rw [stageRoundsM, stageRoundsM, TreeLaws.monad_bind]
      show FreeQuery.bind _ (fun s => FreeQuery.pure s) = _
      rw [TreeLaws.bind_pure_right]
      rfl
  | r + 1, n, state => by
      have ih : stageRoundsM w treeTag castTag sub value joins pin (r + 1) (n + 1) =
          fun s => FreeQuery.bind (stageRoundsM w treeTag castTag sub value joins pin r (n + 1) s)
            (stageRoundM w treeTag castTag sub value joins pin (n + 1 + r)) :=
        funext fun s => stageRoundsM_snoc w treeTag castTag sub value joins pin r (n + 1) s
      rw [stageRoundsM, stageRoundsM]
      simp only [TreeLaws.monad_bind]
      rw [ih, TreeLaws.bind_assoc, show n + 1 + r = n + (r + 1) by omega]

/-! ### The prefix -/

theorem exec_subLanes (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (wSmall : w ≤ 64) (remainder : Lanes rb) (rbLe : rb ≤ 128) (memory : Memory)
    (remCells : ∀ i : Fin laneCount, memory.ram (word (cells.remBase + i.val)) = word (remainder i).val) :
    ∃ after, (Prog.rep laneCount (subLane cells w)).exec memory = some after ∧
      (∀ i : Fin laneCount, after.ram (word (cells.subBase + i.val)) =
        word ((materialize (reduceTo w remainder)) i).val) ∧
      (∀ address, (∀ i, i < laneCount → address ≠ word (cells.subBase + i)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have c5 := layout.c5; have c16 := layout.c16; have c2 := layout.c2
  have c6 := layout.c6; have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9
  have c10 := layout.c10; have c11 := layout.c11; have c12 := layout.c12; have c13 := layout.c13
  have c14 := layout.c14; have c15 := layout.c15
  have hw := Nat.two_pow_pos w
  have lc : laneCount = 104 := rfl
  haveI : NeZero (2 ^ rb) := ⟨by positivity⟩
  have powRb : 2 ^ rb ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) rbLe
  obtain ⟨final, run, subs, frame, bits, regs⟩ := Prog.exec_rep (subLane cells w)
    (fun i current =>
      (∀ i' (b : i' < laneCount), i' < i → current.ram (word (cells.subBase + i')) =
        word ((remainder ⟨i', b⟩).val % 2 ^ w)) ∧
      (∀ address, (∀ i', i' < laneCount → address ≠ word (cells.subBase + i')) →
        current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rAddr →
        current.registers register = memory.registers register)
    laneCount (fun i bound current holds => by
      obtain ⟨done, frame, bits, regs⟩ := holds
      have remNow : current.ram (word (cells.remBase + i)) = word (remainder ⟨i, bound⟩).val := by
        rw [frame _ fun i' ib => word_ne (by omega) (by omega) (by omega)]
        exact remCells ⟨i, bound⟩
      have valSmall : (remainder ⟨i, bound⟩).val < 2 ^ 256 :=
        lt_of_lt_of_le (ZMod.val_lt _) (le_trans powRb (by norm_num))
      refine ⟨_, rfl, fun i' b lt => ?_, fun address off => ?_,
        by simp only [bits_storeRam, bits_setReg]; exact bits, fun register nB nC nAddr => ?_⟩
      · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte,
          remNow]
        rw [eval_and_pow _ w valSmall (by omega)]
        by_cases last : i' = i
        · subst last; rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done i' b (by omega)
      · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte]
        rw [Function.update_of_ne (off i bound)]
        exact frame address off
      · simp only [reg_setReg, reg_storeRam, if_neg nB, if_neg nC, if_neg nAddr]
        exact regs register nB nC nAddr)
    memory ⟨fun _ _ lt => absurd lt (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ _ _ => rfl⟩
  refine ⟨final, run, fun i => ?_, frame, bits, regs⟩
  rw [subs i.val i.isLt i.isLt, materialize_eq, reduceTo, ZMod.val_natCast]

theorem exec_zeroCells (base count : Nat) (memory : Memory) :
    ∃ after, (zeroCells base count).exec memory = some after ∧
      (∀ k, k < count → after.ram (word (base + k)) = word 0) ∧
      (∀ address, (∀ k, k < count → address ≠ word (base + k)) → after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set m0 := setReg memory rB (word 0) with m0Def
  obtain ⟨final, run, zeros, frame, bits, _, regs⟩ := Prog.exec_rep (fun k => storeAt (base + k) rB)
    (fun i current =>
      (∀ k, k < i → current.ram (word (base + k)) = word 0) ∧
      (∀ address, (∀ k, k < count → address ≠ word (base + k)) → current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧ current.registers rB = word 0 ∧
      ∀ register, register ≠ rB → register ≠ rAddr → current.registers register = memory.registers register)
    count (fun i bound current holds => by
      obtain ⟨done, frame, bits, bReg, regs⟩ := holds
      refine ⟨_, exec_storeAt _ _ _ (by decide), fun k lt => ?_, fun address off => ?_, ?_, ?_,
        fun register nB nAddr => ?_⟩
      · simp only [ram_storeRam, ram_setReg, Function.update_apply]
        split_ifs with h
        · exact bReg
        · exact done k (by
            rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt' | eq
            · exact lt'
            · exact absurd (by rw [eq]) h)
      · simp only [ram_storeRam, ram_setReg]
        rw [Function.update_of_ne (off i bound)]
        exact frame address off
      · simp only [bits_storeRam, bits_setReg]; exact bits
      · simp only [reg_storeRam, reg_setReg, if_neg (show rB ≠ rAddr by decide)]; exact bReg
      · simp only [reg_storeRam, reg_setReg, if_neg nAddr]; exact regs register nB nAddr)
    m0 ⟨fun _ lt => absurd lt (Nat.not_lt_zero _), fun _ _ => by rw [m0Def, ram_setReg],
      by rw [m0Def, bits_setReg], by rw [m0Def, reg_setReg, if_pos rfl],
      fun register nB _ => by rw [m0Def, reg_setReg, if_neg nB]⟩
  exact ⟨final, by rw [zeroCells, exec_cst_seq]; exact run, zeros, frame, bits, regs⟩

theorem word_mod_two_xor_one (value : Nat) : word (value % 2) ^^^ word 1 = word (value % 2 ^^^ 1) := by
  rcases Nat.mod_two_eq_zero_or_one value with h | h <;> rw [h] <;> decide

theorem exec_prefixSlot (cells : StageCells) (memory : Memory) (value : Nat) (D : Word)
    (valueCell : memory.ram (word cells.value) = word value) (valueSmall : value < 2 ^ 256)
    (dReg : memory.registers rD = D) (fits : cells.nodeBase + 2 < 2 ^ 256) :
    ∃ after, (prefixSlot cells).exec memory = some after ∧
      after.ram = Function.update (Function.update memory.ram (word cells.slot)
        (word (value % 2 ^^^ 1))) (word (cells.nodeBase + (value % 2 ^^^ 1))) D ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rF → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have slotLt : value % 2 ^^^ 1 < 2 := by
    rcases Nat.mod_two_eq_zero_or_one value with h | h <;> rw [h] <;> decide
  refine ⟨_, rfl, ?_, rfl, fun register nB nF nAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reg_storeRam,
      reduceIte, valueCell, dReg]
    rw [show Arithmetic.and.eval (word value) (word 1) = word (value % 2) from
        eval_and_pow value 1 valueSmall (by norm_num), eval_xor, word_mod_two_xor_one,
      eval_add_word _ cells.nodeBase (by omega), Nat.add_comm (value % 2 ^^^ 1) cells.nodeBase]
  · simp only [reg_setReg, reg_storeRam, if_neg nB, if_neg nF, if_neg nAddr]

theorem exec_storeAt_facts (address : Nat) (source : Register) (memory : Memory)
    (other : source ≠ rAddr) :
    ∃ after, (storeAt address source).exec memory = some after ∧
      after.ram = Function.update memory.ram (word address) (memory.registers source) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAddr → after.registers register = memory.registers register :=
  ⟨_, exec_storeAt address source memory other, by simp only [ram_storeRam, ram_setReg],
    by simp only [bits_storeRam, bits_setReg],
    fun register h => by simp only [reg_storeRam, reg_setReg, if_neg h]⟩

/-- The evaluator's state before the expansion of round 0 (`extStageEvalM`'s `start`). -/
def stageStart {rb : Nat} (w : Nat) (remainder : Lanes rb) : StageState rb :=
  { levelSum := fun _ => 0
    classSum := fun _ => 0
    castSum := fun _ => 0
    leaves := fun _ => 0
    active := laneBit (materialize (reduceTo w remainder)) 0
    bits := fun k => if k = 0 then laneBit (materialize (reduceTo w remainder)) 0 else 0 }

/-- **The prefix**: `sub`, `b_0^E`, zero sums, the closed level-1 slot and its label. -/
theorem exec_stagePrefix (cells : StageCells) (w rb value : Nat) (remainder : Lanes rb)
    (joins : Nat → Label) (pin : Lanes rb) (layout : StageLayout cells w rb) (rbLe : rb ≤ 128)
    (wSmall : w ≤ 64) (wPos : 1 ≤ w) (valueLt : value < 2 ^ w) (m : Memory)
    (inputs : StageInputs cells w rb value remainder joins pin m) :
    ∃ m1, (stagePrefix cells w).exec m = some m1 ∧
      StageRel cells w rb value (materialize (reduceTo w remainder)) 0 1 m (stageStart w remainder) m1 ∧
      m1.ram (word cells.slot) = word (value % 2 ^^^ 1) ∧
      m1.ram (word (cells.nodeBase + (value % 2 ^^^ 1))) =
        labelWord (laneBit (materialize (reduceTo w remainder)) 0) := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have c1 := layout.c1; have c2 := layout.c2; have c3 := layout.c3; have c4 := layout.c4
  have lc : laneCount = 104 := rfl
  have powW : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) wSmall
  have two : 2 ≤ 2 ^ w := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) wPos)
  have slotLt : value % 2 ^^^ 1 < 2 := by
    rcases Nat.mod_two_eq_zero_or_one value with h | h <;> rw [h] <;> decide
  obtain ⟨mA, runA, subA, offA, bitsA, regsA⟩ :=
    exec_subLanes cells w rb layout wSmall remainder rbLe m inputs.remCells
  obtain ⟨mB, runB, ramB, bitsB, dB, regsB⟩ :=
    exec_lanePack cells.subBase 0 mA (materialize (reduceTo w remainder)) subA (by omega) (by norm_num)
  obtain ⟨mC, runC, ramC, bitsC, regsC⟩ := exec_storeAt_facts cells.active rD mB (by decide)
  obtain ⟨mD, runD, ramD, bitsD, regsD⟩ := exec_storeAt_facts cells.bitBase rD mC (by decide)
  obtain ⟨mE, runE, zE, offE, bitsE, regsE⟩ := exec_zeroCells cells.levelSumBase w mD
  obtain ⟨mF, runF, zF, offF, bitsF, regsF⟩ := exec_zeroCells cells.classBase (128 * (w + 1)) mE
  obtain ⟨mG, runG, zG, offG, bitsG, regsG⟩ := exec_zeroCells cells.castSumBase (128 * (w + 1)) mF
  -- RAM below the chain's scratch, and the scratch cells, through the zeroing and the stores
  have offGA : ∀ k, (k < cells.levelSumBase ∨ cells.castSumBase + 128 * (w + 1) ≤ k) → k < 2 ^ 256 →
      mG.ram (word k) = mD.ram (word k) := fun k hk kb => by
    rw [offG _ fun j jb => word_ne kb (by omega) (by omega),
      offF _ fun j jb => word_ne kb (by omega) (by omega),
      offE _ fun j jb => word_ne kb (by omega) (by omega)]
  have offDA : ∀ k, k ≠ cells.active → k ≠ cells.bitBase → k < 2 ^ 256 →
      mD.ram (word k) = mB.ram (word k) := fun k h1 h2 kb => by
    rw [ramD, Function.update_of_ne (word_ne kb (by omega) h2), ramC,
      Function.update_of_ne (word_ne kb (by omega) h1)]
  have dG : mG.registers rD = labelWord (laneBit (materialize (reduceTo w remainder)) 0) := by
    rw [regsG rD (by decide) (by decide), regsF rD (by decide) (by decide),
      regsE rD (by decide) (by decide), regsD rD (by decide), regsC rD (by decide), dB]
  have valueG : mG.ram (word cells.value) = word value := by
    rw [offGA _ (Or.inl (by omega)) (by omega), offDA _ (by omega) (by omega) (by omega), ramB,
      offA _ fun i ib => word_ne (by omega) (by omega) (by omega)]
    exact inputs.valueCell
  obtain ⟨mH, runH, ramH, bitsH, regsH⟩ := exec_prefixSlot cells mG value _ valueG (by omega) dG
    (by omega)
  have offH : ∀ k, k ≠ cells.slot → k ≠ cells.nodeBase + (value % 2 ^^^ 1) → k < 2 ^ 256 →
      mH.ram (word k) = mG.ram (word k) := fun k h1 h2 kb => by
    rw [ramH, Function.update_of_ne (word_ne kb (by omega) h2),
      Function.update_of_ne (word_ne kb (by omega) h1)]
  refine ⟨mH, ?_, ⟨fun L Lw => ?_, fun j jb i => ⟨?_, ?_⟩, ?_, fun b bLt => ?_, fun α _ αNe => ?_,
    fun i => ?_, ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩, ?_, ?_⟩
  · unfold stagePrefix
    rw [Prog.exec_seq_some _ _ m mA runA, Prog.exec_seq_some _ _ mA mB runB,
      Prog.exec_seq_some _ _ mB mC runC, Prog.exec_seq_some _ _ mC mD runD,
      Prog.exec_seq_some _ _ mD mE runE, Prog.exec_seq_some _ _ mE mF runF,
      Prog.exec_seq_some _ _ mF mG runG, runH]
  · rw [offH _ (by omega) (by omega) (by omega), offG _ fun j jb => word_ne (by omega) (by omega) (by omega),
      offF _ fun j jb => word_ne (by omega) (by omega) (by omega), zE L Lw]
    rfl
  · have iLt := i.isLt
    rw [offH _ (by omega) (by omega) (by omega), offG _ fun j' jb' => word_ne (by omega) (by omega) (by omega),
      Nat.add_assoc, zF _ (by omega)]
    show word 0 = word ((0 : ZMod (2 ^ rb)).val)
    rw [ZMod.val_zero]
  · have iLt := i.isLt
    rw [offH _ (by omega) (by omega) (by omega), Nat.add_assoc, zG _ (by omega)]
    show word 0 = word ((0 : ZMod (2 ^ rb)).val)
    rw [ZMod.val_zero]
  · rw [offH _ (by omega) (by omega) (by omega), offGA _ (Or.inr (by omega)) (by omega), ramD,
      Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), ramC, Function.update_self, dB]
    rfl
  · have b0 : b = 0 := by omega
    subst b0
    rw [Nat.add_zero, offH _ (by omega) (by omega) (by omega), offGA _ (Or.inr (by omega)) (by omega),
      ramD, Function.update_self, regsC rD (by decide), dB]
    rfl
  · exact absurd (by rw [pow_zero, Nat.mod_one, Nat.mod_one]) αNe
  · have iLt := i.isLt
    rw [offH _ (by omega) (by omega) (by omega), offGA _ (Or.inl (by omega)) (by omega),
      offDA _ (by omega) (by omega) (by omega), ramB]
    exact subA i
  · rw [ramH, Function.update_of_ne (ne_of_sw outside (sw_node cells w rb (x := value % 2 ^^^ 1) (by omega))),
      Function.update_of_ne (ne_of_sw outside (sw_slot cells w rb)),
      offG address fun k kb => ne_of_sw outside
        (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨k, kb, rfl⟩),
      offF address fun k kb => ne_of_sw outside
        (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨k, kb, rfl⟩),
      offE address fun k kb => ne_of_sw outside (sw_levelSum cells w rb kb), ramD,
      Function.update_of_ne (ne_of_sw outside (by simpa using sw_bit cells w rb (b := 0) (by omega))),
      ramC, Function.update_of_ne (ne_of_sw outside (sw_active cells w rb)), ramB,
      offA address fun i ib => ne_of_sw outside (sw_sub cells w rb ib)]
  · rw [bitsH, bitsG, bitsF, bitsE, bitsD, bitsC, bitsB, bitsA]
  · rw [regsH register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rF (by simp))
      (ne_of_not_stage outside rAddr (by simp)),
      regsG register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rAddr (by simp)),
      regsF register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rAddr (by simp)),
      regsE register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rAddr (by simp)),
      regsD register (ne_of_not_stage outside rAddr (by simp)),
      regsC register (ne_of_not_stage outside rAddr (by simp)),
      regsB register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rD (by simp))
        (ne_of_not_stage outside rE (by simp)) (ne_of_not_stage outside rAddr (by simp)),
      regsA register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rC (by simp))
        (ne_of_not_stage outside rAddr (by simp))]
  · rw [ramH, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), Function.update_self]
  · rw [ramH, Function.update_self]

/-! ### The final block -/

theorem exec_finalTail (cells : StageCells) (w rb i : Nat) (memory : Memory) (U Rv : Nat)
    (cReg : memory.registers rC = word U)
    (remCell : memory.ram (word (cells.remBase + i)) = word Rv)
    (rbLe : rb ≤ 128) (wSmall : w ≤ 64) (USmall : U < 2 ^ rb) (RvSmall : Rv < 2 ^ rb) :
    ∃ after, (finalTail cells w rb i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.nextBase + i))
        (word ((Rv + 2 ^ rb - U) % 2 ^ rb / 2 ^ w)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have powRb : 2 ^ rb ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) rbLe
  have modLt := Nat.mod_lt (Rv + 2 ^ rb - U) (Nat.two_pow_pos rb)
  refine ⟨_, rfl, ?_, rfl, fun register nB nE nAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte, cReg,
      remCell]
    rw [eval_add_word Rv (2 ^ rb) (by omega), eval_sub_word _ U (by omega) (by omega),
      eval_and_pow _ rb (by omega) (by omega), eval_shr_word _ w (by omega) (by omega)]
  · simp only [reg_setReg, reg_storeRam, if_neg nB, if_neg nE, if_neg nAddr]

theorem peel_value {rb : Nat} (w : Nat) (wLe : w ≤ rb) (remainder C P T : Lanes rb) (value : Nat)
    (i : Fin laneCount) :
    ((materialize (peelDiv remainder (materialize (C + scaleLanes value (P - T))) w)) i).val =
      ((remainder i).val + 2 ^ rb - (((P i).val + 2 ^ rb - (T i).val) * value + (C i).val) % 2 ^ rb) %
        2 ^ rb / 2 ^ w := by
  have split : 2 ^ (rb - w) * 2 ^ w = 2 ^ rb := by rw [← pow_add, Nat.sub_add_cancel wLe]
  rw [materialize_eq, peelDiv, ZMod.val_natCast, Pi.sub_apply, zmod_sub_val' (2 ^ rb) (Nat.two_pow_pos rb),
    materialize_eq, Pi.add_apply,
    show scaleLanes value (P - T) i = (value : ZMod (2 ^ rb)) * (P i - T i) from rfl, res_val]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w), split]
  exact Nat.mod_lt _ (Nat.two_pow_pos rb)

theorem exec_finalStore (cells : StageCells) (memory : Memory) (value : Nat) (A : Label)
    (fReg : memory.registers rF = word value)
    (activeCell : memory.ram (word cells.active) = labelWord A)
    (small : cells.nodeBase + value < 2 ^ 256) :
    ∃ after, (Prog.seq (loadAt rE cells.active) (.seq (cst rB cells.nodeBase)
        (.seq (ar .add rAddr rF rB) (.op (.store rAddr rE))))).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.nodeBase + value)) (labelWord A) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register nB nE nAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte, fReg,
      activeCell]
    rw [eval_add_word value cells.nodeBase (by omega), Nat.add_comm value cells.nodeBase]
  · simp only [reg_setReg, reg_storeRam, if_neg nB, if_neg nE, if_neg nAddr]

/-- **The final block**: the next remainder lane by lane, and the active leaf's label at node `s`. -/
theorem exec_stageFinal (cells : StageCells) (w rb value : Nat) (remainder pin C T : Lanes rb)
    (layout : StageLayout cells w rb) (rbLe : rb ≤ 128) (wSmall : w ≤ 64) (wLe : w ≤ rb)
    (valueLt : value < 2 ^ w) (A : Label) (m : Memory)
    (valueCell : m.ram (word cells.value) = word value)
    (remCells : ∀ i : Fin laneCount, m.ram (word (cells.remBase + i.val)) = word (remainder i).val)
    (pinCells : ∀ i : Fin laneCount, m.ram (word (cells.pinBase + i.val)) = word ((pin i).val / 2))
    (pinEven : Parity.EvenLanes pin)
    (classCells : ∀ i : Fin laneCount,
      m.ram (word (cells.classBase + 128 * w + i.val)) = word (C i).val)
    (castCells : ∀ i : Fin laneCount,
      m.ram (word (cells.castSumBase + 128 * w + i.val)) = word (T i).val)
    (activeCell : m.ram (word cells.active) = labelWord A) :
    ∃ m1, (stageFinal cells w rb).exec m = some m1 ∧
      (∀ i : Fin laneCount, m1.ram (word (cells.nextBase + i.val)) =
        word ((materialize (peelDiv remainder (materialize (C + scaleLanes value (pin - T))) w)) i).val) ∧
      m1.ram (word (cells.nodeBase + value)) = labelWord A ∧
      (∀ address, (∀ i, i < laneCount → address ≠ word (cells.nextBase + i)) →
        address ≠ word (cells.nodeBase + value) → m1.ram address = m.ram address) ∧
      m1.bits = m.bits ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rF → register ≠ rAddr →
        m1.registers register = m.registers register := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have c1 := layout.c1; have c2 := layout.c2; have c3 := layout.c3; have c4 := layout.c4
  have lc : laneCount = 104 := rfl
  have powW : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) wSmall
  haveI : NeZero (2 ^ rb) := ⟨by positivity⟩
  set m0 := setReg (setReg m rAddr (word cells.value)) rF (m.ram (word cells.value)) with m0Def
  have ram0 : m0.ram = m.ram := by rw [m0Def, ram_setReg, ram_setReg]
  have f0 : m0.registers rF = word value := by rw [m0Def, reg_setReg, if_pos rfl, valueCell]
  obtain ⟨mL, runL, nextL, frameL, bitsL, fL, regsL⟩ := Prog.exec_rep (finalLane cells w rb)
    (fun i current =>
      (∀ i' (b : i' < laneCount), i' < i → current.ram (word (cells.nextBase + i')) =
        word ((materialize (peelDiv remainder (materialize (C + scaleLanes value (pin - T))) w))
          ⟨i', b⟩).val) ∧
      (∀ address, (∀ i', i' < laneCount → address ≠ word (cells.nextBase + i')) →
        current.ram address = m.ram address) ∧
      current.bits = m.bits ∧ current.registers rF = word value ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        current.registers register = m0.registers register)
    laneCount (fun i bound current holds => by
      obtain ⟨done, frame, bits, fReg, regs⟩ := holds
      have off : ∀ k, k < cells.nextBase → k < 2 ^ 256 → current.ram (word k) = m.ram (word k) :=
        fun k hk kb => frame _ fun i' ib => word_ne kb (by omega) (by omega)
      obtain ⟨m2, run2, ram2, bits2, c2, regs2⟩ := exec_roundRes cells rb w i current value
        (pin ⟨i, bound⟩).val (T ⟨i, bound⟩).val (C ⟨i, bound⟩).val fReg
        (by rw [off _ (by omega) (by omega)]; exact pinCells ⟨i, bound⟩) (pinEven ⟨i, bound⟩)
        (by rw [off _ (by omega) (by omega)]; exact castCells ⟨i, bound⟩)
        (by rw [off _ (by omega) (by omega)]; exact classCells ⟨i, bound⟩)
        rbLe (by omega) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
      obtain ⟨m3, run3, ram3, bits3, regs3⟩ := exec_finalTail cells w rb i m2 _ (remainder ⟨i, bound⟩).val
        c2 (by rw [ram2, off _ (by omega) (by omega)]; exact remCells ⟨i, bound⟩) rbLe wSmall
        (Nat.mod_lt _ (Nat.two_pow_pos rb)) (ZMod.val_lt _)
      refine ⟨m3, ?_, fun i' b lt => ?_, fun address offN => ?_, by rw [bits3, bits2, bits], ?_,
        fun register nB nC nE nAddr => ?_⟩
      · unfold finalLane; rw [Prog.exec_seq_some _ _ current m2 run2, run3]
      · rw [ram3]
        by_cases last : i' = i
        · subst last
          rw [Function.update_self, peel_value w wLe]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), ram2]
          exact done i' b (by omega)
      · rw [ram3, Function.update_of_ne (offN i bound), ram2]; exact frame address offN
      · rw [regs3 rF (by decide) (by decide) (by decide), regs2 rF (by decide) (by decide) (by decide)
          (by decide)]
        exact fReg
      · rw [regs3 register nB nE nAddr, regs2 register nB nC nE nAddr, regs register nB nC nE nAddr])
    m0 ⟨fun _ _ lt => absurd lt (Nat.not_lt_zero _), fun _ _ => by rw [ram0], by rw [m0Def, bits_setReg,
      bits_setReg], f0, fun _ _ _ _ _ => rfl⟩
  have activeL : mL.ram (word cells.active) = labelWord A := by
    rw [frameL _ fun i ib => word_ne (by omega) (by omega) (by omega)]; exact activeCell
  obtain ⟨m1, run1, ram1, bits1, regs1⟩ := exec_finalStore cells mL value A fL activeL (by omega)
  refine ⟨m1, ?_, fun i => ?_, ?_, fun address offN offV => ?_, by rw [bits1, bitsL],
    fun register nB nC nE nF nAddr => ?_⟩
  · unfold stageFinal
    rw [exec_loadAt_seq, ← m0Def, Prog.exec_seq_some _ _ m0 mL runL, run1]
  · rw [ram1, Function.update_of_ne (word_ne (by omega) (by omega) (by have := i.isLt; omega))]
    exact nextL i.val i.isLt i.isLt
  · rw [ram1, Function.update_self]
  · rw [ram1, Function.update_of_ne offV]
    exact frameL address offN
  · rw [regs1 register nB nE nAddr, regsL register nB nC nE nAddr, m0Def, reg_setReg, if_neg nF,
      reg_setReg, if_neg nAddr]

/-! ### Determinism of the straight-line blocks -/

theorem det_subLane (cells : StageCells) (w i : Nat) : (subLane cells w i).OpsSatisfy Op.Det := by
  unfold subLane; simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

theorem det_packLane (base b i : Nat) : (packLane base b i).OpsSatisfy Op.Det := by
  unfold packLane bitInsert; simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

theorem det_lanePack (base b : Nat) : (lanePack base b).OpsSatisfy Op.Det := by
  unfold lanePack
  exact ⟨trivial, det_rep _ _ fun i _ => det_packLane base b i⟩

theorem det_zeroCells (base count : Nat) : (zeroCells base count).OpsSatisfy Op.Det := by
  unfold zeroCells
  exact ⟨trivial, det_rep _ _ fun k _ => ⟨trivial, trivial⟩⟩

theorem det_prefixSlot (cells : StageCells) : (prefixSlot cells).OpsSatisfy Op.Det := by
  unfold prefixSlot; simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

theorem det_stagePrefix (cells : StageCells) (w : Nat) : (stagePrefix cells w).OpsSatisfy Op.Det := by
  unfold stagePrefix
  exact ⟨det_rep _ _ fun i _ => det_subLane cells w i, det_lanePack _ _, ⟨trivial, trivial⟩,
    ⟨trivial, trivial⟩, det_zeroCells _ _, det_zeroCells _ _, det_zeroCells _ _, det_prefixSlot cells⟩

theorem det_finalLane (cells : StageCells) (w rb i : Nat) : (finalLane cells w rb i).OpsSatisfy Op.Det := by
  unfold finalLane finalTail roundRes resHead resTail
  simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

theorem det_stageFinal (cells : StageCells) (w rb : Nat) : (stageFinal cells w rb).OpsSatisfy Op.Det := by
  unfold stageFinal
  exact ⟨⟨trivial, trivial⟩, det_rep _ _ fun i _ => det_finalLane cells w rb i, ⟨trivial, trivial⟩,
    trivial, trivial, trivial⟩

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **Round `n`** (`1 ≤ n < w`) against `stageRoundM`: from `n` levels closed and `n` bits known to
`n + 1` of each. -/
theorem agree_roundReplay (cells : StageCells) (w rb value : Nat) (sub : Lanes w)
    (remainder : Lanes rb) (joins : Nat → Label) (pin : Lanes rb) (layout : StageLayout cells w rb)
    (rbPos : 0 < rb) (rbLe : rb ≤ 128) (wSmall : w ≤ 64)
    (treeBase : Nat → Nat) (castBase stride : Nat) (strideSmall : stride < 2 ^ 64)
    (treeTag castTag : Nat → Nat → Nat)
    (hTag : ∀ L x, L < w → treeTag L x = treeBase L + stride * x)
    (tagSmall : ∀ L x, L < w → x < 2 ^ w → treeBase L + stride * x < 2 ^ 127)
    (hCast : ∀ x part, castTag x part = castBase + stride * x + part)
    (castSmall : ∀ x, x < 2 ^ w → castBase + stride * x + castAnswers rb < 2 ^ 127)
    (n : Nat) (nPos : 1 ≤ n) (nLt : n + 1 ≤ w) (valueLt : value < 2 ^ w) (mStart : Memory)
    (inputs : StageInputs cells w rb value remainder joins pin mStart) (state : StageState rb)
    (m : Memory) (rel : StageRel cells w rb value sub n n mStart state m) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (StageRel cells w rb value sub (n + 1) (n + 1) mStart)
      ((roundReplay cells w rb n treeBase castBase stride).tree m)
      (liftHash (stageRoundM w treeTag castTag sub value joins pin n state)) := by
  obtain ⟨m1, run1, rel1, slot1, node1⟩ := exec_roundPrefix cells w rb value sub remainder joins pin
    layout rbLe wSmall n nPos (by omega) valueLt mStart inputs state m rel
  unfold roundReplay stageRoundM
  rw [tree_seq_exec _ _ (det_roundPrefix cells w rb n) m m1 run1]
  dsimp only
  by_cases hb : value.testBit n
  · rw [if_pos hb]
    have slotEq : roundSlot value n = value % 2 ^ n := by unfold roundSlot; rw [if_pos hb]
    have stateEq : roundState w sub pin joins value n state =
        { state with active := roundHotLabel w sub pin joins value n state,
                     bits := fun k => if k = n then roundBitLabel w sub pin value n state
                       else state.bits k } := by
      unfold roundState; rw [if_pos hb]
    rw [stateEq] at rel1
    rw [slotEq] at slot1 node1
    rw [if_pos hb] at node1
    have lt := roundSlot_lt value n
    rw [slotEq] at lt
    exact agree_expandReplay cells w rb value sub layout rbPos rbLe wSmall treeBase castBase stride
      strideSmall treeTag castTag hTag tagSmall hCast castSmall n (n + 1) nLt nLt (value % 2 ^ n) lt
      (Nat.mod_mod _ _) (by have := roundSlot_ne value n; rwa [slotEq] at this) _ mStart _ m1 rel1
      slot1 node1
  · rw [if_neg hb]
    have slotEq : roundSlot value n = value % 2 ^ n + 2 ^ n := by unfold roundSlot; rw [if_neg hb]
    have stateEq : roundState w sub pin joins value n state =
        { state with active := state.active ^^^ roundHotLabel w sub pin joins value n state,
                     bits := fun k => if k = n then roundBitLabel w sub pin value n state
                       else state.bits k } := by
      unfold roundState; rw [if_neg hb]
    rw [stateEq] at rel1
    rw [slotEq] at slot1 node1
    rw [if_neg hb] at node1
    have lt := roundSlot_lt value n
    rw [slotEq] at lt
    have low := roundSlot_low value n
    rw [slotEq] at low
    exact agree_expandReplay cells w rb value sub layout rbPos rbLe wSmall treeBase castBase stride
      strideSmall treeTag castTag hTag tagSmall hCast castSmall n (n + 1) nLt nLt
      (value % 2 ^ n + 2 ^ n) lt low (by have := roundSlot_ne value n; rwa [slotEq] at this) _ mStart
      _ m1 rel1 slot1 node1

/-- **The rounds `1 .. count`** against `stageRoundsM`. -/
theorem agree_roundsReplay (cells : StageCells) (w rb value : Nat) (sub : Lanes w)
    (remainder : Lanes rb) (joins : Nat → Label) (pin : Lanes rb) (layout : StageLayout cells w rb)
    (rbPos : 0 < rb) (rbLe : rb ≤ 128) (wSmall : w ≤ 64)
    (treeBase : Nat → Nat) (castBase stride : Nat) (strideSmall : stride < 2 ^ 64)
    (treeTag castTag : Nat → Nat → Nat)
    (hTag : ∀ L x, L < w → treeTag L x = treeBase L + stride * x)
    (tagSmall : ∀ L x, L < w → x < 2 ^ w → treeBase L + stride * x < 2 ^ 127)
    (hCast : ∀ x part, castTag x part = castBase + stride * x + part)
    (castSmall : ∀ x, x < 2 ^ w → castBase + stride * x + castAnswers rb < 2 ^ 127)
    (valueLt : value < 2 ^ w) (mStart : Memory)
    (inputs : StageInputs cells w rb value remainder joins pin mStart) :
    ∀ (count : Nat), count + 1 ≤ w → ∀ (state : StageState rb) (m : Memory),
      StageRel cells w rb value sub 1 1 mStart state m →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
        (StageRel cells w rb value sub (count + 1) (count + 1) mStart)
        ((Prog.rep count fun k => roundReplay cells w rb (k + 1) treeBase castBase stride).tree m)
        (liftHash (stageRoundsM w treeTag castTag sub value joins pin count 1 state))
  | 0, _, state, m, rel => by
      rw [Prog.rep, stageRoundsM]
      exact .leaf rel
  | count + 1, le, state, m, rel => by
      rw [Prog.rep, tree_seq, stageRoundsM_snoc, liftHash_bind]
      refine Agree.bindOpt (fun state' m' rel' => ?_)
        (agree_roundsReplay cells w rb value sub remainder joins pin layout rbPos rbLe wSmall treeBase
          castBase stride strideSmall treeTag castTag hTag tagSmall hCast castSmall valueLt mStart inputs
          count (by omega) state m rel)
      rw [show 1 + count = count + 1 by omega]
      exact agree_roundReplay cells w rb value sub remainder joins pin layout rbPos rbLe wSmall treeBase
        castBase stride strideSmall treeTag castTag hTag tagSmall hCast castSmall (count + 1) (by omega)
        (by omega) valueLt mStart inputs state' m' rel'

/-- **The replay of one fused extraction stage** (package M4a) against the evaluator
`extStageEvalM`, in round order: the same questions in the same order, and at the end
the leaves `α < 2 ^ w` at `nodeBase + α`, the bit labels at `bitBase + n`, the next remainder's lanes
at `nextBase + i`, with the frame of `stageWrites` and `stageClobbers`. -/
theorem agree_stageReplay (cells : StageCells) (w rb value : Nat) (remainder : Lanes rb)
    (joins : Nat → Label) (pin : Lanes rb) (layout : StageLayout cells w rb)
    (rbLe : rb ≤ 128) (wPos : 1 ≤ w) (wLe : w ≤ rb) (wSmall : w ≤ 64)
    (treeBase : Nat → Nat) (castBase stride : Nat) (strideSmall : stride < 2 ^ 64)
    (treeTag castTag : Nat → Nat → Nat)
    (hTag : ∀ L x, L < w → treeTag L x = treeBase L + stride * x)
    (tagSmall : ∀ L x, L < w → x < 2 ^ w → treeBase L + stride * x < 2 ^ 127)
    (hCast : ∀ x part, castTag x part = castBase + stride * x + part)
    (castSmall : ∀ x, x < 2 ^ w → castBase + stride * x + castAnswers rb < 2 ^ 127)
    (valueLt : value < 2 ^ w) (m : Memory)
    (inputs : StageInputs cells w rb value remainder joins pin m) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (out : StageEval rb w) after =>
        (∀ α, α < 2 ^ w → after.ram (word (cells.nodeBase + α)) = labelWord (out.leaves α)) ∧
        (∀ n, n < w → after.ram (word (cells.bitBase + n)) = labelWord (out.bits n)) ∧
        (∀ i : Fin laneCount, after.ram (word (cells.nextBase + i.val)) = word (out.next i).val) ∧
        Frame (stageWrites cells w rb) stageClobbers m after)
      ((stageReplay cells w rb treeBase castBase stride).tree m)
      (liftHash (extStageEvalM w treeTag castTag remainder value joins pin)) := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have lc : laneCount = 104 := rfl
  have rbPos : 0 < rb := by omega
  have slotLt : value % 2 ^^^ 1 < 2 := by
    rcases Nat.mod_two_eq_zero_or_one value with h | h <;> rw [h] <;> decide
  have slotNe : value % 2 ^^^ 1 ≠ value % 2 := by
    rcases Nat.mod_two_eq_zero_or_one value with h | h <;> rw [h] <;> decide
  obtain ⟨m1, run1, rel1, slot1, node1⟩ := exec_stagePrefix cells w rb value remainder joins pin layout
    rbLe wSmall wPos valueLt m inputs
  unfold stageReplay extStageEvalM
  rw [tree_seq_exec _ _ (det_stagePrefix cells w) m m1 run1]
  dsimp only
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun afterZero m2 rel2 => ?_)
    (agree_expandReplay cells w rb value (materialize (reduceTo w remainder)) layout rbPos rbLe wSmall
      treeBase castBase stride strideSmall treeTag castTag hTag tagSmall hCast castSmall 0 1
      (by omega) (by omega) (value % 2 ^^^ 1) (by simpa using slotLt)
      (by simp [pow_zero, Nat.mod_one]) (by simpa using slotNe) _ m (stageStart w remainder) m1 rel1
      slot1 node1)
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun final m3 rel3 => ?_)
    (agree_roundsReplay cells w rb value (materialize (reduceTo w remainder)) remainder joins pin layout
      rbPos rbLe wSmall treeBase castBase stride strideSmall treeTag castTag hTag tagSmall hCast
      castSmall valueLt m inputs (w - 1) (by omega) afterZero m2 rel2)
  rw [show w - 1 + 1 = w by omega] at rel3
  have in3 := inputs.at layout rel3.frame
  obtain ⟨m4, run4, next4, node4, frame4, bits4, regs4⟩ := exec_stageFinal cells w rb value remainder pin
    (final.classSum w) (final.castSum w) layout rbLe wSmall wLe valueLt final.active m3 in3.valueCell
    in3.remCells in3.pinCells in3.pinEven (fun i => (rel3.sums w le_rfl i).1) (fun i => (rel3.sums w le_rfl i).2)
    rel3.active
  rw [tree_eq_exec _ (det_stageFinal cells w rb), run4]
  refine .leaf ⟨fun α αb => ?_, fun n nLt => ?_, fun i => ?_, ⟨fun address outside => ?_, ?_,
    fun register outside => ?_⟩⟩
  · simp only [atNat, dif_pos αb, stored_eq]
    by_cases here : α = value
    · subst here
      rw [if_pos rfl]
      exact node4
    · rw [if_neg here, frame4 _ (fun i ib => word_ne (by omega) (by omega) (by omega))
        (word_ne (by omega) (by omega) (by omega))]
      exact rel3.leaves α αb (by rwa [Nat.mod_eq_of_lt αb, Nat.mod_eq_of_lt valueLt])
  · simp only [atNat, dif_pos nLt, stored_eq]
    rw [frame4 _ (fun i ib => word_ne (by omega) (by omega) (by omega))
      (word_ne (by omega) (by omega) (by omega))]
    exact rel3.bits n nLt
  · exact next4 i
  · rw [frame4 address (fun i ib => ne_of_sw outside (sw_next cells w rb ib))
      (ne_of_sw outside (sw_node cells w rb valueLt))]
    exact rel3.frame.ram address outside
  · rw [bits4, rel3.frame.bits]
  · rw [regs4 register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rC (by simp))
      (ne_of_not_stage outside rE (by simp)) (ne_of_not_stage outside rF (by simp))
      (ne_of_not_stage outside rAddr (by simp))]
    exact rel3.frame.registers register outside

end Agreement

end Kriterion.CRT.SimMachine
