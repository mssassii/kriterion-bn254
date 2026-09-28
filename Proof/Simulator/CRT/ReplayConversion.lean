/-
**The replay of the conversion of one odd modulus agrees with `conversionEvalM`** (package M5b,
the conversion part; `Construction/Simulator/CRT/ReplayConversion.lean`).

Part 1: the results of a program (`AllResults`, to carry `hot < m` out of the folds), the layout
of a stage chain, the window, and the small blocks.
-/

import Proof.Simulator.CRT.ReplayExtractStage
import Proof.Simulator.CRT.ReplayFold
import Proof.Simulator.CRT.ReplayChunks
import Construction.Simulator.CRT.ReplayConversion

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### Properties of every result of a program -/

/-- Every result of the program satisfies `Q`, whatever the answers. -/
inductive AllResults {spec : OracleSpec.{0, 0}} {α : Type} (Q : α → Prop) : FreeQuery spec α → Prop
  | pure {value : α} (holds : Q value) : AllResults Q (.pure value)
  | query (request : spec.Query) {next : spec.Answer request → FreeQuery spec α}
      (each : ∀ answer, AllResults Q (next answer)) : AllResults Q (.query request next)

theorem AllResults.of_forall {spec : OracleSpec.{0, 0}} {α : Type} {Q : α → Prop}
    (always : ∀ value, Q value) : ∀ program : FreeQuery spec α, AllResults Q program
  | .pure _ => .pure (always _)
  | .query request next => .query request fun answer => AllResults.of_forall always (next answer)

theorem AllResults.bind {spec : OracleSpec.{0, 0}} {α β : Type} {Q : β → Prop}
    {f : α → FreeQuery spec β} :
    ∀ {program : FreeQuery spec α}, AllResults (fun value => AllResults Q (f value)) program →
      AllResults Q (FreeQuery.bind program f)
  | _, .pure holds => holds
  | _, .query request each => .query request fun answer => AllResults.bind (each answer)

theorem AllResults.liftHash {α : Type} {Q : α → Prop} {FixedIndex EncIndex : Type} :
    ∀ {program : CM α}, AllResults Q program →
      AllResults Q (Kriterion.CRT.liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) program)
  | _, .pure holds => .pure holds
  | _, .query _ each => .query _ fun answer => AllResults.liftHash (each answer)

theorem foldsEvalM_hot_lt (m : Nat) (mPos : 0 < m) (tagOf : Nat → Nat → Nat) (value : Nat)
    (bitLabel join : Nat → Label) :
    ∀ (count start hot : Nat) (labels : Fin m → Label), hot < m →
      AllResults (fun result : (Fin m → Label) × Nat => result.2 < m)
        (foldsEvalM m tagOf value bitLabel join count start hot labels)
  | 0, _, _, _, hotLt => .pure hotLt
  | count + 1, start, hot, labels, _ => by
      rw [foldsEvalM, TreeLaws.monad_bind]
      exact AllResults.bind (AllResults.of_forall (fun next =>
        foldsEvalM_hot_lt m mPos tagOf value bitLabel join count (start + 1) _ next
          (Nat.mod_lt _ mPos)) _)

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- An agreement whose abstract results all satisfy `Q` ends in leaves that satisfy `Q`. -/
theorem Agree.withResults {β : Type} {Post : β → Memory → Prop} {Q : β → Prop} :
    ∀ {tree : FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)}
      {tree' : FreeQuery (publicOracleSpec FixedIndex EncIndex) β},
      Agree Post tree tree' → AllResults Q tree' →
        Agree (fun value memory => Post value memory ∧ Q value) tree tree'
  | _, _, .leaf related, .pure holds => .leaf ⟨related, holds⟩
  | _, _, .node request each, .query _ results =>
      .node request fun answer => Agree.withResults (each answer) (results answer)

end Agreement

/-! ### Widths and the layout of a stage chain -/

theorem castAnswers_le_128 (l : Nat) (h1 : 1 ≤ l) (h2 : l ≤ 128) : castAnswers l ≤ 128 := by
  unfold castAnswers castBlocks lanesPerBlock
  have lb : labelBits = 104 := rfl
  rw [lb]
  have p1 : 1 ≤ 128 / l := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have : (104 + 128 / l - 1) / (128 / l) ≤ 128 := Nat.div_le_of_le_mul (by omega)
  omega

theorem stageChain_layout (S w rb value remBase joinBase pinBase : Nat) (wPos : 1 ≤ w) (wLe : w ≤ 12)
    (rbPos : 1 ≤ rb) (rbLe : rb ≤ 128) (hv : value < S) (hr : remBase + 128 ≤ S)
    (hj : joinBase + w ≤ S) (hp : pinBase + 128 ≤ S) (fits : S + 2 ^ 14 < 2 ^ 256) :
    StageLayout (stageChain S w rb value remBase joinBase pinBase) w rb ∧
      (stageChain S w rb value remBase joinBase pinBase).nextBase + 128 ≤ S + 2 ^ 14 := by
  have ca := castAnswers_le_128 rb rbPos rbLe
  have pw : 2 ^ w ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) wLe
  have hw := Nat.two_pow_pos w
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [stageChain] <;> omega

theorem sw_chain_in (S w rb value remBase joinBase pinBase : Nat) (wLe : w ≤ 12) (rbPos : 1 ≤ rb)
    (rbLe : rb ≤ 128) {a : Word}
    (h : stageWrites (stageChain S w rb value remBase joinBase pinBase) w rb a) :
    ∃ k, S ≤ k ∧ k < S + 2 ^ 14 ∧ a = word k := by
  have ca := castAnswers_le_128 rb rbPos rbLe
  have pw : 2 ^ w ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) wLe
  have hw := Nat.two_pow_pos w
  have lc : laneCount = 104 := rfl
  simp only [stageWrites, Writes.union, Writes.region, Writes.cell, Region.Holds, stageChain] at h
  rcases h with ⟨j, jb, h⟩ | ⟨j, jb, h⟩ | ⟨j, jb, h⟩ | ⟨j, jb, h⟩ | ⟨j, jb, h⟩ | ⟨j, jb, h⟩ |
    ⟨j, jb, h⟩ | ⟨j, jb, h⟩ | h | h | ⟨j, jb, h⟩ | ⟨j, jb, h⟩ <;>
    exact ⟨_, by omega, by omega, h⟩

/-! ### The window -/

theorem inConv (W k : Nat) (lo : W + 256 ≤ k) (hi : k < W + 2 ^ 18) : convWrites W (word k) := by
  show ∃ j, j < 2 ^ 18 - 256 ∧ word k = word (W + 256 + j)
  exact ⟨k - (W + 256), by omega, by rw [show W + 256 + (k - (W + 256)) = k by omega]⟩

theorem ne_of_not_conv {W : Nat} {a : Word} (outside : ¬ convWrites W a) {k : Nat}
    (lo : W + 256 ≤ k) (hi : k < W + 2 ^ 18) : a ≠ word k :=
  fun same => outside (same ▸ inConv W k lo hi)

theorem ne_of_not_convRegs {register : Register} (outside : ¬ convClobbers register) (other : Register)
    (inside : other ∈ [rA, rB, rC, rD, rE, rF, rAddr, rInput, rFirst, rSecond, rAcc, rOut]) :
    register ≠ other := fun same => outside (by rw [same]; exact inside)

/-- A block's frame, weakened into the window's, composed after the window's frame so far. -/
theorem Frame.conv_step {W : Nat} {m0 m m' : Memory} {writes : Writes} {clobbers : Clobbers}
    (before : Frame (convWrites W) convClobbers m0 m) (step : Frame writes clobbers m m')
    (inWindow : ∀ a, writes a → convWrites W a) (inRegs : ∀ r, clobbers r → convClobbers r) :
    Frame (convWrites W) convClobbers m0 m' :=
  (before.trans step).mono (fun a h => h.elim id (inWindow a)) (fun r h => h.elim id (inRegs r))

theorem stageClobbers_sub (register : Register) (inside : stageClobbers register) :
    convClobbers register := by
  unfold stageClobbers convClobbers Clobbers.ofList at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
  rcases inside with h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem treeStepClobbers_sub (register : Register) (inside : treeStepClobbers register) :
    convClobbers register := by
  unfold treeStepClobbers convClobbers Clobbers.ofList at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
  rcases inside with h | h | h | h | h | h | h | h | h <;> simp [h]

/-! ### The small blocks -/

theorem exec_stageValue0 (W w0 : Nat) (memory : Memory) (value : Nat)
    (sigmaCell : memory.ram (word (W + 128)) = word value) (valueSmall : value < 2 ^ 256)
    (w0Small : w0 < 256) :
    ∃ after, (stageValue0 W w0).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (W + 256)) (word (value % 2 ^ w0)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register nA nB nAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte,
      sigmaCell]
    rw [eval_and_pow value w0 valueSmall w0Small]
  · simp only [reg_setReg, reg_storeRam, if_neg nA, if_neg nB, if_neg nAddr]

theorem exec_stageValue1 (W w0 w1 : Nat) (memory : Memory) (value : Nat)
    (sigmaCell : memory.ram (word (W + 128)) = word value) (valueSmall : value < 2 ^ 256)
    (w0Small : w0 < 256) (w1Small : w1 < 256) :
    ∃ after, (stageValue1 W w0 w1).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (W + 257)) (word (value / 2 ^ w0 % 2 ^ w1)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have divSmall : value / 2 ^ w0 < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) valueSmall
  refine ⟨_, rfl, ?_, rfl, fun register nA nB nAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte,
      sigmaCell]
    rw [eval_shr_word value w0 valueSmall (by omega), eval_and_pow _ w1 divSmall w1Small]
  · simp only [reg_setReg, reg_storeRam, if_neg nA, if_neg nB, if_neg nAddr]

theorem det_stageValue0 (W w0 : Nat) : (stageValue0 W w0).OpsSatisfy Op.Det := by
  unfold stageValue0; simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

theorem det_stageValue1 (W w0 w1 : Nat) : (stageValue1 W w0 w1).OpsSatisfy Op.Det := by
  unfold stageValue1; simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

theorem det_lastBitProg (W nextBase : Nat) : (lastBitProg W nextBase).OpsSatisfy Op.Det := by
  unfold lastBitProg
  exact ⟨det_lanePack _ _, ⟨trivial, trivial⟩⟩

theorem det_reindexBlock (levelBase vecBase n m : Nat) :
    (reindexBlock levelBase vecBase n m).OpsSatisfy Op.Det := by
  unfold reindexBlock
  refine det_rep _ _ fun ρ _ => ?_
  unfold reindexResidue
  refine ⟨trivial, det_rep _ _ fun leaf _ => ?_, ⟨trivial, trivial⟩⟩
  unfold reindexStep
  split
  · exact ⟨⟨trivial, trivial⟩, trivial⟩
  · trivial

theorem det_hotInit (cells : FoldCells) (keep m : Nat) : (hotInit cells keep m).OpsSatisfy Op.Det := by
  unfold hotInit
  exact ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, det_barrett _ _ _ _, ⟨trivial, trivial⟩⟩

theorem exec_lastBitProg {l : Nat} (W nextBase : Nat) (memory : Memory) (lanes : Lanes l)
    (laneCells : ∀ i : Fin laneCount, memory.ram (word (nextBase + i.val)) = word (lanes i).val)
    (lSmall : l ≤ 256) :
    ∃ after, (lastBitProg W nextBase).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (W + 258)) (labelWord (laneBit lanes 0)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rD → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨m1, run1, ram1, bits1, d1, regs1⟩ := exec_lanePack nextBase 0 memory lanes laneCells lSmall
    (by norm_num)
  obtain ⟨m2, run2, ram2, bits2, regs2⟩ := exec_storeAt_facts (W + 258) rD m1 (by decide)
  refine ⟨m2, by rw [lastBitProg, Prog.exec_seq_some _ _ memory m1 run1, run2], ?_, by rw [bits2, bits1],
    fun register nB nD nE nAddr => by rw [regs2 register nAddr, regs1 register nB nD nE nAddr]⟩
  rw [ram2, ram1, d1]

/-! ### Tags -/

theorem extTreeTag_affine (coord i q L x : Nat) :
    extTreeTag coord i q L x = extTreeTag coord i q L 0 + 64 * x := by
  unfold extTreeTag tagCode; ring

theorem extCastTag_affine (coord i q x part : Nat) :
    extCastTag coord i q x part = extCastTag coord i q 0 0 + 64 * x + part := by
  unfold extCastTag tagCode; ring

theorem extTreeTag_small (coord i q L x : Nat) (hc : coord < 2) (hi : i < 128) (hq : q < 4)
    (hL : L < 16) (hx : x < 2 ^ 16) : extTreeTag coord i q L 0 + 64 * x < 2 ^ 127 := by
  unfold extTreeTag tagCode Family.extTree; omega

theorem extCastTag_small (coord i q x extra : Nat) (hc : coord < 2) (hi : i < 128) (hq : q < 4)
    (hx : x < 2 ^ 16) (he : extra ≤ 128) : extCastTag coord i q 0 0 + 64 * x + extra < 2 ^ 127 := by
  unfold extCastTag tagCode Family.extCast; omega

theorem growTag_small (coord i L s : Nat) (hc : coord < 2) (hi : i < 128) (hL : L < 16)
    (hs : s < 2 ^ 16) : growTag coord i L s < 2 ^ 127 := by
  unfold growTag tagCode Family.grow; omega

theorem foldTag_small (coord i L ρ : Nat) (hc : coord < 2) (hi : i < 128) (hL : L < 256)
    (hρ : ρ < 2 ^ 16) : foldTag coord i L ρ < 2 ^ 127 := by
  unfold foldTag tagCode Family.fold; omega

/-! ### The layout of the window -/

section Layout

variable (row : OddRow) (W : Nat) (joinBase pinBase : Nat → Nat)

theorem convStage_layouts (w0Pos : 1 ≤ row.width0) (w1Pos : 1 ≤ row.width1) (w0Le : row.width0 ≤ 12)
    (w1Le : row.width1 ≤ 12) (ellEq : row.width0 + row.width1 + 1 = row.ell)
    (fits : W + 2 ^ 18 < 2 ^ 256) (joinBelow : ∀ q, q < 2 → joinBase q + 16 ≤ W)
    (pinBelow : ∀ q, q < 2 → pinBase q + 128 ≤ W) :
    StageLayout (convStage0 row W (joinBase 0) (pinBase 0)) row.width0 row.ell ∧
      (convStage0 row W (joinBase 0) (pinBase 0)).nextBase + 128 ≤ W + 2 ^ 15 ∧
      StageLayout (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)) row.width1
        (row.ell - row.width0) ∧
      (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).nextBase + 128 ≤
        W + 2 ^ 15 + 2 ^ 14 := by
  have j0 := joinBelow 0 (by norm_num); have j1 := joinBelow 1 (by norm_num)
  have p0 := pinBelow 0 (by norm_num); have p1 := pinBelow 1 (by norm_num)
  obtain ⟨l0, e0⟩ := stageChain_layout (W + 2 ^ 14) row.width0 row.ell (W + 256) W (joinBase 0)
    (pinBase 0) w0Pos w0Le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e0' : (convStage0 row W (joinBase 0) (pinBase 0)).nextBase + 128 ≤ W + 2 ^ 15 :=
    le_trans e0 (by omega)
  obtain ⟨l1, e1⟩ := stageChain_layout (W + 2 ^ 15) row.width1 (row.ell - row.width0) (W + 257)
    (convStage0 row W (joinBase 0) (pinBase 0)).nextBase (joinBase 1) (pinBase 1) w1Pos w1Le (by omega)
    (by omega) (by omega) e0' (by omega) (by omega) (by omega)
  exact ⟨l0, e0', l1, e1⟩

/-- The bit labels the growth and the folds read, where they lie. -/
def BitsHeld (bits0 bits1 : Nat → Label) (last : Label) (m : Memory) : Prop :=
  (∀ n, n < row.width0 →
      m.ram (word ((convStage0 row W (joinBase 0) (pinBase 0)).bitBase + n)) = labelWord (bits0 n)) ∧
    (∀ n, n < row.width1 →
      m.ram (word ((convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).bitBase + n)) =
        labelWord (bits1 n)) ∧
    m.ram (word (W + 258)) = labelWord last

theorem BitsHeld.read {bits0 bits1 : Nat → Label} {last : Label} {m : Memory}
    (held : BitsHeld row W joinBase pinBase bits0 bits1 last m) (p : Nat) :
    m.ram (word (convBit row W joinBase pinBase p)) = labelWord (wordBit row bits0 bits1 last p) := by
  unfold convBit wordBit
  split_ifs with h1 h2
  · exact held.1 p h1
  · exact held.2.1 _ (by omega)
  · exact held.2.2

/-- The bit cells lie at `W + 258` or in `[W + 2 ^ 14, W + 2 ^ 16)`. -/
theorem convBit_range (w0Pos : 1 ≤ row.width0) (w1Pos : 1 ≤ row.width1) (w0Le : row.width0 ≤ 12)
    (w1Le : row.width1 ≤ 12) (ellEq : row.width0 + row.width1 + 1 = row.ell)
    (fits : W + 2 ^ 18 < 2 ^ 256) (joinBelow : ∀ q, q < 2 → joinBase q + 16 ≤ W)
    (pinBelow : ∀ q, q < 2 → pinBase q + 128 ≤ W) (p : Nat) :
    convBit row W joinBase pinBase p = W + 258 ∨
      (W + 2 ^ 14 ≤ convBit row W joinBase pinBase p ∧ convBit row W joinBase pinBase p < W + 2 ^ 16) := by
  obtain ⟨l0, e0, l1, e1⟩ := convStage_layouts row W joinBase pinBase w0Pos w1Pos w0Le w1Le ellEq fits
    joinBelow pinBelow
  have a5 := l0.c5; have a6 := l0.c6; have a7 := l0.c7; have a8 := l0.c8; have a9 := l0.c9
  have a10 := l0.c10; have a11 := l0.c11; have a12 := l0.c12; have a13 := l0.c13; have a14 := l0.c14
  have a15 := l0.c15
  have b5 := l1.c5; have b6 := l1.c6; have b7 := l1.c7; have b8 := l1.c8; have b9 := l1.c9
  have b10 := l1.c10; have b11 := l1.c11; have b12 := l1.c12; have b13 := l1.c13; have b14 := l1.c14
  have b15 := l1.c15
  have s0 : (convStage0 row W (joinBase 0) (pinBase 0)).subBase = W + 2 ^ 14 := rfl
  have s1 : (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).subBase = W + 2 ^ 15 := rfl
  have hw0 := Nat.two_pow_pos row.width0
  have hw1 := Nat.two_pow_pos row.width1
  unfold convBit
  split_ifs with h1 h2
  · right; constructor <;> omega
  · right; constructor <;> omega
  · left; rfl

theorem BitsHeld.transfer (w0Pos : 1 ≤ row.width0) (w1Pos : 1 ≤ row.width1) (w0Le : row.width0 ≤ 12)
    (w1Le : row.width1 ≤ 12) (ellEq : row.width0 + row.width1 + 1 = row.ell)
    (fits : W + 2 ^ 18 < 2 ^ 256) (joinBelow : ∀ q, q < 2 → joinBase q + 16 ≤ W)
    (pinBelow : ∀ q, q < 2 → pinBase q + 128 ≤ W) {bits0 bits1 : Nat → Label} {last : Label}
    {m m' : Memory} (held : BitsHeld row W joinBase pinBase bits0 bits1 last m)
    (same : ∀ k, (k = W + 258 ∨ (W + 2 ^ 14 ≤ k ∧ k < W + 2 ^ 16)) → m'.ram (word k) = m.ram (word k)) :
    BitsHeld row W joinBase pinBase bits0 bits1 last m' := by
  obtain ⟨l0, e0, l1, e1⟩ := convStage_layouts row W joinBase pinBase w0Pos w1Pos w0Le w1Le ellEq fits
    joinBelow pinBelow
  have a5 := l0.c5; have a6 := l0.c6; have a7 := l0.c7; have a8 := l0.c8; have a9 := l0.c9
  have a10 := l0.c10; have a11 := l0.c11; have a12 := l0.c12; have a13 := l0.c13; have a14 := l0.c14
  have a15 := l0.c15
  have b5 := l1.c5; have b6 := l1.c6; have b7 := l1.c7; have b8 := l1.c8; have b9 := l1.c9
  have b10 := l1.c10; have b11 := l1.c11; have b12 := l1.c12; have b13 := l1.c13; have b14 := l1.c14
  have b15 := l1.c15
  have s0 : (convStage0 row W (joinBase 0) (pinBase 0)).subBase = W + 2 ^ 14 := rfl
  have s1 : (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).subBase = W + 2 ^ 15 := rfl
  have hw0 := Nat.two_pow_pos row.width0
  have hw1 := Nat.two_pow_pos row.width1
  refine ⟨fun n hn => ?_, fun n hn => ?_, ?_⟩
  · rw [same _ (Or.inr ⟨by omega, by omega⟩)]; exact held.1 n hn
  · rw [same _ (Or.inr ⟨by omega, by omega⟩)]; exact held.2.1 n hn
  · rw [same _ (Or.inl rfl)]; exact held.2.2

end Layout

theorem not_conv_below (W k : Nat) (hk : k < W + 256) (fits : W + 2 ^ 18 < 2 ^ 256) :
    ¬ convWrites W (word k) := by
  rintro ⟨j, jb, h⟩
  have := word_inj (by omega) (by simp only at jb ⊢; omega) h
  simp only at this
  omega

theorem not_treeEval_below (cells : TreeCells) (levels k : Nat) (hk : k < cells.levelBase)
    (order : cells.levelBase ≤ cells.matBase) (kb : k < 2 ^ 256) (fits : cells.matBase + 2 ^ levels < 2 ^ 256) :
    ¬ treeEvalWrites cells levels (word k) := by
  rintro (⟨j, jb, h⟩ | ⟨j, jb, h⟩) <;> simp only at jb h
  · have := word_inj kb (by omega) h; omega
  · have := word_inj kb (by omega) h; omega

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The replay of the conversion of one odd modulus** against `conversionEvalM`: the same
questions in the same order, and at the end the final one-hot at `W + 2 ^ 12 + ρ`, its hot index
at `W + 2 ^ 12 + 2 ^ 11` (below `m`), and nothing written outside `[W + 256, W + 2 ^ 18)`. -/
theorem agree_conversionReplay (coord i : Nat) (row : OddRow) (m value : Nat) (lanes : Lanes row.ell)
    (pub : ConvPublic) (W : Nat) (joinBase pinBase : Nat → Nat) (growJoin foldJoin : Nat → Nat)
    (coordSmall : coord < 2) (iSmall : i < 128)
    (w0Pos : 1 ≤ row.width0) (w1Pos : 1 ≤ row.width1) (w0Le : row.width0 ≤ 12) (w1Le : row.width1 ≤ 12)
    (ellEq : row.width0 + row.width1 + 1 = row.ell) (keepGe : row.width0 ≤ row.keep)
    (keepLe : row.keep ≤ row.ell) (keepSmall : row.keep ≤ 16) (mPos : 0 < m) (mLe : m ≤ 2 ^ 11)
    (valueLt : value < 2 ^ row.ell) (fits : W + 2 ^ 18 < 2 ^ 256)
    (joinBelow : ∀ q, q < 2 → joinBase q + 16 ≤ W) (pinBelow : ∀ q, q < 2 → pinBase q + 128 ≤ W)
    (growJoinBelow : ∀ j, growJoin j < W) (foldJoinBelow : ∀ j, foldJoin j < W) (m0 : Memory)
    (laneCells : ∀ j : Fin laneCount, m0.ram (word (W + j.val)) = word (lanes j).val)
    (sigmaCell : m0.ram (word (W + 128)) = word value)
    (joinCells0 : ∀ n, 1 ≤ n → n < row.width0 →
      m0.ram (word (joinBase 0 + n)) = labelWord (pub.stageJoin i 0 n))
    (joinCells1 : ∀ n, 1 ≤ n → n < row.width1 →
      m0.ram (word (joinBase 1 + n)) = labelWord (pub.stageJoin i 1 n))
    (pinCells0 : ∀ j : Fin laneCount, m0.ram (word (pinBase 0 + j.val)) =
      word ((pinOfBlocks row.ell fun k => pub.stagePin i 0 k.val) j).val)
    (pinCells1 : ∀ j : Fin laneCount, m0.ram (word (pinBase 1 + j.val)) =
      word ((pinOfBlocks (row.ell - row.width0) fun k => pub.stagePin i 1 k.val) j).val)
    (growJoinCells : ∀ n, row.width0 ≤ n → n < row.keep →
      m0.ram (word (growJoin n)) = labelWord (pub.growJoin i n))
    (foldJoinCells : ∀ n, row.keep ≤ n → n < row.ell →
      m0.ram (word (foldJoin n)) = labelWord (pub.foldJoin i n)) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (conv : (Fin m → Label) × Nat) after =>
        (∀ ρ : Fin m, after.ram (word (W + 2 ^ 12 + ρ.val)) = labelWord (conv.1 ρ)) ∧
        after.ram (word (W + 2 ^ 12 + 2 ^ 11)) = word conv.2 ∧ conv.2 < m ∧
        Frame (convWrites W) convClobbers m0 after)
      ((conversionReplay coord i row m W joinBase pinBase growJoin foldJoin).tree m0)
      (liftHash (conversionEvalM coord i row m value lanes pub)) := by
  -- widths and bounds
  have hw0 := Nat.two_pow_pos row.width0
  have hw1 := Nat.two_pow_pos row.width1
  have pw0 : 2 ^ row.width0 ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) w0Le
  have pw1 : 2 ^ row.width1 ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) w1Le
  have pkeep : 2 ^ (row.width0 + (row.keep - row.width0)) ≤ 2 ^ 16 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have lc : laneCount = 104 := rfl
  have ellLe : row.ell ≤ 128 := by omega
  have valueSmall : value < 2 ^ 256 :=
    lt_of_lt_of_le valueLt (Nat.pow_le_pow_right (by norm_num) (by omega))
  have j0 := joinBelow 0 (by norm_num); have j1 := joinBelow 1 (by norm_num)
  have p0 := pinBelow 0 (by norm_num); have p1 := pinBelow 1 (by norm_num)
  obtain ⟨layout0, end0, layout1, end1⟩ := convStage_layouts row W joinBase pinBase w0Pos w1Pos w0Le
    w1Le ellEq fits joinBelow pinBelow
  have a5 := layout0.c5; have a6 := layout0.c6; have a7 := layout0.c7; have a8 := layout0.c8
  have a9 := layout0.c9; have a10 := layout0.c10; have a11 := layout0.c11; have a12 := layout0.c12
  have a13 := layout0.c13; have a14 := layout0.c14; have a15 := layout0.c15
  have b5 := layout1.c5; have b6 := layout1.c6; have b7 := layout1.c7; have b8 := layout1.c8
  have b9 := layout1.c9; have b10 := layout1.c10; have b11 := layout1.c11; have b12 := layout1.c12
  have b13 := layout1.c13; have b14 := layout1.c14; have b15 := layout1.c15
  have s0 : (convStage0 row W (joinBase 0) (pinBase 0)).subBase = W + 2 ^ 14 := rfl
  have n0 : (convStage0 row W (joinBase 0) (pinBase 0)).nodeBase = W + 2 ^ 14 + 128 := rfl
  have s1 : (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).subBase = W + 2 ^ 15 := rfl
  have below : ∀ k, k < W + 256 → ¬ convWrites W (word k) := fun k hk => not_conv_below W k hk fits
  -- the two stage values
  obtain ⟨m1, run1, ram1, bits1, regs1⟩ :=
    exec_stageValue0 W row.width0 m0 value sigmaCell valueSmall (by omega)
  obtain ⟨m2, run2, ram2, bits2, regs2⟩ := exec_stageValue1 W row.width0 row.width1 m1 value
    (by rw [ram1, Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]; exact sigmaCell)
    valueSmall (by omega) (by omega)
  have fr2 : Frame (convWrites W) convClobbers m0 m2 :=
    ⟨fun a out => by
      rw [ram2, Function.update_of_ne (ne_of_not_conv out (by omega) (by omega)), ram1,
        Function.update_of_ne (ne_of_not_conv out (by omega) (by omega))],
     by rw [bits2, bits1],
     fun r out => by
      rw [regs2 r (ne_of_not_convRegs out rA (by simp)) (ne_of_not_convRegs out rB (by simp))
          (ne_of_not_convRegs out rAddr (by simp)),
        regs1 r (ne_of_not_convRegs out rA (by simp)) (ne_of_not_convRegs out rB (by simp))
          (ne_of_not_convRegs out rAddr (by simp))]⟩
  have inputs0 : StageInputs (convStage0 row W (joinBase 0) (pinBase 0)) row.width0 row.ell
      (value % 2 ^ row.width0) lanes (pub.stageJoin i 0)
      (pinOfBlocks row.ell fun k => pub.stagePin i 0 k.val) m2 :=
    ⟨by
      show m2.ram (word (W + 256)) = _
      rw [ram2, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), ram1,
        Function.update_self],
     fun j => by
      show m2.ram (word (W + j.val)) = _
      rw [fr2.ram _ (below _ (by have := j.isLt; omega))]; exact laneCells j,
     fun n h1 h2 => by
      show m2.ram (word (joinBase 0 + n)) = _
      rw [fr2.ram _ (below _ (by omega))]; exact joinCells0 n h1 h2,
     fun j => by
      show m2.ram (word (pinBase 0 + j.val)) = _
      rw [fr2.ram _ (below _ (by have := j.isLt; omega))]; exact pinCells0 j⟩
  unfold conversionReplay conversionEvalM
  rw [tree_seq_exec _ _ (det_stageValue0 W row.width0) m0 m1 run1,
    tree_seq_exec _ _ (det_stageValue1 W row.width0 row.width1) m1 m2 run2]
  try dsimp only
  -- stage 0
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun e0 m3 post3 => ?_)
    (agree_stageReplay (convStage0 row W (joinBase 0) (pinBase 0)) row.width0 row.ell
      (value % 2 ^ row.width0) lanes (pub.stageJoin i 0)
      (pinOfBlocks row.ell fun k => pub.stagePin i 0 k.val) layout0 ellLe w0Pos (by omega) (by omega)
      (fun level => extTreeTag coord i 0 level 0) (extCastTag coord i 0 0 0) 64 (by norm_num)
      (extTreeTag coord i 0) (extCastTag coord i 0)
      (fun L x _ => extTreeTag_affine coord i 0 L x)
      (fun L x hL hx => extTreeTag_small coord i 0 L x coordSmall iSmall (by norm_num) (by omega)
        (by omega))
      (fun x part => extCastTag_affine coord i 0 x part)
      (fun x hx => extCastTag_small coord i 0 x _ coordSmall iSmall (by norm_num) (by omega)
        (castAnswers_le_128 _ (by omega) ellLe))
      (Nat.mod_lt _ hw0) m2 inputs0)
  obtain ⟨leaves3, bits3, next3, frame3⟩ := post3
  have fr3 : Frame (convWrites W) convClobbers m0 m3 :=
    fr2.conv_step frame3 (fun a h => by
      obtain ⟨k, lo, hi, rfl⟩ := sw_chain_in (W + 2 ^ 14) row.width0 row.ell (W + 256) W (joinBase 0)
        (pinBase 0) w0Le (by omega) ellLe h
      exact inConv W k (by omega) (by omega)) stageClobbers_sub
  have off3 : ∀ k, k < W + 2 ^ 14 → k < 2 ^ 256 → m3.ram (word k) = m2.ram (word k) :=
    fun k hk kb => frame3.ram _ (not_sw_below _ _ _ layout0 (by omega))
  have inputs1 : StageInputs (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1))
      row.width1 (row.ell - row.width0) (value / 2 ^ row.width0 % 2 ^ row.width1) e0.next
      (pub.stageJoin i 1) (pinOfBlocks (row.ell - row.width0) fun k => pub.stagePin i 1 k.val) m3 :=
    ⟨by
      show m3.ram (word (W + 257)) = _
      rw [off3 _ (by omega) (by omega), ram2, Function.update_self],
     fun j => next3 j,
     fun n h1 h2 => by
      show m3.ram (word (joinBase 1 + n)) = _
      rw [fr3.ram _ (below _ (by omega))]; exact joinCells1 n h1 h2,
     fun j => by
      show m3.ram (word (pinBase 1 + j.val)) = _
      rw [fr3.ram _ (below _ (by have := j.isLt; omega))]; exact pinCells1 j⟩
  try dsimp only
  -- stage 1
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun e1 m4 post4 => ?_)
    (agree_stageReplay (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)) row.width1
      (row.ell - row.width0) (value / 2 ^ row.width0 % 2 ^ row.width1) e0.next (pub.stageJoin i 1)
      (pinOfBlocks (row.ell - row.width0) fun k => pub.stagePin i 1 k.val) layout1 (by omega) w1Pos
      (by omega) (by omega)
      (fun level => extTreeTag coord i 1 level 0) (extCastTag coord i 1 0 0) 64 (by norm_num)
      (extTreeTag coord i 1) (extCastTag coord i 1)
      (fun L x _ => extTreeTag_affine coord i 1 L x)
      (fun L x hL hx => extTreeTag_small coord i 1 L x coordSmall iSmall (by norm_num) (by omega)
        (by omega))
      (fun x part => extCastTag_affine coord i 1 x part)
      (fun x hx => extCastTag_small coord i 1 x _ coordSmall iSmall (by norm_num) (by omega)
        (castAnswers_le_128 _ (by omega) (by omega)))
      (Nat.mod_lt _ hw1) m3 inputs1)
  obtain ⟨leaves4, bits4, next4, frame4⟩ := post4
  have fr4 : Frame (convWrites W) convClobbers m0 m4 :=
    fr3.conv_step frame4 (fun a h => by
      obtain ⟨k, lo, hi, rfl⟩ := sw_chain_in (W + 2 ^ 15) row.width1 (row.ell - row.width0) (W + 257)
        (convStage0 row W (joinBase 0) (pinBase 0)).nextBase (joinBase 1) (pinBase 1) w1Le (by omega)
        (by omega) h
      exact inConv W k (by omega) (by omega)) stageClobbers_sub
  have off4 : ∀ k, k < W + 2 ^ 15 → k < 2 ^ 256 → m4.ram (word k) = m3.ram (word k) :=
    fun k hk kb => frame4.ram _ (not_sw_below _ _ _ layout1 (by omega))
  -- the stage-2 bit and the copy of stage 0's leaves
  obtain ⟨m5, run5, ram5, bits5, regs5⟩ := exec_lastBitProg W
    (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).nextBase m4 e1.next next4
    (by omega)
  have fr5 : Frame (convWrites W) convClobbers m0 m5 :=
    ⟨fun a out => by
      rw [ram5, Function.update_of_ne (ne_of_not_conv out (by omega) (by omega))]; exact fr4.ram a out,
     by rw [bits5]; exact fr4.bits,
     fun r out => by
      rw [regs5 r (ne_of_not_convRegs out rB (by simp)) (ne_of_not_convRegs out rD (by simp))
        (ne_of_not_convRegs out rE (by simp)) (ne_of_not_convRegs out rAddr (by simp))]
      exact fr4.registers r out⟩
  obtain ⟨m6, run6, cells6, frame6, bits6, regs6⟩ := exec_saveLeaves
    (convStage0 row W (joinBase 0) (pinBase 0)).nodeBase (W + 2 ^ 16) row.width0 0 m5 (by omega)
    (by omega)
  have fr6 : Frame (convWrites W) convClobbers m0 m6 :=
    ⟨fun a out => by
      rw [frame6 a fun leaf hl => ne_of_not_conv out (by omega) (by omega)]; exact fr5.ram a out,
     by rw [bits6]; exact fr5.bits,
     fun r out => by
      rw [regs6 r (ne_of_not_convRegs out rA (by simp)) (ne_of_not_convRegs out rAddr (by simp))]
      exact fr5.registers r out⟩
  have held5 : BitsHeld row W joinBase pinBase e0.bits e1.bits (laneBit e1.next 0) m5 :=
    ⟨fun n hn => by
      rw [ram5, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
        off4 _ (by omega) (by omega)]
      exact bits3 n hn,
     fun n hn => by
      rw [ram5, Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
      exact bits4 n hn,
     by rw [ram5, Function.update_self]⟩
  have held6 := held5.transfer row W joinBase pinBase w0Pos w1Pos w0Le w1Le ellEq fits joinBelow
    pinBelow (m' := m6) fun k hk => frame6 _ fun leaf hl => word_ne (by omega) (by omega) (by omega)
  rw [tree_seq_exec _ _ (det_lastBitProg W _) m4 m5 run5, tree_seq_exec _ _ (det_saveLeaves _ _ _ _) m5 m6 run6]
  try dsimp only
  -- the growth
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun grown m7 post7 => ?_)
    (agree_growEval (convGrowCells row W joinBase pinBase growJoin) (growTag coord i) row.width0 value
      valueSmall (wordBit row e0.bits e1.bits (laneBit e1.next 0)) (pub.growJoin i)
      (stored fun leaf => e0.leaves leaf.val) m6 (row.keep - row.width0) (by omega)
      (fun k hk => by
        have pn : 2 ^ (row.width0 + k + 1) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have pn' : 2 ^ (row.width0 + k) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have range := convBit_range row W joinBase pinBase w0Pos w1Pos w0Le w1Le ellEq fits joinBelow
          pinBelow (row.width0 + k)
        have gj := growJoinBelow (row.width0 + k)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold TreeOutside) <;> simp only [convGrowCells] <;>
          first
          | omega
          | exact ⟨by omega, fun j hj => by omega, fun r hr => by omega⟩)
      (by show m6.ram (word (W + 128)) = _; rw [fr6.ram _ (below _ (by omega))]; exact sigmaCell)
      (fun k hk => by
        show m6.ram (word (growJoin (row.width0 + k))) = _
        rw [fr6.ram _ (below _ (by have := growJoinBelow (row.width0 + k); omega))]
        exact growJoinCells _ (by omega) (by omega))
      (fun k _ => held6.read row W joinBase pinBase (row.width0 + k))
      (fun j => by
        show m6.ram (word (W + 2 ^ 16 + j.val)) = _
        have copy := cells6 j.val j.isLt
        rw [Nat.mul_zero, Nat.add_zero] at copy
        rw [copy, stored_eq, ram5, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
          off4 _ (by omega) (by omega)]
        exact leaves3 j.val j.isLt)
      (fun k s hk hs => growTag_small coord i _ s coordSmall iSmall (by omega) (by
        have : 2 ^ (row.width0 + k) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega))
      (row.keep - row.width0) le_rfl)
  obtain ⟨level7, frame7⟩ := post7
  have fr7 : Frame (convWrites W) convClobbers m0 m7 :=
    fr6.conv_step frame7 (fun a h => by
      rcases h with ⟨k, kb, rfl⟩ | ⟨k, kb, rfl⟩ <;> simp only [convGrowCells] at kb ⊢ <;>
        exact inConv W _ (by omega) (by omega)) treeStepClobbers_sub
  have off7 : ∀ k, k < W + 2 ^ 16 → m7.ram (word k) = m6.ram (word k) := fun k hk =>
    frame7.ram _ (not_treeEval_below _ _ k (by simp only [convGrowCells]; omega)
      (by simp only [convGrowCells]; omega) (by omega) (by simp only [convGrowCells]; omega))
  -- the reindex and the first hot index
  obtain ⟨m8, run8, vec8, frame8, bits8, regs8⟩ := exec_reindexBlock (W + 2 ^ 16) (W + 2 ^ 12)
    (row.width0 + (row.keep - row.width0)) m m7 grown (by omega) (by omega) (by omega)
    (fun j hj ρ hρ => by omega) (fun j => level7 j)
  have fr8 : Frame (convWrites W) convClobbers m0 m8 :=
    ⟨fun a out => by
      rw [frame8 a fun ρ hρ => ne_of_not_conv out (by omega) (by omega)]; exact fr7.ram a out,
     by rw [bits8]; exact fr7.bits,
     fun r out => by
      rw [regs8 r (ne_of_not_convRegs out rC (by simp)) (ne_of_not_convRegs out rD (by simp))
        (ne_of_not_convRegs out rAddr (by simp))]
      exact fr7.registers r out⟩
  obtain ⟨m9, run9, ram9, bits9, regs9⟩ := exec_hotInit (convFoldCells row W joinBase pinBase foldJoin)
    row.keep m m8 value valueSmall keepSmall mPos (by omega)
    (by show m8.ram (word (W + 128)) = _; rw [fr8.ram _ (below _ (by omega))]; exact sigmaCell)
  simp only [convFoldCells] at ram9
  have fr9 : Frame (convWrites W) convClobbers m0 m9 :=
    ⟨fun a out => by
      rw [ram9, Function.update_of_ne (ne_of_not_conv out (by omega) (by omega))]; exact fr8.ram a out,
     by rw [bits9]; exact fr8.bits,
     fun r out => by
      rw [regs9 r (ne_of_not_convRegs out rAcc (by simp)) (ne_of_not_convRegs out rOut (by simp))
        (ne_of_not_convRegs out rB (by simp)) (ne_of_not_convRegs out rD (by simp))
        (ne_of_not_convRegs out rE (by simp)) (ne_of_not_convRegs out rF (by simp))
        (ne_of_not_convRegs out rAddr (by simp))]
      exact fr8.registers r out⟩
  have held9 := held6.transfer row W joinBase pinBase w0Pos w1Pos w0Le w1Le ellEq fits joinBelow
    pinBelow (m' := m9) fun k hk => by
      rw [ram9, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
        frame8 _ fun ρ hρ => word_ne (by omega) (by omega) (by omega), off7 k (by omega)]
  rw [tree_seq_exec _ _ (det_reindexBlock _ _ _ _) m7 m8 run8,
    tree_seq_exec _ _ (det_hotInit _ _ _) m8 m9 run9]
  try dsimp only
  -- the folds
  have agreeF := agree_foldsLoop (FixedIndex := FixedIndex) (EncIndex := EncIndex)
    (convFoldCells row W joinBase pinBase foldJoin) m (foldTag coord i) value valueSmall
    (wordBit row e0.bits e1.bits (laneBit e1.next 0)) (pub.foldJoin i)
    (by simp only [convFoldCells]; exact ⟨by omega, by omega, fun r hr => by omega, fun r hr => by omega⟩)
    (row.ell - row.keep) row.keep (value % 2 ^ row.keep % m) (reindex _ grown m) m9 (by omega)
    (fun k hk => by
      have range := convBit_range row W joinBase pinBase w0Pos w1Pos w0Le w1Le ellEq fits joinBelow
        pinBelow (row.keep + k)
      have fj := foldJoinBelow (row.keep + k)
      refine ⟨mPos, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [convFoldCells] <;>
        first
        | omega
        | exact ⟨by omega, fun r hr => by omega, fun r hr => by omega⟩)
    (Nat.mod_lt _ mPos)
    (by show m9.ram (word (W + 128)) = _; rw [fr9.ram _ (below _ (by omega))]; exact sigmaCell)
    (by show m9.ram (word (W + 2 ^ 12 + 2 ^ 11)) = _; rw [ram9, Function.update_self])
    (fun ρ => by
      show m9.ram (word (W + 2 ^ 12 + ρ.val)) = _
      rw [ram9, Function.update_of_ne (word_ne (by omega) (by omega) (by have := ρ.isLt; omega))]
      exact vec8 ρ)
    (fun k hk => by
      show m9.ram (word (foldJoin (row.keep + k))) = _
      rw [fr9.ram _ (below _ (by have := foldJoinBelow (row.keep + k); omega))]
      exact foldJoinCells _ (by omega) (by omega))
    (fun k _ => held9.read row W joinBase pinBase (row.keep + k))
    (fun k ρ hk hρ => foldTag_small coord i _ ρ coordSmall iSmall (by omega) (by omega))
  refine (Agree.withResults agreeF (AllResults.liftHash (foldsEvalM_hot_lt m mPos (foldTag coord i) value
    _ _ _ _ _ _ (Nat.mod_lt _ mPos)))).mono fun conv after holds => ?_
  obtain ⟨⟨vec, hot, frameF⟩, lt⟩ := holds
  refine ⟨vec, hot, lt, fr9.conv_step frameF (fun a h => ?_) treeStepClobbers_sub⟩
  rcases h with (⟨k, kb, rfl⟩ | ⟨k, kb, rfl⟩) | rfl
  · simp only [convFoldCells] at kb ⊢; exact inConv W _ (by omega) (by omega)
  · simp only [convFoldCells] at kb ⊢; exact inConv W _ (by omega) (by omega)
  · simp only [convFoldCells]; exact inConv W _ (by omega) (by omega)

end Agreement

end Kriterion.CRT.SimMachine
