/-
**The replay of a coordinate's chunks agrees with the evaluator's chunk table**
(`agree_chunkLoop`): the machine's `chunkLoop` against
`liftHash (tableM count fun c => chunkEvalM T coord (fun j => clip (labels j)) v (joins c) (pins c) c)`, the first step
of `coordEvalM` (`Construction/CRT/Coord.lean`).

The composition is by `agree_rep_vector_plain` over bodies of unequal width; every layout fact of
every chunk and level is derived from one chain of regions (`CoordChain`), and the frame of the
loop is one interval (`chunkLoopWrites`).
-/

import Proof.Simulator.CRT.ReplayCast
import Construction.Simulator.CRT.ReplayChunks

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### Regions against intervals -/

private theorem region_in_interval (region : Region) (lo hi : Nat) (low : lo ≤ region.base)
    (high : region.base + region.count ≤ hi) (address : Word)
    (inside : Writes.region region address) :
    ∃ x, lo ≤ x ∧ x < hi ∧ address = word x := by
  obtain ⟨k, kb, same⟩ := inside
  exact ⟨region.base + k, by omega, by omega, same⟩

private theorem not_region_of_apart (region : Region) (x : Nat) (small : x < 2 ^ 256)
    (fits : region.base + region.count ≤ 2 ^ 256)
    (apart : x < region.base ∨ region.base + region.count ≤ x) :
    ¬ Writes.region region (word x) := by
  rintro ⟨k, kb, same⟩
  have := word_inj small (by omega) same
  omega

/-! ### The chain of regions -/

/-- The layout of a coordinate's chunk phase: every input below the scratch, then one chain of
regions (scratch, casts, leaves). -/
structure CoordChain (cc : CoordCells) (count l : Nat) : Prop where
  coordBelow : cc.coordCell < cc.alpha
  labelsBelow : cc.labelBase + 256 ≤ cc.alpha
  joinsBelow : ∀ c, c < count → ∀ n, n < 8 → cc.chunkJoin c n < cc.alpha
  pinsBelow : cc.pinBase + 128 * count ≤ cc.alpha
  alphaBelow : cc.alpha < cc.levelBase
  levelsBelow : cc.levelBase + 256 ≤ cc.matBase
  matsBelow : cc.matBase + 256 ≤ cc.ansBase
  ansBelow : cc.ansBase + 2 * castAnswers l ≤ cc.castBase
  castBelow : cc.castBase + 32768 * count ≤ cc.leafBase
  leafFits : cc.leafBase + 256 * count < 2 ^ 256

/-- The chunk widths and offsets fit the chain. -/
structure ChunkShape (offset width : Nat → Nat) (count bits : Nat) : Prop where
  widthPos : ∀ c, c < count → 1 ≤ width c
  widthSmall : ∀ c, c < count → width c ≤ 8
  offsetFits : ∀ c, c < count → offset c + width c ≤ bits
  bitsLe : bits ≤ 256

private theorem pow_le_256 (k : Nat) (small : k ≤ 8) : 2 ^ k ≤ 256 :=
  (Nat.pow_le_pow_right (by norm_num) small).trans (by norm_num)

theorem treeLayout_chain (cc : CoordCells) (count l : Nat) (chain : CoordChain cc count l)
    (offset width : Nat → Nat) (bits : Nat) (shape : ChunkShape offset width count bits) (c : Nat) (cb : c < count)
    (k : Nat) (kb : k < width c) : TreeLayout (cc.tree (offset c) c) k := by
  have w8 := shape.widthSmall c cb
  have off := shape.offsetFits c cb
  have := shape.bitsLe
  have p1 := pow_le_256 (k + 1) (by omega)
  have p0 := pow_le_256 k (by omega)
  have := chain.coordBelow; have := chain.labelsBelow
  have := chain.pinsBelow; have := chain.alphaBelow; have := chain.levelsBelow
  have := chain.matsBelow; have := chain.ansBelow; have := chain.castBelow; have := chain.leafFits
  have := chain.joinsBelow c cb k (by omega)
  refine ⟨?_, ?_, ⟨?_, fun j jb => ?_, fun r rb => ?_⟩, ⟨?_, fun j jb => ?_, fun r rb => ?_⟩,
    ⟨?_, fun j jb => ?_, fun r rb => ?_⟩⟩ <;>
    simp only [CoordCells.tree] <;> omega

theorem castLayout_chain (cc : CoordCells) (count l : Nat) (chain : CoordChain cc count l)
    (offset width : Nat → Nat) (bits : Nat) (shape : ChunkShape offset width count bits) (c : Nat) (cb : c < count) :
    ChunkCastLayout (cc.cast c) (width c) l := by
  have w8 := shape.widthSmall c cb
  have p0 := pow_le_256 (width c) w8
  have := chain.coordBelow; have := chain.labelsBelow
  have := chain.pinsBelow; have := chain.alphaBelow; have := chain.levelsBelow
  have := chain.matsBelow; have := chain.ansBelow; have := chain.castBelow; have := chain.leafFits
  have c1 : 32768 * c + 32768 ≤ 32768 * count := by omega
  have p1 : 128 * c + 128 ≤ 128 * count := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, fun b bb x xb => ?_, fun leaf lb b bb => ?_, fun leaf lb x xb => ?_,
    fun b bb => ?_, fun x xb => ?_, fun i ib b bb => ?_, fun i ib x xb => ?_⟩ <;>
    simp only [CoordCells.cast] <;> omega

/-! ### The chunk prefix -/

theorem exec_chunkPrefix (coordCell alpha offset width : Nat) (memory : Memory) (v : Nat)
    (coordVal : memory.ram (word coordCell) = word v) (vSmall : v < 2 ^ 256)
    (offsetSmall : offset < 2 ^ 256) (widthSmall : width < 256) :
    ∃ after, (chunkPrefix coordCell alpha offset width).exec memory = some after ∧
      after.ram = Function.update memory.ram (word alpha) (word ((v >>> offset) % 2 ^ width)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have divSmall : v / 2 ^ offset < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) vSmall
  refine ⟨_, rfl, ?_, rfl, fun register n1 n2 n3 => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte,
      coordVal]
    rw [eval_shr_word _ _ vSmall offsetSmall, eval_and_pow _ _ divSmall widthSmall,
      Nat.shiftRight_eq_div_pow]
  · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2, if_neg n3]

theorem det_chunkPrefix (coordCell alpha offset width : Nat) :
    (chunkPrefix coordCell alpha offset width).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩

/-! ### Saving the leaves -/

theorem exec_saveLeaves (levelBase leafBase width c : Nat) (memory : Memory)
    (apart : levelBase + 2 ^ width ≤ leafBase + 256 * c)
    (fits : leafBase + 256 * c + 2 ^ width < 2 ^ 256) :
    ∃ after, (saveLeaves levelBase leafBase width c).exec memory = some after ∧
      (∀ leaf, leaf < 2 ^ width →
        after.ram (word (leafBase + 256 * c + leaf)) = memory.ram (word (levelBase + leaf))) ∧
      (∀ address, (∀ leaf, leaf < 2 ^ width → address ≠ word (leafBase + 256 * c + leaf)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨after, run, done, frame, bits, regs⟩ := Prog.exec_rep
    (fun leaf => .seq (loadAt rA (levelBase + leaf)) (storeAt (leafBase + 256 * c + leaf) rA))
    (fun k current =>
      (∀ leaf, leaf < k →
        current.ram (word (leafBase + 256 * c + leaf)) = memory.ram (word (levelBase + leaf))) ∧
      (∀ address, (∀ leaf, leaf < k → address ≠ word (leafBase + 256 * c + leaf)) →
        current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rAddr →
        current.registers register = memory.registers register)
    (2 ^ width)
    (fun k kb current ⟨done, frame, bits, regs⟩ => by
      have source : current.ram (word (levelBase + k)) = memory.ram (word (levelBase + k)) :=
        frame _ fun leaf lb same => by
          have := word_inj (by omega) (by omega) same
          omega
      refine ⟨_, by rw [exec_loadAt_seq, exec_storeAt _ _ _ (by decide)], fun leaf lb => ?_,
        fun address off => ?_, ?_, fun register n1 n2 => ?_⟩
      · simp only [ram_storeRam, ram_setReg, reg_setReg, ↓reduceIte]
        rcases Nat.lt_or_ge leaf k with lt | ge
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done leaf lt
        · have : leaf = k := by omega
          subst this
          rw [Function.update_self, source]
      · simp only [ram_storeRam, ram_setReg]
        rw [Function.update_of_ne (off k (by omega))]
        exact frame address fun leaf lb => off leaf (by omega)
      · simp only [bits_storeRam, bits_setReg]
        exact bits
      · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2]
        exact regs register n1 n2)
    memory ⟨fun leaf lb => absurd lb (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ _ => rfl⟩
  exact ⟨after, run, done, frame, bits, regs⟩

theorem det_saveLeaves (levelBase leafBase width c : Nat) :
    (saveLeaves levelBase leafBase width c).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-! ### The loop -/

private theorem clobbers_chunkLoop (register : Register)
    (inside : (treeStepClobbers.union chunkCastClobbers) register) : chunkLoopClobbers register := by
  revert register inside
  simp only [Clobbers.union, treeStepClobbers, chunkCastClobbers, chunkLoopClobbers, Clobbers.ofList]
  decide

/-- The invariant of the chunk loop after `k` chunks. -/
def ChunkLoopInv (cc : CoordCells) (width : Nat → Nat) (l count : Nat) (start : Memory) (k : Nat)
    (values : Vector (ChunkEval l) k) (memory : Memory) : Prop :=
  (∀ c (bound : c < k), ∀ leaf, leaf < 2 ^ width c → ∀ i (ib : i < laneCount),
      memory.ram (word (cc.castBase + 32768 * c + 128 * leaf + i)) =
        word ((((values[c]'bound).casts leaf) ⟨i, ib⟩).val)) ∧
    (∀ c (bound : c < k), ∀ leaf, leaf < 2 ^ width c →
      memory.ram (word (cc.leafBase + 256 * c + leaf)) = labelWord ((values[c]'bound).leaves leaf)) ∧
    (∀ address, ¬ chunkLoopWrites cc count address → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ chunkLoopClobbers register → memory.registers register = start.registers register

section Loop

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **A deterministic block after an agreement**: the agreement's post carries through the block. -/
theorem agree_seq_det {β : Type} {Post Post' : β → Memory → Prop}
    (first rest : Prog) (det : rest.OpsSatisfy Op.Det) (memory : Memory)
    (tree' : FreeQuery (publicOracleSpec FixedIndex EncIndex) β)
    (agrees : Agree Post (first.tree memory) tree')
    (continues : ∀ value after, Post value after →
      ∃ final, rest.exec after = some final ∧ Post' value final) :
    Agree Post' ((Prog.seq first rest).tree memory) tree' := by
  rw [tree_seq, ← TreeLaws.bind_pure_right tree']
  refine Agree.bindOpt (fun value after post => ?_) agrees
  obtain ⟨final, run, holds⟩ := continues value after post
  rw [tree_eq_exec rest det, run]
  exact .leaf holds

/-- **One chunk of the loop.** -/
theorem agree_chunkStep (T : CrtTable) (coord : Nat) (cc : CoordCells) (count : Nat)
    (chain : CoordChain cc count T.castWidth)
    (bits : Nat) (shape : ChunkShape T.chunkOffset T.chunkWidth count bits)
    (lPos : 0 < T.castWidth) (lSmall : T.castWidth ≤ 128)
    (labels : Nat → Block) (v : Nat) (vSmall : v < 2 ^ 256) (joins : Nat → Nat → Label)
    (pins : Nat → Lanes T.castWidth) (start : Memory)
    (coordVal : start.ram (word cc.coordCell) = word v)
    (labelCells : ∀ j, j < bits → start.ram (word (cc.labelBase + j)) = blockWord (labels j))
    (joinCells : ∀ c, c < count → ∀ n, 1 ≤ n → n < T.chunkWidth c →
      start.ram (word (cc.chunkJoin c n)) = labelWord (joins c n))
    (pinCells : ∀ c, c < count → ∀ i (ib : i < laneCount),
      start.ram (word (cc.pinBase + 128 * c + i)) = word ((pins c) ⟨i, ib⟩).val)
    (tagTreeSmall : ∀ c k s, c < count → k < T.chunkWidth c → s < 2 ^ k →
      chunkTreeTag coord c k s < 2 ^ 127)
    (tagCastSmall : ∀ c leaf j, c < count → leaf < 2 ^ T.chunkWidth c → j < castAnswers T.castWidth →
      chunkCastTag coord c leaf j < 2 ^ 127)
    (index : Fin count) (values : Vector (ChunkEval T.castWidth) index.val) (memory : Memory)
    (holds : ChunkLoopInv cc T.chunkWidth T.castWidth count start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : ChunkEval T.castWidth) after =>
        ChunkLoopInv cc T.chunkWidth T.castWidth count start (index.val + 1) (values.push result) after)
      ((chunkStep cc T.chunkOffset T.chunkWidth (chunkTreeTag coord) (chunkCastTag coord) T.castWidth
        index.val).tree memory)
      (liftHash (chunkEvalM T coord (fun j => clip (labels j)) v (joins index.val) (pins index.val) index.val)) := by
  obtain ⟨c, cb⟩ := index
  simp only at values holds ⊢
  obtain ⟨done, leavesDone, frame, bitsSame, regs⟩ := holds
  have w1 := shape.widthPos c cb
  have w8 := shape.widthSmall c cb
  have off := shape.offsetFits c cb
  have := shape.bitsLe
  have p0 := pow_le_256 (T.chunkWidth c) w8
  have := chain.coordBelow; have := chain.labelsBelow
  have := chain.pinsBelow; have := chain.alphaBelow; have := chain.levelsBelow
  have := chain.matsBelow; have := chain.ansBelow; have := chain.castBelow; have := chain.leafFits
  have c1 : 32768 * c + 32768 ≤ 32768 * count := by omega
  -- cells below `alpha` are never written by the loop
  have below : ∀ x, x < cc.alpha → memory.ram (word x) = start.ram (word x) := fun x xb =>
    frame _ fun ⟨y, yLow, yHigh, same⟩ => by
      have := word_inj (by omega) (by omega) same
      omega
  obtain ⟨m1, run1, ram1, bits1, regs1⟩ := exec_chunkPrefix cc.coordCell cc.alpha (T.chunkOffset c)
    (T.chunkWidth c) memory v (by rw [below _ (by omega)]; exact coordVal) vSmall (by omega) (by omega)
  have m1Below : ∀ x, x < cc.alpha → m1.ram (word x) = start.ram (word x) := fun x xb => by
    rw [ram1, Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
    exact below x xb
  unfold chunkStep
  rw [tree_seq_exec _ _ (det_chunkPrefix _ _ _ _) memory m1 run1, chunkEvalM_split]
  refine agree_seq_det _ _ (det_saveLeaves _ _ _ _) m1 _ (agree_chunkReplay (cc.tree (T.chunkOffset c) c) (cc.cast c) (chunkTreeTag coord c)
    (chunkCastTag coord c) (T.chunkWidth c) T.castWidth w1 (by omega) lPos lSmall rfl rfl
    (fun k kb => treeLayout_chain cc count T.castWidth chain T.chunkOffset T.chunkWidth bits shape c cb k kb)
    (castLayout_chain cc count T.castWidth chain T.chunkOffset T.chunkWidth bits shape c cb)
    (by
      simp only [CoordCells.tree]
      exact fun inside => by
        rcases inside with inside | inside
        · exact not_region_of_apart _ _ (by omega) (by simp; omega) (Or.inl (by simp; omega)) inside
        · exact not_region_of_apart _ _ (by omega) (by simp; omega) (Or.inl (by simp; omega)) inside)
    (fun i ib => by
      simp only [CoordCells.tree, CoordCells.cast]
      have ib128 : i < 128 := lt_of_lt_of_le ib (by decide : laneCount ≤ 128)
      exact fun inside => by
        rcases inside with inside | inside
        · exact not_region_of_apart _ _ (by omega) (by simp; omega) (Or.inl (by simp; omega)) inside
        · exact not_region_of_apart _ _ (by omega) (by simp; omega) (Or.inl (by simp; omega)) inside)
    (T.chunkValue v c) (Nat.mod_lt _ (Nat.two_pow_pos _)) (fun n => labels (T.chunkOffset c + n))
    (joins c) (pins c) m1
    (by
      show m1.ram (word cc.alpha) = _
      rw [ram1, Function.update_self]
      rfl)
    (fun k k1 kb => by
      show m1.ram (word (cc.chunkJoin c k)) = _
      rw [m1Below _ (chain.joinsBelow c cb k (by omega))]
      exact joinCells c cb k k1 kb)
    (fun k kb => by
      show m1.ram (word (cc.labelBase + T.chunkOffset c + k)) = _
      rw [m1Below _ (by omega), Nat.add_assoc]
      exact labelCells _ (by omega))
    (fun i ib => by
      show m1.ram (word (cc.pinBase + 128 * c + i)) = _
      have ib128 : i < 128 := lt_of_lt_of_le ib (by decide : laneCount ≤ 128)
      rw [m1Below _ (by omega)]
      exact pinCells c cb i ib)
    (fun k s kb sb => tagTreeSmall c k s cb kb sb)
    (fun leaf j lb jb => tagCastSmall c leaf j cb lb jb)) fun result after post => ?_
  obtain ⟨leaves, casts, frameC⟩ := post
  -- every cell the step writes lies in the loop's interval
  have inLoop : ∀ address, (Writes.union (treeEvalWrites (cc.tree (T.chunkOffset c) c) (T.chunkWidth c))
      (chunkCastWrites (cc.cast c) (T.chunkWidth c) T.castWidth)) address →
      chunkLoopWrites cc count address := by
    rintro address ((inside | inside) | (inside | inside))
    · exact region_in_interval _ _ _ (by simp [CoordCells.tree]; omega)
        (by simp [CoordCells.tree]; omega) address inside
    · exact region_in_interval _ _ _ (by simp [CoordCells.tree]; omega)
        (by simp [CoordCells.tree]; omega) address inside
    · exact region_in_interval _ _ _ (by simp [CoordCells.cast]; omega)
        (by simp [CoordCells.cast]; omega) address inside
    · exact region_in_interval _ _ _ (by simp [CoordCells.cast]; omega)
        (by simp [CoordCells.cast]; omega) address inside
  -- every region the replay writes lies below the leaf region
  have notReplay : ∀ x, cc.castBase + 32768 * count ≤ x → x < 2 ^ 256 →
      ¬ (Writes.union (treeEvalWrites (cc.tree (T.chunkOffset c) c) (T.chunkWidth c))
        (chunkCastWrites (cc.cast c) (T.chunkWidth c) T.castWidth)) (word x) := by
    intro x xLow xSmall
    rintro ((inside | inside) | (inside | inside))
    · exact not_region_of_apart _ _ xSmall (by simp [CoordCells.tree]; omega)
        (Or.inr (by simp [CoordCells.tree]; omega)) inside
    · exact not_region_of_apart _ _ xSmall (by simp [CoordCells.tree]; omega)
        (Or.inr (by simp [CoordCells.tree]; omega)) inside
    · exact not_region_of_apart _ _ xSmall (by simp [CoordCells.cast]; omega)
        (Or.inr (by simp [CoordCells.cast]; omega)) inside
    · exact not_region_of_apart _ _ xSmall (by simp [CoordCells.cast]; omega)
        (Or.inr (by simp [CoordCells.cast]; omega)) inside
  have castsAfter : ∀ c' (bound : c' < c + 1), ∀ leaf, leaf < 2 ^ T.chunkWidth c' →
      ∀ i (ib : i < laneCount), after.ram (word (cc.castBase + 32768 * c' + 128 * leaf + i)) =
        word ((((values.push result)[c']'bound).casts leaf) ⟨i, ib⟩).val := by
    intro c' bound leaf lb i ib
    by_cases last : c' = c
    · subst last
      simp only [Vector.getElem_push_eq]
      exact casts leaf lb i ib
    · have lt : c' < c := by omega
      simp only [Vector.getElem_push_lt lt]
      have w8' := shape.widthSmall c' (by omega)
      have p0' := pow_le_256 (T.chunkWidth c') w8'
      have ib128 : i < 128 := lt_of_lt_of_le ib (by decide : laneCount ≤ 128)
      have c1' : 32768 * c' + 32768 ≤ 32768 * c := by omega
      rw [frameC.ram _ ?_, ram1, Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
      · exact done c' lt leaf lb i ib
      · rintro ((inside | inside) | (inside | inside))
        · exact not_region_of_apart _ _ (by omega) (by simp [CoordCells.tree]; omega)
            (Or.inr (by simp [CoordCells.tree]; omega)) inside
        · exact not_region_of_apart _ _ (by omega) (by simp [CoordCells.tree]; omega)
            (Or.inr (by simp [CoordCells.tree]; omega)) inside
        · exact not_region_of_apart _ _ (by omega) (by simp [CoordCells.cast]; omega)
            (Or.inr (by simp [CoordCells.cast]; omega)) inside
        · exact not_region_of_apart _ _ (by omega) (by simp [CoordCells.cast]; omega)
            (Or.inl (by simp [CoordCells.cast]; omega)) inside
  have frameAfter : ∀ address, ¬ chunkLoopWrites cc count address →
      after.ram address = start.ram address := fun address off => by
    rw [frameC.ram address fun inside => off (inLoop address inside), ram1,
      Function.update_of_ne (fun same => off ⟨cc.alpha, le_rfl, by omega, same⟩)]
    exact frame address off
  have c256 : 256 * c + 256 ≤ 256 * count := by omega
  obtain ⟨final, runS, savedS, frameS, bitsS, regsS⟩ := exec_saveLeaves cc.levelBase cc.leafBase
    (T.chunkWidth c) c after (by omega) (by omega)
  have offLeaves : ∀ x, x < cc.leafBase + 256 * c → final.ram (word x) = after.ram (word x) :=
    fun x xb => frameS _ fun leaf lb same => by
      have := word_inj (by omega) (by omega) same
      omega
  refine ⟨final, runS, fun c' bound leaf lb i ib => ?_, fun c' bound leaf lb => ?_,
    fun address off => ?_, ?_, fun register outside => ?_⟩
  · have w8' := shape.widthSmall c' (by omega)
    have p0' := pow_le_256 (T.chunkWidth c') w8'
    have ib' : i < 128 := lt_of_lt_of_le ib (by decide : laneCount ≤ 128)
    have c1' : 32768 * c' + 32768 ≤ 32768 * count := by omega
    rw [offLeaves _ (by omega)]
    exact castsAfter c' bound leaf lb i ib
  · by_cases last : c' = c
    · subst last
      simp only [Vector.getElem_push_eq]
      rw [savedS leaf lb]
      exact leaves leaf lb
    · have lt : c' < c := by omega
      simp only [Vector.getElem_push_lt lt]
      have w8' := shape.widthSmall c' (by omega)
      have p0' := pow_le_256 (T.chunkWidth c') w8'
      have c2 : 256 * c' + 256 ≤ 256 * c := by omega
      rw [offLeaves _ (by omega), frameC.ram _ (notReplay _ (by omega) (by omega)), ram1,
        Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
      exact leavesDone c' lt leaf lb
  · rw [frameS address fun leaf lb same => off ⟨_, by omega, by omega, same⟩]
    exact frameAfter address off
  · rw [bitsS, frameC.bits, bits1]
    exact bitsSame
  · rw [regsS register (fun h => outside (by simp [chunkLoopClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [chunkLoopClobbers, Clobbers.ofList, h])),
      frameC.registers register fun inside => outside (clobbers_chunkLoop register inside),
      regs1 register (fun h => outside (by simp [chunkLoopClobbers, Clobbers.ofList, h]))
        (fun h => outside (by simp [chunkLoopClobbers, Clobbers.ofList, h]))
        (fun h => outside (by simp [chunkLoopClobbers, Clobbers.ofList, h]))]
    exact regs register outside

/-- **The chunks of a coordinate** against the evaluator's chunk table (the first step of
`coordEvalM`): the same questions in the same order, every chunk's cast lanes in the output region,
and the frame of the whole interval. -/
theorem agree_chunkLoop (T : CrtTable) (coord : Nat) (cc : CoordCells) (count : Nat)
    (chain : CoordChain cc count T.castWidth)
    (bits : Nat) (shape : ChunkShape T.chunkOffset T.chunkWidth count bits)
    (lPos : 0 < T.castWidth) (lSmall : T.castWidth ≤ 128)
    (labels : Nat → Block) (v : Nat) (vSmall : v < 2 ^ 256) (joins : Nat → Nat → Label)
    (pins : Nat → Lanes T.castWidth) (memory : Memory)
    (coordVal : memory.ram (word cc.coordCell) = word v)
    (labelCells : ∀ j, j < bits → memory.ram (word (cc.labelBase + j)) = blockWord (labels j))
    (joinCells : ∀ c, c < count → ∀ n, 1 ≤ n → n < T.chunkWidth c →
      memory.ram (word (cc.chunkJoin c n)) = labelWord (joins c n))
    (pinCells : ∀ c, c < count → ∀ i (ib : i < laneCount),
      memory.ram (word (cc.pinBase + 128 * c + i)) = word ((pins c) ⟨i, ib⟩).val)
    (tagTreeSmall : ∀ c k s, c < count → k < T.chunkWidth c → s < 2 ^ k →
      chunkTreeTag coord c k s < 2 ^ 127)
    (tagCastSmall : ∀ c leaf j, c < count → leaf < 2 ^ T.chunkWidth c → j < castAnswers T.castWidth →
      chunkCastTag coord c leaf j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (chunks : Fin count → ChunkEval T.castWidth) after =>
        (∀ c (cb : c < count), ∀ leaf, leaf < 2 ^ T.chunkWidth c → ∀ i (ib : i < laneCount),
          after.ram (word (cc.castBase + 32768 * c + 128 * leaf + i)) =
            word (((chunks ⟨c, cb⟩).casts leaf) ⟨i, ib⟩).val) ∧
          (∀ c (cb : c < count), ∀ leaf, leaf < 2 ^ T.chunkWidth c →
            after.ram (word (cc.leafBase + 256 * c + leaf)) = labelWord ((chunks ⟨c, cb⟩).leaves leaf)) ∧
          Frame (chunkLoopWrites cc count) chunkLoopClobbers memory after)
      ((chunkLoop cc T.chunkOffset T.chunkWidth (chunkTreeTag coord) (chunkCastTag coord) T.castWidth
        count).tree memory)
      (liftHash (tableM count fun c => chunkEvalM T coord (fun j => clip (labels j)) v (joins c.val) (pins c.val) c.val)) := by
  have loop := agree_rep_vector_plain (FixedIndex := FixedIndex) (EncIndex := EncIndex)
    (chunkStep cc T.chunkOffset T.chunkWidth (chunkTreeTag coord) (chunkCastTag coord) T.castWidth)
    (ChunkLoopInv cc T.chunkWidth T.castWidth count memory) count
    (fun c => liftHash (chunkEvalM T coord (fun j => clip (labels j)) v (joins c.val) (pins c.val) c.val))
    (fun index values current holds =>
      agree_chunkStep T coord cc count chain bits shape lPos lSmall labels v vSmall joins pins memory
        coordVal labelCells joinCells pinCells tagTreeSmall tagCastSmall index values current holds)
    memory ⟨fun c bound => absurd bound (Nat.not_lt_zero _), fun c bound => absurd bound (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  unfold chunkLoop tableM
  rw [TreeLaws.monad_bind, liftHash_bind, liftHash_vector, ← bindOpt_pure_right
    ((Prog.rep count (chunkStep cc T.chunkOffset T.chunkWidth (chunkTreeTag coord) (chunkCastTag coord)
      T.castWidth)).tree memory)]
  refine Agree.bindOpt (fun values after inv => ?_) loop
  obtain ⟨casts, leaves, frame, bits, regs⟩ := inv
  refine .leaf ⟨fun c cb leaf lb i ib => ?_, fun c cb leaf lb => ?_, ⟨frame, bits, regs⟩⟩
  · rw [Vector.get_eq_getElem]
    exact casts c cb leaf lb i ib
  · rw [Vector.get_eq_getElem]
    exact leaves c cb leaf lb

/-- The chunk tags are small (arithmetic on `tagCode`). -/
theorem chunkTreeTag_lt (coord c k s : Nat) (coordLt : coord < 2) (cLt : c < 128) (kLt : k < 16)
    (sLt : s < 65536) : chunkTreeTag coord c k s < 2 ^ 127 := by
  unfold chunkTreeTag tagCode Family.chunkTree
  have : (2 : Nat) ^ 40 < 2 ^ 127 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have : (2 : Nat) ^ 40 = 1099511627776 := by norm_num
  omega

theorem chunkCastTag_lt (coord c leaf part : Nat) (coordLt : coord < 2) (cLt : c < 128)
    (leafLt : leaf < 65536) (partLt : part < 64) : chunkCastTag coord c leaf part < 2 ^ 127 := by
  unfold chunkCastTag tagCode Family.chunkCast
  have : (2 : Nat) ^ 40 < 2 ^ 127 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have : (2 : Nat) ^ 40 = 1099511627776 := by norm_num
  omega

/-- **The chunks of a coordinate**, with the tag bounds discharged (`coord < 2`, at most 128 chunks,
at most 64 answers per cast). -/
theorem agree_chunkLoop_tags (T : CrtTable) (coord : Nat) (coordLt : coord < 2) (cc : CoordCells)
    (count : Nat) (countLe : count ≤ 128) (chain : CoordChain cc count T.castWidth)
    (bits : Nat) (shape : ChunkShape T.chunkOffset T.chunkWidth count bits)
    (lPos : 0 < T.castWidth) (lSmall : T.castWidth ≤ 128) (answersLe : castAnswers T.castWidth ≤ 64)
    (labels : Nat → Block) (v : Nat) (vSmall : v < 2 ^ 256) (joins : Nat → Nat → Label)
    (pins : Nat → Lanes T.castWidth) (memory : Memory)
    (coordVal : memory.ram (word cc.coordCell) = word v)
    (labelCells : ∀ j, j < bits → memory.ram (word (cc.labelBase + j)) = blockWord (labels j))
    (joinCells : ∀ c, c < count → ∀ n, 1 ≤ n → n < T.chunkWidth c →
      memory.ram (word (cc.chunkJoin c n)) = labelWord (joins c n))
    (pinCells : ∀ c, c < count → ∀ i (ib : i < laneCount),
      memory.ram (word (cc.pinBase + 128 * c + i)) = word ((pins c) ⟨i, ib⟩).val) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (chunks : Fin count → ChunkEval T.castWidth) after =>
        (∀ c (cb : c < count), ∀ leaf, leaf < 2 ^ T.chunkWidth c → ∀ i (ib : i < laneCount),
          after.ram (word (cc.castBase + 32768 * c + 128 * leaf + i)) =
            word (((chunks ⟨c, cb⟩).casts leaf) ⟨i, ib⟩).val) ∧
          (∀ c (cb : c < count), ∀ leaf, leaf < 2 ^ T.chunkWidth c →
            after.ram (word (cc.leafBase + 256 * c + leaf)) = labelWord ((chunks ⟨c, cb⟩).leaves leaf)) ∧
          Frame (chunkLoopWrites cc count) chunkLoopClobbers memory after)
      ((chunkLoop cc T.chunkOffset T.chunkWidth (chunkTreeTag coord) (chunkCastTag coord) T.castWidth
        count).tree memory)
      (liftHash (tableM count fun c => chunkEvalM T coord (fun j => clip (labels j)) v (joins c.val) (pins c.val) c.val)) :=
  agree_chunkLoop T coord cc count chain bits shape lPos lSmall labels v vSmall joins pins memory coordVal
    labelCells joinCells pinCells
    (fun c k s cb kb sb => chunkTreeTag_lt coord c k s coordLt (by omega)
      (by have := shape.widthSmall c cb; omega)
      (by have := shape.widthSmall c cb
          have : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega))
    (fun c leaf j cb lb jb => chunkCastTag_lt coord c leaf j coordLt (by omega)
      (by have := shape.widthSmall c cb
          have : 2 ^ T.chunkWidth c ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)
      (by omega))

end Loop

end Kriterion.CRT.SimMachine
