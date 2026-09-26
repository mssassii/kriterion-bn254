/-
**Route M's masks on the machine** (`agree_maskStage`): the machine's `maskStage` against
`liftHash (nonCollectorMasksM K digits)`, the last step of `replayRouteM`. Every pair site's two
masks and the single site's mask end up as `fieldWord`s in their cells, with the frame of the
stage.
-/

import Proof.Simulator.CRT.ReplayBody
import Proof.Simulator.ReplayElement
import Construction.Simulator.CRT.ReplayMasks

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC BN254
open Kriterion.ArgoMAC.PlanB (sampleFp)

section Masks

variable [BN254.FieldCertificate]

/-! ### Three blocks to a field element -/

theorem exec_fpLow (src : Nat) (memory : Memory) (a b : Block)
    (cellA : memory.ram (word src) = blockWord a) (cellB : memory.ram (word (src + 1)) = blockWord b) :
    ∃ after, (fpLow src).exec memory = some after ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rA = fieldWord ((a.toNat : BaseField) + (b.toNat : BaseField) * 2 ^ 128) ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, cellA, cellB]
    rw [eval_fieldAdd, eval_fieldMul, fieldWord_cast, blockWord_toNat, blockWord_toNat,
      word_two_pow_128]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

theorem exec_fpHigh (src dst : Nat) (memory : Memory) (c : Block) (low : BaseField)
    (cellC : memory.ram (word (src + 2)) = blockWord c) (lowReg : memory.registers rA = fieldWord low) :
    ∃ after, (fpHigh src dst).exec memory = some after ∧
      after.ram = Function.update memory.ram (word dst)
        (fieldWord (low + (c.toNat : BaseField) * 2 ^ 256)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte, cellC,
      lowReg]
    rw [eval_fieldAdd, eval_fieldMul, fieldWord_cast, fieldWord_cast, blockWord_toNat, word_c256]
  · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-- **`sampleFp` on the machine.** -/
theorem exec_fpRead (src dst : Nat) (memory : Memory) (a b c : Block)
    (cellA : memory.ram (word src) = blockWord a) (cellB : memory.ram (word (src + 1)) = blockWord b)
    (cellC : memory.ram (word (src + 2)) = blockWord c) :
    ∃ after, (fpRead src dst).exec memory = some after ∧
      after.ram = Function.update memory.ram (word dst) (fieldWord (sampleFp a b c)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨m1, run1, ram1, bits1, low1, regs1⟩ := exec_fpLow src memory a b cellA cellB
  obtain ⟨m2, run2, ram2, bits2, regs2⟩ := exec_fpHigh src dst m1 c _ (by rw [ram1]; exact cellC) low1
  refine ⟨m2, by rw [fpRead, Prog.exec_seq_some _ _ _ _ run1, run2], ?_, by rw [bits2, bits1],
    fun register n1 n2 n3 n4 => by rw [regs2 register n1 n2 n3 n4, regs1 register n1 n2 n3 n4]⟩
  rw [ram2, ram1, sampleFp_eq]

omit [BN254.FieldCertificate] in
theorem det_fpRead (src dst : Nat) : (fpRead src dst).OpsSatisfy Op.Det :=
  ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial⟩,
    ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩⟩

/-! ### The layout -/

/-- The layout of the mask stage for `count` entries: the key, the answer scratch and the mask
cells pairwise apart, all in range. -/
structure MaskLayout (mc : MaskCells) (count : Nat) : Prop where
  keySmall : mc.key < 2 ^ 256
  ansFits : mc.ansBase + 6 < 2 ^ 256
  keyOff : ∀ b, b < 6 → mc.key ≠ mc.ansBase + b
  maskSmall : ∀ n, n < count → mc.maskOf n < 2 ^ 256
  maskOffAns : ∀ n, n < count → ∀ b, b < 6 → mc.maskOf n ≠ mc.ansBase + b
  maskOffKey : ∀ n, n < count → mc.maskOf n ≠ mc.key
  maskInj : ∀ n, n < count → ∀ n', n' < count → n ≠ n' → mc.maskOf n ≠ mc.maskOf n'

theorem MaskLayout.not_writes (mc : MaskCells) (count : Nat) (layout : MaskLayout mc count)
    (limit : Nat) (le : limit ≤ count) : ¬ maskWrites mc limit (word mc.key) := by
  rintro (⟨b, bb, same⟩ | ⟨n, nb, same⟩)
  · dsimp only at bb same
    have := layout.ansFits
    exact layout.keyOff b bb (word_inj layout.keySmall (by omega) same)
  · exact layout.maskOffKey n (by omega)
      (word_inj (layout.maskSmall n (by omega)) layout.keySmall same.symm)

private theorem clobbers_cast (register : Register) (inside : castClobbers register) :
    maskClobbers register := by
  simp only [castClobbers, maskClobbers, Clobbers.ofList, List.mem_cons, List.not_mem_nil,
    or_false] at inside ⊢
  rcases inside with h | h | h | h | h | h <;> simp [h]

private theorem clobbers_fp (register : Register)
    (inside : register = rA ∨ register = rB ∨ register = rC ∨ register = rAddr) :
    maskClobbers register := by
  simp only [maskClobbers, Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false]
  rcases inside with h | h | h | h <;> simp [h]

/-! ### One site -/

variable {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The writes of pair site `k`: the answer scratch and its two mask cells. -/
def pairWrites (mc : MaskCells) (k : Nat) : Writes :=
  (Writes.region ⟨mc.ansBase, 6⟩).union
    ((Writes.cell (mc.maskOf (2 * k))).union (Writes.cell (mc.maskOf (2 * k + 1))))

/-- **Pair site `k`**: three answers, the two masks. -/
theorem agree_maskPairSite (mc : MaskCells) (count k : Nat) (layout : MaskLayout mc count)
    (kb : 2 * k + 1 < count) (K : Block) (memory : Memory)
    (keyCell : memory.ram (word mc.key) = blockWord K)
    (tagSmall : ∀ part, part < 3 → maskTag 1 k part < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (masks : BaseField × BaseField) after =>
        after.ram (word (mc.maskOf (2 * k))) = fieldWord masks.1 ∧
          after.ram (word (mc.maskOf (2 * k + 1))) = fieldWord masks.2 ∧
          Frame (pairWrites mc k) maskClobbers memory after)
      ((maskPairSite mc k).tree memory)
      (liftHash (siteAnswersM K 1 k 3 >>= fun answers => pure (readPair answers))) := by
  have := layout.ansFits
  have m0 := layout.maskSmall (2 * k) (by omega)
  have m1 := layout.maskSmall (2 * k + 1) (by omega)
  unfold maskPairSite siteAnswersM tableM
  rw [TreeLaws.monad_bind, TreeLaws.monad_bind, TreeLaws.bind_assoc, liftHash_bind, liftHash_vector,
    tree_seq]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_ansQueries mc.site 3 (by simp only [MaskCells.site]; omega) layout.keySmall
      (fun b bb => layout.keyOff b (by omega)) (maskTag 1 k) K memory keyCell tagSmall)
  obtain ⟨done, frame, bitsSame, regs⟩ := inv
  have c0 := (done 0 (by norm_num)).1
  have c1 := (done 0 (by norm_num)).2
  have c2 := (done 1 (by norm_num)).1
  have c3 := (done 1 (by norm_num)).2
  have c4 := (done 2 (by norm_num)).1
  have c5 := (done 2 (by norm_num)).2
  dsimp only [MaskCells.site] at c0 c1 c2 c3 c4 c5
  rw [show mc.ansBase + 2 * 0 = mc.ansBase from rfl] at c0
  rw [show mc.ansBase + (2 * 0 + 1) = mc.ansBase + 1 from rfl] at c1
  rw [show mc.ansBase + 2 * 1 = mc.ansBase + 2 from rfl] at c2
  rw [show mc.ansBase + (2 * 1 + 1) = mc.ansBase + 3 from rfl] at c3
  rw [show mc.ansBase + 2 * 2 = mc.ansBase + 3 + 1 from rfl] at c4
  rw [show mc.ansBase + (2 * 2 + 1) = mc.ansBase + 3 + 2 from rfl] at c5
  obtain ⟨n1, run1, ram1, bits1, regs1⟩ := exec_fpRead mc.ansBase (mc.maskOf (2 * k)) after _ _ _
    c0 c1 c2
  have keep1 : ∀ b, b < 6 → n1.ram (word (mc.ansBase + b)) = after.ram (word (mc.ansBase + b)) :=
    fun b bb => by
      rw [ram1, Function.update_of_ne (fun same => layout.maskOffAns (2 * k) (by omega) b bb
        (word_inj (by omega) m0 same).symm)]
  obtain ⟨n2, run2, ram2, bits2, regs2⟩ := exec_fpRead (mc.ansBase + 3) (mc.maskOf (2 * k + 1)) n1
    _ _ _ (by rw [keep1 3 (by norm_num)]; exact c3) (by rw [keep1 4 (by norm_num)]; exact c4)
    (by rw [keep1 5 (by norm_num)]; exact c5)
  have det : (Prog.seq (fpRead mc.ansBase (mc.maskOf (2 * k)))
      (fpRead (mc.ansBase + 3) (mc.maskOf (2 * k + 1)))).OpsSatisfy Op.Det :=
    ⟨det_fpRead _ _, det_fpRead _ _⟩
  rw [tree_eq_exec _ det, Prog.exec_seq_some _ _ _ _ run1, run2]
  have apart := layout.maskInj (2 * k) (by omega) (2 * k + 1) (by omega) (by omega)
  refine .leaf ⟨?_, ?_, ⟨fun address off => ?_, ?_, fun register outside => ?_⟩⟩
  · rw [ram2, Function.update_of_ne (fun same => apart (word_inj m0 m1 same)), ram1,
      Function.update_self]
    simp only [readPair, Vector.get_eq_getElem]
    rfl
  · rw [ram2, Function.update_self]
    simp only [readPair, Vector.get_eq_getElem]
    rfl
  · rw [ram2, Function.update_of_ne (fun same => off (Or.inr (Or.inr same))), ram1,
      Function.update_of_ne (fun same => off (Or.inr (Or.inl same)))]
    exact frame address fun b bb same => off (Or.inl ⟨b, by omega, same⟩)
  · rw [bits2, bits1]
    exact bitsSame
  · have nA : register ≠ rA := fun h => outside (clobbers_fp register (Or.inl h))
    have nB : register ≠ rB := fun h => outside (clobbers_fp register (Or.inr (Or.inl h)))
    have nC : register ≠ rC := fun h => outside (clobbers_fp register (Or.inr (Or.inr (Or.inl h))))
    have nD : register ≠ rAddr := fun h => outside (clobbers_fp register (Or.inr (Or.inr (Or.inr h))))
    rw [regs2 register nA nB nC nD, regs1 register nA nB nC nD]
    exact regs register fun inside => outside (clobbers_cast register inside)

/-- The writes of the single site (entry `n`): the answer scratch and its mask cell. -/
def singleWrites (mc : MaskCells) (n : Nat) : Writes :=
  (Writes.region ⟨mc.ansBase, 6⟩).union (Writes.cell (mc.maskOf n))

/-- **The single site** (after `pairs` pair sites): two answers, one mask. -/
theorem agree_maskSingleSite (mc : MaskCells) (count pairs : Nat) (layout : MaskLayout mc count)
    (pb : 2 * pairs < count) (K : Block) (memory : Memory)
    (keyCell : memory.ram (word mc.key) = blockWord K)
    (tagSmall : ∀ part, part < 2 → maskTag 1 pairs part < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (mask : BaseField) after =>
        after.ram (word (mc.maskOf (2 * pairs))) = fieldWord mask ∧
          Frame (singleWrites mc (2 * pairs)) maskClobbers memory after)
      ((maskSingleSite mc pairs).tree memory)
      (liftHash (siteAnswersM K 1 pairs 2 >>= fun answers => pure (readSingle answers))) := by
  have := layout.ansFits
  have m0 := layout.maskSmall (2 * pairs) pb
  unfold maskSingleSite siteAnswersM tableM
  rw [TreeLaws.monad_bind, TreeLaws.monad_bind, TreeLaws.bind_assoc, liftHash_bind, liftHash_vector,
    tree_seq]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_ansQueries mc.site 2 (by simp only [MaskCells.site]; omega) layout.keySmall
      (fun b bb => layout.keyOff b (by omega)) (maskTag 1 pairs) K memory keyCell tagSmall)
  obtain ⟨done, frame, bitsSame, regs⟩ := inv
  have c0 := (done 0 (by norm_num)).1
  have c1 := (done 0 (by norm_num)).2
  have c2 := (done 1 (by norm_num)).1
  dsimp only [MaskCells.site] at c0 c1 c2
  rw [show mc.ansBase + 2 * 0 = mc.ansBase from rfl] at c0
  rw [show mc.ansBase + (2 * 0 + 1) = mc.ansBase + 1 from rfl] at c1
  rw [show mc.ansBase + 2 * 1 = mc.ansBase + 2 from rfl] at c2
  obtain ⟨n1, run1, ram1, bits1, regs1⟩ := exec_fpRead mc.ansBase (mc.maskOf (2 * pairs)) after _ _ _
    c0 c1 c2
  rw [tree_eq_exec _ (det_fpRead _ _), run1]
  refine .leaf ⟨?_, ⟨fun address off => ?_, ?_, fun register outside => ?_⟩⟩
  · rw [ram1, Function.update_self]
    simp only [readSingle, Vector.get_eq_getElem]
    rfl
  · rw [ram1, Function.update_of_ne (fun same => off (Or.inr same))]
    exact frame address fun b bb same => off (Or.inl ⟨b, by show b < 6; omega, same⟩)
  · rw [bits1]
    exact bitsSame
  · have nA : register ≠ rA := fun h => outside (clobbers_fp register (Or.inl h))
    have nB : register ≠ rB := fun h => outside (clobbers_fp register (Or.inr (Or.inl h)))
    have nC : register ≠ rC := fun h => outside (clobbers_fp register (Or.inr (Or.inr (Or.inl h))))
    have nD : register ≠ rAddr := fun h => outside (clobbers_fp register (Or.inr (Or.inr (Or.inr h))))
    rw [regs1 register nA nB nC nD]
    exact regs register fun inside => outside (clobbers_cast register inside)

/-! ### The pair loop -/

/-- The invariant of the pair loop after `k` sites. -/
def PairInv (mc : MaskCells) (start : Memory) (k : Nat) (values : Vector (BaseField × BaseField) k)
    (memory : Memory) : Prop :=
  (∀ k' (bound : k' < k), memory.ram (word (mc.maskOf (2 * k'))) = fieldWord (values[k']'bound).1 ∧
      memory.ram (word (mc.maskOf (2 * k' + 1))) = fieldWord (values[k']'bound).2) ∧
    Frame (maskWrites mc (2 * k)) maskClobbers start memory

private theorem clobbers_union (register : Register)
    (inside : (maskClobbers.union maskClobbers) register) : maskClobbers register := by
  rcases inside with inside | inside <;> exact inside

theorem agree_pairStep (mc : MaskCells) (count pairs : Nat) (layout : MaskLayout mc count)
    (pairsLe : 2 * pairs ≤ count) (K : Block) (start : Memory)
    (keyCell : start.ram (word mc.key) = blockWord K)
    (tagSmall : ∀ k part, k < pairs → part < 3 → maskTag 1 k part < 2 ^ 127)
    (index : Fin pairs) (values : Vector (BaseField × BaseField) index.val) (memory : Memory)
    (holds : PairInv mc start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : BaseField × BaseField) after =>
        PairInv mc start (index.val + 1) (values.push result) after)
      ((maskPairSite mc index.val).tree memory)
      (liftHash (siteAnswersM K 1 index.val 3 >>= fun answers => pure (readPair answers))) := by
  obtain ⟨k, kb⟩ := index
  simp only at values holds ⊢
  obtain ⟨done, frame⟩ := holds
  have := layout.ansFits
  have keyNow : memory.ram (word mc.key) = blockWord K := by
    rw [frame.ram _ (MaskLayout.not_writes mc count layout (2 * k) (by omega))]
    exact keyCell
  refine (agree_maskPairSite mc count k layout (by omega) K memory keyNow
    (fun part pb => tagSmall k part kb pb)).mono fun result after post => ?_
  obtain ⟨r0, r1, frameS⟩ := post
  refine ⟨fun k' bound => ?_, ?_⟩
  · by_cases last : k' = k
    · subst last
      simp only [Vector.getElem_push_eq]
      exact ⟨r0, r1⟩
    · have lt : k' < k := by omega
      simp only [Vector.getElem_push_lt lt]
      have off : ∀ n, n < 2 * k → ¬ pairWrites mc k (word (mc.maskOf n)) := by
        intro n nb
        have mn := layout.maskSmall n (by omega)
        rintro (⟨b, bb, same⟩ | (same | same))
        · dsimp only at bb same
          exact layout.maskOffAns n (by omega) b bb (word_inj mn (by omega) same)
        · exact layout.maskInj n (by omega) (2 * k) (by omega) (by omega)
            (word_inj mn (layout.maskSmall _ (by omega)) same)
        · exact layout.maskInj n (by omega) (2 * k + 1) (by omega) (by omega)
            (word_inj mn (layout.maskSmall _ (by omega)) same)
      rw [frameS.ram _ (off (2 * k') (by omega)), frameS.ram _ (off (2 * k' + 1) (by omega))]
      exact done k' lt
  · refine (frame.trans frameS).mono ?_ clobbers_union
    rintro address ((inside | ⟨n, nb, same⟩) | (⟨b, bb, same⟩ | (same | same)))
    · exact Or.inl inside
    · exact Or.inr ⟨n, by omega, same⟩
    · exact Or.inl ⟨b, bb, same⟩
    · exact Or.inr ⟨2 * k, by omega, same⟩
    · exact Or.inr ⟨2 * k + 1, by omega, same⟩

/-- **The mask stage** against `liftHash (nonCollectorMasksM K digits)`. -/
theorem agree_maskStage (mc : MaskCells) (digits : Nat)
    (layout : MaskLayout mc (nonCollectorCount digits)) (K : Block) (memory : Memory)
    (keyCell : memory.ram (word mc.key) = blockWord K)
    (tagSmall : ∀ site part, site ≤ pairSites digits → part < 3 → maskTag 1 site part < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : (Fin (pairSites digits) → BaseField × BaseField) × BaseField) after =>
        (∀ k (kb : k < pairSites digits),
          after.ram (word (mc.maskOf (2 * k))) = fieldWord (result.1 ⟨k, kb⟩).1 ∧
            after.ram (word (mc.maskOf (2 * k + 1))) = fieldWord (result.1 ⟨k, kb⟩).2) ∧
          (singleSites digits = 1 →
            after.ram (word (mc.maskOf (2 * pairSites digits))) = fieldWord result.2) ∧
          Frame (maskWrites mc (nonCollectorCount digits)) maskClobbers memory after)
      ((maskStage mc digits).tree memory)
      (liftHash (nonCollectorMasksM K digits)) := by
  have split : 2 * pairSites digits + singleSites digits = nonCollectorCount digits := by
    unfold pairSites singleSites
    omega
  have := layout.ansFits
  unfold maskStage nonCollectorMasksM pairMasksM tableM
  rw [tree_seq, TreeLaws.monad_bind, TreeLaws.monad_bind, TreeLaws.bind_assoc, liftHash_bind,
    liftHash_vector]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_rep_vector_plain (maskPairSite mc) (PairInv mc memory) (pairSites digits) _
      (fun index values current holds =>
        agree_pairStep mc (nonCollectorCount digits) (pairSites digits) layout (by omega) K memory
          keyCell (fun k part kb pb => tagSmall k part (by omega) pb) index values current holds)
      memory ⟨fun k bound => absurd bound (Nat.not_lt_zero _), Frame.refl _ _ _⟩)
  obtain ⟨done, frame⟩ := inv
  have pairsDone : ∀ k (kb : k < pairSites digits),
      after.ram (word (mc.maskOf (2 * k))) = fieldWord (values.get ⟨k, kb⟩).1 ∧
        after.ram (word (mc.maskOf (2 * k + 1))) = fieldWord (values.get ⟨k, kb⟩).2 := fun k kb => by
    rw [Vector.get_eq_getElem]
    exact done k kb
  have frameUp : Frame (maskWrites mc (nonCollectorCount digits)) maskClobbers memory after :=
    frame.mono (fun address inside => by
      rcases inside with inside | ⟨n, nb, same⟩
      · exact Or.inl inside
      · exact Or.inr ⟨n, by omega, same⟩) (fun _ inside => inside)
  by_cases single : singleSites digits = 1
  · rw [if_pos single]
    unfold singleMaskM
    rw [if_pos single]
    have keyNow : after.ram (word mc.key) = blockWord K := by
      rw [frame.ram _ (MaskLayout.not_writes mc (nonCollectorCount digits) layout _ (by omega))]
      exact keyCell
    show Agree _ _ (liftHash (FreeQuery.bind (FreeQuery.pure values.get) fun pairs =>
      FreeQuery.bind (FreeQuery.bind (siteAnswersM K 1 (pairSites digits) 2) fun answers =>
        FreeQuery.pure (readSingle answers)) fun single => FreeQuery.pure (pairs, single)))
    rw [liftHash_bind, liftHash_pure]
    show Agree _ _ (liftHash (FreeQuery.bind (FreeQuery.bind (siteAnswersM K 1 (pairSites digits) 2)
      fun answers => FreeQuery.pure (readSingle answers)) fun single => FreeQuery.pure (values.get, single)))
    rw [liftHash_bind, ← bindOpt_pure_right ((maskSingleSite mc (pairSites digits)).tree after)]
    refine Agree.bindOpt (fun mask final post => ?_)
      (agree_maskSingleSite mc (nonCollectorCount digits) (pairSites digits) layout (by omega) K after
        keyNow (fun part pb => tagSmall _ part le_rfl (by omega)))
    obtain ⟨m0, frameS⟩ := post
    refine .leaf ⟨fun k kb => ?_, fun _ => m0, ?_⟩
    · have off : ∀ n, n < 2 * pairSites digits → ¬ singleWrites mc (2 * pairSites digits) (word (mc.maskOf n)) := by
        intro n nb
        have mn := layout.maskSmall n (by omega)
        rintro (⟨b, bb, same⟩ | same)
        · dsimp only at bb same
          exact layout.maskOffAns n (by omega) b bb (word_inj mn (by omega) same)
        · exact layout.maskInj n (by omega) (2 * pairSites digits) (by omega) (by omega)
            (word_inj mn (layout.maskSmall _ (by omega)) same)
      rw [frameS.ram _ (off (2 * k) (by omega)), frameS.ram _ (off (2 * k + 1) (by omega))]
      exact pairsDone k kb
    · refine (frameUp.trans frameS).mono ?_ clobbers_union
      rintro address (inside | (⟨b, bb, same⟩ | same))
      · exact inside
      · exact Or.inl ⟨b, bb, same⟩
      · exact Or.inr ⟨2 * pairSites digits, by omega, same⟩
  · rw [if_neg single]
    unfold singleMaskM
    rw [if_neg single]
    exact .leaf ⟨pairsDone, fun h => absurd h single, frameUp⟩

end Masks

end Kriterion.CRT.SimMachine
