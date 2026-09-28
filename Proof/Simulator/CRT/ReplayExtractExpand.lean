/-
**One expansion of a stage** (package M4a, part 3): the evaluator's state in RAM (`StageRel`) and
the agreement of `expandReplay` with `expandM`.
-/

import Proof.Simulator.CRT.ReplayExtractLeaf

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### The cells of the stage's write set -/

section Writes

variable (cells : StageCells) (w rb : Nat)

theorem sw_sub {i : Nat} (bound : i < laneCount) : stageWrites cells w rb (word (cells.subBase + i)) :=
  Or.inl ⟨i, bound, rfl⟩

theorem sw_node {x : Nat} (bound : x < 2 ^ w) : stageWrites cells w rb (word (cells.nodeBase + x)) :=
  Or.inr <| Or.inl ⟨x, bound, rfl⟩

theorem sw_mat {t : Nat} (bound : t < 2 ^ w) : stageWrites cells w rb (word (cells.matBase + t)) :=
  Or.inr <| Or.inr <| Or.inl ⟨t, bound, rfl⟩

theorem sw_levelSum {L : Nat} (bound : L < w) :
    stageWrites cells w rb (word (cells.levelSumBase + L)) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨L, bound, rfl⟩

theorem sw_class {j i : Nat} (jb : j ≤ w) (ib : i < laneCount) :
    stageWrites cells w rb (word (cells.classBase + 128 * j + i)) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
    ⟨128 * j + i, by change i < 104 at ib; omega, by rw [Nat.add_assoc]⟩

theorem sw_cast {j i : Nat} (jb : j ≤ w) (ib : i < laneCount) :
    stageWrites cells w rb (word (cells.castSumBase + 128 * j + i)) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
    ⟨128 * j + i, by change i < 104 at ib; omega, by rw [Nat.add_assoc]⟩

theorem sw_ans {b : Nat} (bound : b < 2 * castAnswers rb) :
    stageWrites cells w rb (word (cells.ansBase + b)) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨b, bound, rfl⟩

theorem sw_lane {i : Nat} (bound : i < laneCount) : stageWrites cells w rb (word (cells.laneBase + i)) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨i, bound, rfl⟩

theorem sw_active : stageWrites cells w rb (word cells.active) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem sw_slot : stageWrites cells w rb (word cells.slot) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem sw_bit {b : Nat} (bound : b < w) : stageWrites cells w rb (word (cells.bitBase + b)) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inl ⟨b, bound, rfl⟩

theorem sw_next {i : Nat} (bound : i < laneCount) : stageWrites cells w rb (word (cells.nextBase + i)) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr ⟨i, bound, rfl⟩

end Writes

theorem ne_of_sw {cells : StageCells} {w rb : Nat} {address cell : Word}
    (outside : ¬ stageWrites cells w rb address) (inside : stageWrites cells w rb cell) : address ≠ cell :=
  fun same => outside (same ▸ inside)

/-! ### The state between blocks -/

/-- **The evaluator's state in RAM** between the blocks of a stage: the level XORs, the class and
cast sums, the active label, the first `known` bit labels, the leaves of the nodes closed at levels
`≤ closed` (every `α` off the path at level `closed`), `sub`, and the frame since the stage's start. -/
structure StageRel (cells : StageCells) (w rb value : Nat) (sub : Lanes w) (closed known : Nat)
    (mStart : Memory) (state : StageState rb) (m : Memory) : Prop where
  levelSums : ∀ L, L < w → m.ram (word (cells.levelSumBase + L)) = labelWord (state.levelSum L)
  sums : SumCells cells w rb state.classSum state.castSum m
  active : m.ram (word cells.active) = labelWord state.active
  bits : ∀ b, b < known → m.ram (word (cells.bitBase + b)) = labelWord (state.bits b)
  leaves : ∀ α, α < 2 ^ w → α % 2 ^ closed ≠ value % 2 ^ closed →
    m.ram (word (cells.nodeBase + α)) = labelWord (state.leaves α)
  subCells : ∀ i : Fin laneCount, m.ram (word (cells.subBase + i.val)) = word (sub i).val
  frame : Frame (stageWrites cells w rb) stageClobbers mStart m

/-- The two children of a class: a residue mod `2 ^ (n + 1)` off `value`'s but equal to it mod
`2 ^ n` is the sibling `slot`. -/
theorem class_of_ne (n x value slot : Nat) (slotLt : slot < 2 ^ (n + 1))
    (slotLow : slot % 2 ^ n = value % 2 ^ n) (slotNe : slot ≠ value % 2 ^ (n + 1))
    (xLow : x % 2 ^ n = value % 2 ^ n) (xNe : x % 2 ^ (n + 1) ≠ value % 2 ^ (n + 1)) :
    x % 2 ^ (n + 1) = slot := by
  have hs := SliceC.mod_two_pow_succ_split slot n
  rw [Nat.mod_eq_of_lt slotLt] at hs
  rw [SliceC.mod_two_pow_succ_split x n] at xNe ⊢
  rw [SliceC.mod_two_pow_succ_split value n] at xNe slotNe
  split_ifs at xNe slotNe hs ⊢ <;> omega

theorem mod_low (x n : Nat) : x % 2 ^ (n + 1) % 2 ^ n = x % 2 ^ n :=
  Nat.mod_mod_of_dvd x (pow_dvd_pow 2 (Nat.le_succ n))

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **One expansion** against `expandM`: the closed node at level `n + 1`, slot `slot` (the
sibling of the path node), label at `node[slot]`. -/
theorem agree_expandReplay (cells : StageCells) (w rb value : Nat) (sub : Lanes w)
    (layout : StageLayout cells w rb) (rbPos : 0 < rb) (rbLe : rb ≤ 128) (wSmall : w ≤ 64)
    (treeBase : Nat → Nat) (castBase stride : Nat) (strideSmall : stride < 2 ^ 64)
    (treeTag castTag : Nat → Nat → Nat)
    (hTag : ∀ L x, L < w → treeTag L x = treeBase L + stride * x)
    (tagSmall : ∀ L x, L < w → x < 2 ^ w → treeBase L + stride * x < 2 ^ 127)
    (hCast : ∀ x part, castTag x part = castBase + stride * x + part)
    (castSmall : ∀ x, x < 2 ^ w → castBase + stride * x + castAnswers rb < 2 ^ 127)
    (n known : Nat) (nLt : n + 1 ≤ w) (knownLe : known ≤ w) (slot : Nat) (slotLt : slot < 2 ^ (n + 1))
    (slotLow : slot % 2 ^ n = value % 2 ^ n) (slotNe : slot ≠ value % 2 ^ (n + 1))
    (label : Label) (mStart : Memory) (state : StageState rb) (m : Memory)
    (rel : StageRel cells w rb value sub n known mStart state m)
    (slotCell : m.ram (word cells.slot) = word slot)
    (nodeCell : m.ram (word (cells.nodeBase + slot)) = labelWord label) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (StageRel cells w rb value sub (n + 1) known mStart)
      ((expandReplay cells w rb (n + 1) treeBase castBase stride).tree m)
      (liftHash (expandM w treeTag castTag (n + 1) slot label state)) := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have c1 := layout.c1; have c2 := layout.c2; have c3 := layout.c3; have c4 := layout.c4
  have lc : laneCount = 104 := rfl
  have powSplit : 2 ^ (n + 1) * 2 ^ (w - (n + 1)) = 2 ^ w := by
    rw [← pow_add, Nat.add_sub_cancel' nLt]
  have powPos := Nat.two_pow_pos (n + 1)
  unfold expandReplay expandM
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun subtree m1 post1 => ?_)
    (agree_subtreeReplay cells w rb layout (n + 1) stride strideSmall treeBase slot slotLt treeTag hTag
      tagSmall m slotCell label nodeCell (w - (n + 1)) (by omega))
  obtain ⟨nodes1, sums1, _, frame1, bits1, regs1⟩ := post1
  have off1 : ∀ k, (k < cells.nodeBase ∨ cells.levelSumBase + w ≤ k) → k < 2 ^ 256 →
      m1.ram (word k) = m.ram (word k) := fun k hk kb =>
    frame1 _ (fun x xb _ => word_ne kb (by omega) (by omega))
      (fun t tb => word_ne kb (by omega) (by omega)) (fun L Lb => word_ne kb (by omega) (by omega))
  have slot1 : m1.ram (word cells.slot) = word slot := by
    rw [off1 _ (Or.inr (by omega)) (by omega)]; exact slotCell
  have sumsM1 : SumCells cells w rb state.classSum state.castSum m1 :=
    rel.sums.transfer fun j jb i ib =>
      ⟨off1 _ (Or.inr (by omega)) (by omega), off1 _ (Or.inr (by omega)) (by omega)⟩
  unfold tableM
  simp only [TreeLaws.monad_bind, liftHash_bind, liftHash_vector, TreeLaws.bind_assoc]
  rw [← bindOpt_pure_right ((Prog.rep (2 ^ (w - (n + 1)))
    (leafEntry cells w rb (n + 1) castBase stride)).tree m1)]
  refine Agree.bindOpt (fun values m2 post2 => ?_)
    (agree_rep_vector_plain (leafEntry cells w rb (n + 1) castBase stride)
      (LeafInv cells w rb (n + 1) slot state.classSum state.castSum m1) (2 ^ (w - (n + 1))) _
      (fun index values current holds =>
        agree_leafEntry cells w rb layout rbPos rbLe wSmall (n + 1) nLt castBase stride strideSmall
          castTag hCast castSmall slot slotLt subtree.1 state.classSum state.castSum m1 slot1 nodes1
          index values current holds)
      m1 ⟨fun j jb i => by
          simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, ite_self]
          exact sumsM1 j jb i,
        fun _ _ _ _ => rfl, rfl, fun _ _ => rfl⟩)
  obtain ⟨sums2, frame2, bits2, regs2⟩ := post2
  have off2 : ∀ k, (k < cells.classBase ∨ cells.laneBase + 128 ≤ k) → k < 2 ^ 256 →
      m2.ram (word k) = m1.ram (word k) := fun k hk kb =>
    frame2 _ (fun j jb i ib => ⟨word_ne kb (by omega) (by omega), word_ne kb (by omega) (by omega)⟩)
      (fun b bb => word_ne kb (by omega) (by omega)) (fun i ib => word_ne kb (by omega) (by omega))
  refine .leaf ⟨fun L Lw => ?_, fun j jb i => ?_, ?_, fun b bLt => ?_, fun α αb αNe => ?_,
    fun i => ?_, ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩
  · -- level XORs
    dsimp only
    rw [off2 _ (Or.inl (by omega)) (by omega), sums1 L Lw, rel.levelSums L Lw, labelWord_xor]
  · -- class and cast sums
    have jLt : j < w + 1 := by omega
    have h := sums2 j jb i
    simp only [atNat, jLt, dite_true, stored_eq, sumLanes, materialize_eq]
    exact h
  · -- active
    dsimp only
    rw [off2 _ (Or.inr (by omega)) (by omega), off1 _ (Or.inr (by omega)) (by omega)]
    exact rel.active
  · -- bits
    dsimp only
    rw [off2 _ (Or.inr (by omega)) (by omega), off1 _ (Or.inr (by omega)) (by omega)]
    exact rel.bits b bLt
  · -- leaves
    dsimp only
    rw [off2 _ (Or.inl (by omega)) (by omega)]
    by_cases low : α % 2 ^ n = value % 2 ^ n
    · have cls := class_of_ne n α value slot slotLt slotLow slotNe low αNe
      have split := Nat.mod_add_div α (2 ^ (n + 1))
      rw [cls] at split
      have tLt : α / 2 ^ (n + 1) < 2 ^ (w - (n + 1)) := by
        rw [Nat.div_lt_iff_lt_mul powPos, Nat.mul_comm, powSplit]; exact αb
      rw [if_pos ⟨αb, cls⟩, atNat, dif_pos tLt]
      have := nodes1 ⟨α / 2 ^ (n + 1), tLt⟩
      simp only at this
      rw [split] at this
      exact this
    · have notCls : ¬ (α < 2 ^ w ∧ α % 2 ^ (n + 1) = slot) := by
        rintro ⟨_, same⟩
        apply low
        rw [← mod_low α n, same, slotLow]
      rw [if_neg notCls, frame1 _ (fun x xb xc same => low (by
          have := word_inj (by omega) (by omega) same
          rw [show α = x by omega, ← mod_low x n, xc, slotLow]))
        (fun t tb => word_ne (by omega) (by omega) (by omega))
        (fun L Lb => word_ne (by omega) (by omega) (by omega))]
      exact rel.leaves α αb low
  · -- sub
    rw [off2 _ (Or.inl (by have := i.isLt; omega)) (by have := i.isLt; omega),
      off1 _ (Or.inl (by have := i.isLt; omega)) (by have := i.isLt; omega)]
    exact rel.subCells i
  · -- frame: RAM
    rw [frame2 address (fun j jb i ib => ⟨ne_of_sw outside (sw_class cells w rb jb ib),
        ne_of_sw outside (sw_cast cells w rb jb ib)⟩)
      (fun b bb => ne_of_sw outside (sw_ans cells w rb bb))
      (fun i ib => ne_of_sw outside (sw_lane cells w rb ib)),
      frame1 address (fun x xb _ => ne_of_sw outside (sw_node cells w rb xb))
        (fun t tb => ne_of_sw outside (sw_mat cells w rb tb))
        (fun L Lb => ne_of_sw outside (sw_levelSum cells w rb Lb))]
    exact rel.frame.ram address outside
  · rw [bits2, bits1, rel.frame.bits]
  · rw [regs2 register outside, regs1 register outside, rel.frame.registers register outside]

end Agreement

end Kriterion.CRT.SimMachine
