/-
The half-pin codec round-trips every public half-pin and every encoded string,
including the zero-width singleton. Reconstruction of a real full pin additionally
uses its proved evenness.
-/

import Construction.CRT.ParityCast
import Proof.Correctness.CRT.TreeSteps

namespace Kriterion.CRT.Parity.HalfPin

/-- The dense codec stores and recovers every inhabitant of the half-pin type. -/
@[simp] theorem ofBlocks_blocks {width : Nat} (pin : HalfPin width) :
    ofBlocks width pin.blocks = pin := by
  cases pin with
  | mk upper =>
    simp only [ofBlocks, blocks, pinOfBlocks, pinBlocks, Narrow.pinOfBlocks_pinBlocks]

/-- Every narrow-label string is the canonical encoding of its decoded half-pin. -/
@[simp] theorem blocks_ofBlocks {width : Nat} (wire : Fin width → Label) :
    (ofBlocks width wire).blocks = wire := by
  exact Narrow.pinBlocks_pinOfBlocks wire

/-- The public half-pin codec is a bijection on every inhabitant, including width zero. -/
def codecEquiv (width : Nat) : HalfPin width ≃ (Fin width → Label) where
  toFun := blocks
  invFun := ofBlocks width
  left_inv := ofBlocks_blocks
  right_inv := blocks_ofBlocks

/-- Publishing and decoding an even full pin reconstructs it exactly. -/
theorem expand_ofBlocks_ofFull {width : Nat} (pin : Lanes (width + 1)) (even : EvenLanes pin) :
    (ofBlocks width (ofFull pin).blocks).expand = pin := by
  rw [ofBlocks_blocks, expand_ofFull pin even]

end Kriterion.CRT.Parity.HalfPin

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Kriterion.ArgoMAC

/-- Prefix XOR, used to prove tree parity without assumptions on its materials. -/
def parityXorRange (f : Nat → Label) : Nat → Label
  | 0 => 0
  | n + 1 => parityXorRange f n ^^^ f n

private theorem parityXorRange_congr (f g : Nat → Label) : ∀ n,
    (∀ i < n, f i = g i) → parityXorRange f n = parityXorRange g n
  | 0, _ => rfl
  | n + 1, h => by
      rw [parityXorRange, parityXorRange, parityXorRange_congr f g n
        (fun i hi => h i (by omega)), h n (by omega)]

private theorem parityXorRange_add (f : Nat → Label) (m : Nat) : ∀ n,
    parityXorRange f (m + n) = parityXorRange f m ^^^ parityXorRange (fun i => f (m + i)) n
  | 0 => by simp [parityXorRange]
  | n + 1 => by
      rw [← Nat.add_assoc, parityXorRange, parityXorRange_add f m n, parityXorRange]
      simp only [BitVec.xor_assoc]

private theorem parityXorRange_xor (f g : Nat → Label) : ∀ n,
    parityXorRange (fun i => f i ^^^ g i) n = parityXorRange f n ^^^ parityXorRange g n
  | 0 => by simp [parityXorRange]
  | n + 1 => by
      simp only [parityXorRange, parityXorRange_xor f g n]
      ac_rfl

private theorem xorFold_nat (f : Nat → Label) : ∀ n,
    xorFold (fun i : Fin n => f i.val) = parityXorRange f n
  | 0 => rfl
  | n + 1 => by
      rw [xorFold, Fin.foldl_succ_last]
      change xorFold (fun i : Fin n => f i.val) ^^^ f n = _
      rw [xorFold_nat f n]
      rfl

private theorem xorFold_atNat {n : Nat} (f : Fin n → Label) :
    xorFold f = parityXorRange (atNat f 0) n := by
  have h : f = fun i : Fin n => atNat f 0 i.val := by
    funext i
    simp [atNat, i.isLt]
  calc
    xorFold f = xorFold (fun i : Fin n => atNat f 0 i.val) := congrArg xorFold h
    _ = _ := xorFold_nat _ _

/-- A tree level extension preserves the XOR of all labels. -/
theorem xorFold_extendLevel (n : Nat) (parent right : Fin (2 ^ n) → Label) :
    xorFold (extendLevel n parent right) = xorFold parent := by
  rw [xorFold_atNat, xorFold_atNat]
  have split : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
  conv_lhs => arg 2; rw [split]
  rw [parityXorRange_add]
  have left : parityXorRange (atNat (extendLevel n parent right) 0) (2 ^ n) =
      parityXorRange (fun i => atNat parent 0 i ^^^ atNat right 0 i) (2 ^ n) := by
    apply parityXorRange_congr
    intro i hi
    have hitotal : i < 2 ^ (n + 1) := by rw [split]; omega
    simp only [atNat, dif_pos hi, dif_pos hitotal, extendLevel]
  have rightHalf : parityXorRange (fun i => atNat (extendLevel n parent right) 0 (2 ^ n + i))
      (2 ^ n) = parityXorRange (atNat right 0) (2 ^ n) := by
    apply parityXorRange_congr
    intro i hi
    have hitotal : 2 ^ n + i < 2 ^ (n + 1) := by rw [split]; omega
    have hinot : ¬ 2 ^ n + i < 2 ^ n := by omega
    simp only [atNat, dif_pos hi, dif_pos hitotal, extendLevel, dif_neg hinot,
      Nat.add_sub_cancel_left]
  rw [left, rightHalf, parityXorRange_xor]
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Every complete garbled tree has leaf XOR equal to its root offset. -/
theorem treeGarbleM_xor (H : HashN) (tagOf : Nat → Nat → Nat) (delta bit0 : Label) :
    ∀ levels, xorFold ((treeGarbleM tagOf delta bit0 levels).eval H).1 = delta
  | 0 => by
      change (0 : Label) ^^^ delta = delta
      exact BitVec.zero_xor
  | n + 1 => by
      simp only [treeGarbleM, FreeQuery.eval_bind]
      by_cases hn : n = 0
      · simp only [if_pos hn, FreeQuery.eval_pure, stored_eq, xorFold_extendLevel]
        exact treeGarbleM_xor H tagOf delta bit0 n
      · simp only [if_neg hn, FreeQuery.eval_bind, eval_garbleStepM, FreeQuery.eval_pure, xorFold_extendLevel]
        exact treeGarbleM_xor H tagOf delta bit0 n

/-- The low plane of a finite arithmetic sum is the XOR of the low planes. -/
theorem laneBit_sum_zero {width : Nat} : ∀ {count : Nat} (f : Fin count → Lanes (width + 1)),
    laneBit (∑ i, f i) 0 = xorFold (fun i => laneBit (f i) 0) := by
  intro count
  induction count with
  | zero => intro f; simp [xorFold, Parity.laneBit_zero]
  | succ count ih =>
      intro f
      rw [Fin.sum_univ_castSucc, Parity.laneBit_add_zero, xorFold, Fin.foldl_succ_last]
      change laneBit (∑ i : Fin count, f i.castSucc) 0 ^^^ laneBit (f (Fin.last count)) 0 =
        xorFold (fun i : Fin count => laneBit (f i.castSucc) 0) ^^^ laneBit (f (Fin.last count)) 0
      rw [ih]

/-- Casts whose low planes are a complete one-hot tree yield an even full pin. -/
theorem pin_even_of_leaf_xor {width count : Nat} (casts : Fin count → Lanes (width + 1))
    (leaves : Fin count → Label) (delta : Label)
    (low : ∀ i, laneBit (casts i) 0 = leaves i) (tree : xorFold leaves = delta) :
    Parity.EvenLanes ((∑ i, casts i) + deltaLanes (width + 1) delta) := by
  apply (Parity.evenLanes_iff_laneBit_zero _).mpr
  rw [Parity.laneBit_add_zero, laneBit_sum_zero, Parity.laneBit_deltaLanes_zero]
  have castBits : (fun i => laneBit (casts i) 0) = leaves := funext low
  rw [castBits, tree, BitVec.xor_self]
  rfl

/-- The zero-width lane ring is the singleton zero pin. -/
theorem evenLanes_width_zero (pin : Lanes 0) : Parity.EvenLanes pin := by
  intro i
  have h : (pin i).val < 1 := ZMod.val_lt (pin i)
  have hz : (pin i).val = 0 := by omega
  rw [hz, Nat.zero_mod]

/-- Total-width version; width-zero pins are automatically even. -/
theorem pin_even_of_leaf_xor_total {width count : Nat} (casts : Fin count → Lanes width)
    (leaves : Fin count → Label) (delta : Label)
    (low : 0 < width → ∀ i, laneBit (casts i) 0 = leaves i) (tree : xorFold leaves = delta) :
    Parity.EvenLanes ((∑ i, casts i) + deltaLanes width delta) := by
  cases width with
  | zero => exact evenLanes_width_zero _
  | succ width => exact pin_even_of_leaf_xor casts leaves delta (low (by omega)) tree

theorem parityCastLanes_low {width : Nat} (positive : 0 < width) (label : Label) (value : Nat) :
    laneBit (Parity.parityCastLanes width label value) 0 = label := by
  cases width with
  | zero => omega
  | succ width => exact Parity.laneBit_parityCastLanes_zero width label value

end Kriterion.CRT.SliceC
