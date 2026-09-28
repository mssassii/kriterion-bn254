/-
The 101-lane arithmetic labels and their dense pin codec.

This module is a leaf: the existing 128-bit construction does not import it.
The pin codec has exactly `ell` labels, with 101-bit stride. Its arithmetic
input also has exactly 101 lanes. Both directions include `ell = 0`.
-/

import Construction.CRT.Label
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Batteries.Data.BitVec.Basic
import Lean.Elab.Tactic.Omega

namespace Kriterion.CRT.Narrow

open scoped BigOperators

/-- Arithmetic labels: one ring element for each active label bit. -/
abbrev LLanes (ell : Nat) := Fin labelBits → ZMod (2 ^ ell)

/-- Lane `i` is bit `i` of the active delta. -/
def deltaLanes (ell : Nat) (delta : Label) : LLanes ell :=
  fun i => if delta.getLsbD i then 1 else 0

/-- Collect bit `n` of each arithmetic lane into one active label. -/
def laneBit {ell : Nat} (lanes : LLanes ell) (n : Nat) : Label :=
  BitVec.ofFnLE fun i => (lanes i).val.testBit n

/-- Reduce every arithmetic lane to a smaller (or larger) power-of-two ring. -/
def reduceTo {ell : Nat} (width : Nat) (lanes : LLanes ell) : LLanes width :=
  fun i => ((lanes i).val : ZMod (2 ^ width))

/-- Concatenate the lane representatives, each occupying `ell` bits. -/
def pinNat {ell : Nat} (lanes : LLanes ell) : Nat :=
  ∑ lane : Fin labelBits, (lanes lane).val * 2 ^ (ell * lane.val)

/-- The little-endian integer represented by `ell` consecutive 101-bit labels. -/
def pinBlocksNat {ell : Nat} (blocks : Fin ell → Label) : Nat :=
  ∑ index : Fin ell, (blocks index).toNat * 2 ^ (labelBits * index.val)

/-- Pack 101 arithmetic lanes densely into exactly `ell` active labels. -/
def pinBlocks {ell : Nat} (lanes : LLanes ell) : Fin ell → Label :=
  fun index => BitVec.ofNat labelBits (pinNat lanes >>> (labelBits * index.val))

/-- Unpack exactly `ell` active labels into 101 arithmetic lanes. -/
def pinOfBlocks (ell : Nat) (blocks : Fin ell → Label) : LLanes ell :=
  fun lane => ((pinBlocksNat blocks >>> (ell * lane.val) : Nat) : ZMod (2 ^ ell))

/-! The following radix facts are local copies of the elementary argument used
by `Proof.Correctness.CRT.FoldChain`, so the new codec does not import that
module or the old interface. -/

private theorem digits_lt {B : Nat} (hB : 0 < B) :
    ∀ (k : Nat) (d : Fin k → Nat), (∀ i, d i < B) →
      ∑ i : Fin k, d i * B ^ i.val < B ^ k := by
  intro k
  induction k with
  | zero => intro d _; simp
  | succ k ih =>
    intro d hd
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i => d i.castSucc) (fun i => hd _)
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    have h2 : d (Fin.last k) + 1 ≤ B := hd _
    calc ∑ i : Fin k, d i.castSucc * B ^ i.val + d (Fin.last k) * B ^ k
        < B ^ k + d (Fin.last k) * B ^ k := by omega
      _ = (d (Fin.last k) + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ h2
      _ = B ^ (k + 1) := by ring

private theorem digits_get {B : Nat} (hB : 0 < B) :
    ∀ (k : Nat) (d : Fin k → Nat), (∀ i, d i < B) → ∀ j : Fin k,
      (∑ i : Fin k, d i * B ^ i.val) / B ^ j.val % B = d j := by
  intro k
  induction k with
  | zero => intro d _ j; exact j.elim0
  | succ k ih =>
    intro d hd j
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlow := digits_lt hB k (fun i => d i.castSucc) (fun i => hd _)
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.val_last]
      rw [Nat.add_mul_div_right _ _ (Nat.pow_pos hB), Nat.div_eq_of_lt hlow, Nat.zero_add,
        Nat.mod_eq_of_lt (hd _)]
    | cast j =>
      simp only [Fin.val_castSucc]
      have hjk : j.val < k := j.isLt
      have hsplit : d (Fin.last k) * B ^ k =
          (d (Fin.last k) * B ^ (k - j.val)) * B ^ j.val := by
        rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hjk)]
      have hkj : k - j.val = (k - j.val - 1) + 1 := by omega
      rw [hsplit, Nat.add_mul_div_right _ _ (Nat.pow_pos hB), hkj, pow_succ,
        show d (Fin.last k) * (B ^ (k - j.val - 1) * B) =
            B * (d (Fin.last k) * B ^ (k - j.val - 1)) by ring,
        Nat.add_mul_mod_self_left]
      exact ih (fun i => d i.castSucc) (fun i => hd _) j

private theorem bits_reassemble (stride N : Nat) :
    ∀ c : Nat, ∑ k : Fin c, (N / 2 ^ (stride * k.val) % 2 ^ stride) *
      2 ^ (stride * k.val) = N % 2 ^ (stride * c) := by
  intro c
  induction c with
  | zero => simp [Nat.mod_one]
  | succ c ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, show stride * (c + 1) = stride * c + stride by ring, pow_add, Nat.mod_mul]
    ring

/-- All 101 lane representatives occupy at most `101 * ell` bits. -/
theorem pinNat_lt {ell : Nat} (lanes : LLanes ell) :
    pinNat lanes < 2 ^ (labelBits * ell) := by
  have h := digits_lt (Nat.two_pow_pos ell) labelBits
    (fun i => (lanes i).val) (fun i => ZMod.val_lt (lanes i))
  calc
    pinNat lanes = ∑ i : Fin labelBits, (lanes i).val * (2 ^ ell) ^ i.val := by
      simp only [pinNat, pow_mul]
    _ < (2 ^ ell) ^ labelBits := h
    _ = 2 ^ (labelBits * ell) := by rw [← pow_mul, Nat.mul_comm]

/-- Exactly `ell` labels occupy at most `101 * ell` bits. -/
theorem pinBlocksNat_lt {ell : Nat} (blocks : Fin ell → Label) :
    pinBlocksNat blocks < 2 ^ (labelBits * ell) := by
  have h := digits_lt (Nat.two_pow_pos labelBits) ell
    (fun i => (blocks i).toNat) (fun i => (blocks i).isLt)
  simpa only [pinBlocksNat, pow_mul] using h

theorem pinBlocksNat_pinBlocks {ell : Nat} (lanes : LLanes ell) :
    pinBlocksNat (pinBlocks lanes) = pinNat lanes := by
  simp only [pinBlocksNat, pinBlocks, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [bits_reassemble, Nat.mod_eq_of_lt (pinNat_lt lanes)]

/-- The dense active-label pin codec decodes its encoding, including width zero. -/
theorem pinOfBlocks_pinBlocks {ell : Nat} (lanes : LLanes ell) :
    pinOfBlocks ell (pinBlocks lanes) = lanes := by
  funext lane
  unfold pinOfBlocks
  rw [pinBlocksNat_pinBlocks, Nat.shiftRight_eq_div_pow]
  have hget := digits_get (Nat.two_pow_pos ell) labelBits
    (fun i => (lanes i).val) (fun i => ZMod.val_lt (lanes i)) lane
  unfold pinNat
  simp only [pow_mul]
  rw [← ZMod.natCast_mod _ (2 ^ ell), hget, ZMod.natCast_zmod_val]

theorem pinNat_pinOfBlocks {ell : Nat} (blocks : Fin ell → Label) :
    pinNat (pinOfBlocks ell blocks) = pinBlocksNat blocks := by
  -- CHECK: confirm the ZMod representative and finite-sum normalization at ell = 0.
  simp only [pinNat, pinOfBlocks, ZMod.val_natCast, Nat.shiftRight_eq_div_pow]
  rw [bits_reassemble, Nat.mul_comm ell labelBits,
    Nat.mod_eq_of_lt (pinBlocksNat_lt blocks)]

/-- Every sequence of `ell` active labels is the canonical encoding of its lanes. -/
theorem pinBlocks_pinOfBlocks {ell : Nat} (blocks : Fin ell → Label) :
    pinBlocks (pinOfBlocks ell blocks) = blocks := by
  funext index
  apply BitVec.eq_of_toNat_eq
  simp only [pinBlocks, pinNat_pinOfBlocks, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hget := digits_get (Nat.two_pow_pos labelBits) ell
    (fun i => (blocks i).toNat) (fun i => (blocks i).isLt) index
  simpa only [pinBlocksNat, pow_mul] using hget

/-- The dense codec is an equivalence, useful for uniformity transfer. -/
def pinCodecEquiv (ell : Nat) : LLanes ell ≃ (Fin ell → Label) where
  toFun := pinBlocks
  invFun := pinOfBlocks ell
  left_inv := pinOfBlocks_pinBlocks
  right_inv := pinBlocks_pinOfBlocks

end Kriterion.CRT.Narrow
