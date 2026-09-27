/-
**Bits of encodings**, for the CRT machine's wire (`Proof/Simulator/CRT/Stage1Wire.lean`): an encoding's bytes
behind a regular head (`encodeOf`, so that no encoding of a concrete width is ever unfolded), the byte bits of pairs,
maps and vectors, little-endian digit sums (`digitSum_bits`), the regrouping of flattened lists (`flatten_ofFn_add`,
`flatten_ofFn_mul`) and the emitted bits of a stored word (`bitRun_ofNat`).
-/

import Proof.Simulator.Stage1Bits
import Proof.Simulator.Emit

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography

/-- The byte bits of a flattened list of byte lists. -/
theorem byteBits_flatten (lists : List (List (Fin 256))) :
    byteBits lists.flatten = (lists.map byteBits).flatten := by
  induction lists with
  | nil => rfl
  | cons first rest ih => rw [List.flatten_cons, byteBits_append, ih, List.map_cons, List.flatten_cons]

/-- An encoding's bytes, behind a regular (non-projection) head: the kernel compares
`encodeOf E x` with `encodeOf E y` by comparing `x` with `y`, and never unfolds `E` (the
encodings of large widths must never be unfolded). -/
def encodeOf {α : Type} (encoding : Encoding α) (value : α) : List (Fin 256) := encoding.encode value

theorem encode_eq {α : Type} (encoding : Encoding α) (value : α) :
    encoding.encode value = encodeOf encoding value := rfl

theorem encodeOf_map {α β : Type} (encoding : Encoding α) (encode : β → α) (decode : α → β)
    (inverse : ∀ value, decode (encode value) = value) (value : β) :
    encodeOf (encoding.map encode decode inverse) value = encodeOf encoding (encode value) := rfl

theorem encodeOf_pair {α β : Type} (first : Encoding α) (second : Encoding β) (left : α)
    (right : β) :
    encodeOf (first.pair second) (left, right) = encodeOf first left ++ encodeOf second right := rfl

/-- The byte bits of a vector encoding. -/
theorem byteBits_vector {α : Type} (encoding : Encoding α) (count : Nat) (values : Vector α count) :
    byteBits (encodeOf (encoding.vector count) values) =
      (List.ofFn fun index : Fin count => byteBits (encodeOf encoding values[index.val])).flatten := by
  unfold encodeOf
  rw [vector_encode, byteBits_flatten, List.map_ofFn]
  rfl


/-! ### Regrouping flattened lists -/

theorem flatten_ofFn_add {α : Type} {first second : Nat} (lists : Fin (first + second) → List α) :
    (List.ofFn lists).flatten =
      (List.ofFn fun index : Fin first => lists (index.castAdd second)).flatten ++
        (List.ofFn fun index : Fin second => lists (index.natAdd first)).flatten := by
  rw [List.ofFn_add, List.flatten_append]
  rfl

theorem flatten_ofFn_mul {α : Type} {outer inner : Nat} (lists : Fin (outer * inner) → List α) :
    (List.ofFn lists).flatten =
      (List.ofFn fun block : Fin outer => (List.ofFn fun index : Fin inner =>
        lists ⟨block.val * inner + index.val, by
          have blockSmall := block.isLt
          have indexSmall := index.isLt
          calc block.val * inner + index.val < (block.val + 1) * inner := by
                rw [Nat.add_mul, Nat.one_mul]; omega
            _ ≤ outer * inner := Nat.mul_le_mul_right _ blockSmall⟩).flatten).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  rfl

/-- The emitted bits of a stored word. -/
theorem bitRun_ofNat (value width : Nat) (small : width ≤ 256) :
    bitRun (BitVec.ofNat 256 value) 0 width = lsbs width value := by
  unfold bitRun lsbs
  refine congrArg List.ofFn (funext fun index => ?_)
  rw [Nat.zero_add, BitVec.getLsbD_ofNat]
  have : index.val < 256 := lt_of_lt_of_le index.isLt small
  simp [this]

/-! ### The chunk word -/

/-- A little-endian digit sum of `count` digits of `width` bits. -/
def digitSum (width count : Nat) (digit : Fin count → Nat) : Nat :=
  ∑ slot : Fin count, digit slot * 2 ^ (width * slot.val)

theorem digitSum_succ (width count : Nat) (digit : Fin (count + 1) → Nat) :
    digitSum width (count + 1) digit =
      digit 0 + 2 ^ width * digitSum width count fun slot => digit slot.succ := by
  unfold digitSum
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun slot _ => ?_
    rw [Fin.val_succ, Nat.mul_succ, pow_add]
    ring

theorem digitSum_lt (width : Nat) : ∀ (count : Nat) (digit : Fin count → Nat),
    (∀ slot, digit slot < 2 ^ width) → digitSum width count digit < 2 ^ (width * count)
  | 0, _, _ => by simp [digitSum]
  | count + 1, digit, small => by
      rw [digitSum_succ]
      have rest := digitSum_lt width count (fun slot => digit slot.succ) (fun slot => small _)
      have head := small 0
      rw [Nat.mul_succ, pow_add]
      calc digit 0 + 2 ^ width * digitSum width count (fun slot => digit slot.succ)
          < 2 ^ width + 2 ^ width * digitSum width count (fun slot => digit slot.succ) := by omega
        _ = 2 ^ width * (digitSum width count (fun slot => digit slot.succ) + 1) := by ring
        _ ≤ 2 ^ width * 2 ^ (width * count) := Nat.mul_le_mul_left _ rest
        _ = 2 ^ (width * count) * 2 ^ width := Nat.mul_comm _ _

/-- **The bits of a digit sum are its digits' bits.** -/
theorem digitSum_bits (width : Nat) : ∀ (count : Nat) (digit : Fin count → Nat),
    (∀ slot, digit slot < 2 ^ width) →
      lsbs (width * count) (digitSum width count digit) =
        (List.ofFn fun slot : Fin count => lsbs width (digit slot)).flatten
  | 0, _, _ => by simp [lsbs]
  | count + 1, digit, small => by
      rw [Nat.mul_succ, Nat.add_comm, lsbs_add, List.ofFn_succ, List.flatten_cons]
      have head := small 0
      have split := digitSum_succ width count digit
      congr 1
      · rw [← lsbs_mod, split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt head]
      · rw [split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos width), Nat.div_eq_of_lt head,
          Nat.zero_add]
        exact digitSum_bits width count (fun slot => digit slot.succ) (fun slot => small _)

end Kriterion.ArgoMAC.PlanB.SimMachine
