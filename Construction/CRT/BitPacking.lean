/-
Fixed-width bit codecs, composed before the final byte boundary. The inverse law
is for every inhabitant, independently of the garbler and the simulator.
-/
import Encoding

namespace Kriterion.CRT

structure BitPacking (α : Type) (width : Nat) where
  encode : α → Vector Bool width
  decode : Vector Bool width → α
  inverse : ∀ value, decode (encode value) = value

namespace BitPacking

def map (base : BitPacking α width) (encode : β → α) (decode : α → β)
    (inverse : ∀ value, decode (encode value) = value) : BitPacking β width where
  encode value := base.encode (encode value)
  decode bits := decode (base.decode bits)
  inverse value := by rw [base.inverse, inverse]

def pair (first : BitPacking α left) (second : BitPacking β right) :
    BitPacking (α × β) (left + right) where
  encode value := first.encode value.1 ++ second.encode value.2
  decode bits := (first.decode (Vector.ofFn fun i : Fin left => bits[i.val]),
    second.decode (Vector.ofFn fun i : Fin right => bits[left + i.val]))
  inverse value := by
    have hleft : (Vector.ofFn fun i : Fin left =>
        (first.encode value.1 ++ second.encode value.2)[i.val]) = first.encode value.1 := by
      ext i h
      simp
    have hright : (Vector.ofFn fun i : Fin right =>
        (first.encode value.1 ++ second.encode value.2)[left + i.val]) = second.encode value.2 := by
      ext i h
      simp
    rw [hleft, hright, first.inverse, second.inverse]

def vector (base : BitPacking α width) (count : Nat) : BitPacking (Vector α count) (count * width) where
  encode values := (values.map base.encode).flatten
  decode bits := Vector.ofFn fun i : Fin count => base.decode
    (Vector.ofFn fun j : Fin width => bits[i.val * width + j.val]'(by
      have := i.isLt
      have := j.isLt
      nlinarith))
  inverse values := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have same : (Vector.ofFn fun j : Fin width =>
        (values.map base.encode).flatten[i * width + j.val]'(by
          have := j.isLt; nlinarith)) = base.encode values[i] := by
      ext j hj
      simp only [Vector.getElem_ofFn, Vector.getElem_flatten, Vector.getElem_map]
      have hw : 0 < width := by omega
      have q : (i * width + j) / width = i := by
        rw [Nat.mul_comm i width, Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero]
      simp [q, Nat.add_mod, Nat.mod_eq_of_lt hj]
    rw [same, base.inverse]

/-- Little-endian bits of a bounded natural. -/
def natural (width : Nat) : BitPacking (Fin (2 ^ width)) width where
  encode value := Vector.ofFn fun i => value.val.testBit i.val
  decode bits := ⟨(BitVec.ofBoolListLE bits.toList).toNat, by
    simpa using (BitVec.ofBoolListLE bits.toList).isLt⟩
  inverse value := by
    apply Fin.ext
    have eq : BitVec.ofBoolListLE (Vector.ofFn fun i : Fin width => value.val.testBit i.val).toList =
        (BitVec.ofFin value).cast (by simp) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      by_cases hi : i < width
      · simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofFin,
          BitVec.getLsbD_ofBoolListLE, Vector.toList_ofFn]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
        simp
      · rw [BitVec.getLsbD_of_ge _ _ (by simpa using Nat.le_of_not_gt hi)]
        simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi)]
    simpa using congrArg BitVec.toNat eq

/-- A byte vector codec with direct list conversion, avoiding a deeply nested pair codec. -/
def bytes (count : Nat) : Encoding (Vector (Fin 256) count) where
  encode value := value.toList
  decode input := if h : count ≤ input.length then
    some (⟨(input.take count).toArray, by simp [List.length_take, Nat.min_eq_left h]⟩,
      input.drop count)
    else none
  decode_encode value tail := by
    simp only [List.length_append, Vector.length_toList]
    rw [dif_pos (by omega)]
    simp [Vector.toList]

/-- Zero padding to the next byte boundary. -/
def padding (width : Nat) : Nat := (8 - width % 8) % 8

theorem padded_width (width : Nat) : width + padding width = ((width + 7) / 8) * 8 := by
  unfold padding
  omega

/-- Extend with zero bits. -/
def padded (bits : Vector Bool width) : Vector Bool (((width + 7) / 8) * 8) :=
  Vector.ofFn fun i => if h : i.val < width then bits[i.val] else false

def packBytes (bits : Vector Bool width) : Vector (Fin 256) ((width + 7) / 8) :=
  let paddedBits := padded bits
  Vector.ofFn fun i => (natural 8).decode (Vector.ofFn fun j : Fin 8 =>
    paddedBits[i.val * 8 + j.val]'(by have := i.isLt; have := j.isLt; omega))

def unpackBytes (input : Vector (Fin 256) ((width + 7) / 8)) : Vector Bool width :=
  Vector.ofFn fun i => ((natural 8).encode (input[i.val / 8]'(by have := i.isLt; omega)))[i.val % 8]

theorem natural_encode_decode (bits : Vector Bool width) :
    (natural width).encode ((natural width).decode bits) = bits := by
  ext i hi
  simp only [natural, Vector.getElem_ofFn]
  change (BitVec.ofBoolListLE bits.toList).getLsbD i = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem unpack_pack (bits : Vector Bool width) : unpackBytes (packBytes bits) = bits := by
  ext i hi
  dsimp only [unpackBytes, Vector.getElem_ofFn, packBytes]
  simp only [natural_encode_decode, Vector.getElem_ofFn]
  dsimp only [padded, Vector.getElem_ofFn]
  have index : i / 8 * 8 + i % 8 = i := by omega
  simp [index, hi]

/-- Complete fixed-size byte codec; only the last byte may contain zero padding. -/
def encoding (base : BitPacking α width) : Encoding α :=
  (bytes ((width + 7) / 8)).map
    (fun value => packBytes (base.encode value))
    (fun value => base.decode (unpackBytes value))
    (fun value => by rw [unpack_pack, base.inverse])

theorem encoding_length (base : BitPacking α width) (value : α) :
    (base.encoding.encode value).length = (width + 7) / 8 := by
  exact Vector.length_toList

end BitPacking
end Kriterion.CRT
