/-
The compact exception entry occupies one byte: kind 0 in the low nibble and kind 1 in the high
nibble. Every pair of masked nibbles has a lossless encoding, including unused digit codes.
-/
import Construction.ArgoMAC.Exception
import Encoding

namespace Kriterion.ArgoMAC.Exception

/-- Pack both independently masked exception codes into one byte. -/
def pack (entry : Entry) : BitVec 8 :=
  BitVec.ofNat 8 (entry[0].toNat + 16 * entry[1].toNat)

/-- Read the two nibbles of a packed exception entry. -/
def unpack (byte : BitVec 8) : Entry :=
  Vector.ofFn fun i => BitVec.ofNat 4 (if i.val = 0 then byte.toNat else byte.toNat / 16)

/-- Packing loses no bits of an entry. -/
theorem unpack_pack (entry : Entry) : unpack (pack entry) = entry := by
  apply Vector.ext
  intro i hi
  have lo := entry[0].isLt
  have high := entry[1].isLt
  have bound : entry[0].toNat + 16 * entry[1].toNat < 256 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [unpack, Vector.getElem_ofFn, pack, BitVec.toNat_ofNat]
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> norm_num at * <;> omega

/-- A byte represented as a bit vector. -/
def gadgetByte : Kriterion.Encoding (BitVec 8) :=
  Kriterion.Encoding.byte.map
    (fun value : BitVec 8 => ⟨value.toNat, value.isLt⟩)
    (fun value => BitVec.ofNat 8 value.val)
    (fun value => by simp)

/-- The one-byte codec for two exception kinds. -/
def entryEncoding : Kriterion.Encoding Entry := gadgetByte.map pack unpack unpack_pack

/-- Every exception entry occupies exactly one byte. -/
theorem entryEncoding_length (entry : Entry) : (entryEncoding.encode entry).length = 1 := rfl

end Kriterion.ArgoMAC.Exception
