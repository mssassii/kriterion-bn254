import Construction.CRT.Label
import Encoding

/-!
# Thirteen-byte encoding for one conversion label, and the packed label vector

`labelEncoding` stores one label in 13 bytes (retained for single labels). The public conversion vectors use
`packedLabels`: `n` labels as one contiguous little-endian natural of `labelBits · n` bits in
`packedBytes n = ⌈labelBits · n / 8⌉` bytes (Opus, P1b: at 101-bit labels the 13-byte codec would pad every
label with 3 zero bits, which the simulator's lane-major pin serialization does not produce).
-/

namespace Kriterion.CRT.Narrow

/-- A conversion label occupies exactly thirteen bytes, with no tag. -/
def labelEncoding : Kriterion.Encoding Label :=
  (Kriterion.Encoding.natural 13).map
    (fun value : Label => ⟨value.toNat, by
      have fits : 2 ^ labelBits ≤ (256 : Nat) ^ 13 := by
        norm_num [labelBits]
      exact lt_of_lt_of_le value.isLt fits⟩)
    (fun value => BitVec.ofNat labelBits value.val)
    (fun value => by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.isLt])

/-- The encoded label has a fixed width, including labels with leading zeros. -/
@[simp] theorem labelEncoding_length (value : Label) :
    (labelEncoding.encode value).length = 13 := by
  -- CHECK: unbuilt; this uses the source-verified `Encoding.natural_length` API.
  simp only [labelEncoding, Kriterion.Encoding.map, Kriterion.Encoding.natural_length]

/-- Decoding an encoded label preserves the entire following byte stream. -/
@[simp] theorem labelEncoding_decode_encode_append (value : Label)
    (tail : List (Fin 256)) :
    labelEncoding.decode (labelEncoding.encode value ++ tail) = some (value, tail) :=
  labelEncoding.decode_encode value tail

/-- The standalone thirteen-byte codec round trip. -/
@[simp] theorem labelEncoding_decode_encode (value : Label) :
    labelEncoding.decode (labelEncoding.encode value) = some (value, []) := by
  simpa only [List.append_nil] using labelEncoding_decode_encode_append value []

end Kriterion.CRT.Narrow
