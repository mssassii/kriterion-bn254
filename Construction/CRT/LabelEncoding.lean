import Construction.CRT.Label
import Encoding

/-!
# Thirteen-byte encoding for conversion labels

This is a leaf codec: the existing public transcript still uses its original
block encoding until the mixed-width consumers are integrated.  `natural 13`
uses the same little-endian byte order as the current public block codec.
-/

namespace Kriterion.CRT.Narrow

/-- A conversion label occupies exactly thirteen bytes, with no tag. -/
def labelEncoding : Kriterion.Encoding Label :=
  (Kriterion.Encoding.natural 13).map
    (fun value : Label => ⟨value.toNat, by
      -- CHECK: unbuilt; `labelBits` unfolds to the fixed width 104 here.
      have expand : (256 : Nat) ^ 13 = 2 ^ labelBits := by
        norm_num [labelBits]
      rw [expand]
      exact value.isLt⟩)
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
