/-
**Packed conversion-label vectors** (Opus, P1b).

`packedLabels n` encodes `n` conversion labels as one little-endian natural `Σ_i l_i · 2^(labelBits · i)` of
`labelBits · n` bits, in `packedBytes n = ⌈labelBits · n / 8⌉` bytes (the top `8 · packedBytes n − labelBits · n`
bits are zero). The digit facts are `LabelLanes`' (`pinBlocksNat`, `pinBlocks_pinOfBlocks`): a vector is the
`n`-label "pin" `pinBlocksNat`, read back label by label.
-/

import Construction.CRT.LabelLanes
import Encoding

namespace Kriterion.CRT.Narrow

/-- `⌈labelBits · n / 8⌉` bytes. -/
def packedBytes (n : Nat) : Nat := (labelBits * n + 7) / 8

theorem labelBits_le_packed (n : Nat) : labelBits * n ≤ 8 * packedBytes n := by
  unfold packedBytes
  omega

theorem pow_le_packed (n : Nat) : 2 ^ (labelBits * n) ≤ 256 ^ packedBytes n := by
  rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (labelBits_le_packed n)

/-- The packed natural of a label vector. -/
def packNat {n : Nat} (labels : Vector Label n) : Nat := pinBlocksNat fun i : Fin n => labels.get i

theorem packNat_lt {n : Nat} (labels : Vector Label n) : packNat labels < 2 ^ (labelBits * n) :=
  pinBlocksNat_lt _

/-- Label `i` of a packed natural. -/
def unpackAt (value i : Nat) : Label := BitVec.ofNat labelBits (value >>> (labelBits * i))

theorem unpackAt_packNat {n : Nat} (labels : Vector Label n) (i : Fin n) :
    unpackAt (packNat labels) i.val = labels.get i := by
  have same := congrFun (pinBlocks_pinOfBlocks (fun j : Fin n => labels.get j)) i
  simp only [pinBlocks, pinNat_pinOfBlocks] at same
  exact same

/-- **The packed label vector codec.** -/
def packedLabels (n : Nat) : Kriterion.Encoding (Vector Label n) :=
  (Kriterion.Encoding.natural (packedBytes n)).map
    (fun labels => ⟨packNat labels, lt_of_lt_of_le (packNat_lt labels) (pow_le_packed n)⟩)
    (fun value => Vector.ofFn fun i : Fin n => unpackAt value.val i.val)
    (fun labels => by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      exact unpackAt_packNat labels ⟨i, hi⟩)

@[simp] theorem packedLabels_length (n : Nat) (labels : Vector Label n) :
    ((packedLabels n).encode labels).length = packedBytes n := by
  simp only [packedLabels, Kriterion.Encoding.map, Kriterion.Encoding.natural_length]

end Kriterion.CRT.Narrow
