/-
This file defines the Plan B public value: everything the garbler publishes.

The plan source is `2026-09-17-planB.md`, section D.5. Every field has a
fixed width and there are no `Option` tags anywhere, so *every* inhabitant of `Public` encodes
to exactly `ciphertextBytesConstant` bytes; the byte-count theorem therefore does not mention
`garble` at all.

| Field       | Encoding                                 | Bytes   |
|-------------|------------------------------------------|---------|
| `curve`     | `3 * Wire.field`                          | 96      |
| `rows`      | `Vector RowGamma 91`, 3 field elements    | 8,736   |
| `exception` | `Vector (Vector (BitVec 4) 2) 91`        | 91   |
| `curveXHot` | `Vector Block 127`                        | 2,032   |
| `curveYHot` | `Vector Block 127`                        | 2,032   |
| `pointXHot` | `Vector Block 127`                        | 2,032   |
| `pointYHot` | `Vector Block 127`                        | 2,032   |
| `scale`     | `Vector (BitVec 163072) 127`              | 2,588,768 |
| **total**   |                                           | **2,605,819** |
-/

import Construction.ArgoMAC.Exception
import Construction.PGS.Packing

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The three published constants of one digit's three rows.

Every other row coefficient is carried in the element slopes (`Biquadratic.slopes`), so a digit
publishes the `X` and `Z` row constants and the sign row's `x²` coefficient. -/
structure RowGamma where
  /-- `X` row constant `c0`. -/
  xC0 : BaseField
  /-- Sign row coefficient `c4` (of `x²`). -/
  yC4 : BaseField
  /-- `Z` row constant `c0`. -/
  zC0 : BaseField

/-- The complete public value of a Plan B garbling.

Every field is fixed-width: there are no `Option` tags, so every inhabitant encodes to exactly
`ciphertextBytesConstant` bytes. -/
structure Public where
  /-- The curve-membership check: three published constants. -/
  curve : BaseField × BaseField × BaseField
  /-- The three published row constants of each digit. -/
  rows : Vector RowGamma digitCount
  /-- The exception gadget, one byte per digit. -/
  exception : Vector Exception.Entry digitCount
  /-- System A's `bin-to-hot` fold joins on the x coordinate's raw Lamport labels. -/
  curveXHot : Vector Block foldStepCount
  /-- System A's `bin-to-hot` fold joins on the y coordinate's raw Lamport labels. -/
  curveYHot : Vector Block foldStepCount
  /-- System B's `bin-to-hot` fold joins on the x coordinate's EncPRF-whitened labels. -/
  pointXHot : Vector Block foldStepCount
  /-- System B's `bin-to-hot` fold joins on the y coordinate's EncPRF-whitened labels. -/
  pointYHot : Vector Block foldStepCount
  /-- The `scale-hot` join of each chunk, all four lanes interleaved into one word. -/
  scale : Vector (BitVec chunkJoinBits) chunkCount

/-- The Plan B ciphertext size in bytes. -/
def ciphertextBytesConstant : Nat := 2605819

end Kriterion.ArgoMAC.PlanB
