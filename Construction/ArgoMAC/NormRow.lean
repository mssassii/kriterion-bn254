/-
The published row data of one digit after row normalization (research note §2).

The `Z` row and the sign row are scaled so that their published constants are the bits
`ε_Z = [K_z = 0]` and `ε_S = [K_c = 0]` (`K_z`, `K_c` the offsets of the collectors `rowZ_x9` and
`rowY_cubic`); the sign row's scale `κ` need not be a square, so the digit also publishes
`ν = [χ(κ) = −1]`, and the evaluator reads the sign row as `(−1)^ν S`. A digit publishes the `X`
row constant (a field element) and one flags byte (`ν + 2 ε_Z + 4 ε_S`).
-/

import BN254
import Encoding

namespace Kriterion.ArgoMAC.PlanB

open BN254

/-- **One digit's published row data**: the `X` row constant and three bits. -/
structure NormRow where
  /-- The `X` row constant. -/
  xC0 : BaseField
  /-- `ε_Z`: the `Z` row's published constant (`0` or `1`). -/
  zFlag : Bool
  /-- `ε_S`: the sign row's published `x²` constant (`0` or `1`). -/
  sFlag : Bool
  /-- `ν`: the evaluator negates the sign row. -/
  sign : Bool

/-- The flags byte `ν + 2 ε_Z + 4 ε_S`. -/
def NormRow.flagByte (zFlag sFlag sign : Bool) : Fin 256 :=
  ⟨sign.toNat + 2 * zFlag.toNat + 4 * sFlag.toNat, by
    cases zFlag <;> cases sFlag <;> cases sign <;> decide⟩

/-- The three flags of a byte (bits `0`, `1`, `2`: `ν`, `ε_Z`, `ε_S`). -/
def NormRow.flagsOf (byte : Fin 256) : Bool × Bool × Bool :=
  (byte.val / 2 % 2 == 1, byte.val / 4 % 2 == 1, byte.val % 2 == 1)

theorem NormRow.flagsOf_flagByte (zFlag sFlag sign : Bool) :
    NormRow.flagsOf (NormRow.flagByte zFlag sFlag sign) = (zFlag, sFlag, sign) := by
  cases zFlag <;> cases sFlag <;> cases sign <;> rfl

/-- The flags byte codec (one byte; every triple of flags round-trips). -/
def NormRow.flagsEncoding : Kriterion.Encoding (Bool × Bool × Bool) :=
  Kriterion.Encoding.byte.map (fun flags => NormRow.flagByte flags.1 flags.2.1 flags.2.2) NormRow.flagsOf
    (fun flags => NormRow.flagsOf_flagByte flags.1 flags.2.1 flags.2.2)

theorem NormRow.flagsEncoding_length (flags : Bool × Bool × Bool) :
    (NormRow.flagsEncoding.encode flags).length = 1 := rfl

end Kriterion.ArgoMAC.PlanB
