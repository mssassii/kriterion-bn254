/-
The half-pin codec round-trips every public half-pin and every encoded string,
including the zero-width singleton. Reconstruction of a real full pin additionally
uses its proved evenness.
-/

import Construction.CRT.ParityCast

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
