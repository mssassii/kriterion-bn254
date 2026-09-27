/-
**P45.0: the structural encodings against the flat encoding index** (`Fin 367` and `Fin 275` in release-r1's order; tier 2 keeps `BMR.Enc`).

`x`: the point encodings `0..363` digit-major with slot `e mod 4` (`xElementIndex`), then the curve encodings
`364, 365, 366` (`x3, x5, x7`); `y`: `0..272` digit-major with slot `e mod 3` (`yElementIndex`), then `273, 274`
(`y4, y6`). Both maps are bijections (`xEncEquiv`, `yEncEquiv`).
-/

import Proof.Privacy.CRT.Core.BodyMaskRow

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-- The flat index of an `x` encoding. -/
def xFlat : XEnc → Fin 367
  | .inl (d, x) => ⟨(xElementIndex d x).val, by have := (xElementIndex d x).isLt; unfold pointElementCountX at this; omega⟩
  | .inr c => ⟨364 + c.slot.val, by have := c.slot.isLt; omega⟩

/-- The flat index of a `y` encoding. -/
def yFlat : YEnc → Fin 275
  | .inl (d, y) => ⟨(yElementIndex d y).val, by have := (yElementIndex d y).isLt; unfold pointElementCountY at this; omega⟩
  | .inr c => ⟨273 + c.slot.val, by have := c.slot.isLt; omega⟩

theorem xFlat_injective : Function.Injective xFlat := by
  rintro (⟨d, x⟩ | c) (⟨d', x'⟩ | c') same <;> simp only [xFlat, Fin.mk.injEq] at same
  · have := xElementIndex_injective (a₁ := (d, x)) (a₂ := (d', x')) (Fin.ext same)
    exact congrArg Sum.inl this
  · have := (xElementIndex d x).isLt; unfold pointElementCountX at this; omega
  · have := (xElementIndex d' x').isLt; unfold pointElementCountX at this; omega
  · exact congrArg Sum.inr (CurveXElement.slot_injective (Fin.ext (by omega)))

theorem yFlat_injective : Function.Injective yFlat := by
  rintro (⟨d, y⟩ | c) (⟨d', y'⟩ | c') same <;> simp only [yFlat, Fin.mk.injEq] at same
  · have := yElementIndex_injective (a₁ := (d, y)) (a₂ := (d', y')) (Fin.ext same)
    exact congrArg Sum.inl this
  · have := (yElementIndex d y).isLt; unfold pointElementCountY at this; omega
  · have := (yElementIndex d' y').isLt; unfold pointElementCountY at this; omega
  · exact congrArg Sum.inr (CurveYElement.slot_injective (Fin.ext (by omega)))

theorem card_xEnc : Fintype.card XEnc = 367 := by
  simp [XEnc, Fintype.card_sum, Fintype.card_prod]
  decide

theorem card_yEnc : Fintype.card YEnc = 275 := by
  simp [YEnc, Fintype.card_sum, Fintype.card_prod]
  decide

/-- **The `x` encodings in the flat order.** -/
noncomputable def xEncEquiv : XEnc ≃ Fin 367 :=
  Equiv.ofBijective xFlat ((Fintype.bijective_iff_injective_and_card xFlat).2
    ⟨xFlat_injective, by rw [card_xEnc, Fintype.card_fin]⟩)

/-- **The `y` encodings in the flat order.** -/
noncomputable def yEncEquiv : YEnc ≃ Fin 275 :=
  Equiv.ofBijective yFlat ((Fintype.bijective_iff_injective_and_card yFlat).2
    ⟨yFlat_injective, by rw [card_yEnc, Fintype.card_fin]⟩)

/-- The collectors sit at the flat `x` indices `4 d + 1`, `4 d + 2`, `4 d + 3`. -/
theorem xFlat_collector (d : Fin 91) :
    (xFlat (.inl (d, .rowX_x9))).val = 4 * d.val + 1 ∧ (xFlat (.inl (d, .rowY_cubic))).val = 4 * d.val + 2 ∧
      (xFlat (.inl (d, .rowZ_x9))).val = 4 * d.val + 3 :=
  ⟨rfl, rfl, rfl⟩

end Kriterion.CRT.Privacy.BMR
