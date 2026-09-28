/- Algebraic research only. These identities do not alter the submitted construction
or prove a privacy-preserving record reduction. -/
import Construction.ArgoMAC.Coordinates
import Mathlib.Tactic

namespace Kriterion.StructuralResearch

open BN254

/-- Share the Z delivery with a candidate second affine x delivery. This factorization
matches the X row exactly when the second delivery's offset has a prescribed relation
with the hidden point and projective scale. -/
theorem x_row_factor_error [FieldCertificate]
    (a b rho phi x y offset : BaseField) :
    rho ^ 2 * (6 + a ^ 2 * phi ^ 4 * x - 2 * b * phi ^ 3 * y +
        a * phi ^ 8 * x ^ 2) -
      ((rho * (phi ^ 4 * x - a)) * (rho * a * phi ^ 4 * x + offset) -
        2 * rho ^ 2 * b * phi ^ 3 * y + 6 * rho ^ 2 + rho * a * offset) =
      rho * phi ^ 4 * (2 * rho * a ^ 2 - offset) * x := by
  ring

/-- Conditional correctness of replacing the two X-row x deliveries and the Z-row
x delivery with two x deliveries in total. The required offset is not a free public value. -/
theorem x_row_factor_of_offset [FieldCertificate]
    (a b rho phi x y : BaseField) :
    rho ^ 2 * (6 + a ^ 2 * phi ^ 4 * x - 2 * b * phi ^ 3 * y +
        a * phi ^ 8 * x ^ 2) =
      ((rho * (phi ^ 4 * x - a)) * (rho * a * phi ^ 4 * x + 2 * rho * a ^ 2) -
        2 * rho ^ 2 * b * phi ^ 3 * y + 6 * rho ^ 2 + 2 * rho ^ 2 * a ^ 3) := by
  ring

/-- Under the nonzero normalizer, the needed new offset is -2a times the Z offset. -/
theorem offset_relation [FieldCertificate] (a rho : BaseField) :
    2 * rho * a ^ 2 = -2 * a * (-rho * a) := by ring

/-- For nonzero input/scales, this offset relation is also necessary for the simple
factored expression. Thus independent existing offsets cannot simply be reused. -/
theorem x_row_factor_iff [FieldCertificate]
    (a b rho phi x y offset : BaseField)
    (rho_ne : rho ≠ 0) (phi_ne : phi ≠ 0) (x_ne : x ≠ 0) :
    (rho ^ 2 * (6 + a ^ 2 * phi ^ 4 * x - 2 * b * phi ^ 3 * y +
        a * phi ^ 8 * x ^ 2) =
      ((rho * (phi ^ 4 * x - a)) * (rho * a * phi ^ 4 * x + offset) -
        2 * rho ^ 2 * b * phi ^ 3 * y + 6 * rho ^ 2 + rho * a * offset)) ↔
      offset = 2 * rho * a ^ 2 := by
  rw [← sub_eq_zero, x_row_factor_error]
  simp only [mul_eq_zero, rho_ne, pow_ne_zero 4 phi_ne, x_ne, false_or, or_false,
    sub_eq_zero]
  exact eq_comm

#print axioms x_row_factor_error
#print axioms x_row_factor_of_offset
#print axioms x_row_factor_iff

end Kriterion.StructuralResearch
