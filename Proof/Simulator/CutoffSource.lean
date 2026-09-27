/-
Small facts about the machine's draws that the CRT machine's source law uses (`Proof/Simulator/CRT/SamplerBounds.lean`):
`total_apply` (a family read as a total function), `bitVec_ofNat_toNat`, `wordProduct_eq` (independent coin words are
uniform `Fin` words), and the row constants of a digit by slot (`rowField`, `rowGamma_eq`).
-/

import Proof.Simulator.CutoffSamplers

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- Field `k` of a row, in the machine's cell order (`xC0, yC4, zC0`). -/
def rowField (row : RowGamma) : Nat → BaseField
  | 0 => row.xC0
  | 1 => row.yC4
  | _ => row.zC0

theorem rowGamma_eq (row : RowGamma) :
    (⟨rowField row 0, rowField row 1, rowField row 2⟩ : RowGamma) = row := by
  cases row
  rfl

theorem total_apply {count : Nat} {α : Type} (zero : α) (family : Fin count → α) (index : Nat)
    (inside : index < count) : total zero family index = family ⟨index, inside⟩ := by
  simp [total, inside]

theorem bitVec_ofNat_toNat {width : Nat} (value : BitVec width) :
    BitVec.ofNat width value.toNat = value := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- The word draws of the machine, as uniform `Fin` draws. -/
theorem wordProduct_eq [FieldCertificate] (count width : Nat) :
    optionProduct count (fun _ => (wordLaw width).map some) =
      (PMF.uniformOfFintype (Fin count → Fin (2 ^ width))).map
        fun words => some fun index => (words index).val := by
  have single : (wordLaw width).map some =
      ((PMF.uniformOfFintype (Fin (2 ^ width))).map some).map (Option.map Fin.val) := by
    unfold wordLaw
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  have : Nonempty (Fin (2 ^ width)) := ⟨⟨0, Nat.two_pow_pos width⟩⟩
  simp only [single]
  rw [optionProduct_map, optionProduct_uniform, PMF.map_comp]
  rfl

end

end Kriterion.ArgoMAC.PlanB.SimMachine
