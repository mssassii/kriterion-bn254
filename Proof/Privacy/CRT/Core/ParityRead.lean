/-
The parity cast's raw-answer distribution, preserving the original full-width
hash readings. Only the upper planes are independent uniform lanes. The low
plane is fixed by the control label, so no full-width cast uniformity is claimed.
-/

import Construction.CRT.ParityCast
import Proof.Privacy.CRT.Core.LabelUniform
import Proof.Privacy.CRT.Swap.Reading

namespace Kriterion.CRT.Privacy.ParityRead

open Cryptography
open Kriterion.CRT.Parity
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)

noncomputable section

/-- The exact support of a parity cast at a fixed control label. -/
abbrev Coset (width : Nat) (label : Label) :=
  {lanes : Lanes (width + 1) // laneBit lanes 0 = label}

instance cosetNonempty (width : Nat) (label : Label) : Nonempty (Coset width label) :=
  ⟨parityEquiv width label 0⟩

instance cosetFintype (width : Nat) (label : Label) : Fintype (Coset width label) :=
  Fintype.ofEquiv (Lanes width) (parityEquiv width label)

/-- Dropping the low plane of a uniform full-width lane vector gives uniform
upper planes. Its fibres are equivalent by preserving each lane's low bit. -/
theorem halfLanes_uniform (width : Nat) :
    (PMF.uniformOfFintype (Lanes (width + 1))).map halfLanes =
      PMF.uniformOfFintype (Lanes width) := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun b b' => ?_
  exact {
    toFun := fun p => ⟨parityLift b' (laneBit p.1 0), halfLanes_parityLift _ _⟩
    invFun := fun p => ⟨parityLift b (laneBit p.1 0), halfLanes_parityLift _ _⟩
    left_inv := fun p => by
      apply Subtype.ext
      simp only [laneBit_parityLift_zero]
      simpa only [p.property] using parityLift_halfLanes_laneBit p.val
    right_inv := fun p => by
      apply Subtype.ext
      simp only [laneBit_parityLift_zero]
      simpa only [p.property] using parityLift_halfLanes_laneBit p.val }

/-- Total-width version used by the generic conversion core, including its
empty-row singleton convention. -/
theorem pinHalf_uniform (width : Nat) :
    (PMF.uniformOfFintype (Lanes width)).map (pinHalf width) =
      PMF.uniformOfFintype (Lanes (width - 1)) := by
  cases width with
  | zero => exact PMF.map_id _
  | succ width => exact halfLanes_uniform width

/-- Independent upper planes retain the original full-width answer count and
packing. The old low random plane is discarded. -/
def readUpper (width : Nat)
    (answers : Fin (castAnswers (width + 1)) → Block × Block) : Lanes width :=
  halfLanes (castLanes (width + 1) (packAnswers (castAnswers (width + 1)) answers))

/-- Read the full cast as an inhabitant of its exact label-dependent support. -/
def readCoset (width : Nat) (label : Label)
    (answers : Fin (castAnswers (width + 1)) → Block × Block) : Coset width label :=
  parityEquiv width label (readUpper width answers)

/-- Uniform raw answers give independent uniform upper planes, including upper
width zero. Full-width reading is used only before the low plane is discarded. -/
theorem readUpper_uniform (width : Nat) (hw : width + 1 ≤ 128) :
    (PMF.uniformOfFintype (Fin (castAnswers (width + 1)) → Block × Block)).map (readUpper width) =
      PMF.uniformOfFintype (Lanes width) := by
  change (PMF.uniformOfFintype _).map
    (halfLanes ∘ fun answers => castLanes (width + 1) (packAnswers (castAnswers (width + 1)) answers)) = _
  rw [← PMF.map_comp, Privacy.castLanes_uniform (width + 1) (by omega) hw,
    halfLanes_uniform]

/-- At a fixed control label the raw cast is uniform on exactly its parity
coset. Its low plane is label-dependent, not independent randomness. -/
theorem readCoset_uniform (width : Nat) (hw : width + 1 ≤ 128) (label : Label) :
    (PMF.uniformOfFintype (Fin (castAnswers (width + 1)) → Block × Block)).map (readCoset width label) =
      PMF.uniformOfFintype (Coset width label) := by
  change (PMF.uniformOfFintype _).map ((parityEquiv width label) ∘ readUpper width) = _
  rw [← PMF.map_comp, readUpper_uniform width hw]
  exact uniformOfFintype_map_equiv (parityEquiv width label)

/-- The construction's full lane vector is the inclusion of its coset law;
it is not uniform over all full-width lane vectors. -/
theorem parityCastLanes_uniform_coset (width : Nat) (hw : width + 1 ≤ 128) (label : Label) :
    (PMF.uniformOfFintype (Fin (castAnswers (width + 1)) → Block × Block)).map
        (fun answers => parityCastLanes (width + 1) label (packAnswers (castAnswers (width + 1)) answers)) =
      (PMF.uniformOfFintype (Coset width label)).map Subtype.val := by
  have factor : (fun answers : Fin (castAnswers (width + 1)) → Block × Block =>
      parityCastLanes (width + 1) label (packAnswers (castAnswers (width + 1)) answers)) =
      Subtype.val ∘ readCoset width label := rfl
  rw [factor, ← PMF.map_comp, readCoset_uniform width hw label]

end

end Kriterion.CRT.Privacy.ParityRead
