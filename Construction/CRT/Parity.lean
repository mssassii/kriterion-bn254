/-
Parity-constrained arithmetic labels. The independent cast data has one fewer bit in
 each lane. Its low plane is supplied by the control label, and an even pin stores
 only its upper planes. All lane widths here are parametric, including width zero
 for the upper planes.
-/

import Construction.CRT.Lanes
import Batteries.Data.BitVec
import Lean.Elab.Tactic.Omega

namespace Kriterion.CRT.Parity

open Cryptography

/-- Embed upper planes as an even arithmetic label. -/
def doubleLanes {width : Nat} (upper : Lanes width) : Lanes (width + 1) :=
  fun i => ((2 * (upper i).val : Nat) : ZMod (2 ^ (width + 1)))

/-- Omit the low plane of an arithmetic label. -/
def halfLanes {width : Nat} (lanes : Lanes (width + 1)) : Lanes width :=
  fun i => (((lanes i).val / 2 : Nat) : ZMod (2 ^ width))

/-- Lift independent upper planes with the control label as the low plane. -/
def parityLift {width : Nat} (upper : Lanes width) (label : Label) : Lanes (width + 1) :=
  fun i => ((2 * (upper i).val + (if label.getLsbD i.val then 1 else 0) : Nat) :
    ZMod (2 ^ (width + 1)))

/-- The omitted low plane of an even pin is zero in every lane. -/
def EvenLanes {width : Nat} (lanes : Lanes width) : Prop :=
  ∀ i, (lanes i).val % 2 = 0

@[simp] theorem doubleLanes_val {width : Nat} (upper : Lanes width) (i : Fin laneCount) :
    (doubleLanes upper i).val = 2 * (upper i).val := by
  have h := ZMod.val_lt (upper i)
  simp only [doubleLanes, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  rw [pow_succ]
  omega

@[simp] theorem parityLift_val {width : Nat} (upper : Lanes width) (label : Label)
    (i : Fin laneCount) :
    (parityLift upper label i).val =
      2 * (upper i).val + (if label.getLsbD i.val then 1 else 0) := by
  have h := ZMod.val_lt (upper i)
  simp only [parityLift, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  rw [pow_succ]
  split <;> omega

@[simp] theorem doubleLanes_zero (width : Nat) : doubleLanes (0 : Lanes width) = 0 := by
  funext i
  simp [doubleLanes]

/-- The natural-number definition is the intended lane-wise formula `2 U + bit(label)`. -/
theorem parityLift_eq {width : Nat} (upper : Lanes width) (label : Label) :
    parityLift upper label = doubleLanes upper + deltaLanes (width + 1) label := by
  funext i
  simp only [parityLift, doubleLanes, Pi.add_apply, deltaLanes, Nat.cast_add]
  split <;> simp

@[simp] theorem halfLanes_doubleLanes {width : Nat} (upper : Lanes width) :
    halfLanes (doubleLanes upper) = upper := by
  funext i
  simp [halfLanes]

@[simp] theorem halfLanes_parityLift {width : Nat} (upper : Lanes width) (label : Label) :
    halfLanes (parityLift upper label) = upper := by
  funext i
  simp only [halfLanes, parityLift_val]
  have hdiv : (2 * (upper i).val + (if label.getLsbD i.val then 1 else 0)) / 2 =
      (upper i).val := by split <;> omega
  rw [hdiv, ZMod.natCast_zmod_val]

theorem doubleLanes_injective (width : Nat) : Function.Injective (@doubleLanes width) := by
  intro a b h
  simpa using congrArg halfLanes h

theorem parityLift_injective {width : Nat} (label : Label) :
    Function.Injective (fun upper : Lanes width => parityLift upper label) := by
  intro a b h
  simpa using congrArg halfLanes h

@[simp] theorem laneBit_parityLift_zero {width : Nat} (upper : Lanes width) (label : Label) :
    laneBit (parityLift upper label) 0 = label := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [laneBit, BitVec.getLsbD_ofFnLE, hi, dite_true, parityLift_val,
    Nat.testBit_zero]
  cases h : label.getLsbD i <;> simp

@[simp] theorem evenLanes_doubleLanes {width : Nat} (upper : Lanes width) :
    EvenLanes (doubleLanes upper) := by
  intro i
  simp

/-- Doubling the stored half-pin reconstructs every even full pin. -/
theorem doubleLanes_halfLanes {width : Nat} (lanes : Lanes (width + 1))
    (even : EvenLanes lanes) : doubleLanes (halfLanes lanes) = lanes := by
  funext i
  have hlt : (lanes i).val / 2 < 2 ^ width := by
    have h : (lanes i).val < 2 ^ width * 2 := by
      simpa only [pow_succ] using ZMod.val_lt (lanes i)
    omega
  simp only [doubleLanes, halfLanes, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have heq : 2 * ((lanes i).val / 2) = (lanes i).val := by
    have h := even i
    omega
  rw [heq, ZMod.natCast_zmod_val]

theorem halfLanes_injective_on_even {width : Nat} {a b : Lanes (width + 1)}
    (ha : EvenLanes a) (hb : EvenLanes b) (h : halfLanes a = halfLanes b) : a = b := by
  rw [← doubleLanes_halfLanes a ha, ← doubleLanes_halfLanes b hb, h]

@[simp] theorem laneBit_zero (width bit : Nat) : laneBit (0 : Lanes width) bit = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [laneBit, hi]

/-- The low plane takes lane addition to XOR. -/
theorem laneBit_add_zero {width : Nat} (a b : Lanes (width + 1)) :
    laneBit (a + b) 0 = laneBit a 0 ^^^ laneBit b 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [laneBit, BitVec.getLsbD_xor, BitVec.getLsbD_ofFnLE, hi, dite_true,
    Pi.add_apply, ZMod.val_add, Nat.testBit_zero]
  have hdiv : 2 ∣ 2 ^ (width + 1) := by
    rw [pow_succ]
    exact dvd_mul_left _ _
  rw [Nat.mod_mod_of_dvd _ hdiv]
  rcases Nat.mod_two_eq_zero_or_one (a ⟨i, hi⟩).val with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (b ⟨i, hi⟩).val with hb | hb <;>
    simp [Nat.add_mod, ha, hb]

@[simp] theorem laneBit_deltaLanes_zero (width : Nat) (label : Label) :
    laneBit (deltaLanes (width + 1) label) 0 = label := by
  have h := laneBit_parityLift_zero (0 : Lanes width) label
  simpa [parityLift_eq] using h

/-- Even pins are exactly arithmetic labels whose low Boolean plane is zero. -/
theorem evenLanes_iff_laneBit_zero {width : Nat} (lanes : Lanes width) :
    EvenLanes lanes ↔ laneBit lanes 0 = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [laneBit, hi, Nat.testBit_zero, h ⟨i, hi⟩]
  · intro h i
    have hi := congrArg (fun b : Label => b.getLsbD i.val) h
    simp only [laneBit, BitVec.getLsbD_ofFnLE, i.isLt, dite_true,
      Nat.testBit_zero] at hi
    rcases Nat.mod_two_eq_zero_or_one (lanes i).val with heven | hodd
    · exact heven
    · simp [hodd] at hi

/-- Reinsert the actual low plane after omitting it. -/
theorem parityLift_halfLanes_laneBit {width : Nat} (lanes : Lanes (width + 1)) :
    parityLift (halfLanes lanes) (laneBit lanes 0) = lanes := by
  funext i
  have hlt : (lanes i).val / 2 < 2 ^ width := by
    have h : (lanes i).val < 2 ^ width * 2 := by
      simpa only [pow_succ] using ZMod.val_lt (lanes i)
    omega
  simp only [parityLift, halfLanes, ZMod.val_natCast, Nat.mod_eq_of_lt hlt,
    laneBit, BitVec.getLsbD_ofFnLE, i.isLt, dite_true, Nat.testBit_zero]
  have hbit : (if decide ((lanes i).val % 2 = 1) then 1 else 0) =
      (lanes i).val % 2 := by
    rcases Nat.mod_two_eq_zero_or_one (lanes i).val with h | h <;> simp [h]
  rw [hbit, Nat.div_add_mod, ZMod.natCast_zmod_val]

/-- The cast law is a bijection onto a label-dependent parity coset. -/
def parityEquiv (width : Nat) (label : Label) :
    Lanes width ≃ {lanes : Lanes (width + 1) // laneBit lanes 0 = label} where
  toFun upper := ⟨parityLift upper label, laneBit_parityLift_zero upper label⟩
  invFun lanes := halfLanes lanes.val
  left_inv upper := halfLanes_parityLift upper label
  right_inv lanes := by
    apply Subtype.ext
    dsimp
    simpa only [lanes.property] using parityLift_halfLanes_laneBit lanes.val

/-- Half-pins range over all upper-plane vectors, and exactly the even full pins. -/
def evenEquiv (width : Nat) : Lanes width ≃ {lanes : Lanes (width + 1) // EvenLanes lanes} where
  toFun upper := ⟨doubleLanes upper, evenLanes_doubleLanes upper⟩
  invFun lanes := halfLanes lanes.val
  left_inv upper := halfLanes_doubleLanes upper
  right_inv lanes := by
    apply Subtype.ext
    exact doubleLanes_halfLanes lanes.val lanes.property

/-- Omit a full pin's low plane, with a total width-zero convention. -/
def pinHalf : (width : Nat) → Lanes width → Lanes (width - 1)
  | 0, lanes => lanes
  | width + 1, lanes => halfLanes lanes

/-- Supply the low plane of a full-width cast, with a total width-zero convention. -/
def liftUpper : (width : Nat) → Lanes (width - 1) → Label → Lanes width
  | 0, lanes, _ => lanes
  | width + 1, lanes, label => parityLift lanes label

@[simp] theorem pinHalf_liftUpper (width : Nat) (upper : Lanes (width - 1)) (label : Label) :
    pinHalf width (liftUpper width upper label) = upper := by
  cases width <;> simp [pinHalf, liftUpper]

theorem liftUpper_injective (width : Nat) (label : Label) :
    Function.Injective (fun upper => liftUpper width upper label) := by
  intro a b same
  simpa using congrArg (pinHalf width) same

@[simp] theorem laneBit_liftUpper_zero (width : Nat) (upper : Lanes (width - 1))
    (label : Label) (positive : 1 ≤ width) :
    laneBit (liftUpper width upper label) 0 = label := by
  cases width with
  | zero => omega
  | succ width => exact laneBit_parityLift_zero upper label

/-- Restore an omitted zero plane; the width-zero case is the identity. -/
def pinExpand : (width : Nat) → Lanes (width - 1) → Lanes width
  | 0, lanes => lanes
  | width + 1, lanes => doubleLanes lanes

/-- Every stored pin is recovered after expansion, including width zero. -/
@[simp] theorem pinHalf_pinExpand (width : Nat) (pin : Lanes (width - 1)) :
    pinHalf width (pinExpand width pin) = pin := by
  cases width <;> simp [pinHalf, pinExpand]

/-- Expansion reconstructs every even full pin, including width zero. -/
theorem pinExpand_pinHalf (width : Nat) (pin : Lanes width) (even : EvenLanes pin) :
    pinExpand width (pinHalf width pin) = pin := by
  cases width with
  | zero => rfl
  | succ width => exact doubleLanes_halfLanes pin even

/-- Compression is injective on even full pins at every width. -/
theorem pinHalf_injective_on_even (width : Nat) {a b : Lanes width}
    (ha : EvenLanes a) (hb : EvenLanes b) (same : pinHalf width a = pinHalf width b) : a = b := by
  rw [← pinExpand_pinHalf width a ha, ← pinExpand_pinHalf width b hb, same]

/-- Every expanded stored pin has an omitted zero plane. -/
@[simp] theorem evenLanes_pinExpand (width : Nat) (pin : Lanes (width - 1)) :
    EvenLanes (pinExpand width pin) := by
  cases width with
  | zero =>
    intro i
    have h : (pin i).val < 1 := ZMod.val_lt (pin i)
    have hz : (pin i).val = 0 := by omega
    simpa [pinExpand, hz]
  | succ width => exact evenLanes_doubleLanes pin

/-- At a positive width every expanded lane is twice the stored lane. -/
theorem pinExpand_val (width : Nat) (positive : 1 ≤ width) (pin : Lanes (width - 1))
    (i : Fin laneCount) : (pinExpand width pin i).val = 2 * (pin i).val := by
  cases width with
  | zero => omega
  | succ width => exact doubleLanes_val pin i

/-- At a positive width the stored lane is half the expanded lane. -/
theorem pinExpand_val_half (width : Nat) (positive : 1 ≤ width) (pin : Lanes (width - 1))
    (i : Fin laneCount) : (pinExpand width pin i).val / 2 = (pin i).val := by
  rw [pinExpand_val width positive]
  omega

end Kriterion.CRT.Parity
