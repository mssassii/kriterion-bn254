/-
An isolated executable parity cast and half-pin wire type. This module does not
replace the entry's active cast: the privacy source and replay integration must
first be updated to use the label-dependent parity law.
-/

import Construction.CRT.Parity
import Construction.CRT.Query

namespace Kriterion.CRT.Parity

open Cryptography Kriterion.ArgoMAC

/-- Preserve the original full-width hash reading; its low plane is discarded. -/
def parityCastAnswers (width : Nat) : Nat := castAnswers width

/-- A total cast reading: the original block-aligned reading of `width` bits per lane, with the
low plane of every lane replaced by the corresponding bit of the control label. At width zero
(`liftUpper 0`, `pinHalf 0` are the identity) it is the old reading of the singleton type. -/
def parityCastLanes (width : Nat) (label : Label) (value : Nat) : Lanes width :=
  liftUpper width (pinHalf width (castLanes width value)) label

/-- The computable parity cast keeps the original raw hash reads and block alignment.
Only the low bit of each parsed lane changes, to the corresponding control-label bit. -/
def parityCastM (width : Nat) (label : Label) (tagOf : Nat → Nat) : CM (Lanes width) :=
  hlongM (embed label) tagOf (castAnswers width) >>= fun value =>
    pure (materialize (parityCastLanes width label value))

@[simp] theorem eval_parityCastM (H : HashN) (width : Nat) (label : Label)
    (tagOf : Nat → Nat) :
    (parityCastM width label tagOf).eval H =
      parityCastLanes width label (hlong H (embed label) tagOf (parityCastAnswers width)) := by
  simp [parityCastM, parityCastAnswers, materialize_eq]

theorem bounded_parityCastM (width : Nat) (label : Label) (tagOf : Nat → Nat) :
    (parityCastM width label tagOf).Bounded (parityCastAnswers width) :=
  (FreeQuery.Bounded.bind (bounded_hlongM (embed label) tagOf (castAnswers width))
    fun _ => FreeQuery.Bounded.pure' _ 0).of_eq (by simp [parityCastAnswers])

/-- Every nonempty arithmetic cast has the control label as its low plane. -/
@[simp] theorem laneBit_parityCastLanes_zero (width : Nat) (label : Label) (value : Nat) :
    laneBit (parityCastLanes (width + 1) label value) 0 = label :=
  laneBit_parityLift_zero _ _

/-- Keeping the original readings preserves the query count at every width. -/
@[simp] theorem parityCastAnswers_eq (width : Nat) :
    parityCastAnswers width = castAnswers width := rfl

/-- A public half-pin stores the upper planes only. `width` is its stored lane width;
its reconstructed full pin has width `width + 1`. -/
structure HalfPin (width : Nat) where
  upper : Lanes width

namespace HalfPin

/-- Construct public data from a full even pin. The caller proves evenness when
using the expansion theorem; the wire representation contains no proof field. -/
def ofFull {width : Nat} (pin : Lanes (width + 1)) : HalfPin width :=
  ⟨halfLanes pin⟩

/-- Expand a public half-pin to the original full-width arithmetic vector. -/
def expand {width : Nat} (pin : HalfPin width) : Lanes (width + 1) :=
  doubleLanes pin.upper

/-- Exactly `width` narrow labels encode the `104 * width` stored bits. -/
def blocks {width : Nat} (pin : HalfPin width) : Fin width → Label := pinBlocks pin.upper

/-- Every string of `width` narrow labels decodes to a public half-pin. -/
def ofBlocks (width : Nat) (wire : Fin width → Label) : HalfPin width :=
  ⟨pinOfBlocks width wire⟩

@[simp] theorem expand_even {width : Nat} (pin : HalfPin width) : EvenLanes pin.expand :=
  evenLanes_doubleLanes _

theorem expand_ofFull {width : Nat} (pin : Lanes (width + 1)) (even : EvenLanes pin) :
    (ofFull pin).expand = pin := doubleLanes_halfLanes pin even

@[simp] theorem ofFull_expand {width : Nat} (pin : HalfPin width) :
    ofFull pin.expand = pin := by
  cases pin
  simp [ofFull, expand]

end HalfPin

end Kriterion.CRT.Parity
