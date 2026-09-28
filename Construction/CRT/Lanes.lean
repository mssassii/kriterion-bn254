/-
Arithmetic labels (Heath 2024): an arithmetic label of a value `σ` in
`Z_{2^l}` is a vector of 101 lanes; the garbler holds the mask `A`, the evaluator `A + σ • Δ⃗`,
where `Δ⃗` reads the global offset `Δ` lane by lane as 0 or 1. Sums and multiplication by public
naturals are free.

This file defines `Δ⃗` (`deltaLanes`), the boolean label of one bit plane (`laneBit`), the
reduction to a smaller width (`reduceTo`, a ring hom when the width shrinks, L6), the exact peel
(`peelDiv`, L11), scaling by a public natural, and `materialize`, the identity that stores the 101
lanes in an array (programs call it at stage boundaries so that the interpreter does not
recompute a lane).
-/

import Construction.CRT.Params

namespace Kriterion.CRT

open Cryptography

variable {width : Nat}

/-- `Δ⃗`: lane `i` is bit `i` of `Δ` (frozen text). -/
def deltaLanes (l : Nat) (Δ : Label) : Lanes l := fun i => if Δ.getLsbD i.1 then 1 else 0

/-- The boolean label of bit plane `b`: bit `i` of the block is bit `b` of lane `i` (frozen text). -/
def laneBit {l : Nat} (A : Lanes l) (b : Nat) : Label :=
  BitVec.ofFnLE (fun i : Fin laneCount => (A i).val.testBit b)

/-- Reduction to width `target` lane by lane (`x ↦ x mod 2 ^ target`); a ring hom when
`target ≤ width` (L6). -/
def reduceTo (target : Nat) (lanes : Lanes width) : Lanes target :=
  fun lane => ((lanes lane).val : ZMod (2 ^ target))

/-- The exact peel (L11): `((R - U) mod 2 ^ rb) / 2 ^ w` lane by lane, of width `rb - w`
(frozen text). -/
def peelDiv {rb : Nat} (R U : Lanes rb) (w : Nat) : Lanes (rb - w) :=
  fun i => ((((R - U) i).val / 2 ^ w : Nat) : ZMod (2 ^ (rb - w)))

/-- Multiplication of every lane by a public natural. -/
def scaleLanes (factor : Nat) (lanes : Lanes width) : Lanes width :=
  fun lane => (factor : ZMod (2 ^ width)) * lanes lane

/-- Reading back an array built by `Vector.ofFn`. -/
@[simp] theorem vector_get_ofFn {α : Type} {count : Nat} (values : Fin count → α) (index : Fin count) :
    (Vector.ofFn values).get index = values index := by
  simp [Vector.get]; rfl

/-- Reading back an array built by `Vector.ofFn`, as a function. -/
@[simp] theorem vector_get_ofFn_fun {α : Type} {count : Nat} (values : Fin count → α) :
    (Vector.ofFn values).get = values :=
  funext (vector_get_ofFn values)

/-- The identity on lanes (it used to store the lanes in an array; Lean compiles a top-level
function whose type ends in a function type at full arity, so a stored array is rebuilt at every
read). Programs materialize through `materializeM`
(`Query.lean`), where the array is a bind parameter. -/
def materialize (lanes : Lanes width) : Lanes width := lanes

theorem materialize_eq (lanes : Lanes width) : materialize lanes = lanes := by
  funext lane
  simp [materialize, vector_get_ofFn]

/-- The identity on finite families (see `materialize`; programs use `storeM`). -/
def stored {α : Type} {count : Nat} (family : Fin count → α) : Fin count → α := family

@[simp] theorem stored_eq {α : Type} {count : Nat} (family : Fin count → α) :
    stored family = family := by
  funext index
  simp [stored]

/-- Read a finite family as a total function of a natural index (`default` off range). -/
def atNat {α : Type} {count : Nat} (family : Fin count → α) (default : α) (index : Nat) : α :=
  if inRange : index < count then family ⟨index, inRange⟩ else default

end Kriterion.CRT
