/-
**No chunk joins, privacy groundwork (1/4): the XOR bijection** (ROUND2 §5, `r2_zerojoins_notes.md`).

Standalone: imports only the narrow label boundary and Mathlib's `Equiv`; no privacy-chain module.

A raw 128-bit block is a low 101-bit conversion part (`clip`) and a high part. `setLow x l` keeps the high
part of `x` and installs the low part `l`. With no chunk joins, the actual zero label of a non-first chunk
bit is `setLow Z (levelSum)`: the coins' zero label `Z` with its low part replaced by the XOR of the
level's tree materials (`Key.lean`). With the level sum split as `hot ⊕ cold` (hot material at the
evaluator's active slot, `cold` the XOR of the others):

* `hotXorEquiv` (**the XOR bijection**): for fixed `cold`, `Δ` and bit `b`, the hot material `h` and the
  low part of the selected label `ℓ = h ⊕ cold ⊕ b·clip Δ` determine each other
  (`h = ℓ ⊕ cold ⊕ b·clip Δ`); an involution of `Label`.
* `bitEquiv`: per coordinate bit, the pair (coins' zero label, raw hot answer) is in bijection with the
  pair (actual zero label, residual), the residual being the raw answer with its low part replaced by the
  low part of the coins' zero label (non-first bits) or the raw answer itself (first bits, where the
  actual zero label is the coins' one). The bijection reads neither `Δ` nor the input: it transfers the
  hot tree material into the actual zero label, and the low part of the coins' zero label, which the
  construction no longer uses, into the residual.
* `keysEquiv`: the same, for all bits of both coordinates at once (a product of `bitEquiv`s).

Everything here holds for every `cold` and every raw value (no uniformity yet; laws are in `Law.lean`).
-/

import Construction.CRT.Label
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Basic

namespace Kriterion.CRT.Privacy.NoJoins

open Kriterion.CRT.Narrow

/-! ### Literal zeros (the `BitVec` lemmas are stated at `0#w`) -/

theorem raw_xor_zero (x : RawBlock) : x ^^^ (0 : RawBlock) = x := BitVec.xor_zero

theorem label_xor_zero (x : Label) : x ^^^ (0 : Label) = x := BitVec.xor_zero

theorem label_zero_xor (x : Label) : (0 : Label) ^^^ x = x := BitVec.zero_xor

/-! ### Low and high parts of a raw block -/

/-- Keep the high `128 − 101` bits of `x` and install the low part `l`. -/
def setLow (x : RawBlock) (l : Label) : RawBlock := x ^^^ embed (clip x) ^^^ embed l

@[simp] theorem clip_setLow (x : RawBlock) (l : Label) : clip (setLow x l) = l := by
  unfold setLow
  rw [clip_xor, clip_xor, clip_embed, clip_embed, BitVec.xor_self, BitVec.zero_xor]

@[simp] theorem setLow_setLow (x : RawBlock) (l l' : Label) : setLow (setLow x l) l' = setLow x l' := by
  unfold setLow
  rw [clip_xor, clip_xor, clip_embed, clip_embed]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, embed_xor]
  cases (embed (clip x)).getLsbD i <;> cases (embed l).getLsbD i <;> cases (embed l').getLsbD i <;>
    cases x.getLsbD i <;> rfl

@[simp] theorem setLow_clip (x : RawBlock) : setLow x (clip x) = x := by
  unfold setLow
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `setLow` in the form the construction produces it: the zero label XOR the lifted `levelSum ⊕ clip Z`
(`Entry.keyZeroOf` with `J = levelSum ⊕ clip Z`). -/
theorem xor_embed_eq_setLow (Z : RawBlock) (sum : Label) :
    Z ^^^ embed (sum ^^^ clip Z) = setLow Z sum := by
  unfold setLow
  rw [embed_xor, BitVec.xor_comm (embed sum) (embed (clip Z)), ← BitVec.xor_assoc]

/-- A raw block is determined by its low part and its high part (`setLow x 0`). -/
theorem setLow_ext {x y : RawBlock} (low : clip x = clip y) (high : setLow x 0 = setLow y 0) : x = y := by
  rw [← setLow_clip x, ← setLow_clip y, ← setLow_setLow x 0, ← setLow_setLow y 0, high, low]

/-! ### The XOR bijection of the hot material -/

/-- The mask of the hot material at a non-first bit: the cold XOR and the bit's share of `clip Δ`. -/
def hotMask (cold : Label) (delta : RawBlock) (bit : Bool) : Label :=
  cold ^^^ (if bit then clip delta else 0)

/-- **The XOR bijection**: at a non-first chunk bit, the low part of the selected label is
`ℓ = h ⊕ cold ⊕ b·clip Δ` for the hot material `h`; for fixed `cold`, `Δ`, `b` this is an involution,
and `h = ℓ ⊕ cold ⊕ b·clip Δ`. -/
def hotXorEquiv (cold : Label) (delta : RawBlock) (bit : Bool) : Label ≃ Label where
  toFun h := h ^^^ hotMask cold delta bit
  invFun l := l ^^^ hotMask cold delta bit
  left_inv h := by
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv l := by
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem hotXorEquiv_apply (cold : Label) (delta : RawBlock) (bit : Bool) (h : Label) :
    hotXorEquiv cold delta bit h = h ^^^ hotMask cold delta bit := rfl

/-- The low part of the selected label at a non-first bit is the image of the hot material. -/
theorem clip_selected_hot (Z delta : RawBlock) (h cold : Label) (bit : Bool) :
    clip (setLow Z (h ^^^ cold) ^^^ (if bit then delta else 0)) = hotXorEquiv cold delta bit h := by
  rw [hotXorEquiv_apply, hotMask, clip_xor, clip_setLow, BitVec.xor_assoc]
  cases bit
  · simp only [Bool.false_eq_true, if_false, clip_zero]
  · simp only [if_true]

/-! ### One coordinate bit -/

/-- A raw hash answer (two blocks; the conversion reads the low part of the first). -/
abbrev Answer := RawBlock × RawBlock

/-- **The bit relabelling**, forward: `(Z, a) ↦ (Z', r)`. A first bit keeps both. A non-first bit with cold
XOR `cold` gets the actual zero label `Z' = setLow Z (clip a.1 ⊕ cold)` and the residual
`r = (setLow a.1 (clip Z), a.2)`. -/
def bitFwd (first : Bool) (cold : Label) (p : RawBlock × Answer) : RawBlock × Answer :=
  if first then p else (setLow p.1 (clip p.2.1 ^^^ cold), (setLow p.2.1 (clip p.1), p.2.2))

/-- The bit relabelling, backward. -/
def bitInv (first : Bool) (cold : Label) (q : RawBlock × Answer) : RawBlock × Answer :=
  if first then q else (setLow q.1 (clip q.2.1), (setLow q.2.1 (clip q.1 ^^^ cold), q.2.2))

theorem bitInv_bitFwd (first : Bool) (cold : Label) (p : RawBlock × Answer) :
    bitInv first cold (bitFwd first cold p) = p := by
  obtain ⟨z, a1, a2⟩ := p
  cases first
  · simp only [bitFwd, bitInv, Bool.false_eq_true, if_false, clip_setLow, setLow_setLow, setLow_clip,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rfl

theorem bitFwd_bitInv (first : Bool) (cold : Label) (q : RawBlock × Answer) :
    bitFwd first cold (bitInv first cold q) = q := by
  obtain ⟨z, r1, a2⟩ := q
  cases first
  · simp only [bitFwd, bitInv, Bool.false_eq_true, if_false, clip_setLow, setLow_setLow, setLow_clip,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rfl

/-- **The bit relabelling** as an equivalence (it reads neither `Δ` nor the input bit). -/
def bitEquiv (first : Bool) (cold : Label) : (RawBlock × Answer) ≃ (RawBlock × Answer) where
  toFun := bitFwd first cold
  invFun := bitInv first cold
  left_inv := bitInv_bitFwd first cold
  right_inv := bitFwd_bitInv first cold

theorem bitEquiv_fst (first : Bool) (cold : Label) (p : RawBlock × Answer) :
    (bitEquiv first cold p).1 = if first then p.1 else setLow p.1 (clip p.2.1 ^^^ cold) := by
  show (bitFwd first cold p).1 = _
  unfold bitFwd
  split <;> rfl

/-! ### All bits of both coordinates -/

/-- The coordinate bit positions. -/
abbrev Bits := Fin 254

/-- Zero labels of both coordinates (`0` is `x`). -/
abbrev KeyZeros := Fin 2 → Bits → RawBlock

/-- Raw hot tree answers of both coordinates, indexed by coordinate bit (read at non-first bits only). -/
abbrev HotAnswers := Fin 2 → Bits → Answer

/-- Pair the zero labels and the hot answers bit by bit. -/
def zipKeys : KeyZeros × HotAnswers ≃ (Fin 2 → Bits → RawBlock × Answer) where
  toFun p κ j := (p.1 κ j, p.2 κ j)
  invFun q := (fun κ j => (q κ j).1, fun κ j => (q κ j).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem zipKeys_apply (p : KeyZeros × HotAnswers) (κ : Fin 2) (j : Bits) :
    zipKeys p κ j = (p.1 κ j, p.2 κ j) := rfl

theorem zipKeys_symm_apply_fst (q : Fin 2 → Bits → RawBlock × Answer) (κ : Fin 2) (j : Bits) :
    (zipKeys.symm q).1 κ j = (q κ j).1 := rfl

/-- **The key relabelling**: bitwise `bitEquiv` with first-bit flags `first κ j` and cold XORs `cold κ j`. -/
def keysEquiv (first : Fin 2 → Bits → Bool) (cold : Fin 2 → Bits → Label) :
    KeyZeros × HotAnswers ≃ KeyZeros × HotAnswers :=
  zipKeys.trans ((Equiv.piCongrRight fun κ => Equiv.piCongrRight fun j => bitEquiv (first κ j) (cold κ j)).trans
    zipKeys.symm)

/-- The first component of the key relabelling: the actual zero labels. -/
theorem keysEquiv_fst (first : Fin 2 → Bits → Bool) (cold : Fin 2 → Bits → Label)
    (p : KeyZeros × HotAnswers) (κ : Fin 2) (j : Bits) :
    (keysEquiv first cold p).1 κ j =
      if first κ j then p.1 κ j else setLow (p.1 κ j) (clip (p.2 κ j).1 ^^^ cold κ j) :=
  bitEquiv_fst (first κ j) (cold κ j) (p.1 κ j, p.2 κ j)

end Kriterion.CRT.Privacy.NoJoins
