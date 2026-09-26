/-
**The designed rule of the hidden hop, with F3 applied**.

The rule decides, at input `u`, which of the garbler's entries count as visible. It is xinshu's `Designed` shape
(`Proof/Privacy/Phase3/Hidden/Reduction.lean:139-141`: scalar, tape, input, entry), over any index types and any
tape whose coins carry the bridge input `t` and the digest's exceptional inputs:

1. `x = t` is tested **first**, from the tape (F3): the bridge is visible iff `u` is on the curve; no tag is ever
   decoded from `t`, so no range term is charged;
2. families 0 to 6 (the conversion layer and the body pads): visible iff the position is cold at `u` (`hotTag`);
3. family 7 (the Embryo masks, read at `K = (hash t).1`): visible iff `u` is on the curve;
4. family 8 (the digest labels): visible iff the entry's bit is the bit `u` holds, **on and off the curve** (the digest
   is keyed on raw Lamport labels, unlike xinshu's gadget);
5. family 9 (the digest finals): the final of digit `o` is visible iff `u = exc_o`, read from the tape;
6. everything else (and every permutation entry, of which the CRT entry has none, D2): hidden.
-/

import Proof.Privacy.CRT.Sites

namespace Kriterion.CRT.Privacy

open BN254 Cryptography Kriterion.CRT

/-- A garbler entry: a public query with its answer (xinshu's `Entry`). -/
abbrev Entry (FI EI : Type) := Σ query : PublicQuery FI EI, query.Answer

/-- Bit `i` of coordinate `κ` of an input (the Lamport bit the evaluator holds). -/
def inputBit (u : AffineInput) (κ i : ℕ) : ℕ := coordValue u κ / 2 ^ i % 2

/-- What the designed rule reads from the tape: the exceptional input of each digit (a function of the scalar and
the garbler's offsets; `none` when the digit has none). The bridge key is a labelled position
(family 10), so the rule does not read `t`. -/
structure TapeView (Coins Oracle : Type) where
  exceptional : NonZeroScalar → Coins × Oracle → ℕ → Option AffineInput

/-- **The CRT designed rule** (F3). -/
def crtDesigned {FI EI Coins Oracle : Type} (T : CrtTable) (view : TapeView Coins Oracle) :
    NonZeroScalar → (Coins × Oracle) → AffineInput → Entry FI EI → Bool :=
  fun scalar tape u entry =>
    match entry.1 with
    | .hash x =>
      let tag := x.val / 2 ^ 128
      match tagFamily tag with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => !hotTag T u tag
      | 7 | 10 => validate u
      | 8 => tagPart tag == inputBit u (tagCoord tag) (tagSlot tag)
      | 9 => view.exceptional scalar tape (tagSlot tag) == some u
      | _ => false
    | _ => false

/-- The rule never shows a hot conversion or body position. -/
theorem crtDesigned_hot {FI EI Coins Oracle : Type} (T : CrtTable) (view : TapeView Coins Oracle)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) (u : AffineInput) (x : BaseField) (answer : Block × Block)
    (tag : ℕ) (htag : x.val / 2 ^ 128 = tag) (family : tagFamily tag ≤ 6)
    (hot : hotTag T u tag = true) :
    crtDesigned (FI := FI) (EI := EI) T view scalar tape u ⟨.hash x, answer⟩ = false := by
  unfold crtDesigned
  dsimp only
  rw [htag]
  generalize hfam : tagFamily tag = fam at family
  interval_cases fam <;> simp [hot]

/-- Off the curve the masks and the bridge key are hidden. -/
theorem crtDesigned_offCurve_mask {FI EI Coins Oracle : Type} (T : CrtTable) (view : TapeView Coins Oracle)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) (u : AffineInput) (x : BaseField) (answer : Block × Block)
    (tag : ℕ) (htag : x.val / 2 ^ 128 = tag) (off : validate u = false)
    (mask : tagFamily tag = 7 ∨ tagFamily tag = 10) :
    crtDesigned (FI := FI) (EI := EI) T view scalar tape u ⟨.hash x, answer⟩ = false := by
  unfold crtDesigned
  dsimp only
  rw [htag]
  rcases mask with fam | fam <;> rw [fam] <;> exact off

end Kriterion.CRT.Privacy
