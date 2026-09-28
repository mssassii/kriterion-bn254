/-
The chunk analogue of the restricted extraction-stage bijection. A chunk's
published joins determine its hidden tree materials before its pin is solved.
Cold casts are allowed to depend on their leaf labels. This is an abstract
kernel; connecting its frame to chunkGarbleM is a separate obligation.
-/

import Proof.Privacy.CRT.Core.ParityExtractStage

namespace Kriterion.CRT.Privacy.ExtractStage

open Cryptography

/-- On a tag table, a chunk join is its hidden tree material XOR a fixed
block (the cold material sum XOR the input zero label). -/
def parityChunkPublish {w r : ℕ} (F : Frame labelBits w (r + 1)) (s : ℕ)
    (joinMask : Fin (w - 1) → Label) (h : ParityHidden w r) : ParityPublished w r :=
  (fun k => joinMask k ^^^ h.1 k,
    Parity.halfLanes (pin F s (embedParityHidden F s h)))

/-- Recover the hidden tree materials first, then cancel every cold cast.
This does not assume that cold casts are independent of their labels. -/
theorem parityChunkPublish_injective {w r : ℕ} (F : Frame labelBits w (r + 1))
    (hw : 1 ≤ w) (cold : ∀ α G, Kriterion.CRT.laneBit (F.cast α G) 0 = G)
    (s : ℕ) (hs : s < 2 ^ w) (joinMask : Fin (w - 1) → Label) :
    Function.Injective (parityChunkPublish F s joinMask) := by
  intro h h' same
  have trees : h.1 = h'.1 := by
    funext k
    have e := congrFun (congrArg Prod.fst same) k
    change joinMask k ^^^ h.1 k = joinMask k ^^^ h'.1 k at e
    have e' := congrArg (fun x => joinMask k ^^^ x) e
    simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using e'
  have halves := congrArg Prod.snd same
  have pins : pin F s (embedParityHidden F s h) = pin F s (embedParityHidden F s h') :=
    Parity.halfLanes_injective_on_even (pin_embedParityHidden_even F hw cold s h)
      (pin_embedParityHidden_even F hw cold s h') halves
  have casts : ∀ α, α ≠ s →
      castAt F s (embedParityHidden F s h) α = castAt F s (embedParityHidden F s h') α := by
    intro α hα
    simp only [castAt, if_neg hα, embedParityHidden, trees]
  have sums : castSum F s (embedParityHidden F s h) = castSum F s (embedParityHidden F s h') :=
    add_right_cancel pins
  have hmem : s ∈ Finset.range (2 ^ w) := Finset.mem_range.mpr hs
  unfold castSum at sums
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at sums
  have others : ∑ α ∈ (Finset.range (2 ^ w)).erase s, castAt F s (embedParityHidden F s h) α =
      ∑ α ∈ (Finset.range (2 ^ w)).erase s, castAt F s (embedParityHidden F s h') α :=
    Finset.sum_congr rfl fun α hα => casts α (Finset.ne_of_mem_erase hα)
  rw [others] at sums
  have hot := add_right_cancel sums
  have lifts : (embedParityHidden F s h).2 = (embedParityHidden F s h').2 := by
    simpa only [castAt, ↓reduceIte] using hot
  apply embedParityHidden_injective F s
  exact Prod.ext trees lifts

/-- The chunk's independent upper cast and hot tree materials give exactly
one preimage of every tuple of joins and half-pin. -/
theorem parityChunkPublish_bijective {w r : ℕ} (F : Frame labelBits w (r + 1))
    (hw : 1 ≤ w) (cold : ∀ α G, Kriterion.CRT.laneBit (F.cast α G) 0 = G)
    (s : ℕ) (hs : s < 2 ^ w) (joinMask : Fin (w - 1) → Label) :
    Function.Bijective (parityChunkPublish F s joinMask) :=
  bijective_of_injective_card (parityChunkPublish_injective F hw cold s hs joinMask) rfl

/-- Conditional on any fixed frame, the public chunk is uniform in its
actual reduced space. -/
theorem parity_chunk_published_uniform {w r : ℕ} {Rest : Type*} (rest : PMF Rest)
    (frame : Rest → Frame labelBits w (r + 1)) (hw : 1 ≤ w)
    (cold : ∀ x α G, Kriterion.CRT.laneBit ((frame x).cast α G) 0 = G)
    (s : ℕ) (hs : s < 2 ^ w) (joinMask : Rest → Fin (w - 1) → Label) :
    (rest.bind fun x => (PMF.uniformOfFintype (ParityHidden w r)).map fun h =>
      (x, parityChunkPublish (frame x) s (joinMask x) h)) =
    rest.bind fun x => (PMF.uniformOfFintype (ParityPublished w r)).map fun b => (x, b) :=
  bind_map_uniform_of_injective rest (fun x => parityChunkPublish (frame x) s (joinMask x))
    (fun x => parityChunkPublish_injective (frame x) hw (cold x) s hs (joinMask x)) rfl

end Kriterion.CRT.Privacy.ExtractStage
