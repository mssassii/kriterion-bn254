import Init.Data.BitVec.Lemmas
import Init.Data.Function

/-!
The narrow conversion-label boundary.  `RawBlock` is definitionally the
challenge's `Cryptography.Block`, without importing its cryptographic and
probability infrastructure.  Hash answers, hash-input strides, external input
labels, and digest labels remain raw blocks.

This module has no existing consumers yet.  It deliberately does not assert
`embed (clip x) = x`: the upper 24 bits of a raw block are discarded.
-/

namespace Kriterion.CRT.Narrow

abbrev labelBits : Nat := 104
abbrev RawBlock := BitVec 128
abbrev Label := BitVec labelBits

/-- Keep the low conversion-label bits of a raw block. -/
def clip (x : RawBlock) : Label := x.setWidth labelBits

/-- Canonical zero extension at the raw hash-input boundary. -/
def embed (x : Label) : RawBlock := x.setWidth 128

@[simp] theorem clip_xor (a b : RawBlock) :
    clip (a ^^^ b) = clip a ^^^ clip b :=
  BitVec.setWidth_xor

@[simp] theorem embed_xor (a b : Label) :
    embed (a ^^^ b) = embed a ^^^ embed b :=
  BitVec.setWidth_xor

@[simp] theorem clip_zero : clip 0 = 0 := BitVec.setWidth_zero _ _

@[simp] theorem embed_zero : embed 0 = 0 := BitVec.setWidth_zero _ _

@[simp] theorem clip_embed (x : Label) : clip (embed x) = x := by
  unfold clip embed
  rw [BitVec.setWidth_setWidth_of_le x (by decide : labelBits ≤ 128),
    BitVec.setWidth_eq]

theorem embed_injective : Function.Injective embed := by
  intro a b same
  have projected := congrArg clip same
  simpa only [clip_embed] using projected

theorem clip_surjective : Function.Surjective clip := by
  intro x
  exact ⟨embed x, clip_embed x⟩

@[simp] theorem clip_xor_embed (x : RawBlock) (l : Label) :
    clip (x ^^^ embed l) = clip x ^^^ l := by
  rw [clip_xor, clip_embed]

@[simp] theorem clip_embed_xor (l : Label) (x : RawBlock) :
    clip (embed l ^^^ x) = l ^^^ clip x := by
  rw [clip_xor, clip_embed]

@[simp] theorem embed_toNat (x : Label) : (embed x).toNat = x.toNat :=
  BitVec.toNat_setWidth_of_le (by decide : labelBits ≤ 128)

theorem clip_toNat (x : RawBlock) :
    (clip x).toNat = x.toNat % 2 ^ labelBits :=
  BitVec.toNat_setWidth _ _

theorem embed_toNat_lt (x : Label) : (embed x).toNat < 2 ^ labelBits := by
  rw [embed_toNat]
  exact x.isLt

theorem embed_clip_of_lt (x : RawBlock) (small : x.toNat < 2 ^ labelBits) :
    embed (clip x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [embed_toNat, clip_toNat, Nat.mod_eq_of_lt small]

end Kriterion.CRT.Narrow
