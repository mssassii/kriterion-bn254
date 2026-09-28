/-
**The garbler's tail through the fine view** (for `Hidden/DeltaView.lean`):
`DeltaView.tailRel : DeltaView.TailRel`.

Two coins with the same fine coins (`eCoins u κ`) and two tables with the same masks (`maskTable u κ`) run the
garbler's tail (the key, the masks, the digest) on related question lists with the same values:

* the key (family 10), the masks (family 7) and the digest finals (family 9) are never hot conversion tags, so the two
  hashes agree at every input these blocks ask, and each block asks the same inputs with the same values
  (`Paths.SameVisible.asked_congr`); the key's and the finals' inputs are fixed by the bridge key and by the digest
  table's value, which is label-free on a tag table;
* the digest table (family 8) asks, per coordinate and position, bit 0 at `Z` and bit 1 at `Z ⊕ Δ`. Off coordinate
  `κ` the two coins agree. On `κ`, at `u`'s bit the label is `u`'s label `E`, the same on both sides, and at the other
  bit it is `E ⊕ Δ`, so the two labels differ by `Δ ⊕ Δ'` exactly at the `Shifted` tags (`digestTable_rel`).
-/

import Proof.Privacy.CRT.Hidden.DeltaView
import Proof.Privacy.CRT.Paths.SameVisible

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.DeltaView

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Laws.LabelsSplitProof (LabelKeys coinKeys)
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_askN asked_tableM asked_garbleEntryM
  asked_digestTableM asked_of_tagged hashInput_div digestLabelTag_fields digestFinalTag_fields maskKeyTag_family
  tagFamily_key)
open Kriterion.ArgoMAC.PlanB (digitCount)

namespace DeltaTail

/-! ### Block algebra -/

theorem xor_shift (a d d' : Block) : a ^^^ d = a ^^^ d' ^^^ (d ^^^ d') := by
  rw [BitVec.xor_assoc a d', ← BitVec.xor_assoc d' d d', BitVec.xor_comm d' d, BitVec.xor_assoc d d' d',
    BitVec.xor_self, BitVec.xor_zero]

theorem xor_shift' {z z' d d' : Block} (same : z ^^^ d = z' ^^^ d') : z = z' ^^^ (d ^^^ d') := by
  calc z = z ^^^ d ^^^ d := (xor_xor_cancel z d).symm
    _ = z' ^^^ d' ^^^ d := by rw [same]
    _ = z' ^^^ (d ^^^ d') := by rw [BitVec.xor_assoc, BitVec.xor_comm d' d]

/-- A labelled input's low 128 bits, as a block, are its label. -/
theorem ofNat_hashInput (label : Block) (τ : ℕ) : BitVec.ofNat 128 (hashInput label τ) = label := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Paths.hashInput_label]

/-- `u`'s bit as the digest reads it (`inputBit`) and as the labels select it (`uBit`). -/
theorem inputBit_uBit (u : AffineInput) (κ : Fin 2) (p : ℕ) : inputBit u κ.val p = if uBit u κ p then 1 else 0 := by
  unfold inputBit uBit coordValue
  by_cases zero : κ.val = 0
  · simp only [zero, if_true]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (u.x.val / 2 ^ p) with m | m <;> simp [m]
  · simp only [zero, if_false]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (u.y.val / 2 ^ p) with m | m <;> simp [m]

/-! ### Relations of single inputs -/

/-- Two labelled inputs at one tag are related when their labels are equal off `hot` and shifted by `δ` on it. -/
theorem elem_rel (hot : ℕ → Prop) (δ : Block) (τ : ℕ) (l₁ l₂ : Block) (off : ¬ hot τ → l₁ = l₂)
    (on : hot τ → l₁ = l₂ ^^^ δ) (wide : 6 < tagFamily τ) :
    hashInput l₁ τ / 2 ^ 128 = hashInput l₂ τ / 2 ^ 128 ∧
      (¬ hot (hashInput l₁ τ / 2 ^ 128) → hashInput l₁ τ = hashInput l₂ τ) ∧
      (hot (hashInput l₁ τ / 2 ^ 128) →
        BitVec.ofNat 128 (hashInput l₁ τ) = BitVec.ofNat 128 (hashInput l₂ τ) ^^^ queryShift δ (hashInput l₁ τ / 2 ^ 128)) := by
  rw [hashInput_div, hashInput_div]
  refine ⟨rfl, fun cold => by rw [off cold], fun hot => ?_⟩
  rw [ofNat_hashInput, ofNat_hashInput]
  simpa only [queryShift, if_neg (by omega : ¬ tagFamily τ ≤ 6)] using on hot

theorem RelAsked.flatMap {ι : Type} {hot : ℕ → Prop} {δ : Block} (l : List ι) (f g : ι → List ℕ)
    (each : ∀ i ∈ l, RelAsked hot δ (f i) (g i)) : RelAsked hot δ (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons i rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact DeltaView.RelAsked.append (each i List.mem_cons_self)
      (ih fun j inside => each j (List.mem_cons_of_mem _ inside))

/-! ### The digest table -/

section Table

variable {u : AffineInput} {κ : Fin 2} {c c' : Entry.Coins}

/-- **The digest labels of the two coins**, per coordinate, position and bit. -/
theorem label_rel (same : eCoins u κ c = eCoins u κ c') (cc : Fin 2) (p : Fin coordinateBitCount) (b : ℕ)
    (hb : b < 2) :
    let l₁ := if b = 0 then Entry.zeroOf c cc p else Entry.zeroOf c cc p ^^^ Entry.deltaOf c cc
    let l₂ := if b = 0 then Entry.zeroOf c' cc p else Entry.zeroOf c' cc p ^^^ Entry.deltaOf c' cc
    (¬ Shifted u κ (digestLabelTag cc.val p.val b) → l₁ = l₂) ∧
      (Shifted u κ (digestLabelTag cc.val p.val b) → l₁ = l₂ ^^^ (deltaAt κ c ^^^ deltaAt κ c')) := by
  intro l₁ l₂
  obtain ⟨fam, hcoord, hslot, hpart⟩ := digestLabelTag_fields (b := b) cc.isLt
    (lt_of_lt_of_le p.isLt (by decide)) (by omega)
  have shifted : Shifted u κ (digestLabelTag cc.val p.val b) ↔ cc = κ ∧ b ≠ inputBit u κ.val p.val := by
    unfold Shifted
    rw [fam, hcoord, hslot, hpart]
    constructor
    · rintro ⟨sameCoord, ⟨small, _⟩ | ⟨_, bit⟩⟩
      · omega
      · exact ⟨Fin.ext sameCoord, bit⟩
    · rintro ⟨rfl, bit⟩
      exact ⟨rfl, Or.inr ⟨rfl, bit⟩⟩
  rw [shifted, deltaAt_eq_deltaOf, deltaAt_eq_deltaOf]
  by_cases coordSame : cc = κ
  · subst coordSame
    have labels := congrFun (eLabel_eq same) p
    unfold eLabel at labels
    rw [← zeroOf_eq_coinKeys, ← zeroOf_eq_coinKeys, ← deltaOf_eq_coinKeys, ← deltaOf_eq_coinKeys] at labels
    rw [inputBit_uBit]
    by_cases bit : uBit u cc p.val = true
    · simp only [if_pos bit] at labels ⊢
      rcases (show b = 0 ∨ b = 1 by omega) with zero | one
      · subst zero
        simp only [l₁, l₂, if_true]
        exact ⟨fun h => by simp at h, fun _ => xor_shift' labels⟩
      · subst one
        simp only [l₁, l₂, one_ne_zero, if_false]
        exact ⟨fun _ => labels, fun h => by simp at h⟩
    · simp only [if_neg bit] at labels ⊢
      rcases (show b = 0 ∨ b = 1 by omega) with zero | one
      · subst zero
        simp only [l₁, l₂, if_true]
        exact ⟨fun _ => labels, fun h => by simp at h⟩
      · subst one
        simp only [l₁, l₂, one_ne_zero, if_false]
        refine ⟨fun h => by simp at h, fun _ => ?_⟩
        rw [labels]
        exact xor_shift _ _ _
  · have other := keys_other same cc coordSame
    rw [← zeroOf_eq_coinKeys, ← zeroOf_eq_coinKeys, ← deltaOf_eq_coinKeys, ← deltaOf_eq_coinKeys] at other
    refine ⟨fun _ => ?_, fun h => absurd h.1 coordSame⟩
    simp only [l₁, l₂, other.1, other.2]

/-- **The digest table's question lists are related.** -/
theorem digestTable_rel (same : eCoins u κ c = eCoins u κ c') (H H' : HashN) :
    RelAsked (Shifted u κ) (deltaAt κ c ^^^ deltaAt κ c')
      (asked H (digestTableM coordinateBitCount (Entry.zeroOf c) (Entry.deltaOf c)))
      (asked H' (digestTableM coordinateBitCount (Entry.zeroOf c') (Entry.deltaOf c'))) := by
  rw [asked_digestTableM, asked_digestTableM]
  refine RelAsked.flatMap _ _ _ fun cc _ => RelAsked.flatMap _ _ _ fun p _ => ?_
  obtain ⟨off0, on0⟩ := label_rel same cc p 0 (by norm_num)
  obtain ⟨off1, on1⟩ := label_rel same cc p 1 (by norm_num)
  simp only [if_true, one_ne_zero, if_false] at off0 on0 off1 on1
  have wide : ∀ b, b < 2 → 6 < tagFamily (digestLabelTag cc.val p.val b) := by
    intro b hb
    rw [(digestLabelTag_fields (b := b) cc.isLt (lt_of_lt_of_le p.isLt (by decide)) (by omega)).1]
    norm_num
  exact List.Forall₂.cons (elem_rel _ _ _ _ _ off0 on0 (wide 0 (by norm_num)))
    (List.Forall₂.cons (elem_rel _ _ _ _ _ off1 on1 (wide 1 (by norm_num))) List.Forall₂.nil)

/-- **The digest table's value is the same** on two tables with the same masks. -/
theorem digestTable_eval {t t' : TagTable} (tsame : maskTable u κ t = maskTable u κ t') :
    (digestTableM coordinateBitCount (Entry.zeroOf c) (Entry.deltaOf c)).eval (hashOf t) =
      (digestTableM coordinateBitCount (Entry.zeroOf c') (Entry.deltaOf c')).eval (hashOf t') := by
  rw [eval_digestTableM, eval_digestTableM]
  funext cc p
  have small : ∀ b, b < 2 → digestLabelTag cc.val p.val b < 2 ^ 40 := fun b hb => by
    have := (Paths.TagKey.code_lt (k := ⟨8, cc.val, 0, 0, 0, p.val, b⟩)
      ⟨by norm_num, cc.isLt, by norm_num, by norm_num, by norm_num, lt_of_lt_of_le p.isLt (by decide),
        show b < 64 by omega⟩)
    exact this
  have cold : ∀ b (hb : b < 2), ¬ H8.hotConvTag Entry.table u κ.val ⟨_, small b hb⟩ := fun b hb => by
    unfold H8.hotConvTag
    rw [(digestLabelTag_fields (b := b) cc.isLt (lt_of_lt_of_le p.isLt (by decide)) (by omega)).1]
    omega
  simp only [digestTable, h128]
  rw [hashOf_hashInput t _ _ (small 0 (by norm_num)), hashOf_hashInput t _ _ (small 1 (by norm_num)),
    hashOf_hashInput t' _ _ (small 0 (by norm_num)), hashOf_hashInput t' _ _ (small 1 (by norm_num)),
    table_agree tsame _ (cold 0 (by norm_num)), table_agree tsame _ (cold 1 (by norm_num))]

end Table

/-! ### The key, the masks, the finals -/

theorem notShifted {u : AffineInput} {κ : Fin 2} {τ : ℕ} (fam : tagFamily τ = 7 ∨ tagFamily τ = 9 ∨ tagFamily τ = 10) :
    ¬ Shifted u κ τ := by
  rintro ⟨_, ⟨small, _⟩ | ⟨eight, _⟩⟩ <;> omega

theorem cold_of_fam {u : AffineInput} {κ : Fin 2} {τ : ℕ} (small : τ < 2 ^ 40) (fam : 5 < tagFamily τ) :
    ¬ H8.hotConvTag Entry.table u κ.val ⟨τ, small⟩ := by
  unfold H8.hotConvTag
  intro hot
  have low : tagFamily τ ≤ 5 := hot.1
  omega

section Blocks

variable {u : AffineInput} {κ : Fin 2} {t t' : TagTable} (tsame : maskTable u κ t = maskTable u κ t')

include tsame

theorem key_agree (b : BaseField) : hashOf t (maskKeyInput b) = hashOf t' (maskKeyInput b) := by
  have small : maskKeyTag < 2 ^ 40 := by
    unfold maskKeyTag tagCode Family.key
    norm_num
  unfold maskKeyInput
  exact hash_agree tsame _ _ _ small (cold_of_fam small (by rw [maskKeyTag_family]; norm_num))

theorem mask_agree (K : Block) :
    ∀ n ∈ asked (hashOf t) (maskAnswersM K digitCount), hashOf t n = hashOf t' n := by
  intro n inside
  obtain ⟨k, member, range, label, rfl⟩ :=
    asked_of_tagged (Paths.maskAnswersM_tagged K digitCount (by decide) (by decide)) _ n inside
  have small := Paths.TagKey.code_lt range
  exact hash_agree tsame _ _ _ small (cold_of_fam small (by
    rw [tagFamily_key range, Paths.maskKeys_fam k member]; norm_num))

theorem finals_agree {bits : ℕ} (table : Fin 2 → Fin bits → Block × Block) (digitOf : Fin digitCount → Digit)
    (offsetOf : Fin digitCount → AffineInput) (padOf : Fin digitCount → Exception.Entry) :
    ∀ n ∈ asked (hashOf t) (tableM digitCount fun o => garbleEntryM table o.val (digitOf o) (offsetOf o) (padOf o)),
      hashOf t n = hashOf t' n := by
  intro n inside
  rw [asked_tableM] at inside
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at inside
  obtain ⟨o, inEntry⟩ := inside
  rw [asked_garbleEntryM] at inEntry
  split at inEntry
  · exact absurd inEntry List.not_mem_nil
  · have final : ∀ (site : ℕ) (label : Block), site < 65536 →
        hashOf t (hashInput label (digestFinalTag site)) = hashOf t' (hashInput label (digestFinalTag site)) := by
      intro site label siteSmall
      have small : digestFinalTag site < 2 ^ 40 :=
        Paths.TagKey.code_lt (k := ⟨9, 0, 0, 0, 0, site, 0⟩)
          ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, siteSmall, by norm_num⟩
      exact hash_agree tsame _ _ _ small (cold_of_fam small (by
        rw [(digestFinalTag_fields siteSmall).1]; norm_num))
    have oSmall : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inEntry
    rcases inEntry with rfl | rfl
    · exact final _ _ (by omega)
    · exact final _ _ oSmall

end Blocks

theorem key_notShifted {u : AffineInput} {κ : Fin 2} (H : HashN) (b : BaseField) :
    ∀ n ∈ asked H (keyM b), ¬ Shifted u κ (n / 2 ^ 128) := by
  intro n inside
  simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inside
  subst inside
  unfold maskKeyInput
  rw [hashInput_div]
  exact notShifted (Or.inr (Or.inr maskKeyTag_family))

theorem mask_notShifted {u : AffineInput} {κ : Fin 2} (H : HashN) (K : Block) :
    ∀ n ∈ asked H (maskAnswersM K digitCount), ¬ Shifted u κ (n / 2 ^ 128) := by
  intro n inside
  obtain ⟨k, member, range, label, rfl⟩ :=
    asked_of_tagged (Paths.maskAnswersM_tagged K digitCount (by decide) (by decide)) _ n inside
  rw [hashInput_div]
  exact notShifted (Or.inl (by rw [tagFamily_key range]; exact Paths.maskKeys_fam k member))

theorem finals_notShifted {u : AffineInput} {κ : Fin 2} (H : HashN) {bits : ℕ}
    (table : Fin 2 → Fin bits → Block × Block) (digitOf : Fin digitCount → Digit)
    (offsetOf : Fin digitCount → AffineInput) (padOf : Fin digitCount → Exception.Entry) :
    ∀ n ∈ asked H (tableM digitCount fun o => garbleEntryM table o.val (digitOf o) (offsetOf o) (padOf o)),
      ¬ Shifted u κ (n / 2 ^ 128) := by
  intro n inside
  rw [asked_tableM] at inside
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at inside
  obtain ⟨o, inEntry⟩ := inside
  rw [asked_garbleEntryM] at inEntry
  split at inEntry
  · exact absurd inEntry List.not_mem_nil
  · have oSmall : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inEntry
    rcases inEntry with rfl | rfl
    · rw [hashInput_div]
      exact notShifted (Or.inr (Or.inl (digestFinalTag_fields (o := 2 * o.val) (by omega)).1))
    · rw [hashInput_div]
      exact notShifted (Or.inr (Or.inl (digestFinalTag_fields oSmall).1))

end DeltaTail

open DeltaTail in
/-- **The garbler's tail through the fine view** (`TailRel`). -/
theorem tailRel : TailRel := by
  intro scalar u κ c c' t t' same tsame
  have bridge : c.bridgeKey = c'.bridgeKey := bridgeKey_eq same
  have pads : c.exceptionPad = c'.exceptionPad := exceptionPad_eq same
  have outputs : Entry.outputKeysOf scalar c = Entry.outputKeysOf scalar c' := by
    unfold Entry.outputKeysOf
    rw [offsets_eq same]
  have keyEval : (keyM c.bridgeKey).eval (hashOf t') = (keyM c.bridgeKey).eval (hashOf t) := by
    rw [eval_keyM, eval_keyM]
    unfold maskKey
    rw [key_agree tsame]
  have keyAsked : asked (hashOf t') (keyM c.bridgeKey) = asked (hashOf t) (keyM c.bridgeKey) := by
    simp only [keyM, asked_bind, asked_askN, asked_pure]
  have maskSame := Paths.SameVisible.asked_congr (hashOf t) (hashOf t')
    (maskAnswersM ((keyM c.bridgeKey).eval (hashOf t)) digitCount) (mask_agree tsame _)
  have tableEval := digestTable_eval (c := c) (c' := c') tsame
  set T := (digestTableM coordinateBitCount (Entry.zeroOf c) (Entry.deltaOf c)).eval (hashOf t) with hT
  have fa := finals_agree tsame T (fun o => ((Entry.outputKeysOf scalar c).get o).digit)
    (fun o => ((Entry.outputKeysOf scalar c).get o).offset.coordinates) (fun o => c.exceptionPad.get o)
  have finalsSame := Paths.SameVisible.asked_congr (hashOf t) (hashOf t') _ fa
  unfold tailM digestGarbleM
  simp only [asked_bind, asked_pure, List.append_nil, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [← bridge, ← pads, ← outputs, keyEval, ← tableEval, keyAsked, maskSame.1, maskSame.2, finalsSame.1,
    finalsSame.2]
  refine ⟨?_, rfl⟩
  exact RelAsked.append (RelAsked.refl (key_notShifted _ _))
    (RelAsked.append (RelAsked.refl (mask_notShifted _ _))
      (RelAsked.append (digestTable_rel same _ _) (RelAsked.refl (finals_notShifted _ _ _ _ _))))

end Kriterion.CRT.Privacy.DeltaView
