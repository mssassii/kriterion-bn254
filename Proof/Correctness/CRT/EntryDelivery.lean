/-
C7 part A: the configuration-E replay delivers, on honest material, `slope_e · v + O_e` for every
encoding of both coordinates (the entry-level form of `coord_delivery`).

Ingredients: the evaluator reads only the labels of the coordinate's 254 bits
(`coordEvalM_labels_congr`); the restored Lamport labels are `Z_j ⊕ bit_j Δ` (`labelX_selected`,
`labelY_selected`); the published conversion vector reads back as the garbler's material on every
read cell (`FlatLayout.convAgree_unflatten` with `convVector_toArray`); the published records are
the garbler's records (`record_toRecord`, since `2 M < 256 ^ 78`).
-/

import Proof.Correctness.CRT.FlatLayout
import Proof.Correctness.CRT.RealTable
import Construction.CRT.BudgetFacts
import Proof.LamportCompatibility.Labels

namespace Kriterion.CRT.EntryDelivery

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
open Kriterion.CRT Kriterion.CRT.Entry Kriterion.CRT.FlatLayout

/-! ### The evaluator reads only the labels of the coordinate's bits -/

theorem treeEvalM_bits_congr (tagOf : Nat → Nat → Nat) (value : Nat) (B₁ B₂ J : Nat → Label)
    (levels : Nat) (agree : ∀ n < levels, B₁ n = B₂ n) :
    treeEvalM tagOf value B₁ J levels = treeEvalM tagOf value B₂ J levels := by
  induction levels with
  | zero => rfl
  | succ n ih =>
      rw [treeEvalM, treeEvalM, ih fun k lower => agree k (by omega)]
      congr 1
      funext previous
      by_cases zero : n = 0
      · subst zero
        simp only [if_true, agree 0 (by omega)]
      · rw [if_neg zero, if_neg zero, agree n (by omega)]

theorem chunkWidth_add_offset_le (T : CrtTable) (c n : Nat) (inRange : n < T.chunkWidth c) :
    T.chunkOffset c + n < T.inputBits := by
  unfold CrtTable.chunkWidth at inRange
  unfold CrtTable.chunkOffset
  have := Nat.lt_min.mp inRange
  omega

theorem coordEvalM_labels_congr (T : CrtTable) (S coord : Nat) (pub : ConvPublic) (records : Fin S → Nat)
    (v : Nat) (l₁ l₂ : Nat → Label) (agree : ∀ j < T.inputBits, l₁ j = l₂ j) :
    coordEvalM T S coord pub records v l₁ = coordEvalM T S coord pub records v l₂ := by
  have chunks : ∀ c : Fin T.chunkCount,
      chunkEvalM T coord l₁ v (pub.chunkJoin c.val) (Parity.pinExpand T.castWidth (pinOfBlocks (T.castWidth - 1) fun k => pub.chunkPin c.val k.val))
          c.val =
        chunkEvalM T coord l₂ v (pub.chunkJoin c.val)
          (Parity.pinExpand T.castWidth (pinOfBlocks (T.castWidth - 1) fun k => pub.chunkPin c.val k.val)) c.val := by
    intro c
    have tree := treeEvalM_bits_congr (chunkTreeTag coord c.val) (T.chunkValue v c.val)
      (fun n => l₁ (T.chunkOffset c.val + n)) (fun n => l₂ (T.chunkOffset c.val + n)) (pub.chunkJoin c.val)
      (T.chunkWidth c.val) fun n lower => agree _ (chunkWidth_add_offset_le T c.val n lower)
    unfold chunkEvalM
    simp only [tree]
  unfold coordEvalM
  simp only [chunks]

/-! ### The restored labels -/

theorem vector_toArray_getD {α : Type} {n : Nat} (f : Fin n → α) (j : Nat) (d : α) (h : j < n) :
    (Vector.ofFn f).toArray.getD j d = f ⟨j, h⟩ := by
  simp [Array.getD, h]

theorem labelX_selected (mac : InputMac) (j : Nat) (low : j < coordinateBitCount) :
    labelX (Lamport.selectedLabels mac) j = mac.x.get ⟨j, low⟩ := by
  have lowNat : j < 254 := low
  unfold labelX Lamport.selectedLabels
  rw [vector_toArray_getD _ _ _ (by omega)]
  simp only [dif_pos lowNat]

theorem labelY_selected (mac : InputMac) (j : Nat) (low : j < coordinateBitCount) :
    labelY (Lamport.selectedLabels mac) j = mac.y.get ⟨j, low⟩ := by
  have lowNat : j < 254 := low
  unfold labelY Lamport.selectedLabels
  rw [vector_toArray_getD _ _ _ (by show 254 + j < 508; omega)]
  have notLow : ¬ (254 + j < 254) := by omega
  simp only [coordinateBitCount] at *
  rw [dif_neg notLow]
  exact congrArg mac.y.get (Fin.ext (by show 254 + j - 254 = j; omega))

/-! ### The published conversion vector and records -/

theorem convVector_toArray (p : ConvPublic) : (convVector p).toArray = (p.flatten table).toArray := by
  have length : (p.flatten table).length = convCount := by
    rw [flatten_length, convBlocks_table]
  apply Array.ext
  · simp [convVector, length]
  · intro i hi hi'
    simp only [convVector, Vector.toArray_ofFn, Array.getElem_ofFn]
    simp only [List.size_toArray] at hi'
    simp [Array.getD, hi']

theorem convAgree_convOf (p : ConvPublic) : ConvAgree table (convOf (convVector p)) p := by
  unfold convOf
  rw [convVector_toArray]
  exact convAgree_unflatten table p

theorem toRecord_val (r : Nat) (small : r < 256 ^ recordBytes) : (toRecord r).val = r := by
  simp [toRecord, Nat.mod_eq_of_lt small]

theorem records_small {S : Nat} (g : CoordGarbled table S) (slopes : Fin S → Nat) (e : Fin S) :
    g.records slopes e < 256 ^ recordBytes :=
  lt_of_lt_of_le (CrtTable.records_roundtrip table g slopes e SliceC.bn254_modulus_pos).1
    bn254Table_record_fits

/-- **One coordinate delivers through the published material**: the flat conversion vector and the
records as published, and any labels that agree with the honest labels on the coordinate's bits. -/
theorem published_delivery (H : HashN) (S coord : Nat) (Δ : Label) (Z : Nat → Label)
    (slopes : Fin S → Nat) (v : Nat) (hv : v < 2 ^ 254) (hav : ∀ e, slopes e * v < table.wrapBound)
    (labels : Nat → Label) (hlabels : ∀ j < 254, labels j = Z j ^^^ (if v.testBit j then Δ else 0))
    (records : Fin S → Nat)
    (hrecords : ∀ e, records e = ((coordGarbleM table S coord Δ Z).eval H).records slopes e) (e : Fin S) :
    ((coordEvalM table S coord (convOf (convVector ((coordGarbleM table S coord Δ Z).eval H).pub))
        records v labels).eval H).decoded e =
      slopes e * v + ((coordGarbleM table S coord Δ Z).eval H).offset e := by
  have recordsEq : records = ((coordGarbleM table S coord Δ Z).eval H).records slopes := funext hrecords
  rw [recordsEq, coordEvalM_labels_congr table S coord _ _ v labels
      (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) hlabels,
    coordEvalM_congr table S coord _ _ _ v _ (convAgree_convOf _)]
  exact SliceC.coord_delivery H table S coord Δ Z slopes v SliceC.bn254_correctTable hv hav e

/-! ### The entry's labels -/

theorem coordinateBits_getLsb (value : BaseField) (j : Fin coordinateBitCount) :
    (ArgoMAC.coordinateBits value).getLsb j = value.val.testBit j.val := by
  unfold ArgoMAC.coordinateBits BitVec.getLsb
  rw [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp [j.isLt]

theorem labelX_honest (key : InputMacKey) (Z : Fin coordinateBitCount → Block) (Δ : Block)
    (hkey : ∀ j : Fin coordinateBitCount, key.x[j.val] = ⟨Z j, Z j ^^^ Δ⟩)
    (input : AffineInput) (j : Nat) (low : j < 254) :
    labelX (Lamport.selectedLabels (key.encode (BitInput.ofAffine input))) j =
      atNat Z 0 j ^^^ (if input.x.val.testBit j then Δ else 0) := by
  rw [labelX_selected _ j low]
  simp only [InputMacKey.encode, encodeCoordinate, BitInput.ofAffine, Vector.get_ofFn,
    coordinateBits_getLsb, BitAdaptor.encode]
  rw [hkey ⟨j, low⟩]
  simp only [atNat, dif_pos (show j < coordinateBitCount from low)]
  split <;> simp

theorem labelY_honest (key : InputMacKey) (Z : Fin coordinateBitCount → Block) (Δ : Block)
    (hkey : ∀ j : Fin coordinateBitCount, key.y[j.val] = ⟨Z j, Z j ^^^ Δ⟩)
    (input : AffineInput) (j : Nat) (low : j < 254) :
    labelY (Lamport.selectedLabels (key.encode (BitInput.ofAffine input))) j =
      atNat Z 0 j ^^^ (if input.y.val.testBit j then Δ else 0) := by
  rw [labelY_selected _ j low]
  simp only [InputMacKey.encode, encodeCoordinate, BitInput.ofAffine, Vector.get_ofFn,
    coordinateBits_getLsb, BitAdaptor.encode]
  rw [hkey ⟨j, low⟩]
  simp only [atNat, dif_pos (show j < coordinateBitCount from low)]
  split <;> simp

/-- Conversion sees only the low label bits; digest consumers retain `labelX_honest`. -/
theorem clip_labelX_honest (key : InputMacKey) (Z : Fin coordinateBitCount → Block) (Δ : Block)
    (hkey : ∀ j : Fin coordinateBitCount, key.x[j.val] = ⟨Z j, Z j ^^^ Δ⟩)
    (input : AffineInput) (j : Nat) (low : j < 254) :
    clip (labelX (Lamport.selectedLabels (key.encode (BitInput.ofAffine input))) j) =
      clip (atNat Z 0 j) ^^^ (if input.x.val.testBit j then clip Δ else 0) := by
  rw [labelX_honest key Z Δ hkey input j low, Narrow.clip_xor]
  split <;> simp only [show clip (0 : Block) = 0 from Narrow.clip_zero, BitVec.xor_zero]

/-- Conversion sees only the low label bits; digest consumers retain `labelY_honest`. -/
theorem clip_labelY_honest (key : InputMacKey) (Z : Fin coordinateBitCount → Block) (Δ : Block)
    (hkey : ∀ j : Fin coordinateBitCount, key.y[j.val] = ⟨Z j, Z j ^^^ Δ⟩)
    (input : AffineInput) (j : Nat) (low : j < 254) :
    clip (labelY (Lamport.selectedLabels (key.encode (BitInput.ofAffine input))) j) =
      clip (atNat Z 0 j) ^^^ (if input.y.val.testBit j then clip Δ else 0) := by
  rw [labelY_honest key Z Δ hkey input j low, Narrow.clip_xor]
  split <;> simp only [show clip (0 : Block) = 0 from Narrow.clip_zero, BitVec.xor_zero]

theorem coins_key_x (coins : Coins) (j : Fin coordinateBitCount) :
    coins.inputMacKey.x[j.val] = ⟨coins.inputZero .x j, coins.inputZero .x j ^^^ coins.inputDelta .x⟩ := by
  simp [Scheme.Coins.inputMacKey]

theorem coins_key_y (coins : Coins) (j : Fin coordinateBitCount) :
    coins.inputMacKey.y[j.val] = ⟨coins.inputZero .y j, coins.inputZero .y j ^^^ coins.inputDelta .y⟩ := by
  simp [Scheme.Coins.inputMacKey]

end Kriterion.CRT.EntryDelivery
