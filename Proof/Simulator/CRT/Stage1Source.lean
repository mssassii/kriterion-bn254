/-
**The source a memory holds** (M2): `sourceOf` builds `Entry.Source` from the draws, `extract ram = sourceOf
(readDraw ram)` reads it back from RAM, and `sourceHolds_extract` says RAM holds its own extracted source in the
serializer's sense (`CrtPieces.SourceHolds`) whenever every cell is in range (`CellsValid`).
-/

import Proof.Simulator.CRT.Stage1Stored
import Proof.Simulator.CutoffSource

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.CRT.Entry (joinCount pinCount pinWidth Source)
open CrtStage1 CrtDraws CrtStored CrtConv CrtPieces CrtRecord

namespace CrtSource

noncomputable section

/-! ### The source of the draws -/

/-- The record `r` (`x` then `y`) of the draws: the mixed-radix integer of its digits. -/
def recordNat (d : Draw) (r : Nat) : Nat :=
  ∑ i ∈ Finset.range moduliCount, total 0 d.digits (r * moduliCount + i) * radixAt i

/-- **The source of the draws.** -/
def sourceOf (d : Draw) : Source where
  curve := (total 0 d.fields 0, total 0 d.fields 1, total 0 d.fields 2)
  rows g := ⟨total 0 d.fields (3 + 3 * g.val), total 0 d.fields (3 + 3 * g.val + 1),
    total 0 d.fields (3 + 3 * g.val + 2)⟩
  exception g := Vector.ofFn fun b : Fin 2 => BitVec.ofNat 4 (total 0 d.bytes (2 * g.val + b.val))
  joins κ i := BitVec.ofNat labelBits (total 0 d.joins (κ.val * joinCount + i.val))
  pins κ k lane := ((total 0 d.pins ((κ.val * pinCount + k.val) * laneCount + lane.val) : Nat) : ZMod (2 ^ pinWidth k))
  recX e := ⟨recordNat d e.val % Entry.table.product, Nat.mod_lt _ Entry.table_product_pos⟩
  recY e := ⟨recordNat d (Entry.xCount + e.val) % Entry.table.product, Nat.mod_lt _ Entry.table_product_pos⟩
  zeros κ i := BitVec.ofNat 128 (total 0 d.zeros (254 * κ.val + i.val))
  deltas κ := BitVec.ofNat 128 (total 0 d.deltas κ.val)

/-- **The source a memory holds.** -/
def extract (ram : Word → Word) : Source := sourceOf (readDraw ram)

/-- Every cell of the stage-1 regions is in range. -/
structure CellsValid (ram : Word → Word) : Prop where
  fields : ∀ index, index < fieldCount → (ram (word (fieldBase + index))).toNat < baseFieldModulus
  bytes : ∀ n, n < exceptionCellCount → (ram (word (exceptionBase + n))).toNat < 2 ^ 4
  joins : ∀ n, n < 2 * joinCount → (ram (word (joinAddr n))).toNat < 2 ^ labelBits
  pins : ∀ n, n < 2 * (pinCount * laneCount) → (ram (word (pinAddr n))).toNat < 2 ^ pinWidthAt (pinOf n)
  digits : ∀ n, n < recordCount * moduliCount →
    (ram (word (digitAddr n))).toNat < modulusAt (n % moduliCount)

/-! ### The product of the moduli -/

theorem suffixProduct_zero_eq : suffixProduct 0 = Entry.table.product := by
  unfold suffixProduct CrtTable.product
  decide +kernel

/-! ### RAM holds its extracted source -/

variable [FieldCertificate]

theorem fieldOf_extract (ram : Word → Word) (index : Nat) (inside : index < fieldCount) :
    fieldOf (extract ram) index = total 0 (readDraw ram).fields index := by
  have small : index < 276 := inside
  unfold fieldOf extract sourceOf
  by_cases h0 : index = 0
  · subst h0; rfl
  by_cases h1 : index = 1
  · subst h1; rfl
  by_cases h2 : index = 2
  · subst h2; rfl
  rw [if_neg h0, if_neg h1, if_neg h2, dif_pos (by omega)]
  obtain ⟨q, r, hr, split⟩ : ∃ q r, r < 3 ∧ index = 3 + 3 * q + r :=
    ⟨(index - 3) / 3, (index - 3) % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  subst split
  simp only [show 3 + 3 * q + r - 3 = 3 * q + r by omega, show (3 * q + r) / 3 = q by omega,
    show (3 * q + r) % 3 = r by omega]
  interval_cases r <;> rfl

theorem field_cell (ram : Word → Word) (valid : CellsValid ram) (index : Nat) (inside : index < fieldCount) :
    ram (word (fieldBase + index)) = fieldWord (fieldOf (extract ram) index) := by
  rw [fieldOf_extract ram index inside, total_apply _ _ _ inside]
  simp only [readDraw, fieldWord]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (valid.fields index inside)]
  exact (CrtSerial.word_toNat_self _).symm

theorem byte_cell (ram : Word → Word) (valid : CellsValid ram) (d : Fin 91) (b : Fin 2) :
    ram (word (exceptionBase + (2 * d.val + b.val))) = word ((extract ram).exception d)[b.val].toNat := by
  have inside : 2 * d.val + b.val < exceptionCellCount := by
    have := d.isLt; have := b.isLt; unfold exceptionCellCount; omega
  simp only [extract, sourceOf, Vector.getElem_ofFn, BitVec.toNat_ofNat]
  rw [total_apply _ _ _ inside]
  simp only [readDraw]
  rw [Nat.mod_eq_of_lt (valid.bytes _ inside)]
  exact (CrtSerial.word_toNat_self _).symm

theorem convHolds_extract (ram : Word → Word) (valid : CellsValid ram) (κ : Fin 2) :
    ConvHolds ram (extract ram) κ where
  joins index inside := by
    have kSmall := κ.isLt
    have n_in : κ.val * joinCount + index < 2 * joinCount := by
      have := joinCount_eq; rw [this] at inside ⊢; omega
    have addr : joinAddr (κ.val * joinCount + index) = Layout.sourceJoin κ index := by
      unfold joinAddr
      rw [joinCount_eq] at inside ⊢
      congr 1 <;> omega
    simp only [extract, sourceOf, word]
    rw [total_apply _ _ _ n_in, BitVec.toNat_ofNat]
    simp only [readDraw]
    rw [addr, Nat.mod_eq_of_lt (by have := valid.joins _ n_in; rwa [addr] at this)]
    exact (CrtSerial.word_toNat_self _).symm
  pins k inside lane small := by
    have active : laneCount = 104 := rfl
    have laneSmall : lane < 104 := small
    have kSmall := κ.isLt
    have pins200 : pinCount = 200 := CrtConv.pinCount_eq
    have n_in : (κ.val * pinCount + k) * laneCount + lane < 2 * (pinCount * laneCount) := by
      rw [pins200] at inside ⊢; simp only [laneCount, Narrow.labelBits] at *; omega
    have pinIs : pinOf ((κ.val * pinCount + k) * laneCount + lane) = k := by
      unfold pinOf; rw [pins200] at inside ⊢; simp only [laneCount, Narrow.labelBits] at *; omega
    have addr : pinAddr ((κ.val * pinCount + k) * laneCount + lane) = Layout.sourcePin κ k lane := by
      unfold pinAddr pinCoord
      rw [pinIs]
      rw [pins200] at inside ⊢
      simp only [laneCount, Narrow.labelBits] at *
      congr 1 <;> omega
    have bound := valid.pins _ n_in
    rw [pinIs, pinWidthAt_eq k inside, addr] at bound
    haveI : NeZero (2 ^ pinWidth ⟨k, inside⟩) := ⟨pow_ne_zero _ two_ne_zero⟩
    simp only [extract, sourceOf]
    rw [total_apply _ _ _ n_in, ZMod.val_natCast]
    simp only [readDraw]
    rw [addr, Nat.mod_eq_of_lt bound]
    exact (CrtSerial.word_toNat_self _).symm

theorem digit_cell (ram : Word → Word) (κ e i : Nat) (hκ : κ < 2) (he : e < encCount κ) (hi : i < moduliCount) :
    digitAddr ((if κ = 0 then e else Entry.xCount + e) * moduliCount + i) = Layout.residueCell κ i e := by
  have : moduliCount = 85 := rfl
  have : Entry.xCount = 367 := rfl
  unfold digitAddr recordCoord recordIndex
  unfold encCount at he
  interval_cases κ
  · simp only [if_true] at he ⊢
    congr 1 <;> simp only [*] at * <;> (try split_ifs) <;> omega
  · simp only [show (1 : Nat) ≠ 0 from by decide, if_false] at he ⊢
    congr 1 <;> simp only [*] at * <;> (try split_ifs) <;> omega

theorem digitsSmall_of_valid (ram : Word → Word) (valid : CellsValid ram) : CrtSerial.DigitsSmall ram := by
  intro κ e i hκ he hi
  have n_in : (if κ = 0 then e else Entry.xCount + e) * moduliCount + i < recordCount * moduliCount := by
    have := CrtSerial.encCount_le κ
    unfold encCount at he
    have : moduliCount = 85 := rfl
    have : recordCount = 642 := rfl
    have : Entry.xCount = 367 := rfl
    have : Entry.yCount = 275 := rfl
    split_ifs at he ⊢ <;> simp only [*] at * <;> nlinarith
  have bound := valid.digits _ n_in
  rw [digit_cell ram κ e i hκ he hi, show ((if κ = 0 then e else Entry.xCount + e) * moduliCount + i) %
    moduliCount = i by have : moduliCount = 85 := rfl; rw [this] at hi ⊢; omega] at bound
  exact bound

theorem recordNat_eq (ram : Word → Word) (κ e : Nat) (hκ : κ < 2) (he : e < encCount κ) :
    recordNat (readDraw ram) (if κ = 0 then e else Entry.xCount + e) = recordValue ram κ e := by
  unfold recordNat recordValue
  refine Finset.sum_congr rfl fun i member => ?_
  have hi := Finset.mem_range.mp member
  have n_in : (if κ = 0 then e else Entry.xCount + e) * moduliCount + i < recordCount * moduliCount := by
    unfold encCount at he
    have : moduliCount = 85 := rfl
    have : recordCount = 642 := rfl
    have : Entry.xCount = 367 := rfl
    have : Entry.yCount = 275 := rfl
    split_ifs at he ⊢ <;> simp only [*] at * <;> nlinarith
  rw [total_apply _ _ _ n_in]
  simp only [readDraw]
  rw [digit_cell ram κ e i hκ he hi]

theorem recordValue_lt (ram : Word → Word) (valid : CellsValid ram) (κ e : Nat) (hκ : κ < 2)
    (he : e < encCount κ) : recordValue ram κ e < Entry.table.product := by
  have digits := digitsSmall_of_valid ram valid
  rw [← suffixProduct_zero_eq]
  have value : recordValue ram κ e =
      hornerSuffix (fun i => (ram (word (Layout.residueCell κ i e))).toNat) 0 := by
    rw [hornerSuffix_zero]; rfl
  rw [value]
  exact hornerSuffix_lt _ (fun i hi => digits κ e i hκ he hi) moduliCount 0 (by rfl)

/-- **RAM holds its extracted source**, cell by cell, when every cell is in range. -/
theorem sourceHolds_extract (ram : Word → Word) (valid : CellsValid ram) : SourceHolds ram (extract ram) where
  fields index inside := field_cell ram valid index inside
  bytes d b := byte_cell ram valid d b
  conv κ := convHolds_extract ram valid κ
  records κ e hκ he := by
    have small := recordValue_lt ram valid κ e hκ he
    have natIs := recordNat_eq ram κ e hκ he
    unfold recordOf extract sourceOf
    interval_cases κ
    · rw [if_pos rfl, dif_pos (show e < Entry.xCount from he)]
      simp only [↓reduceIte] at natIs
      show _ = recordNat (readDraw ram) e % Entry.table.product
      rw [natIs, Nat.mod_eq_of_lt small]
    · rw [if_neg (by decide), dif_pos (show e < Entry.yCount from he)]
      simp only [show (1 : Nat) ≠ 0 from by decide, ↓reduceIte] at natIs
      show _ = recordNat (readDraw ram) (Entry.xCount + e) % Entry.table.product
      rw [natIs, Nat.mod_eq_of_lt small]

end

end CrtSource

end Kriterion.CRT.SimMachine
