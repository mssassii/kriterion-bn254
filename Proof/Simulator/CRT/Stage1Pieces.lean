/-
**The serializer's pieces are the wire** (M2).

`SourceHolds ram source`: RAM holds the source's field cells, sign bits, exception nibbles, joins, pins and records (as
their mixed-radix digits). `pieces_bits`: then the bits of `CrtStage1.pieces`, piece by piece, are exactly the byte bits of
`Wire.encoding.encode (publish source)`.
-/

import Proof.Simulator.CRT.Stage1Conv

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.CRT.Entry (Source convCount xCount yCount)
open CrtStage1 CrtConv

namespace CrtPieces

/-! ### The source's cells -/

/-- Field cell `index` of a source: the curve constants, then the row constants `3 + 3 d + slot`. -/
def fieldOf (source : Source) (index : Nat) : BaseField :=
  if index = 0 then source.curve.1
  else if index = 1 then source.curve.2.1
  else if index = 2 then source.curve.2.2
  else if inside : index - 3 < 273 then
    CrtWire.rowField (source.rows ⟨(index - 3) / 3, by unfold digitCount; omega⟩) ((index - 3) % 3)
  else 0

/-- The record of encoding `e` of coordinate `κ`, as a natural. -/
def recordOf (source : Source) (κ e : Nat) : Nat :=
  if κ = 0 then (if inside : e < xCount then (source.recX ⟨e, inside⟩).val else 0)
  else (if inside : e < yCount then (source.recY ⟨e, inside⟩).val else 0)

/-- **RAM holds the source** (the cells the serializer reads). -/
structure SourceHolds (ram : Word → Word) (source : Source) : Prop where
  fields : ∀ index, index < fieldCount → ram (word (fieldBase + index)) = fieldWord (fieldOf source index)
  signs : ∀ d : Fin 91, ram (word (Layout.signCell d.val)) = word (source.signs d).toNat
  bytes : ∀ (d : Fin 91) (b : Fin 2),
    ram (word (exceptionBase + (2 * d.val + b.val))) = word (source.exception d)[b.val].toNat
  conv : ∀ κ, ConvHolds ram source κ
  records : ∀ κ e, κ < 2 → e < encCount κ → recordValue ram κ e = recordOf source κ e

/-! ### The segments -/

theorem curve_bits (ram : Word → Word) (source : Source) (holds : SourceHolds ram source) :
    pieceListBits ram ((List.range curveCellCount).map fun index => Piece.word (fieldBase + index) 256) =
      lsbs 256 source.curve.1.val ++ lsbs 256 source.curve.2.1.val ++ lsbs 256 source.curve.2.2.val := by
  unfold pieceListBits
  rw [List.map_map, map_range_eq_ofFn]
  have cell : ∀ index : Fin curveCellCount,
      (pieceBits ram ∘ fun index => Piece.word (fieldBase + index) 256) index.val =
        lsbs 256 (fieldOf source index.val).val := by
    intro index
    have small : index.val < 3 := index.isLt
    simp only [Function.comp_apply, pieceBits]
    rw [holds.fields index.val (by unfold fieldCount curveCellCount rowCellCount; omega), fieldWord,
      bitRun_ofNat _ _ le_rfl]
  simp only [cell]
  simp only [curveCellCount, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
    Fin.val_zero, Fin.val_succ, fieldOf, List.append_assoc]
  rfl

/-- The flags byte of a published source row is its sign bit. -/
theorem flagsOf_publish (source : Source) (d : Fin digitCount) :
    CrtWire.flagsOf (Entry.publish source).rows[d.val] = (source.signs d).toNat := by
  simp only [Entry.publish, Vector.getElem_ofFn, Entry.Source.normRow, CrtWire.flagsOf, NormRow.flagByte]
  cases source.signs d <;> rfl

theorem rows_bits (ram : Word → Word) (source : Source) (holds : SourceHolds ram source) :
    pieceListBits ram rowPieces =
      (List.ofFn fun digit : Fin digitCount =>
          lsbs 256 (Entry.publish source).rows[digit.val].xC0.val ++
            lsbs 8 (CrtWire.flagsOf (Entry.publish source).rows[digit.val])).flatten := by
  unfold pieceListBits rowPieces
  rw [List.map_flatten, List.flatten_flatten, List.map_map, map_range_eq_ofFn, List.map_ofFn]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun digit => ?_))
  have digitSmall : digit.val < 91 := digit.isLt
  simp only [Function.comp_apply, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, pieceBits]
  rw [holds.fields (3 + 3 * digit.val) (by unfold fieldCount curveCellCount rowCellCount; omega), fieldWord,
    bitRun_ofNat _ _ le_rfl, holds.signs digit, bitRun_ofNat _ _ (by norm_num)]
  refine congrArg₂ (· ++ ·) (congrArg (lsbs 256) ?_) (congrArg (lsbs 8) (flagsOf_publish source digit).symm)
  congr 1
  unfold fieldOf
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  simp only [Entry.publish, Vector.getElem_ofFn, Entry.Source.normRow]
  rw [show 3 + 3 * digit.val - 3 = 3 * digit.val by omega, show 3 * digit.val / 3 = digit.val by omega,
    show 3 * digit.val % 3 = 0 by omega]
  rfl

theorem bytes_bits (ram : Word → Word) (source : Source) (holds : SourceHolds ram source) :
    pieceListBits ram ((List.range exceptionCellCount).map fun index => Piece.word (exceptionBase + index) 4) =
      (List.ofFn fun digit : Fin digitCount =>
          (List.ofFn fun index : Fin 2 =>
            lsbs 4 (Entry.publish source).exception[digit.val][index.val].toNat).flatten).flatten := by
  unfold pieceListBits
  rw [List.map_map, map_range_eq_ofFn, show exceptionCellCount = digitCount * 2 from rfl, flatten_ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun digit => ?_))
  refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
  simp only [Function.comp_apply, pieceBits, Fin.val_mk]
  rw [show digit.val * 2 + index.val = 2 * digit.val + index.val by ring, holds.bytes digit index,
    bitRun_ofNat _ _ (by norm_num)]
  simp only [Entry.publish, Vector.getElem_ofFn]

theorem convVector_bits (pub : ConvPublic) :
    (List.ofFn fun k : Fin convCount => lsbs labelBits (Entry.convVector pub)[k.val].toNat).flatten =
      blockBits (ConvPublic.flatten Entry.table pub) := by
  unfold blockBits
  refine congrArg List.flatten ?_
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_map, flatten_length]
  · intro n first second
    rw [List.length_ofFn] at first
    simp only [List.getElem_ofFn, List.getElem_map, Entry.convVector, Vector.getElem_ofFn]
    congr 2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [List.size_toArray, flatten_length]; exact first),
      Option.getD_some, List.getElem_toArray]

theorem records_bits (ram : Word → Word) (source : Source) (holds : SourceHolds ram source) (κ : Nat)
    (small : κ < 2) (values : Fin (encCount κ) → Nat)
    (same : ∀ e : Fin (encCount κ), lsbs 624 (recordOf source κ e) = lsbs 624 (values e)) :
    pieceListBits ram (recordPieces κ) = (List.ofFn fun e => lsbs 624 (values e)).flatten := by
  unfold pieceListBits recordPieces
  rw [List.map_map, map_range_eq_ofFn]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun e => ?_))
  simp only [Function.comp_apply, pieceBits]
  rw [holds.records κ e small e.isLt, same e]

theorem record_mod (value : Nat) : lsbs 624 (value % 256 ^ 78) = lsbs 624 value := by
  rw [show (256 : Nat) ^ 78 = 2 ^ 624 by rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul], lsbs_mod]

/-- **The pieces are the wire.** -/
theorem pieces_bits (ram : Word → Word) (source : Source) (holds : SourceHolds ram source) :
    pieceListBits ram pieces = byteBits (Entry.Wire.encoding.encode (Entry.publish source)) := by
  rw [CrtWire.wire_bits]
  unfold pieces
  simp only [pieceListBits_append]
  rw [curve_bits ram source holds, rows_bits ram source holds, bytes_bits ram source holds]
  have conv0 := conv_bits ram source 0 (holds.conv 0)
  have conv1 := conv_bits ram source 1 (holds.conv 1)
  rw [show ((0 : Fin 2) : Nat) = 0 from rfl] at conv0
  rw [show ((1 : Fin 2) : Nat) = 1 from rfl] at conv1
  rw [← conv0, ← conv1, ← convVector_bits, ← convVector_bits]
  rw [records_bits ram source holds 0 (by decide) (fun e => (Entry.publish source).recX[e.val].val)
      (fun e => by
        unfold recordOf
        rw [if_pos rfl, dif_pos (show e.val < xCount from e.isLt)]
        simp only [Entry.publish, Vector.getElem_ofFn, Entry.toRecord]
        rw [record_mod]),
    records_bits ram source holds 1 (by decide) (fun e => (Entry.publish source).recY[e.val].val)
      (fun e => by
        unfold recordOf
        rw [if_neg (show (1 : Nat) ≠ 0 by decide), dif_pos (show e.val < yCount from e.isLt)]
        simp only [Entry.publish, Vector.getElem_ofFn, Entry.toRecord]
        rw [record_mod])]
  simp only [Entry.publish, List.append_assoc]
  rfl

end CrtPieces

end Kriterion.CRT.SimMachine
