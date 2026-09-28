/-
The evaluator's reads of a published source (for the machine's M5b chain):
for a stage-1 source `s` and `pub := publish s`, what the replay reads from `pub` is `s`, field by field.

(i) joins: the conversion material the evaluator reads, `convOf pub.crtX` (and `crtY`), agrees with
    `s.conv κ` on every read cell (`convAgree_publishX/Y`); at the read indices this is `0` for the chunk
    joins (no chunk joins: `chunkJoin_publish`; the source's chunk-join cells are never read) and the
    source's joins at the flat source indices otherwise (`stageJoin_publish`, `growJoin_publish`,
    `foldJoin_publish`);
(ii) pins: the lanes `pinOfBlocks` decodes from the published blocks are the source's pin lanes
     (`chunkPin_lanes`, `stagePin_lanes`);
(iii) records: the published record is the source's natural below `M` (`recX_val`, `recY_val`), its hint is 0
      (`hintX_publish`, `hintY_publish`), and `recordJoin` reads its mixed-radix digits
      (`recordJoinX_publish`, `recordJoinY_publish`, the digits of `mixedRadixEquiv.symm`).

Stated for the real table (`Entry.table`) and for both coordinates (`κ = 0` for `x`, `1` for `y`).
-/

import Proof.Correctness.CRT.EntryDelivery
import Construction.CRT.Layout

namespace Kriterion.CRT.SourceReads

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
open Kriterion.CRT Kriterion.CRT.Entry Kriterion.CRT.FlatLayout Kriterion.CRT.EntryDelivery

variable (s : Source)

/-! ### (i) Joins -/

/-- The source's conversion material has no chunk joins. -/
theorem conv_chunkJoin (κ : Fin 2) (c n : Nat) : (s.conv κ).chunkJoin c n = 0 := rfl

theorem convAgree_publishX : ConvAgree table (convOf (publish s).crtX) (s.conv 0) :=
  (convAgree_convOf (s.conv 0)).of_dropChunkJoins (conv_chunkJoin s 0)

theorem convAgree_publishY : ConvAgree table (convOf (publish s).crtY) (s.conv 1) :=
  (convAgree_convOf (s.conv 1)).of_dropChunkJoins (conv_chunkJoin s 1)

/-- The published conversion material of coordinate `κ`. -/
def convPub (κ : Fin 2) : ConvPublic :=
  if κ = 0 then convOf (publish s).crtX else convOf (publish s).crtY

theorem convAgree_publish (κ : Fin 2) : ConvAgree table (convPub s κ) (s.conv κ) := by
  unfold convPub
  split
  · rename_i h
    subst h
    exact convAgree_publishX s
  · rename_i h
    have one : κ = 1 := by omega
    subst one
    exact convAgree_publishY s

/-- No chunk joins: the evaluator reads every chunk join as `0`. -/
theorem chunkJoin_publish (κ : Fin 2) (c n : Nat) :
    (convPub s κ).chunkJoin c n = 0 := by
  unfold convPub
  split <;> rfl

theorem stageJoin0_publish (κ : Fin 2) (i : Fin table.count) (row : OddRow) (kind : table.kind i = .odd row)
    (n : Nat) (lower : 1 ≤ n) (upper : n < row.width0) :
    (convPub s κ).stageJoin i 0 n = s.joinAt κ (modJoinBase i + (n - 1)) :=
  ((convAgree_publish s κ).2.2 i row kind).1 n lower upper

theorem stageJoin1_publish (κ : Fin 2) (i : Fin table.count) (row : OddRow) (kind : table.kind i = .odd row)
    (n : Nat) (lower : 1 ≤ n) (upper : n < row.width1) :
    (convPub s κ).stageJoin i 1 n = s.joinAt κ (modJoinBase i + ((rowAt i).width0 - 1) + (n - 1)) :=
  ((convAgree_publish s κ).2.2 i row kind).2.1 n lower upper

theorem growJoin_publish (κ : Fin 2) (i : Fin table.count) (row : OddRow) (kind : table.kind i = .odd row)
    (j : Nat) (lower : row.width0 ≤ j) (upper : j < row.keep) :
    (convPub s κ).growJoin i j = s.joinAt κ (modJoinBase i + ((rowAt i).width0 - 1) + ((rowAt i).width1 - 1)
      + (j - (rowAt i).width0)) :=
  ((convAgree_publish s κ).2.2 i row kind).2.2.2.2.1 j lower upper

theorem foldJoin_publish (κ : Fin 2) (i : Fin table.count) (row : OddRow) (kind : table.kind i = .odd row)
    (j : Nat) (lower : row.keep ≤ j) (upper : j < row.ell) :
    (convPub s κ).foldJoin i j = s.joinAt κ (modJoinBase i + ((rowAt i).width0 - 1) + ((rowAt i).width1 - 1)
      + ((rowAt i).keep - (rowAt i).width0) + (j - (rowAt i).keep)) :=
  ((convAgree_publish s κ).2.2 i row kind).2.2.2.2.2 j lower upper

theorem rowAt_eq (i : Fin table.count) (row : OddRow) (kind : table.kind i = .odd row) : rowAt i = row := by
  unfold rowAt CrtTable.kindAt
  simp [i.isLt, kind]

/-! ### (ii) Pins -/

theorem atNat_pinBlocks {w : Nat} (P : Lanes w) : (fun k : Fin w => atNat (pinBlocks P) 0 k.val) = pinBlocks P := by
  funext k
  simp [atNat, k.isLt]

/-- A pin read back at another name of its width. -/
theorem pin_readback (w L : Nat) (P : Lanes w) (same : w = L) (positive : 0 < L) (lane : Fin laneCount) :
    ((pinOfBlocks L fun k => atNat (pinBlocks P) 0 k.val) lane).val = (P lane).val := by
  subst same
  rw [atNat_pinBlocks, SliceC.pinOfBlocks_pinBlocks positive]

theorem pinWidth_chunk (c : Nat) (hc : c < table.chunkCount) (hk : c < pinCount) :
    pinWidth ⟨c, hk⟩ = table.castWidth - 1 := by
  have h : c < pinWidths.length := hk
  show pinWidths[c]'h = table.castWidth - 1
  have key : ∀ (l : List Nat), l = List.replicate table.chunkCount (table.castWidth - 1) ++
      (List.finRange table.count).flatMap (fun i => modPinWidths (table.kind i)) →
      ∀ (h : c < l.length), l[c]'h = table.castWidth - 1 := by
    intro l hl h
    subst hl
    rw [List.getElem_append_left (by simpa using hc)]
    simp
  exact key pinWidths rfl h

theorem chunkPin_lanes (κ : Fin 2) (c : Nat) (hc : c < table.chunkCount) (hk : c < pinCount)
    (lane : Fin laneCount) :
    ((pinOfBlocks (table.castWidth - 1) fun k => (convPub s κ).chunkPin c k.val) lane).val =
      ((s.pins κ ⟨c, hk⟩) lane).val := by
  have reads : (fun k : Fin (table.castWidth - 1) => (convPub s κ).chunkPin c k.val) =
      fun k => atNat (pinBlocks (s.pins κ ⟨c, hk⟩)) 0 k.val := by
    funext k
    rw [(convAgree_publish s κ).2.1 c hc k.val k.isLt]
    simp only [Source.conv, Source.pinBlockAt, dif_pos hk]
  rw [reads]
  exact pin_readback _ _ _ (pinWidth_chunk c hc hk) (by decide) lane

/-- A stage pin read back, given the width of its pin index (`ell - 1` for stage 0, `ell - width0 - 1` for stage 1). -/
theorem stagePin_lanes (κ : Fin 2) (i : Fin table.count) (row : OddRow) (kind : table.kind i = .odd row)
    (stage : Nat) (width : Nat) (widthEq : width = if stage = 0 then row.ell - 1 else row.ell - row.width0 - 1)
    (hk : modPinBase i + stage < pinCount) (sameWidth : pinWidth ⟨modPinBase i + stage, hk⟩ = width)
    (positive : 0 < width) (stageLe : stage ≤ 1) (lane : Fin laneCount) :
    ((pinOfBlocks width fun k => (convPub s κ).stagePin i stage k.val) lane).val =
      ((s.pins κ ⟨modPinBase i + stage, hk⟩) lane).val := by
  have agree := (convAgree_publish s κ).2.2 i row kind
  have reads : (fun k : Fin width => (convPub s κ).stagePin i stage k.val) =
      fun k => atNat (pinBlocks (s.pins κ ⟨modPinBase i + stage, hk⟩)) 0 k.val := by
    funext k
    obtain ⟨kv, kLt⟩ := k
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp stageLe with zero | one
    · subst zero
      have kLt' : kv < row.ell - 1 := by
        have h := kLt
        rw [widthEq, if_pos rfl] at h
        exact h
      rw [agree.2.2.1 kv kLt']
      simp only [Source.conv, Source.pinBlockAt, dif_pos hk]
    · subst one
      have kLt' : kv < row.ell - row.width0 - 1 := by
        have h := kLt
        rw [widthEq, if_neg (by decide)] at h
        exact h
      rw [agree.2.2.2.1 kv kLt']
      simp only [Source.conv, Source.pinBlockAt, dif_pos hk]
  rw [reads]
  exact pin_readback _ _ _ sameWidth positive lane

/-! ### (iii) Records -/

theorem product_small : table.product < 2 ^ recordBits := by
  have fits : 2 * table.product ≤ 2 ^ 618 := bn254Table_record_fits_bits
  have pos := table_product_pos
  show table.product < 2 ^ 618
  omega

theorem recX_val (e : Fin xCount) : ((publish s).recX.get e).val = (s.recX e).val := by
  simp only [publish, vector_get_ofFn]
  exact toRecord_val _ (lt_trans (s.recX e).isLt product_small)

theorem recY_val (e : Fin yCount) : ((publish s).recY.get e).val = (s.recY e).val := by
  simp only [publish, vector_get_ofFn]
  exact toRecord_val _ (lt_trans (s.recY e).isLt product_small)

/-- The published hint is 0. -/
theorem hintX_publish (e : Fin xCount) : decide (table.product ≤ ((publish s).recX.get e).val) = false := by
  rw [recX_val]
  simp [(s.recX e).isLt]

theorem hintY_publish (e : Fin yCount) : decide (table.product ≤ ((publish s).recY.get e).val) = false := by
  rw [recY_val]
  simp [(s.recY e).isLt]

/-- `recordJoin` reads the source record's mixed-radix digits. -/
theorem recordJoinX_publish (e : Fin xCount) (i : Fin table.count) :
    recordJoin table table.product (stored table.radix) ((publish s).recX.get e).val i =
      ((table.mixedRadixEquiv.symm (s.recX e)) i).val := by
  rw [recX_val, CrtTable.mixedRadixEquiv_symm_val]
  simp only [recordJoin, stored_eq, Nat.mod_eq_of_lt (s.recX e).isLt]

theorem recordJoinY_publish (e : Fin yCount) (i : Fin table.count) :
    recordJoin table table.product (stored table.radix) ((publish s).recY.get e).val i =
      ((table.mixedRadixEquiv.symm (s.recY e)) i).val := by
  rw [recY_val, CrtTable.mixedRadixEquiv_symm_val]
  simp only [recordJoin, stored_eq, Nat.mod_eq_of_lt (s.recY e).isLt]

/-! ### The pin widths of the stage pins -/

/-- The modulus pin lists indexed by naturals (empty off range). -/
def modPinsNat (i : Nat) : List Nat :=
  if h : i < table.count then modPinWidths (table.kind ⟨i, h⟩) else []

theorem modPinsNat_length (i : Nat) :
    (modPinsNat i).length = (match table.kindAt i with
      | some kind => (modPinWidths kind).length
      | none => 0) := by
  unfold modPinsNat CrtTable.kindAt
  split <;> rfl

theorem pinWidths_eq : pinWidths = List.replicate table.chunkCount (table.castWidth - 1) ++
    (List.range table.count).flatMap modPinsNat := by
  unfold pinWidths
  rw [flatMap_finRange_eq]
  rfl

theorem modPinBase_eq (i : Nat) :
    modPinBase i = table.chunkCount + ∑ i' ∈ Finset.range i, (modPinsNat i').length := by
  unfold modPinBase
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i' => (modPinsNat i').length) i]
  exact Finset.sum_congr rfl fun i' _ => (modPinsNat_length i'.val).symm

/-- **The stored width of stage `q`'s half-pin of an odd modulus**: `ell - 1` for stage 0, `ell - width0 - 1` for
stage 1. -/
theorem pinWidth_stage (i : Fin table.count) (row : OddRow) (kind : table.kind i = .odd row) (stage : Nat)
    (stageLe : stage ≤ 1) :
    ∃ hk : modPinBase i + stage < pinCount,
      pinWidth ⟨modPinBase i + stage, hk⟩ = if stage = 0 then row.ell - 1 else row.ell - row.width0 - 1 := by
  have section_ : modPinsNat i.val = [row.ell - 1, row.ell - row.width0 - 1] := by
    simp [modPinsNat, i.isLt, kind, modPinWidths]
  have lengths : ∀ c, (modPinsNat c).length = (modPinsNat c).length := fun _ => rfl
  have total : pinCount = table.chunkCount + ∑ c ∈ Finset.range table.count, (modPinsNat c).length := by
    unfold pinCount
    rw [pinWidths_eq, List.length_append, List.length_replicate,
      length_flatMap_range _ _ lengths table.count]
  have split := Finset.sum_range_add_sum_Ico (fun c => (modPinsNat c).length) (Nat.le_of_lt i.isLt)
  have more : (modPinsNat i.val).length ≤ ∑ c ∈ Finset.Ico i.val table.count, (modPinsNat c).length :=
    Finset.single_le_sum (f := fun c => (modPinsNat c).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_Ico.mpr ⟨le_refl _, i.isLt⟩)
  rw [section_] at more
  simp only [List.length_cons, List.length_nil] at more
  have hk : modPinBase i + stage < pinCount := by
    rw [total, modPinBase_eq]
    omega
  refine ⟨hk, ?_⟩
  have read : pinWidths.getD (modPinBase i + stage) 0 = (modPinsNat i.val).getD stage 0 := by
    rw [pinWidths_eq, modPinBase_eq, Nat.add_assoc]
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.add_sub_cancel_left]
    exact getD_flatMap_range _ _ lengths 0 _ i.val stage i.isLt (by rw [section_]; simp; omega)
  have asGet : pinWidth ⟨modPinBase i + stage, hk⟩ = pinWidths.getD (modPinBase i + stage) 0 := by
    unfold pinWidth
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  rw [asGet, read, section_]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp stageLe with zero | one
  · subst zero
    simp
  · subst one
    simp

end Kriterion.CRT.SourceReads
