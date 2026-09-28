/-
**The conversion vectors on the wire, piece by piece** (M2).

`conv_bits`: when RAM holds a source's joins (one block per word) and pins (one lane per word), the machine's
conversion pieces of coordinate `κ` emit exactly the bits of `ConvPublic.flatten table (source.conv κ)`, block by
block. A pin's `101` lanes of `w` bits are its `w` blocks (`pinNat`, least significant lane first).

The table facts (every join and pin index in range, every pin's width) are checked on the concrete table by
`decide +kernel` (`chunkFacts`, `modFacts_all`); `flatten_length` is `2885` for every `ConvPublic` (no chunk
joins: a chunk contributes its half-pin only; the source's chunk-join cells are drawn but not serialized).
-/

import Proof.Simulator.CRT.Stage1Wire
import Proof.Simulator.ReplayBase
import Construction.Simulator.CRT.Stage1

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.CRT.Entry (Source joinCount pinCount pinWidth pinWidths chunkJoinBase modJoinBase modPinBase
  rowAt convCount)
open CrtStage1

namespace CrtConv

/-! ### Facts of the concrete table -/

theorem chunkCount_eq : Entry.table.chunkCount = 32 := by decide

theorem castWidth_eq : Entry.table.castWidth = 14 := rfl

/-- Every chunk's joins and pin are in range, and a chunk's stored half-pin has one lane bit less than the cast
width. -/
theorem chunkFacts : ∀ c : Fin 32, chunkJoinBase c + (Entry.table.chunkWidth c - 1) ≤ joinCount ∧
    c.val < pinCount ∧ pinWidthAt c = Entry.table.castWidth - 1 := by
  decide +kernel

/-- The facts of one modulus. -/
def modFacts (i : Fin Entry.table.count) : Bool :=
  match Entry.table.kind i with
  | .chunkZero => true
  | .odd row =>
    decide (modJoinBase i + (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0) + (row.ell - row.keep)
      ≤ joinCount) &&
    decide (modPinBase i + 1 < pinCount) && decide (pinWidthAt (modPinBase i) = row.ell - 1) &&
    decide (pinWidthAt (modPinBase i + 1) = row.ell - row.width0 - 1)

set_option maxRecDepth 100000 in
theorem modFacts_all : ∀ i, modFacts i = true := by decide +kernel

theorem modFacts_of (i : Fin Entry.table.count) (row : OddRow) (odd : Entry.table.kind i = .odd row) :
    modJoinBase i + (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0) + (row.ell - row.keep)
        ≤ joinCount ∧
      modPinBase i + 1 < pinCount ∧ pinWidthAt (modPinBase i) = row.ell - 1 ∧
      pinWidthAt (modPinBase i + 1) = row.ell - row.width0 - 1 := by
  have facts := modFacts_all i
  simp only [modFacts, odd, Bool.and_eq_true, decide_eq_true_eq] at facts
  exact ⟨facts.1.1.1, facts.1.1.2, facts.1.2, facts.2⟩

theorem rowAt_of (i : Fin Entry.table.count) (row : OddRow) (odd : Entry.table.kind i = .odd row) :
    rowAt i = row := by
  simp only [rowAt, CrtTable.kindAt, dif_pos i.isLt, odd]

theorem flatten_length_indep (T : CrtTable) (p q : ConvPublic) :
    (ConvPublic.flatten T p).length = (ConvPublic.flatten T q).length := by
  unfold ConvPublic.flatten
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_range]
  congr 2
  apply List.map_congr_left
  intro a _
  split <;> simp

/-- A conversion material with every block zero. -/
def zeroConv : ConvPublic := ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

theorem flatten_length (pub : ConvPublic) : (ConvPublic.flatten Entry.table pub).length = convCount := by
  rw [flatten_length_indep Entry.table pub zeroConv]
  decide +kernel

theorem pinWidthAt_eq (k : Nat) (inside : k < pinCount) : pinWidthAt k = pinWidth ⟨k, inside⟩ := by
  unfold pinWidthAt pinWidth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
  rfl

/-! ### Bits -/

/-- The bits of a list of blocks. -/
def blockBits (blocks : List Label) : List Bool := (blocks.map fun block => lsbs labelBits block.toNat).flatten

/-- The mixed radix of modulus `i`. -/
def radixAt (i : Nat) : Nat := ∏ j ∈ Finset.range i, modulusAt j

/-- The record of encoding `e` of coordinate `κ`: the mixed-radix integer of its digits in RAM. -/
def recordValue (ram : Word → Word) (κ e : Nat) : Nat :=
  ∑ i ∈ Finset.range moduliCount, (ram (word (Layout.residueCell κ i e))).toNat * radixAt i

/-- The bits one piece puts on the wire. -/
def pieceBits (ram : Word → Word) : Piece → List Bool
  | .word address width => bitRun (ram (word address)) 0 width
  | .record κ e => lsbs 624 (recordValue ram κ e)
  | .zeros width => bitRun (word 0) 0 width

/-- The bits of a list of pieces. -/
def pieceListBits (ram : Word → Word) (pieces : List Piece) : List Bool := (pieces.map (pieceBits ram)).flatten

theorem blockBits_append (first second : List Label) :
    blockBits (first ++ second) = blockBits first ++ blockBits second := by
  simp [blockBits]

theorem pieceListBits_append (ram : Word → Word) (first second : List Piece) :
    pieceListBits ram (first ++ second) = pieceListBits ram first ++ pieceListBits ram second := by
  simp [pieceListBits]

theorem blockBits_flatMap {α : Type} (list : List α) (f : α → List Label) :
    blockBits (list.flatMap f) = (list.map fun a => blockBits (f a)).flatten := by
  induction list with
  | nil => rfl
  | cons head tail ih => rw [List.flatMap_cons, blockBits_append, ih]; rfl

theorem pieceListBits_flatMap {α : Type} (ram : Word → Word) (list : List α) (f : α → List Piece) :
    pieceListBits ram (list.flatMap f) = (list.map fun a => pieceListBits ram (f a)).flatten := by
  induction list with
  | nil => rfl
  | cons head tail ih => rw [List.flatMap_cons, pieceListBits_append, ih]; rfl

theorem map_range_eq_ofFn {α : Type} (count : Nat) (g : Nat → α) :
    (List.range count).map g = List.ofFn fun index : Fin count => g index.val := by
  apply List.ext_getElem <;> simp

/-- `w` consecutive 101-bit windows of a natural are its low `101 w` bits. -/
theorem range_windows (value : Nat) : ∀ count : Nat,
    ((List.range count).map fun b => lsbs labelBits (value / 2 ^ (labelBits * b))).flatten = lsbs (labelBits * count) value
  | 0 => rfl
  | count + 1 => by
      rw [List.range_succ, List.map_append, List.flatten_append, range_windows value count,
        show labelBits * (count + 1) = labelBits * count + labelBits by ring, lsbs_add]
      simp

/-! ### The source in RAM -/

/-- **Coordinate `κ`'s joins and pins in RAM.** -/
structure ConvHolds (ram : Word → Word) (source : Source) (κ : Fin 2) : Prop where
  joins : ∀ index (inside : index < joinCount),
    ram (word (Layout.sourceJoin κ index)) = word (source.joins κ ⟨index, inside⟩).toNat
  pins : ∀ k (inside : k < pinCount) lane (small : lane < labelBits),
    ram (word (Layout.sourcePin κ k lane)) = word (source.pins κ ⟨k, inside⟩ ⟨lane, small⟩).val

theorem joins_bits (ram : Word → Word) (source : Source) (κ : Fin 2) (holds : ConvHolds ram source κ)
    (start count : Nat) (inRange : start + count ≤ joinCount) (f : Nat → Label)
    (same : ∀ n, n < count → f n = source.joinAt κ (start + n)) :
    blockBits ((List.range count).map f) = pieceListBits ram (joinPieces κ start count) := by
  unfold blockBits pieceListBits joinPieces
  rw [List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro n member
  have small : n < count := List.mem_range.mp member
  simp only [Function.comp_apply, pieceBits]
  rw [holds.joins (start + n) (by omega), same n small, Source.joinAt, atNat, dif_pos (by omega), word,
    bitRun_ofNat _ _ (by norm_num)]

theorem pinWidth_small : ∀ k : Fin 198, pinWidthAt k ≤ 14 := by decide +kernel

theorem pinCount_eq : pinCount = 198 := by decide +kernel

theorem pin_bits (ram : Word → Word) (source : Source) (κ : Fin 2) (holds : ConvHolds ram source κ)
    (k : Nat) (inside : k < pinCount) (f : Nat → Label)
    (same : ∀ b, b < pinWidthAt k → f b = source.pinBlockAt κ k b) :
    blockBits ((List.range (pinWidthAt k)).map f) = pieceListBits ram (pinPieces κ k) := by
  set lanes := source.pins κ ⟨k, inside⟩ with lanesDef
  haveI : NeZero (2 ^ pinWidth ⟨k, inside⟩) := ⟨pow_ne_zero _ two_ne_zero⟩
  have widthIs := pinWidthAt_eq k inside
  have widthSmall : pinWidthAt k ≤ 256 :=
    le_trans (pinWidth_small ⟨k, by rw [← pinCount_eq]; exact inside⟩) (by norm_num)
  have left : blockBits ((List.range (pinWidthAt k)).map f) = lsbs (labelBits * pinWidthAt k) (pinNat lanes) := by
    rw [← range_windows]
    unfold blockBits
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro b member
    have small : b < pinWidthAt k := List.mem_range.mp member
    simp only [Function.comp_apply]
    rw [same b small, Source.pinBlockAt, dif_pos inside, atNat, dif_pos (by rw [← widthIs]; exact small)]
    simp only [pinBlocks, Narrow.pinBlocks, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    exact lsbs_mod labelBits _
  have right : pieceListBits ram (pinPieces κ k) =
      (List.ofFn fun lane : Fin labelBits => lsbs (pinWidthAt k) (lanes lane).val).flatten := by
    unfold pieceListBits pinPieces
    rw [List.map_map, map_range_eq_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun lane => ?_)
    simp only [Function.comp_apply, pieceBits]
    rw [holds.pins k inside lane lane.isLt, bitRun_ofNat _ _ widthSmall]
  rw [left, right, widthIs, Nat.mul_comm, ← digitSum_bits (pinWidth ⟨k, inside⟩) labelBits _
    (fun lane => (lanes lane).val_lt)]
  rfl

/-- **The conversion vector of coordinate `κ` on the wire**: the machine's pieces emit exactly the bits of
`ConvPublic.flatten table (source.conv κ)`. -/
theorem conv_bits (ram : Word → Word) (source : Source) (κ : Fin 2) (holds : ConvHolds ram source κ) :
    blockBits (ConvPublic.flatten Entry.table (source.conv κ)) = pieceListBits ram (convPieces κ.val) := by
  unfold ConvPublic.flatten convPieces
  rw [blockBits_append, pieceListBits_append, blockBits_flatMap, blockBits_flatMap, pieceListBits_flatMap,
    pieceListBits_flatMap]
  -- `congr 1` here would try `rfl` on the chunk halves and unfold the table (maximum recursion)
  refine congrArg₂ HAppend.hAppend (congrArg List.flatten (List.map_congr_left fun c member => ?_))
    (congrArg List.flatten (List.map_congr_left fun i _ => ?_))
  · have small : c < 32 := by rw [← chunkCount_eq]; exact List.mem_range.mp member
    obtain ⟨_, pinIn, pinWidthIs⟩ := chunkFacts ⟨c, small⟩
    rw [show Entry.table.castWidth - 1 = pinWidthAt c from pinWidthIs.symm]
    exact pin_bits ram source κ holds c pinIn _ (fun b _ => by simp [Source.conv])
  · split
    · rename_i zero
      simp only [zero]
      rfl
    · rename_i row odd
      obtain ⟨joinsIn, pinIn, pin0, pin1⟩ := modFacts_of i row odd
      have rowIs := rowAt_of i row odd
      simp only [odd]
      have part1 := joins_bits ram source κ holds (modJoinBase i) (row.width0 - 1) (by omega)
        (fun n => (source.conv κ).stageJoin i 0 (n + 1)) (fun n _ => by simp [Source.conv])
      have part2 := pin_bits ram source κ holds (modPinBase i) (by omega) ((source.conv κ).stagePin i 0)
        (fun b _ => by simp [Source.conv])
      have part3 := joins_bits ram source κ holds (modJoinBase i + (row.width0 - 1)) (row.width1 - 1) (by omega)
        (fun n => (source.conv κ).stageJoin i 1 (n + 1)) (fun n _ => by simp [Source.conv, rowIs])
      have part4 := pin_bits ram source κ holds (modPinBase i + 1) pinIn ((source.conv κ).stagePin i 1)
        (fun b _ => by simp [Source.conv])
      have part5 := joins_bits ram source κ holds (modJoinBase i + (row.width0 - 1) + (row.width1 - 1))
        (row.keep - row.width0) (by omega) (fun n => (source.conv κ).growJoin i (row.width0 + n))
        (fun n _ => by simp [Source.conv, rowIs])
      have part6 := joins_bits ram source κ holds
        (modJoinBase i + (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0))
        (row.ell - row.keep) (by omega) (fun n => (source.conv κ).foldJoin i (row.keep + n))
        (fun n _ => by simp [Source.conv, rowIs])
      rw [pin0] at part2
      rw [pin1] at part4
      simp only [blockBits_append, pieceListBits_append]
      rw [part1, part2, part3, part4, part5, part6]

end CrtConv

end Kriterion.CRT.SimMachine
