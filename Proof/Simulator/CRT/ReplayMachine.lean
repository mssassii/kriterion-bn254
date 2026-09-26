/-
**Route M's replay on the global layout agrees with `Entry.replayRouteM`** (M5b, concrete):
`agree_coordProg` for each coordinate from what the coordinate's blocks read (`CoordReads`), and
`agree_replay` for the whole replay, posting `OutHolds`.
-/

import Proof.Simulator.CRT.ReplayEntry
import Proof.Simulator.CRT.ReplayDispatch
import Proof.Simulator.CRT.ReplayConversion
import Proof.Simulator.CRT.ReplayIndexFacts
import Construction.Simulator.CRT.ReplayMachine

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB BN254

namespace Machine

/-- **What coordinate `κ`'s replay reads**, as the abstract program reads it (`conv` the published
conversion material, `records` the records, `v` the coordinate value, `labelsOf` the labels). The
source layer derives these from the stage-1 RAM. -/
structure CoordReads (κ S : Nat) (conv : ConvPublic) (records : Fin S → Nat) (v : Nat)
    (labelsOf : Nat → Block) (memory : Memory) : Prop where
  coordVal : memory.ram (word (coordCellOf κ)) = word v
  labelCells : ∀ j, j < 254 → memory.ram (word (labelBase + 254 * κ + j)) = blockWord (labelsOf j)
  chunkJoins : ∀ c, c < 32 → ∀ n, 1 ≤ n → n < Entry.table.chunkWidth c →
    memory.ram (word (Layout.sourceJoin κ (Entry.chunkJoinBase c + (n - 1)))) = blockWord (conv.chunkJoin c n)
  chunkPins : ∀ c, c < 32 → ∀ i (ib : i < laneCount),
    memory.ram (word (Layout.sourcePin κ 0 0 + 128 * c + i)) =
      word ((pinOfBlocks 14 fun k => conv.chunkPin c k.val) ⟨i, ib⟩).val
  stageJoins0 : ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
    ∀ n, 1 ≤ n → n < row.width0 →
      memory.ram (word (stageJoin κ i.val 0 + n)) = blockWord (conv.stageJoin i.val 0 n)
  stageJoins1 : ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
    ∀ n, 1 ≤ n → n < row.width1 →
      memory.ram (word (stageJoin κ i.val 1 + n)) = blockWord (conv.stageJoin i.val 1 n)
  stagePins0 : ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
    ∀ j : Fin laneCount, memory.ram (word (stagePin κ i.val 0 + j.val)) =
      word ((pinOfBlocks row.ell fun k => conv.stagePin i.val 0 k.val) j).val
  stagePins1 : ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
    ∀ j : Fin laneCount, memory.ram (word (stagePin κ i.val 1 + j.val)) =
      word ((pinOfBlocks (row.ell - row.width0) fun k => conv.stagePin i.val 1 k.val) j).val
  growJoins : ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
    ∀ n, row.width0 ≤ n → n < row.keep →
      memory.ram (word (growJoin κ i.val n)) = blockWord (conv.growJoin i.val n)
  foldJoins : ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
    ∀ n, row.keep ≤ n → n < row.ell →
      memory.ram (word (foldJoin κ i.val n)) = blockWord (conv.foldJoin i.val n)
  residues : ∀ (i : Fin Entry.table.count) (e : Fin S),
    memory.ram (word (Layout.residueCell κ i.val 0 + e.val)) = word (recordJoins Entry.table records i e)
  hints : ∀ e : Fin S, memory.ram (word (Layout.hintCell κ 0 + e.val)) =
    word (if decide (Entry.table.product ≤ records e) then 1 else 0)

/-- Coordinate `κ`'s writes. -/
def coordWrites (κ S : Nat) : Writes :=
  ((chunkLoopWrites (coordCells κ) Entry.table.chunkCount).union (modsRegion (modBase κ) Entry.table.count)).union
    (decodeWrites (decodeCells κ) 6 S)

/-- A coordinate's registers. -/
def coordClobbers : Clobbers :=
  (chunkLoopClobbers.union (bodyClobbers.union convClobbers)).union reconstructClobbers

theorem convWrites_region (W : Nat) (address : Word) (inside : convWrites W address) :
    convRegion W address := by
  obtain ⟨k, kb, same⟩ := inside
  dsimp only at kb same
  exact ⟨W + 256 + k, by omega, by omega, same⟩

section Coord

variable [FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **Coordinate `κ` on the global layout** against `liftHash (coordEvalM …)`. -/
theorem agree_coordProg (κ : Nat) (κLt : κ < 2) (S : Nat) (sSmall : S ≤ 512) (conv : ConvPublic)
    (records : Fin S → Nat) (v : Nat) (vSmall : v < 2 ^ 256) (labelsOf : Nat → Block) (memory : Memory)
    (reads : CoordReads κ S conv records v labelsOf memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (ce : CoordEval Entry.table S) after =>
        (∀ e : Fin S, after.ram (word (Layout.decodedCell κ 0 + e.val)) =
          fieldWord ((ce.decoded e : Nat) : BaseField)) ∧
          Frame (coordWrites κ S) coordClobbers memory after)
      ((coordProg κ S).tree memory)
      (liftHash (coordEvalM Entry.table S κ conv records v labelsOf)) := by
  have cc32 : Entry.table.chunkCount = 32 := TableFacts.chunkCount
  have cnt85 : Entry.table.count = 85 := TableFacts.count
  have ca := TableFacts.castAnswers_le
  have R : Layout.replayScratch κ = 2 ^ 60 + 2 ^ 40 * κ := rfl
  have chain : CoordChain (coordCells κ) Entry.table.chunkCount Entry.table.castWidth := by
    rw [cc32]
    refine ⟨?_, ?_, fun c cb n nb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [coordCells, coordCellOf, R, Layout.sourceJoin, Layout.sourcePin, labelBase, reqX, reqY,
        requestBase]
    · split <;> omega
    · omega
    · have := IndexFacts.chunkJoinBase_le c; omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have dchain : DecodeChain (decodeCells κ) Entry.table.count 6 S := by
    rw [cnt85]
    refine ⟨?_, fun i ib => ?_, fun i ib => ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [decodeCells, windowOut, windowAt, modBase, R, Layout.hintCell, Layout.decodedCell] <;>
      omega
  have W : ∀ i, windowAt κ i = 2 ^ 60 + 2 ^ 40 * κ + 2 ^ 21 + 2 ^ 20 * i := fun i => rfl
  -- the numeric facts of the moduli
  have sourceSmall : ∀ idx, idx < 2 ^ 24 → Layout.sourceJoin κ idx < 2 ^ 60 := fun idx h => by
    simp only [Layout.sourceJoin]; omega
  refine agree_coordReplay Entry.table S κ κLt (coordCells κ) (by rw [cc32]; norm_num) chain
    TableFacts.shape (by rw [TableFacts.castWidth]; norm_num) (by rw [TableFacts.castWidth]; norm_num)
    TableFacts.castAnswers_le TableFacts.modulus_pos SliceC.bn254_coprime TableFacts.garnerTable conv
    records v vSmall labelsOf _ (modBase κ) (bodyClobbers.union convClobbers) (decodeCells κ) 6 dchain
    TableFacts.product_le TableFacts.wrapBound_lt
    (by simp only [decodeCells, coordCells, R, Layout.decodedCell]; omega)
    (by simp only [coordCells, modBase, R]; rw [cc32]; omega)
    (by simp only [decodeCells, modBase, R]; rw [cnt85]; omega)
    (fun i ib => by
      rw [cnt85] at ib
      simp only [decodeCells, windowOut, windowAt, modBase, R]
      constructor <;> omega)
    memory reads.coordVal
    (fun j jb => by
      rw [TableFacts.inputBits] at jb
      exact reads.labelCells j jb)
    (fun c cb n n1 nb => reads.chunkJoins c (by rw [cc32] at cb; exact cb) n n1 nb)
    (fun c cb i ib => reads.chunkPins c (by rw [cc32] at cb; exact cb) i ib)
    reads.hints ?_
  intro chunkTable base out
  refine modContract_of Entry.table S κ conv (recordJoins Entry.table records) v vSmall (coordCells κ) chain
    (modBase κ) (joinBaseOf κ) (convProg κ) (fun i => windowAt κ i + 2 ^ 12)
    (fun i => windowAt κ i + 2 ^ 12 + 2 ^ 11) convClobbers TableFacts.chunkZero_facts
    (fun i row kind => by
      obtain ⟨_, _, _, _, _, ellLe, _⟩ := TableFacts.odd_facts i row kind
      rw [TableFacts.castWidth]; omega)
    TableFacts.modulus_pos (fun i => (TableFacts.modulus_le i).trans (by norm_num))
    (TableFacts.padAnswers_le S sSmall) sSmall (by rw [cc32]; norm_num)
    (fun c cb => by rw [TableFacts.chunkOffset, cc32] at *; omega)
    (fun c cb => TableFacts.shape.widthSmall c cb)
    (fun i ρ j ρb jb => TableFacts.bodyTag_small κ i.val ρ j κLt
      (by have := lt_of_lt_of_eq i.isLt cnt85; omega)
      (by have := TableFacts.modulus_le i; omega) (by have := TableFacts.padAnswers_lt S sSmall i; omega))
    (by simp only [coordCells, modBase, R]; rw [cc32]; omega)
    (by simp only [modBase, R]; rw [cnt85]; omega)
    (fun i ib => by simp only [joinBaseOf, coordCells, R, Layout.residueCell]; rw [cnt85] at ib; omega)
    (fun i ib => by
      have modLe : modNat Entry.table i ≤ 439 := by
        simp only [modNat, dif_pos ib]; exact TableFacts.modulus_le _
      simp only [windowAt, modBase, R]
      rw [cnt85] at ib
      refine ⟨by omega, by omega, by omega⟩)
    memory reads.coordVal (fun i e => reads.residues i e)
    (fun i e => by
      unfold recordJoins recordJoin
      simp only [stored_eq]
      exact Nat.mod_lt _ (TableFacts.modulus_pos i))
    chunkTable base out ?_
  -- the conversions
  intro i row kind m0 lanes sigma below
  have ib := i.isLt
  have iLt : i.val < 85 := lt_of_lt_of_eq ib cnt85
  obtain ⟨w0Pos, w1Pos, ellEq, keepGe, keepLe, ellLe, countLt⟩ := TableFacts.odd_facts i row kind
  have rowEq : Entry.rowAt i.val = row := IndexFacts.rowAt_eq i.val ib row kind
  have joinBase := IndexFacts.modJoinBase_le i.val
  have pinBase := IndexFacts.modPinBase_le i.val
  have mLe := TableFacts.modulus_le i
  have lc : laneCount = 128 := rfl
  -- every source cell is below the replay's scratch
  have memEq : ∀ x, x < 2 ^ 60 → m0.ram (word x) = memory.ram (word x) := fun x xb =>
    below x (by simp only [coordCells, R]; omega)
  unfold convProg
  rw [dif_pos ib]
  split
  · next row' heq =>
      rw [show (⟨i.val, ib⟩ : Fin Entry.table.count) = i from rfl, kind] at heq
      cases heq
      refine (agree_conversionReplay κ i.val row (Entry.table.modulus i) (Entry.table.wordValue (Entry.table.modulus i) v)
        _ conv (windowAt κ i.val) (stageJoin κ i.val) (stagePin κ i.val) (growJoin κ i.val) (foldJoin κ i.val)
        κLt (by omega) w0Pos w1Pos (by omega) (by omega) ellEq keepGe keepLe (by omega)
        (TableFacts.modulus_pos i) (by omega)
        (SliceC.wordValue_lt Entry.table _ v row.ell (TableFacts.modulus_pos i) countLt)
        (by simp only [W]; omega)
        (fun q qb => by
          simp only [stageJoin, rowEq, W, Layout.sourceJoin]
          split <;> omega)
        (fun q qb => by simp only [stagePin, W, Layout.sourcePin]; omega)
        (fun j => by simp only [growJoin, rowEq, W, Layout.sourceJoin]; omega)
        (fun j => by simp only [foldJoin, rowEq, W, Layout.sourceJoin]; omega)
        m0 (fun j => lanes j.val j.isLt) sigma
        (fun n n1 nb => by
          rw [memEq _ (by simp only [stageJoin, rowEq, Layout.sourceJoin]; split <;> omega)]
          exact reads.stageJoins0 i row kind n n1 nb)
        (fun n n1 nb => by
          rw [memEq _ (by simp only [stageJoin, rowEq, Layout.sourceJoin]; split <;> omega)]
          exact reads.stageJoins1 i row kind n n1 nb)
        (fun j => by
          rw [memEq _ (by simp only [stagePin, Layout.sourcePin]; have := j.isLt; omega)]
          exact reads.stagePins0 i row kind j)
        (fun j => by
          rw [memEq _ (by simp only [stagePin, Layout.sourcePin]; have := j.isLt; omega)]
          exact reads.stagePins1 i row kind j)
        (fun n n0 nb => by
          rw [memEq _ (by simp only [growJoin, rowEq, Layout.sourceJoin]; omega)]
          exact reads.growJoins i row kind n n0 nb)
        (fun n n0 nb => by
          rw [memEq _ (by simp only [foldJoin, rowEq, Layout.sourceJoin]; omega)]
          exact reads.foldJoins i row kind n n0 nb)).mono fun conv' after post =>
          ⟨post.1, post.2.1, post.2.2.1, post.2.2.2.mono (convWrites_region _) fun _ h => h⟩
  · next heq =>
      rw [show (⟨i.val, ib⟩ : Fin Entry.table.count) = i from rfl, kind] at heq
      cases heq

end Coord

/-! ### The whole replay -/

/-- Every cell a coordinate writes is at or above `2 ^ 56`, and its decoded cells are its own. -/
theorem coordWrites_high (κ S : Nat) (κLt : κ < 2) (sSmall : S ≤ 512) (x : Nat) (xLow : x < 2 ^ 56) :
    ¬ coordWrites κ S (word x) := by
  have cc32 : Entry.table.chunkCount = 32 := TableFacts.chunkCount
  have cnt85 : Entry.table.count = 85 := TableFacts.count
  rintro ((⟨y, yLow, yHigh, same⟩ | ⟨y, yLow, yHigh, same⟩) | (⟨y, yLow, yHigh, same⟩ | ⟨k, kb, same⟩))
  · simp only [coordCells, Layout.replayScratch] at yLow yHigh
    rw [cc32] at yHigh
    have := word_inj (by omega) (by omega) same
    omega
  · simp only [modBase, Layout.replayScratch] at yLow yHigh
    rw [cnt85] at yHigh
    have := word_inj (by omega) (by omega) same
    omega
  · simp only [decodeCells, Layout.replayScratch] at yLow yHigh
    have := word_inj (by omega) (by omega) same
    omega
  · simp only [decodeCells, Layout.decodedCell] at kb same
    have := word_inj (by omega) (by omega) same
    omega

theorem xDecoded_safe (e : Nat) (eLt : e < 1024) :
    ¬ coordWrites 1 Entry.yCount (word (Layout.decodedCell 0 e)) := by
  have cc32 : Entry.table.chunkCount = 32 := TableFacts.chunkCount
  have cnt85 : Entry.table.count = 85 := TableFacts.count
  have yc : Entry.yCount = 275 := rfl
  simp only [Layout.decodedCell]
  rintro ((⟨y, yLow, yHigh, same⟩ | ⟨y, yLow, yHigh, same⟩) | (⟨y, yLow, yHigh, same⟩ | ⟨k, kb, same⟩))
  · simp only [coordCells, Layout.replayScratch] at yLow yHigh
    rw [cc32] at yHigh
    have := word_inj (by omega) (by omega) same
    omega
  · simp only [modBase, Layout.replayScratch] at yLow yHigh
    rw [cnt85] at yHigh
    have := word_inj (by omega) (by omega) same
    omega
  · simp only [decodeCells, Layout.replayScratch] at yLow yHigh
    have := word_inj (by omega) (by omega) same
    omega
  · simp only [decodeCells, Layout.decodedCell] at kb same
    rw [yc] at kb
    have := word_inj (by omega) (by omega) same
    omega

/-- **The reads transport** to any memory that agrees below `2 ^ 56`. -/
theorem CoordReads.transport {κ S : Nat} {conv : ConvPublic} {records : Fin S → Nat} {v : Nat}
    {labelsOf : Nat → Block} {memory m1 : Memory} (κLt : κ < 2) (sSmall : S ≤ 512)
    (reads : CoordReads κ S conv records v labelsOf memory)
    (agree : ∀ x, x < 2 ^ 56 → m1.ram (word x) = memory.ram (word x)) :
    CoordReads κ S conv records v labelsOf m1 := by
  have cnt85 : Entry.table.count = 85 := TableFacts.count
  have lc : laneCount = 128 := rfl
  have rowFacts : ∀ i : Nat, (Entry.rowAt i).width0 ≤ 12 ∧ (Entry.rowAt i).width1 ≤ 12 ∧
      (Entry.rowAt i).keep ≤ 14 := fun i => by
    obtain ⟨ell, w0, w1, keep, _⟩ := IndexFacts.rowAt_bounds i
    omega
  refine ⟨?_, fun j jb => ?_, fun c cb n n1 nb => ?_, fun c cb i ib => ?_, fun i row kind n n1 nb => ?_,
    fun i row kind n n1 nb => ?_, fun i row kind j => ?_, fun i row kind j => ?_, fun i row kind n n0 nb => ?_,
    fun i row kind n n0 nb => ?_, fun i e => ?_, fun e => ?_⟩
  · rw [agree _ (by simp only [coordCellOf, reqX, reqY, requestBase]; split <;> omega)]
    exact reads.coordVal
  · rw [agree _ (by simp only [labelBase]; omega)]
    exact reads.labelCells j jb
  · have := IndexFacts.chunkJoinBase_le c
    have : Entry.table.chunkWidth c ≤ 8 := by rw [TableFacts.chunkWidth]; omega
    rw [agree _ (by simp only [Layout.sourceJoin]; omega)]
    exact reads.chunkJoins c cb n n1 nb
  · rw [agree _ (by simp only [Layout.sourcePin]; omega)]
    exact reads.chunkPins c cb i ib
  · have := IndexFacts.modJoinBase_le i.val
    have := lt_of_lt_of_eq i.isLt cnt85
    have := rowFacts i.val
    have row0 := (TableFacts.odd_facts i row kind)
    rw [agree _ (by simp only [stageJoin, Layout.sourceJoin]; split <;> omega)]
    exact reads.stageJoins0 i row kind n n1 nb
  · have := IndexFacts.modJoinBase_le i.val
    have := lt_of_lt_of_eq i.isLt cnt85
    have := rowFacts i.val
    have row0 := (TableFacts.odd_facts i row kind)
    rw [agree _ (by simp only [stageJoin, Layout.sourceJoin]; split <;> omega)]
    exact reads.stageJoins1 i row kind n n1 nb
  · have := IndexFacts.modPinBase_le i.val
    have := lt_of_lt_of_eq i.isLt cnt85
    have := j.isLt
    rw [agree _ (by simp only [stagePin, Layout.sourcePin]; omega)]
    exact reads.stagePins0 i row kind j
  · have := IndexFacts.modPinBase_le i.val
    have := lt_of_lt_of_eq i.isLt cnt85
    have := j.isLt
    rw [agree _ (by simp only [stagePin, Layout.sourcePin]; omega)]
    exact reads.stagePins1 i row kind j
  · have := IndexFacts.modJoinBase_le i.val
    have := lt_of_lt_of_eq i.isLt cnt85
    have := rowFacts i.val
    rw [agree _ (by simp only [growJoin, Layout.sourceJoin]; omega)]
    exact reads.growJoins i row kind n n0 nb
  · have := IndexFacts.modJoinBase_le i.val
    have := lt_of_lt_of_eq i.isLt cnt85
    have := rowFacts i.val
    rw [agree _ (by simp only [foldJoin, Layout.sourceJoin]; omega)]
    exact reads.foldJoins i row kind n n0 nb
  · have := lt_of_lt_of_eq i.isLt cnt85
    have := e.isLt
    rw [agree _ (by simp only [Layout.residueCell]; omega)]
    exact reads.residues i e
  · have := e.isLt
    rw [agree _ (by simp only [Layout.hintCell]; omega)]
    exact reads.hints e

theorem maskScratch_low : 2 ^ 59 ≤ maskScratch := by
  unfold maskScratch Layout.replayScratch
  omega

theorem maskScratch_fits : maskScratch + 6 < 2 ^ 256 := by
  unfold maskScratch Layout.replayScratch
  omega

/-- The replay's writes. -/
def replayWrites : Writes :=
  (((coordWrites 0 Entry.xCount).union (coordWrites 1 Entry.yCount)).union (Writes.cell Layout.keyCell)).union
    (maskWrites (entryMaskCells maskScratch) (nonCollectorCount digitCount))

/-- The replay's registers. -/
def replayClobbers : Clobbers := ((coordClobbers.union coordClobbers).union keyClobbers).union maskClobbers

section Replay

variable [FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **M5b: route M's replay on the machine** asks what `Entry.replayRouteM` asks and leaves
`OutHolds` of its output (read in the tier-2 index), with the frame `replayWrites`, from what the
two coordinates read (`CoordReads`), the request and the curve constants. -/
theorem agree_replay (pub : Entry.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature)
    (memory : Memory)
    (readsX : CoordReads 0 Entry.xCount (Entry.convOf pub.crtX) (fun e => (pub.recX.get e).val)
      input.x.val (Entry.labelX labels) memory)
    (readsY : CoordReads 1 Entry.yCount (Entry.convOf pub.crtY) (fun e => (pub.recY.get e).val)
      input.y.val (Entry.labelY labels) memory)
    (reqXCell : memory.ram (word reqX) = fieldWord input.x)
    (reqYCell : memory.ram (word reqY) = fieldWord input.y)
    (c0Cell : memory.ram (word fieldBase) = fieldWord pub.curve.1)
    (c1Cell : memory.ram (word (fieldBase + 1)) = fieldWord pub.curve.2.1)
    (c2Cell : memory.ram (word (fieldBase + 2)) = fieldWord pub.curve.2.2) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (out : Entry.RouteMOut) after =>
        OutCells.OutHolds (routeView out) after ∧ Frame replayWrites replayClobbers memory after)
      (replay.tree memory)
      (liftHash (Entry.replayRouteM pub input labels)) := by
  have xs : Entry.xCount ≤ 512 := by decide
  have ys : Entry.yCount ≤ 512 := by decide
  have valSmall : ∀ z : BaseField, z.val < 2 ^ 256 := fun z =>
    lt_trans z.val_lt (by unfold baseFieldModulus; norm_num)
  have decodedEq : ∀ κ e, Layout.decodedCell κ 0 + e = Layout.decodedCell κ e := fun κ e => by
    simp only [Layout.decodedCell]; omega
  refine agree_entryReplay pub input labels (coordProg 0 Entry.xCount) (coordProg 1 Entry.yCount)
    maskScratch maskScratch_low maskScratch_fits
    (coordWrites 0 Entry.xCount) (coordWrites 1 Entry.yCount) coordClobbers coordClobbers memory
    ((agree_coordProg 0 (by norm_num) Entry.xCount xs _ _ _ (valSmall _) _ memory readsX).mono
      fun ce after post => ⟨fun e => by rw [← decodedEq]; exact post.1 e, post.2⟩)
    (fun m1 agreeOut =>
      (agree_coordProg 1 (by norm_num) Entry.yCount ys _ _ _ (valSmall _) _ m1
        (readsY.transport (by norm_num) ys fun x xb =>
          agreeOut _ (coordWrites_high 0 _ (by norm_num) xs x xb))).mono
        fun ce after post => ⟨fun e => by rw [← decodedEq]; exact post.1 e, post.2⟩)
    (fun e => xDecoded_safe e.val (lt_of_lt_of_le e.isLt (by decide)))
    reqXCell reqYCell c0Cell c1Cell c2Cell
    (fun x hx => by
      have low : x < 2 ^ 56 := by
        rcases hx with h | h | h | h | h <;> subst h <;> simp only [reqX, reqY, requestBase, fieldBase] <;>
          norm_num
      exact ⟨coordWrites_high 0 _ (by norm_num) xs x low, coordWrites_high 1 _ (by norm_num) ys x low⟩)

end Replay

end Machine

end Kriterion.CRT.SimMachine
