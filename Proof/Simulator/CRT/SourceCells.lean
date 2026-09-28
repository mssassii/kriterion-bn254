/-
**The replay's reads from the stage-1 source** (for M5b): the two
`Machine.CoordReads` instances that `Machine.agree_replay` takes, for the published material
`pub := Entry.publish s` of a source `s` that RAM holds.

What stage 1 leaves in RAM (`CrtPieces.SourceHolds` and `CrtSerial.DigitsSmall`,
`Proof/Simulator/CRT/Stage1Source.lean`) is the source field by field: every join at
`Layout.sourceJoin κ index`, every pin lane at `Layout.sourcePin κ k lane`, and every record as its
mixed-radix digits at `Layout.residueCell κ i e`, each digit below its modulus. The source reads of
`Proof/Correctness/CRT/SourceReads.lean` say what the evaluator reads from `pub`: the joins at the flat
source indices, the pin lanes, and the digits of the record below `M`. This file puts the two together, cell
by cell:

* the conversion cells (`chunkPins`, `stageJoins0/1`, `stagePins0/1`, `growJoins`, `foldJoins`)
  for either coordinate, from `CrtConv.ConvHolds`; the chunk joins (`chunkJoins`) from a hypothesis that the zero
  cell `Layout.zeroJoin` holds `word 0` (no chunk joins: the published ones are `0`, `SourceReads.chunkJoin_publish`);
* the residue cells (`residuesX/Y`) from the record facts, through the mixed-radix digit read-back
  (`CrtTable.digit_mixedRadix`);
* the hint cells (`hintsX/Y`) from a hypothesis that the hint cells hold `word 0` (stage 1 does not write
  them; the published hint of a source record is 0, `SourceReads.hintX_publish`).

The coordinate value and the label cells are not source cells; `coordReadsX/Y` take them as hypotheses,
as the request block and the label selection establish them. `coordReadsX/Y_extract` specialize to the
extracted source `CrtSource.extract ram` of a RAM whose stage-1 cells are in range (`CellsValid`).
-/

import Proof.Simulator.CRT.ReplayMachine
import Proof.Simulator.CRT.Stage1Source
import Proof.Correctness.CRT.SourceReads

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.CRT.Entry (Source joinCount pinCount pinWidth chunkJoinBase modJoinBase modPinBase rowAt
  convOf publish)
open Kriterion.CRT.SourceReads (convPub)

namespace SourceCells

variable (ram : Word → Word) (s : Source)

/-! ### The published conversion material of each coordinate -/

theorem convPub_zero : convPub s ⟨0, by decide⟩ = convOf (publish s).crtX := if_pos rfl

theorem convPub_one : convPub s ⟨1, by decide⟩ = convOf (publish s).crtY := if_neg (by decide)

/-! ### Joins and pins -/

/-- A join cell holds the source's join at that flat index. -/
theorem joinAt_cell (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) (index : Nat)
    (inside : index < joinCount) :
    ram (word (Layout.sourceJoin κ index)) = labelWord (s.joinAt ⟨κ, hκ⟩ index) := by
  rw [holds.joins index inside]
  simp only [Source.joinAt, atNat, dif_pos inside, labelWord_eq_word]

/-- **No chunk joins**: the published chunk joins are `0`, and the zero cell holds `0` (a hypothesis: stage 1
never writes it and its start RAM is zero, `CrtValidStart.Retained.zeroJoin`). -/
theorem chunkJoins (κ : Nat) (hκ : κ < 2) (zero : ram (word Layout.zeroJoin) = word 0) :
    ∀ c, c < 32 → ∀ n, 1 ≤ n → n < Entry.table.chunkWidth c →
      ram (word Layout.zeroJoin) = labelWord ((convPub s ⟨κ, hκ⟩).chunkJoin c n) := by
  intro c _ n _ _
  rw [SourceReads.chunkJoin_publish s ⟨κ, hκ⟩ c n, zero, labelWord_eq_word]
  rfl

theorem chunkPins (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) :
    ∀ c, c < 32 → ∀ i (ib : i < laneCount),
      ram (word (Layout.sourcePin κ 0 0 + 128 * c + i)) =
        word ((pinOfBlocks 13 fun k => (convPub s ⟨κ, hκ⟩).chunkPin c k.val) ⟨i, ib⟩).val := by
  intro c hc i ib
  have hk : c < pinCount := (CrtConv.chunkFacts ⟨c, hc⟩).2.1
  have hc' : c < Entry.table.chunkCount := by rw [CrtConv.chunkCount_eq]; exact hc
  have addr : Layout.sourcePin κ 0 0 + 128 * c + i = Layout.sourcePin κ c i := by
    simp only [Layout.sourcePin]
    omega
  rw [addr, holds.pins c hk i ib]
  exact congrArg word (SourceReads.chunkPin_lanes s ⟨κ, hκ⟩ c hc' hk ⟨i, ib⟩).symm

theorem stageJoins0 (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) :
    ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
      ∀ n, 1 ≤ n → n < row.width0 →
        ram (word (Machine.stageJoin κ i.val 0 + n)) = labelWord ((convPub s ⟨κ, hκ⟩).stageJoin i.val 0 n) := by
  intro i row kind n lower upper
  have facts := (CrtConv.modFacts_of i row kind).1
  have addr : Machine.stageJoin κ i.val 0 + n = Layout.sourceJoin κ (modJoinBase i + (n - 1)) := by
    simp only [Machine.stageJoin, ↓reduceIte, Layout.sourceJoin]
    omega
  rw [addr, SourceReads.stageJoin0_publish s ⟨κ, hκ⟩ i row kind n lower upper]
  exact joinAt_cell ram s κ hκ holds _ (by omega)

theorem stageJoins1 (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) :
    ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
      ∀ n, 1 ≤ n → n < row.width1 →
        ram (word (Machine.stageJoin κ i.val 1 + n)) = labelWord ((convPub s ⟨κ, hκ⟩).stageJoin i.val 1 n) := by
  intro i row kind n lower upper
  have facts := (CrtConv.modFacts_of i row kind).1
  have rowEq := CrtConv.rowAt_of i row kind
  have addr : Machine.stageJoin κ i.val 1 + n =
      Layout.sourceJoin κ (modJoinBase i + ((rowAt i).width0 - 1) + (n - 1)) := by
    simp only [Machine.stageJoin, one_ne_zero, ↓reduceIte, Layout.sourceJoin]
    omega
  rw [addr, SourceReads.stageJoin1_publish s ⟨κ, hκ⟩ i row kind n lower upper]
  exact joinAt_cell ram s κ hκ holds _ (by rw [rowEq]; omega)

theorem stagePins0 (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) :
    ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
      ∀ j : Fin laneCount, ram (word (Machine.stagePin κ i.val 0 + j.val)) =
        word ((pinOfBlocks (row.ell - 1) fun k => (convPub s ⟨κ, hκ⟩).stagePin i.val 0 k.val) j).val := by
  intro i row kind j
  obtain ⟨-, pinsIn, width0, -⟩ := CrtConv.modFacts_of i row kind
  obtain ⟨w0pos, -, ellEq, -, -, -, -⟩ := TableFacts.odd_facts i row kind
  have hk : modPinBase i + 0 < pinCount := by omega
  have addr : Machine.stagePin κ i.val 0 + j.val = Layout.sourcePin κ (modPinBase i + 0) j.val := by
    simp only [Machine.stagePin, Layout.sourcePin]
    omega
  rw [addr, holds.pins _ hk j.val j.isLt]
  have sameWidth : pinWidth ⟨modPinBase i + 0, hk⟩ = row.ell - 1 := by
    rw [← CrtConv.pinWidthAt_eq, Nat.add_zero]
    exact width0
  exact congrArg word (SourceReads.stagePin_lanes s ⟨κ, hκ⟩ i row kind 0 (row.ell - 1) (by simp) hk sameWidth
    (by omega) (by omega) j).symm

theorem stagePins1 (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) :
    ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
      ∀ j : Fin laneCount, ram (word (Machine.stagePin κ i.val 1 + j.val)) =
        word ((pinOfBlocks (row.ell - row.width0 - 1) fun k => (convPub s ⟨κ, hκ⟩).stagePin i.val 1 k.val) j).val := by
  intro i row kind j
  obtain ⟨-, pinsIn, -, width1⟩ := CrtConv.modFacts_of i row kind
  obtain ⟨-, w1pos, ellEq, -, -, -, -⟩ := TableFacts.odd_facts i row kind
  have addr : Machine.stagePin κ i.val 1 + j.val = Layout.sourcePin κ (modPinBase i + 1) j.val := by
    simp only [Machine.stagePin, Layout.sourcePin]
    omega
  rw [addr, holds.pins _ pinsIn j.val j.isLt]
  have sameWidth : pinWidth ⟨modPinBase i + 1, pinsIn⟩ = row.ell - row.width0 - 1 := by
    rw [← CrtConv.pinWidthAt_eq]
    exact width1
  exact congrArg word (SourceReads.stagePin_lanes s ⟨κ, hκ⟩ i row kind 1 (row.ell - row.width0 - 1) (by simp)
    pinsIn sameWidth (by omega) (by omega) j).symm

theorem growJoins (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) :
    ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
      ∀ n, row.width0 ≤ n → n < row.keep →
        ram (word (Machine.growJoin κ i.val n)) = labelWord ((convPub s ⟨κ, hκ⟩).growJoin i.val n) := by
  intro i row kind n lower upper
  have facts := (CrtConv.modFacts_of i row kind).1
  obtain ⟨-, -, -, -, keepLe, ellLe, -⟩ := TableFacts.odd_facts i row kind
  have rowEq := CrtConv.rowAt_of i row kind
  rw [SourceReads.growJoin_publish s ⟨κ, hκ⟩ i row kind n lower upper, rowEq]
  have addr : Machine.growJoin κ i.val n =
      Layout.sourceJoin κ (modJoinBase i + (row.width0 - 1) + (row.width1 - 1) + (n - row.width0)) := by
    simp only [Machine.growJoin, rowEq, Layout.sourceJoin]
    omega
  rw [addr]
  exact joinAt_cell ram s κ hκ holds _ (by omega)

theorem foldJoins (κ : Nat) (hκ : κ < 2) (holds : CrtConv.ConvHolds ram s ⟨κ, hκ⟩) :
    ∀ (i : Fin Entry.table.count) (row : OddRow), Entry.table.kind i = .odd row →
      ∀ n, row.keep ≤ n → n < row.ell →
        ram (word (Machine.foldJoin κ i.val n)) = labelWord ((convPub s ⟨κ, hκ⟩).foldJoin i.val n) := by
  intro i row kind n lower upper
  have facts := (CrtConv.modFacts_of i row kind).1
  obtain ⟨-, -, -, -, keepLe, ellLe, -⟩ := TableFacts.odd_facts i row kind
  have rowEq := CrtConv.rowAt_of i row kind
  rw [SourceReads.foldJoin_publish s ⟨κ, hκ⟩ i row kind n lower upper, rowEq]
  have addr : Machine.foldJoin κ i.val n =
      Layout.sourceJoin κ (modJoinBase i + (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0)
        + (n - row.keep)) := by
    simp only [Machine.foldJoin, rowEq, Layout.sourceJoin]
    omega
  rw [addr]
  exact joinAt_cell ram s κ hκ holds _ (by omega)

/-! ### Records: the residue digits -/

theorem modulus_eq (i : Fin Entry.table.count) : Entry.table.modulus i = CrtStage1.modulusAt i.val := by
  unfold CrtStage1.modulusAt Array.getD
  rw [dif_pos (show i.val < bn254Moduli.size from i.isLt)]
  rfl

theorem radix_eq (i : Fin Entry.table.count) : Entry.table.radix i = CrtConv.radixAt i.val := by
  unfold CrtTable.radix CrtConv.radixAt
  rw [← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun j _ => modulus_eq _

/-- The digit a residue cell of coordinate `κ` holds, record `e`, modulus `i`. -/
def digitOf (κ e i : Nat) : Nat := (ram (word (Layout.residueCell κ i e))).toNat

/-- The residue vector the cells of record `e` of coordinate `κ` hold. -/
def residuesOf (κ e : Nat) (hκ : κ < 2) (he : e < CrtStage1.encCount κ) (digits : CrtSerial.DigitsSmall ram) :
    Entry.table.Residues :=
  fun i => ⟨digitOf ram κ e i.val, by
    rw [modulus_eq]
    exact digits κ e i.val hκ he (lt_of_lt_of_eq i.isLt TableFacts.count)⟩

theorem mixedRadix_residuesOf (κ e : Nat) (hκ : κ < 2) (he : e < CrtStage1.encCount κ)
    (digits : CrtSerial.DigitsSmall ram) :
    Entry.table.mixedRadix (residuesOf ram κ e hκ he digits) = CrtConv.recordValue ram κ e := by
  unfold CrtTable.mixedRadix CrtConv.recordValue
  have step : ∀ i : Fin Entry.table.count, ((residuesOf ram κ e hκ he digits) i).val * Entry.table.radix i =
      (fun i' => digitOf ram κ e i' * CrtConv.radixAt i') i.val := fun i => by
    rw [radix_eq]
    rfl
  rw [Finset.sum_congr rfl fun i _ => step i]
  refine (Fin.sum_univ_eq_sum_range (fun i' => digitOf ram κ e i' * CrtConv.radixAt i') Entry.table.count).trans ?_
  rw [TableFacts.count]
  rfl

/-- A residue cell holds the digit the evaluator reads from the record. -/
theorem residue_cell (κ e : Nat) (hκ : κ < 2) (he : e < CrtStage1.encCount κ) (digits : CrtSerial.DigitsSmall ram)
    (record : Nat) (value : CrtConv.recordValue ram κ e = record) (i : Fin Entry.table.count) :
    ram (word (Layout.residueCell κ i.val 0 + e)) = word (record / Entry.table.radix i % Entry.table.modulus i) := by
  rw [← value, ← mixedRadix_residuesOf ram κ e hκ he digits, CrtTable.digit_mixedRadix]
  have addr : Layout.residueCell κ i.val 0 + e = Layout.residueCell κ i.val e := by
    simp only [Layout.residueCell]
    omega
  rw [addr]
  exact (CrtSerial.word_toNat_self _).symm

theorem residuesX (holds : CrtPieces.SourceHolds ram s) (digits : CrtSerial.DigitsSmall ram) :
    ∀ (i : Fin Entry.table.count) (e : Fin Entry.xCount),
      ram (word (Layout.residueCell 0 i.val 0 + e.val)) =
        word (recordJoins Entry.table (fun e => ((publish s).recX.get e).val) i e) := by
  intro i e
  have he : e.val < CrtStage1.encCount 0 := by simp [CrtStage1.encCount]
  have value : CrtConv.recordValue ram 0 e.val = (s.recX e).val := by
    rw [holds.records 0 e.val (by decide) he]
    simp [CrtPieces.recordOf]
  have key := SourceReads.recordJoinX_publish s e i
  simp only [stored_eq] at key
  simp only [recordJoins, stored_eq]
  rw [key, CrtTable.mixedRadixEquiv_symm_val]
  exact residue_cell ram 0 e.val (by decide) he digits _ value i

theorem residuesY (holds : CrtPieces.SourceHolds ram s) (digits : CrtSerial.DigitsSmall ram) :
    ∀ (i : Fin Entry.table.count) (e : Fin Entry.yCount),
      ram (word (Layout.residueCell 1 i.val 0 + e.val)) =
        word (recordJoins Entry.table (fun e => ((publish s).recY.get e).val) i e) := by
  intro i e
  have he : e.val < CrtStage1.encCount 1 := by simp [CrtStage1.encCount]
  have value : CrtConv.recordValue ram 1 e.val = (s.recY e).val := by
    rw [holds.records 1 e.val (by decide) he]
    simp [CrtPieces.recordOf]
  have key := SourceReads.recordJoinY_publish s e i
  simp only [stored_eq] at key
  simp only [recordJoins, stored_eq]
  rw [key, CrtTable.mixedRadixEquiv_symm_val]
  exact residue_cell ram 1 e.val (by decide) he digits _ value i

/-! ### Hints -/

theorem hintsX (hints : ∀ e, e < Entry.xCount → ram (word (Layout.hintCell 0 e)) = word 0) :
    ∀ e : Fin Entry.xCount, ram (word (Layout.hintCell 0 0 + e.val)) =
      word (if decide (Entry.table.product ≤ ((publish s).recX.get e).val) then 1 else 0) := by
  intro e
  rw [SourceReads.hintX_publish s e]
  have addr : Layout.hintCell 0 0 + e.val = Layout.hintCell 0 e.val := by
    simp only [Layout.hintCell]
    omega
  rw [addr, hints e.val e.isLt]
  rfl

theorem hintsY (hints : ∀ e, e < Entry.yCount → ram (word (Layout.hintCell 1 e)) = word 0) :
    ∀ e : Fin Entry.yCount, ram (word (Layout.hintCell 1 0 + e.val)) =
      word (if decide (Entry.table.product ≤ ((publish s).recY.get e).val) then 1 else 0) := by
  intro e
  rw [SourceReads.hintY_publish s e]
  have addr : Layout.hintCell 1 0 + e.val = Layout.hintCell 1 e.val := by
    simp only [Layout.hintCell]
    omega
  rw [addr, hints e.val e.isLt]
  rfl

/-! ### The two instances -/

/-- **The `x` coordinate's reads** from a source RAM holds. -/
theorem coordReadsX (memory : Memory) (holds : CrtPieces.SourceHolds memory.ram s)
    (digits : CrtSerial.DigitsSmall memory.ram)
    (hints : ∀ e, e < Entry.xCount → memory.ram (word (Layout.hintCell 0 e)) = word 0)
    (zero : memory.ram (word Layout.zeroJoin) = word 0)
    (v : Nat) (labelsOf : Nat → Block)
    (coordVal : memory.ram (word (Machine.coordCellOf 0)) = word v)
    (labelCells : ∀ j, j < 254 → memory.ram (word (labelBase + 254 * 0 + j)) = blockWord (labelsOf j)) :
    Machine.CoordReads 0 Entry.xCount (convOf (publish s).crtX) (fun e => ((publish s).recX.get e).val) v
      labelsOf memory := by
  have conv := holds.conv ⟨0, by decide⟩
  rw [← convPub_zero s]
  exact
    { coordVal := coordVal
      labelCells := labelCells
      chunkJoins := chunkJoins memory.ram s 0 (by decide) zero
      chunkPins := chunkPins memory.ram s 0 (by decide) conv
      stageJoins0 := stageJoins0 memory.ram s 0 (by decide) conv
      stageJoins1 := stageJoins1 memory.ram s 0 (by decide) conv
      stagePins0 := stagePins0 memory.ram s 0 (by decide) conv
      stagePins1 := stagePins1 memory.ram s 0 (by decide) conv
      growJoins := growJoins memory.ram s 0 (by decide) conv
      foldJoins := foldJoins memory.ram s 0 (by decide) conv
      residues := residuesX memory.ram s holds digits
      hints := hintsX memory.ram s hints }

/-- **The `y` coordinate's reads** from a source RAM holds. -/
theorem coordReadsY (memory : Memory) (holds : CrtPieces.SourceHolds memory.ram s)
    (digits : CrtSerial.DigitsSmall memory.ram)
    (hints : ∀ e, e < Entry.yCount → memory.ram (word (Layout.hintCell 1 e)) = word 0)
    (zero : memory.ram (word Layout.zeroJoin) = word 0)
    (v : Nat) (labelsOf : Nat → Block)
    (coordVal : memory.ram (word (Machine.coordCellOf 1)) = word v)
    (labelCells : ∀ j, j < 254 → memory.ram (word (labelBase + 254 * 1 + j)) = blockWord (labelsOf j)) :
    Machine.CoordReads 1 Entry.yCount (convOf (publish s).crtY) (fun e => ((publish s).recY.get e).val) v
      labelsOf memory := by
  have conv := holds.conv ⟨1, by decide⟩
  rw [← convPub_one s]
  exact
    { coordVal := coordVal
      labelCells := labelCells
      chunkJoins := chunkJoins memory.ram s 1 (by decide) zero
      chunkPins := chunkPins memory.ram s 1 (by decide) conv
      stageJoins0 := stageJoins0 memory.ram s 1 (by decide) conv
      stageJoins1 := stageJoins1 memory.ram s 1 (by decide) conv
      stagePins0 := stagePins0 memory.ram s 1 (by decide) conv
      stagePins1 := stagePins1 memory.ram s 1 (by decide) conv
      growJoins := growJoins memory.ram s 1 (by decide) conv
      foldJoins := foldJoins memory.ram s 1 (by decide) conv
      residues := residuesY memory.ram s holds digits
      hints := hintsY memory.ram s hints }

/-! ### On the extracted source -/

variable [FieldCertificate]

/-- `coordReadsX` for the source stage 1 leaves in RAM (`CrtSource.extract`). -/
theorem coordReadsX_extract (memory : Memory) (valid : CrtSource.CellsValid memory.ram)
    (hints : ∀ e, e < Entry.xCount → memory.ram (word (Layout.hintCell 0 e)) = word 0)
    (zero : memory.ram (word Layout.zeroJoin) = word 0)
    (v : Nat) (labelsOf : Nat → Block)
    (coordVal : memory.ram (word (Machine.coordCellOf 0)) = word v)
    (labelCells : ∀ j, j < 254 → memory.ram (word (labelBase + 254 * 0 + j)) = blockWord (labelsOf j)) :
    Machine.CoordReads 0 Entry.xCount (convOf (publish (CrtSource.extract memory.ram)).crtX)
      (fun e => ((publish (CrtSource.extract memory.ram)).recX.get e).val) v labelsOf memory :=
  coordReadsX _ memory (CrtSource.sourceHolds_extract _ valid) (CrtSource.digitsSmall_of_valid _ valid) hints zero
    v labelsOf coordVal labelCells

/-- `coordReadsY` for the source stage 1 leaves in RAM (`CrtSource.extract`). -/
theorem coordReadsY_extract (memory : Memory) (valid : CrtSource.CellsValid memory.ram)
    (hints : ∀ e, e < Entry.yCount → memory.ram (word (Layout.hintCell 1 e)) = word 0)
    (zero : memory.ram (word Layout.zeroJoin) = word 0)
    (v : Nat) (labelsOf : Nat → Block)
    (coordVal : memory.ram (word (Machine.coordCellOf 1)) = word v)
    (labelCells : ∀ j, j < 254 → memory.ram (word (labelBase + 254 * 1 + j)) = blockWord (labelsOf j)) :
    Machine.CoordReads 1 Entry.yCount (convOf (publish (CrtSource.extract memory.ram)).crtY)
      (fun e => ((publish (CrtSource.extract memory.ram)).recY.get e).val) v labelsOf memory :=
  coordReadsY _ memory (CrtSource.sourceHolds_extract _ valid) (CrtSource.digitsSmall_of_valid _ valid) hints zero
    v labelsOf coordVal labelCells

end SourceCells

end Kriterion.CRT.SimMachine
