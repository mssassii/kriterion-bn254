/-
**The valid arm's start**: `CrtValid.ValidStart` from what stage 1 leaves in RAM and
the stage-2 prefix's run on a defined output.

The prefix (release-r1's `Request.prefixProgram`, `memSem_prefix`) writes only the request cells (the input, the
output tags and `Q`) and the label region (label `i` is the key cell `keyBase + 2 i + bit i`); every other cell of the
retained memory is unchanged (`prefix_keeps`). So the valid arm reads, on the memory the prefix leaves:

* the stage-1 source through `CrtSource.extract` (unchanged cells, `readDraw_keeps`, `cellsValid_keeps`), hence the
  replay's `CoordReads` (`SourceCells.coordReads*_extract`), the curve and the row constants (`CrtSource.field_cell`);
* the request's input and output cells (`parsedRam`);
* the selected labels as blocks: the key cells hold `Z` and `Z ⊕ Δ` below `2^128` (`KeyCellsHold`, `label_cell`).

`validStart_of_prefix` states this for one retained memory; `validStart_of_support` for every stage-1 result, from a
stage-1 support premise (`Stage1Holds … Retained`); `stage2_some_validStart` joins it to `CrtStage2Start`'s
`machine_stage2_some`: on a defined output the machine's stage 2 is the valid arm from a memory where the start holds.
-/

import Proof.Simulator.CRT.Stage2Valid
import Proof.Simulator.CRT.Stage2Start
import Proof.Simulator.CRT.Stage2Invalid
import Proof.Simulator.CRT.SourceCells

namespace Kriterion.CRT.SimMachine

namespace CrtValidStart

open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine
open CrtStage2Invalid (KeyCellsHold label_extract)

noncomputable section

/-! ### What stage 1 leaves -/

/-- **The stage-1 facts the valid arm's start needs** (`CrtStage1Retained.Retained`, field for
field): the stage-1 cells in range, the hint cells zero, the key cells `Z` and `Z ⊕ Δ`, and `Z`, `Δ` below `2^128`. -/
structure Retained (memory : Memory) : Prop where
  cells : CrtSource.CellsValid memory.ram
  hints : ∀ κ, κ < 2 → ∀ e, e < CrtStage1.encCount κ → memory.ram (word (Layout.hintCell κ e)) = word 0
  keys : ∀ j, j < labelCount → memory.ram (word (keyBase + 2 * j + 1)) =
    memory.ram (word (keyBase + 2 * j)) ^^^ memory.ram (word (Layout.deltaCell (j / 254)))
  zerosSmall : ∀ j, j < labelCount → (memory.ram (word (keyBase + 2 * j))).toNat < 2 ^ 128
  deltasSmall : ∀ κ, κ < 2 → (memory.ram (word (Layout.deltaCell κ))).toNat < 2 ^ 128

theorem pure_some_inj {α : Type} {a b : α} (same : (PMF.pure (some a) : PMF (Option α)) = PMF.pure (some b)) :
    a = b := by
  have supports := congrArg PMF.support same
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff, Option.some.injEq] at supports
  exact supports

/-- A word below `2^128` is the block word of its low block. -/
theorem blockWord_low (value : Word) (small : value.toNat < 2 ^ 128) :
    value = blockWord (BitVec.ofNat 128 value.toNat) := by
  apply BitVec.eq_of_toNat_eq
  unfold blockWord
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega)]

section Labels

variable [FieldCertificate]

/-- **A selected key cell is the block word of the label** `Entry.labels` of the extracted source. -/
theorem label_cell (memory : Memory) (retained : Retained memory) (input : AffineInput) (i : Nat)
    (bound : i < 508) :
    memory.ram (word (keyBase + 2 * i + inputBit input.x.val input.y.val i)) =
      blockWord ((Kriterion.CRT.Entry.labels (CrtSource.extract memory.ram) input)[i]) := by
  rw [← label_extract memory.ram retained.keys input i bound]
  refine blockWord_low _ ?_
  have bitLe := inputBit_le input.x.val input.y.val i
  rcases (show inputBit input.x.val input.y.val i = 0 ∨ inputBit input.x.val input.y.val i = 1 by omega)
    with zero | one
  · rw [zero, Nat.add_zero]
    exact retained.zerosSmall i (by unfold labelCount; omega)
  · rw [one, retained.keys i (by unfold labelCount; omega), BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow (retained.zerosSmall i (by unfold labelCount; omega))
      (retained.deltasSmall _ (by omega))

omit [FieldCertificate] in
theorem labelX_get (labels : LamportSignature) (j : Nat) (low : j < 254) :
    Kriterion.CRT.Entry.labelX labels j = labels[j] := by
  unfold Kriterion.CRT.Entry.labelX
  simp [Array.getD, show j < 508 by omega]

omit [FieldCertificate] in
theorem labelY_get (labels : LamportSignature) (j : Nat) (low : j < 254) :
    Kriterion.CRT.Entry.labelY labels j = labels[254 + j] := by
  unfold Kriterion.CRT.Entry.labelY
  simp [Array.getD, coordinateBitCount, show 254 + j < 508 by omega]

end Labels

/-! ### The prefix's effect -/

section Prefix

variable [FieldCertificate]

/-- A cell off the request cells and the label region. -/
def Kept (n : Nat) : Prop :=
  n < 2 ^ 256 ∧ ¬ (requestBase ≤ n ∧ n < requestBase + 6) ∧ ¬ (labelBase ≤ n ∧ n < labelBase + labelCount)

/-- **What the prefix of a defined output leaves**: every kept cell unchanged, the request's input and output
cells, the selected labels, an empty response stack. -/
theorem prefix_keeps (memory middle : Memory) (input : AffineInput) (target : Point)
    (run : Request.prefixProgram.memSem (CrtStage2Start.stage2Start memory input (some target)) =
      PMF.pure (some middle)) :
    (∀ n, Kept n → middle.ram (word n) = memory.ram (word n)) ∧
      middle.ram (word reqX) = word input.x.val ∧ middle.ram (word reqY) = word input.y.val ∧
      (middle.ram (word reqTag0), middle.ram (word reqQX), middle.ram (word reqQY)) = outputWords target ∧
      (∀ i, i < 508 → middle.ram (word (labelBase + i)) =
        memory.ram (word (keyBase + 2 * i + inputBit input.x.val input.y.val i))) ∧
      middle.bits 3 = [] := by
  obtain ⟨after, runAfter, bitsAfter, labels, away, _⟩ := memSem_prefix
    (CrtStage2Start.stage2Start memory input (some target)) input.x.val input.y.val (coord_small _)
    (coord_small _) (SimulatorProtocol.output (some target)) (outTags target).1 (outTags target).2.1
    (outTags target).2.2.1 (outTags target).2.2.2 (outTags_bits target)
    (afterTag_request memory input (some target))
  have same : after = middle := pure_some_inj (runAfter.symm.trans run)
  subst same
  have startRam : (CrtStage2Start.stage2Start memory input (some target)).ram = memory.ram :=
    afterTag_ram memory input (some target)
  have parsed : ∀ n, n < 2 ^ 256 → ¬ (labelBase ≤ n ∧ n < labelBase + labelCount) →
      after.ram (word n) = parsedRam memory.ram input.x.val input.y.val (outTags target).1
        (outTags target).2.1 (outTags target).2.2.1 (outTags target).2.2.2 (word n) := by
    intro n small outside
    rw [away _ fun position bound => word_ne small (by unfold labelBase labelCount at *; omega)
      (by unfold labelBase labelCount at *; omega), startRam]
  refine ⟨fun n kept => ?_, ?_, ?_, ?_, fun i bound => ?_, ?_⟩
  · obtain ⟨small, offRequest, offLabels⟩ := kept
    rw [parsed n small offLabels, parsedRam_off _ _ _ _ _ _ _ _ fun offset inside =>
      word_ne small (by unfold requestBase; omega) (by omega)]
  · rw [parsed reqX (by unfold reqX requestBase; norm_num)
      (by unfold reqX requestBase labelBase; norm_num), parsedRam_x]
  · rw [parsed reqY (by unfold reqY requestBase; norm_num)
      (by unfold reqY requestBase labelBase; norm_num), parsedRam_y]
  · rw [outTags_words, parsed reqTag0 (by unfold reqTag0 requestBase; norm_num)
      (by unfold reqTag0 requestBase labelBase; norm_num),
      parsed reqQX (by unfold reqQX requestBase; norm_num) (by unfold reqQX requestBase labelBase; norm_num),
      parsed reqQY (by unfold reqQY requestBase; norm_num) (by unfold reqQY requestBase labelBase; norm_num),
      parsedRam_tag0, parsedRam_qx, parsedRam_qy]
  · rw [labels i bound, startRam]
  · rw [bitsAfter, Function.update_of_ne (by decide)]
    exact afterTag_response memory input (some target)

omit [FieldCertificate] in
/-- The stage-1 draws read from two RAMs that agree on the kept cells are the same. -/
theorem readDraw_keeps (ram ram' : Word → Word) (agree : ∀ n, Kept n → ram (word n) = ram' (word n)) :
    CrtStored.readDraw ram = CrtStored.readDraw ram' := by
  have kept : ∀ n, n < 2 ^ 256 → (n < requestBase ∨ labelBase + labelCount ≤ n) → Kept n := by
    intro n small side
    refine ⟨small, ?_, ?_⟩ <;> unfold requestBase labelBase labelCount at * <;> omega
  unfold CrtStored.readDraw
  congr 1
  · funext index
    have := index.isLt
    rw [agree _ (kept _ (by unfold fieldBase CrtStage1.fieldCount curveCellCount rowCellCount at *; omega)
      (Or.inl (by unfold fieldBase requestBase CrtStage1.fieldCount curveCellCount rowCellCount at *; omega)))]
  · funext n
    have := n.isLt
    rw [agree _ (kept _ (by unfold exceptionBase exceptionByteCount at *; omega)
      (Or.inl (by unfold exceptionBase requestBase exceptionByteCount at *; omega)))]
  · funext n
    have := CrtStored.joinAddr_range n.val n.isLt
    rw [agree _ (kept _ (by omega) (Or.inr (by unfold labelBase labelCount; omega)))]
  · funext n
    have := CrtStored.pinAddr_range n.val n.isLt
    rw [agree _ (kept _ (by omega) (Or.inr (by unfold labelBase labelCount; omega)))]
  · funext n
    have := CrtStored.digitAddr_range n.val n.isLt
    rw [agree _ (kept _ (by omega) (Or.inr (by unfold labelBase labelCount; omega)))]
  · funext j
    have := j.isLt
    rw [agree _ (kept _ (by unfold keyBase labelCount at *; omega)
      (Or.inr (by unfold keyBase labelBase labelCount at *; omega)))]
  · funext κ
    have := κ.isLt
    rw [agree _ (kept _ (by unfold Layout.deltaCell; omega)
      (Or.inr (by unfold Layout.deltaCell labelBase labelCount; omega)))]

omit [FieldCertificate] in
/-- The stage-1 cells are in range on a RAM that agrees on the kept cells. -/
theorem cellsValid_keeps (ram ram' : Word → Word) (agree : ∀ n, Kept n → ram (word n) = ram' (word n))
    (valid : CrtSource.CellsValid ram') : CrtSource.CellsValid ram := by
  have kept : ∀ n, n < 2 ^ 256 → (n < requestBase ∨ labelBase + labelCount ≤ n) → Kept n := by
    intro n small side
    refine ⟨small, ?_, ?_⟩ <;> unfold requestBase labelBase labelCount at * <;> omega
  refine ⟨fun index inside => ?_, fun n inside => ?_, fun n inside => ?_, fun n inside => ?_, fun n inside => ?_⟩
  · rw [agree _ (kept _ (by unfold fieldBase CrtStage1.fieldCount curveCellCount rowCellCount at *; omega)
      (Or.inl (by unfold fieldBase requestBase CrtStage1.fieldCount curveCellCount rowCellCount at *; omega)))]
    exact valid.fields index inside
  · rw [agree _ (kept _ (by unfold exceptionBase exceptionByteCount at *; omega)
      (Or.inl (by unfold exceptionBase requestBase exceptionByteCount at *; omega)))]
    exact valid.bytes n inside
  · have := CrtStored.joinAddr_range n inside
    rw [agree _ (kept _ (by omega) (Or.inr (by unfold labelBase labelCount; omega)))]
    exact valid.joins n inside
  · have := CrtStored.pinAddr_range n inside
    rw [agree _ (kept _ (by omega) (Or.inr (by unfold labelBase labelCount; omega)))]
    exact valid.pins n inside
  · have := CrtStored.digitAddr_range n inside
    rw [agree _ (kept _ (by omega) (Or.inr (by unfold labelBase labelCount; omega)))]
    exact valid.digits n inside

end Prefix

/-! ### The valid arm's start -/

section Start

variable [FieldCertificate]

omit [FieldCertificate] in
/-- A published row constant is the source's. -/
theorem gammaOf_publish (src : Kriterion.CRT.Entry.Source) (d : Fin digitCount) :
    Kriterion.CRT.Entry.gammaOf (Kriterion.CRT.Entry.publish src) d = src.rows d := by
  show (Vector.ofFn src.rows).get d = src.rows d
  rw [Vector.get_eq_getElem, Vector.getElem_ofFn]

omit [FieldCertificate] in
/-- The row cell `3 + 4 d + slot` of the stage-1 field cells. -/
theorem fieldOf_row (src : Kriterion.CRT.Entry.Source) (d : Fin 91) (slot : Nat) (small : slot < 4) :
    CrtPieces.fieldOf src (3 + 4 * d.val + slot) = CrtWire.rowField (src.rows d) slot := by
  have dSmall := d.isLt
  unfold CrtPieces.fieldOf
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  congr 2
  · exact Fin.ext (by simp only; omega)
  · omega

/-- **The valid arm's start** from a retained memory and the prefix's run on a defined output. -/
theorem validStart_of_prefix (memory middle : Memory) (retained : Retained memory) (input : AffineInput)
    (target : Point)
    (run : Request.prefixProgram.memSem (CrtStage2Start.stage2Start memory input (some target)) =
      PMF.pure (some middle)) :
    CrtValid.ValidStart (Kriterion.CRT.Entry.publish (CrtSource.extract memory.ram)) input
      (Kriterion.CRT.Entry.labels (CrtSource.extract memory.ram) input) target middle := by
  obtain ⟨keeps, xCell, yCell, outCells, labelCells, empty⟩ := prefix_keeps memory middle input target run
  have sourceEq : CrtSource.extract middle.ram = CrtSource.extract memory.ram := by
    unfold CrtSource.extract
    rw [readDraw_keeps middle.ram memory.ram keeps]
  have valid : CrtSource.CellsValid middle.ram := cellsValid_keeps middle.ram memory.ram keeps retained.cells
  have rb : requestBase = 2 ^ 43 := rfl
  have lb : labelBase = 2 ^ 44 := rfl
  have lc : labelCount = 508 := rfl
  have fb : fieldBase = 2 ^ 40 := rfl
  have fc : CrtStage1.fieldCount = 367 := rfl
  have keptLow : ∀ n, n < requestBase → Kept n := by
    intro n small
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  have keptHigh : ∀ n, n < 2 ^ 256 → labelBase + labelCount ≤ n → Kept n := by
    intro n small high
    refine ⟨small, ?_, ?_⟩ <;> omega
  have hints : ∀ κ e, κ < 2 → e < CrtStage1.encCount κ → middle.ram (word (Layout.hintCell κ e)) = word 0 := by
    intro κ e hκ he
    have eSmall : e < 512 := by
      unfold CrtStage1.encCount at he
      split at he <;> simp only [Kriterion.CRT.Entry.xCount, Kriterion.CRT.Entry.yCount] at he <;> omega
    rw [keeps _ (keptHigh _ (by unfold Layout.hintCell; omega) (by unfold Layout.hintCell; omega))]
    exact retained.hints κ hκ e he
  have labelAt : ∀ i (bound : i < 508), middle.ram (word (labelBase + i)) =
      blockWord ((Kriterion.CRT.Entry.labels (CrtSource.extract memory.ram) input)[i]) := fun i bound =>
    (labelCells i bound).trans (label_cell memory retained input i bound)
  have field : ∀ index, index < CrtStage1.fieldCount →
      middle.ram (word (fieldBase + index)) =
        fieldWord (CrtPieces.fieldOf (CrtSource.extract memory.ram) index) := by
    intro index inside
    rw [keeps _ (keptLow _ (by omega))]
    exact CrtSource.field_cell memory.ram retained.cells index inside
  refine
    { readsX := ?_, readsY := ?_, reqXCell := xCell, reqYCell := yCell, c0Cell := ?_, c1Cell := ?_, c2Cell := ?_,
      outputCells := outCells, rowCells := fun d => ?_, labelCells := labelAt, empty := empty }
  · have reads := SourceCells.coordReadsX_extract middle valid (fun e he => hints 0 e (by decide) he)
      input.x.val (Kriterion.CRT.Entry.labelX (Kriterion.CRT.Entry.labels (CrtSource.extract memory.ram) input))
      xCell (fun j low => by
        rw [labelX_get _ j low, Nat.mul_zero, Nat.add_zero]
        exact labelAt j (by omega))
    rw [sourceEq] at reads
    exact reads
  · have reads := SourceCells.coordReadsY_extract middle valid (fun e he => hints 1 e (by decide) he)
      input.y.val (Kriterion.CRT.Entry.labelY (Kriterion.CRT.Entry.labels (CrtSource.extract memory.ram) input))
      yCell (fun j low => by
        rw [labelY_get _ j low, Nat.mul_one, Nat.add_assoc]
        exact labelAt (254 + j) (by omega))
    rw [sourceEq] at reads
    exact reads
  · rw [show fieldBase = fieldBase + 0 from rfl, field 0 (by decide)]
    rfl
  · exact field 1 (by decide)
  · exact field 2 (by decide)
  · have dSmall := d.isLt
    have cell : ∀ slot, slot < 4 → middle.ram (word (Opening.rowCell d.val slot)) =
        fieldWord (CrtPieces.fieldOf (CrtSource.extract memory.ram) (3 + 4 * d.val + slot)) := by
      intro slot small
      rw [show Opening.rowCell d.val slot = fieldBase + (3 + 4 * d.val + slot) by
          unfold Opening.rowCell curveCellCount; omega,
        field _ (by omega)]
    rw [cell 0 (by decide), cell 1 (by decide), cell 2 (by decide), cell 3 (by decide)]
    generalize CrtSource.extract memory.ram = src
    rw [gammaOf_publish src d, fieldOf_row src d 0 (by decide), fieldOf_row src d 1 (by decide),
      fieldOf_row src d 2 (by decide), fieldOf_row src d 3 (by decide)]
    exact ⟨rfl, rfl, rfl, rfl⟩

end Start

/-! ### On the stage-1 support -/

section Support

variable (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)

/-- **The valid arm's start on the stage-1 support**: at `Stage2Law`'s binders and instances, for every stage-1 result
of the machine, input, target and memory `middle` the prefix leaves on the output `some target`, the valid arm's start
holds at the extracted source, from the support predicate (`retainedOf`). -/
theorem validStart_of_support
    (retainedOf : CrtStage2Invalid.Stage1Holds Privacy.Instance.crtEntry (CrtTop.machine s1 r replay within)
      Retained)
    (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) :
    letI := Fintype.ofFinite Empty
    letI := Fintype.ofFinite Empty
    letI := Classical.decEq Empty
    letI := Classical.decEq Empty
    ∀ result, some result ∈ ((LawShape.machineAbstract (FI := Empty) (EI := Empty)
        Privacy.Instance.crtEntry.encoding Privacy.Instance.crtEntry.bytes (CrtTop.machine s1 r replay within)).stage1
        parameter LazyOracle.empty).support →
      ∀ (input : AffineInput) (target : Point) (middle : Memory),
        Request.prefixProgram.memSem (CrtStage2Start.stage2Start result.2.1.memory input (some target)) =
          PMF.pure (some middle) →
        CrtValid.ValidStart (Kriterion.CRT.Entry.publish (CrtSource.extract result.2.1.memory.ram)) input
          (Kriterion.CRT.Entry.labels (CrtSource.extract result.2.1.memory.ram) input) target middle := by
  intro result member input target middle run
  exact validStart_of_prefix result.2.1.memory middle (retainedOf field group parameter result member) input target
    run

/-- **Stage 2 on a defined output, with its start**: on the stage-1 support the machine's stage 2 is the valid arm
from the memory `middle` the prefix leaves, followed by the parse, and the valid arm's start holds at `middle`
(`CrtStage2Start.machine_stage2_some` with `validStart_of_support`). -/
theorem stage2_some_validStart (sizeR : r.size = replay.size) (costR : r.cost = replay.cost)
    (retainedOf : CrtStage2Invalid.Stage1Holds Privacy.Instance.crtEntry (CrtTop.machine s1 r replay within)
      Retained)
    (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) :
    letI := Fintype.ofFinite Empty
    letI := Fintype.ofFinite Empty
    letI := Classical.decEq Empty
    letI := Classical.decEq Empty
    ∀ result, some result ∈ ((LawShape.machineAbstract (FI := Empty) (EI := Empty)
        Privacy.Instance.crtEntry.encoding Privacy.Instance.crtEntry.bytes (CrtTop.machine s1 r replay within)).stage1
        parameter LazyOracle.empty).support →
      ∀ (input : AffineInput) (target : Point) (oracle : OState Empty Empty), ∃ middle : Memory,
        (LawShape.machineAbstract (FI := Empty) (EI := Empty) Privacy.Instance.crtEntry.encoding
            Privacy.Instance.crtEntry.bytes (CrtTop.machine s1 r replay within)).stage2
            result.2.1 input (some target) oracle =
          ((CrtTop.validArm replay).sem middle oracle).bind CrtValid.finishK ∧
        CrtValid.ValidStart (Kriterion.CRT.Entry.publish (CrtSource.extract result.2.1.memory.ram)) input
          (Kriterion.CRT.Entry.labels (CrtSource.extract result.2.1.memory.ram) input) target middle := by
  intro result member input target oracle
  obtain ⟨middle, run, stage2⟩ := @CrtStage2Start.machine_stage2_some field Empty Empty (Fintype.ofFinite Empty)
    (Fintype.ofFinite Empty) (Classical.decEq Empty) (Classical.decEq Empty) s1 r replay within sizeR costR
    result.2.1 input target oracle _ Privacy.Instance.crtEntry.encoding Privacy.Instance.crtEntry.bytes
  exact ⟨middle, stage2,
    validStart_of_support s1 r replay within retainedOf field group parameter result member input target middle run⟩

end Support

end

end CrtValidStart

end Kriterion.CRT.SimMachine
