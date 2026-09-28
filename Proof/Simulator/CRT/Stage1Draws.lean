/-
**Stage 1's draws** (M2): the sampling blocks of `CrtStage1.program` are independent draws, and the program is the
draws followed by its deterministic tail (the true labels, the wire, the clears).

* `Draw`, `drawLaw`: the field cells, the exception nibbles, the joins, the pin lanes, the records' digits, the zero
  labels, the offsets and the sign bits, each block an `optionProduct` of its cell laws (flat indices as
  `memSem_rep_nest` makes them);
* `storedMem`: the memory after the draws, a fold of stores per block;
* `program_law`: `program.memSem memory = optBind drawLaw fun d => tail.memSem (storedMem memory d)`.
-/

import Proof.Simulator.CRT.Stage1Cells
import Proof.Simulator.OpeningPreimage

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.ArgoMAC.Phase3.Glue (optionProduct)
open Kriterion.CRT.Entry (joinCount pinCount)
open CrtStage1

namespace CrtDraws

noncomputable section

/-! ### Option binds -/

/-- A bind of abort-or-value laws: an abort aborts. -/
def optBind {α β : Type} (law : PMF (Option α)) (next : α → PMF (Option β)) : PMF (Option β) :=
  law.bind fun drawn => match drawn with
    | none => PMF.pure none
    | some value => next value

theorem optBind_assoc {α β γ : Type} (law : PMF (Option α)) (next : α → PMF (Option β))
    (last : β → PMF (Option γ)) :
    optBind (optBind law next) last = optBind law fun value => optBind (next value) last := by
  unfold optBind
  rw [PMF.bind_bind]
  congr 1
  funext drawn
  cases drawn with
  | none => simp
  | some value => rfl

theorem optBind_pure {α β : Type} (value : α) (next : α → PMF (Option β)) :
    optBind (PMF.pure (some value)) next = next value := by
  simp [optBind]

variable [FieldCertificate]

theorem memSem_seq_law {α : Type} (block rest : Prog) (law : PMF (Option α)) (store : α → Memory)
    (memory : Memory) (blockLaw : block.memSem memory = law.map (Option.map store)) :
    (Prog.seq block rest).memSem memory = optBind law fun value => rest.memSem (store value) := by
  rw [memSem_seq, blockLaw, PMF.bind_map]
  unfold optBind
  congr 1
  funext drawn
  cases drawn <;> rfl

/-! ### Cell laws and stores -/

/-- A digit below `m`. -/
def digitLaw (m : Nat) : PMF (Option Nat) := rejectLaw (digitWidth m) (fun value => decide (value < m)) attempts

/-- The store of a word of `width` coins at `address`. -/
def wordStore (address : Nat) (memory : Memory) (value : Nat) : Memory :=
  clearRegs (storeRam memory (word address) (BitVec.ofNat 256 value)) [rAcc, rBit, rAddr]

/-- The store of a bounded cell at `address`. -/
def cellStore (address : Nat) (memory : Memory) (value : Nat) : Memory :=
  clearRegs (storeRam memory (word address) (BitVec.ofNat 256 value)) samplerScratch

/-- **Word cells at any addresses and widths.** -/
theorem memSem_wordCells (count : Nat) (width address : Nat → Nat) (small : ∀ n, width n ≤ 256)
    (memory : Memory) :
    (Prog.rep count fun n => Stage1.wordCell (width n) (address n)).memSem memory =
      (optionProduct count fun n => (wordLaw (width n.val)).map some).map
        (Option.map (foldStore (fun n => wordStore (address n)) count memory)) :=
  memSem_rep_law_idx (fun _ => True) count (fun n => (wordLaw (width n)).map some) _
    (fun n => wordStore (address n))
    (fun n _ memory _ => by
      rw [memSem_wordCell (width n) (address n) (small n), PMF.map_comp]
      rfl)
    (fun _ _ _ _ _ => trivial) memory trivial

/-- **Digit cells.** -/
theorem memSem_digitCells (count : Nat) (modulus address : Nat → Nat)
    (small : ∀ n, digitWidth (modulus n) ≤ 256 ∧ modulus n < 2 ^ 256) (memory : Memory) :
    (Prog.rep count fun n => digitCell (modulus n) (address n)).memSem memory =
      (optionProduct count fun n => digitLaw (modulus n.val)).map
        (Option.map (foldStore (fun n => cellStore (address n)) count memory)) :=
  memSem_rep_law_idx (fun _ => True) count (fun n => digitLaw (modulus n)) _ (fun n => cellStore (address n))
    (fun n _ memory _ => by
      rw [show digitCell (modulus n) (address n) = Prog.seq (bounded (digitWidth (modulus n))
          (testBelow (modulus n)) attempts (storeAt (address n) rOut)) (zeroRegs samplerScratch) from rfl,
        CrtCells.memSem_boundedCell _ _ _ (small n).1 (small n).2]
      rfl)
    (fun _ _ _ _ _ => trivial) memory trivial

/-- **Field cells** (release-r1's). -/
theorem memSem_fieldCells (memory : Memory) :
    fields.memSem memory =
      (optionProduct fieldCount fun _ => fieldCellLaw).map
        (Option.map (foldStore (cellStep fieldBase) fieldCount memory)) :=
  memSem_fields fieldBase fieldCount memory

/-! ### The draws -/

omit [FieldCertificate] in
/-- **The stage-1 draws.** -/
structure Draw where
  fields : Fin fieldCount → BaseField
  bytes : Fin exceptionCellCount → Nat
  joins : Fin (2 * joinCount) → Nat
  pins : Fin (2 * (pinCount * laneCount)) → Nat
  digits : Fin (recordCount * moduliCount) → Nat
  zeros : Fin labelCount → Nat
  deltas : Fin 2 → Nat
  signs : Fin 91 → Nat

def signsLaw : PMF (Option (Fin 91 → Nat)) := optionProduct 91 fun _ => (wordLaw 1).map some
def fieldsLaw : PMF (Option (Fin fieldCount → BaseField)) := optionProduct fieldCount fun _ => fieldCellLaw
def bytesLaw : PMF (Option (Fin exceptionCellCount → Nat)) :=
  optionProduct exceptionCellCount fun _ => (wordLaw 4).map some
def joinsLaw : PMF (Option (Fin (2 * joinCount) → Nat)) := optionProduct (2 * joinCount) fun _ => (wordLaw labelBits).map some
def pinsLaw : PMF (Option (Fin (2 * (pinCount * laneCount)) → Nat)) :=
  optionProduct (2 * (pinCount * laneCount)) fun n => (wordLaw (pinWidthAt (pinOf n.val))).map some
def digitsLaw : PMF (Option (Fin (recordCount * moduliCount) → Nat)) :=
  optionProduct (recordCount * moduliCount) fun n => digitLaw (modulusAt (n.val % moduliCount))
def zerosLaw : PMF (Option (Fin labelCount → Nat)) := optionProduct labelCount fun _ => (wordLaw 128).map some
def deltasLaw : PMF (Option (Fin 2 → Nat)) := optionProduct 2 fun _ => (wordLaw 128).map some

/-- **The law of the draws.** -/
def drawLaw : PMF (Option Draw) :=
  optBind fieldsLaw fun f => optBind bytesLaw fun b => optBind joinsLaw fun j => optBind pinsLaw fun p =>
    optBind digitsLaw fun d => optBind zerosLaw fun z => optBind deltasLaw fun dl => optBind signsLaw fun sg =>
      PMF.pure (some ⟨f, b, j, p, d, z, dl, sg⟩)

/-- The address of join word `n`. -/
def joinAddr (n : Nat) : Nat := Layout.sourceJoin (n / joinCount) (n % joinCount)
/-- The address of lane word `n`. -/
def pinAddr (n : Nat) : Nat := Layout.sourcePin (pinCoord n) (pinOf n) (n % laneCount)
/-- The address of digit `n`. -/
def digitAddr (n : Nat) : Nat :=
  Layout.residueCell (recordCoord (n / moduliCount)) (n % moduliCount) (recordIndex (n / moduliCount))

/-- **The memory after the draws.** -/
def storedMem (memory : Memory) (d : Draw) : Memory :=
  foldStore (fun n => wordStore (Layout.signCell n)) 91
    (foldStore (fun n => wordStore (Layout.deltaCell n)) 2
      (foldStore (fun n => wordStore (keyBase + 2 * n)) labelCount
        (foldStore (fun n => cellStore (digitAddr n)) (recordCount * moduliCount)
          (foldStore (fun n => wordStore (pinAddr n)) (2 * (pinCount * laneCount))
            (foldStore (fun n => wordStore (joinAddr n)) (2 * joinCount)
              (foldStore (wordStep exceptionBase) exceptionCellCount
                (foldStore (cellStep fieldBase) fieldCount memory d.fields) d.bytes) d.joins) d.pins) d.digits)
        d.zeros) d.deltas) d.signs

/-- The deterministic tail: the wire, the true labels, the clears. -/
def tail : Prog := Prog.seqList [serialize, keyTrue, clearLimbs, zeroRegs allRegisters]

theorem pinWidthAt_small (k : Nat) : pinWidthAt k ≤ 256 := le_trans (CrtSerial.pinWidthAt_le k) (by norm_num)

theorem digitWidth_small_fin : ∀ i : Fin 85, digitWidth (modulusAt i) ≤ 256 ∧ modulusAt i < 2 ^ 256 := by
  decide +kernel

theorem digitWidth_small (n : Nat) : digitWidth (modulusAt (n % moduliCount)) ≤ 256 ∧
    modulusAt (n % moduliCount) < 2 ^ 256 :=
  digitWidth_small_fin ⟨n % moduliCount, Nat.mod_lt _ (by decide)⟩

theorem seq_signs (rest : Prog) (memory : Memory) :
    (Prog.seq signs rest).memSem memory =
      optBind signsLaw fun sg => rest.memSem (foldStore (fun n => wordStore (Layout.signCell n)) 91 memory sg) :=
  memSem_seq_law _ _ _ _ _ (memSem_wordCells 91 (fun _ => 1) Layout.signCell (fun _ => by norm_num) memory)

theorem seq_fields (rest : Prog) (memory : Memory) :
    (Prog.seq fields rest).memSem memory =
      optBind fieldsLaw fun f => rest.memSem (foldStore (cellStep fieldBase) fieldCount memory f) :=
  memSem_seq_law _ _ _ _ _ (memSem_fieldCells memory)

theorem seq_bytes (rest : Prog) (memory : Memory) :
    (Prog.seq bytes rest).memSem memory =
      optBind bytesLaw fun b => rest.memSem (foldStore (wordStep exceptionBase) exceptionCellCount memory b) :=
  memSem_seq_law _ _ _ _ _ (memSem_words 4 exceptionBase exceptionCellCount (by norm_num) memory)

theorem seq_joins (rest : Prog) (memory : Memory) :
    (Prog.seq joins rest).memSem memory =
      optBind joinsLaw fun j => rest.memSem (foldStore (fun n => wordStore (joinAddr n)) (2 * joinCount) memory j) :=
  memSem_seq_law _ _ _ _ _ (memSem_wordCells (2 * joinCount) (fun _ => labelBits) joinAddr (fun _ => by norm_num) memory)

theorem seq_pins (rest : Prog) (memory : Memory) :
    (Prog.seq pins rest).memSem memory =
      optBind pinsLaw fun p =>
        rest.memSem (foldStore (fun n => wordStore (pinAddr n)) (2 * (pinCount * laneCount)) memory p) :=
  memSem_seq_law _ _ _ _ _ (memSem_wordCells (2 * (pinCount * laneCount)) (fun n => pinWidthAt (pinOf n)) pinAddr
    (fun n => pinWidthAt_small _) memory)

theorem seq_digits (rest : Prog) (memory : Memory) :
    (Prog.seq digits rest).memSem memory =
      optBind digitsLaw fun d =>
        rest.memSem (foldStore (fun n => cellStore (digitAddr n)) (recordCount * moduliCount) memory d) :=
  memSem_seq_law _ _ _ _ _ (memSem_digitCells (recordCount * moduliCount) (fun n => modulusAt (n % moduliCount))
    digitAddr digitWidth_small memory)

theorem seq_zeros (rest : Prog) (memory : Memory) :
    (Prog.seq zeros rest).memSem memory =
      optBind zerosLaw fun z => rest.memSem (foldStore (fun n => wordStore (keyBase + 2 * n)) labelCount memory z) :=
  memSem_seq_law _ _ _ _ _ (memSem_wordCells labelCount (fun _ => 128) (fun n => keyBase + 2 * n)
    (fun _ => by norm_num) memory)

theorem seq_deltas (rest : Prog) (memory : Memory) :
    (Prog.seq deltas rest).memSem memory =
      optBind deltasLaw fun dl => rest.memSem (foldStore (fun n => wordStore (Layout.deltaCell n)) 2 memory dl) :=
  memSem_seq_law _ _ _ _ _ (memSem_wordCells 2 (fun _ => 128) Layout.deltaCell (fun _ => by norm_num) memory)

/-- **The stage-1 program is the draws, then the tail.** -/
theorem program_law (memory : Memory) :
    program.memSem memory = optBind drawLaw fun d => tail.memSem (storedMem memory d) := by
  unfold program tail
  simp only [Prog.seqList]
  simp only [seq_fields, seq_bytes, seq_joins, seq_pins, seq_digits, seq_zeros, seq_deltas, seq_signs]
  simp only [drawLaw, optBind_assoc, optBind_pure]
  rfl

end

end CrtDraws

end Kriterion.CRT.SimMachine
