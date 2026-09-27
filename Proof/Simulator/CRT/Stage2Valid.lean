/-
**Stage 2's valid arm on the CRT machine** (the valid arm of `LawShape.Stage2Law`).

From a memory `middle` at the start of the valid arm that holds what the stage-1 source and the stage-2 prefix leave
(`ValidStart`: the two coordinates' reads of `Machine.agree_replay`, the request, the curve constants, the output
cells, the row constants, the label cells, an empty response stack), the valid arm
`seqList [Machine.replay, Design.rowsProgram, Solve.solve, Preimages.preimages, Programs.programs …,
Request.emitLabels]` followed by the protocol's parse (`finishK`) is route M's stage 2 at a defined output, with
the bounded samplers (`CrtBounded.samplers`: rows `CrtBounded.rows`, `preimageLaw`, the view's fourth
block) and the lazy reader (`valid_law`). Every sampler abort inside the arm (a tail point, the head clamp, a
randomiser, a preimage multiplier) is part of the equation.

* `valid_machine`: the arm is the replay's tree followed by the rest (release-r1's `sem_eq_runT`, with
  `TreeOps.treeOps_replay`);
* `rows_bind`: the rows program (release-r1's tail, Horner and head clamp, lambdas, lifts) followed by a continuation
  that reads only what the rows leave is `CrtBounded.rows` followed by the matching abstract continuation;
* `afterRows_law`: the collector solve, the preimages with their fourth blocks, the programs and the emission are the
  abstract `drawAll` and `programHashAll` (`Solve.exec_solve`, `OutCells.maskFormula_eq`,
  `Preimages.sem_preimagesPrograms`, `Preimages.drawAll_sites`, `Preimages.drawn_eq`);
* `continuation_law`: everything after the replay, from the replay's outputs in RAM (`OutCells.OutHolds`);
* `valid_law`: the composition with `Machine.agree_replay`, `agree_run` and `Lazy.runT_replayRouteM`.
-/

import Proof.Simulator.CRT.Finish
import Proof.Simulator.CRT.ReplayTreeOps
import Proof.Simulator.CRT.ReplayLazy
import Proof.Simulator.CRT.OutCells
import Proof.Simulator.CRT.Preimages
import Proof.Simulator.CRT.Bounded
import Proof.Simulator.OpeningLaw
import Construction.Simulator.CRT.Design

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit
open Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.ArgoMAC.PlanB (RowGamma)
open Kriterion.ArgoMAC.Phase3.Glue (optionProduct targetRows digitPoints)
open Kriterion.CRT.Privacy (ReplayOut lazyReader routeMReplay collectorMasks drawAll collectorList programHashAll
  programRequests)

noncomputable section

namespace CrtValid

/-! ### Abort-or-value binds and the parse -/

/-- Bind an abort-or-value law into an abort-or-value continuation. -/
def optBind {α γ : Type} (distribution : PMF (Option α)) (next : α → PMF (Option γ)) : PMF (Option γ) :=
  distribution.bind fun result => match result with
    | none => PMF.pure none
    | some value => next value

theorem optBind_bind {α γ δ : Type} (distribution : PMF (Option α)) (next : α → PMF (Option γ))
    (after : Option γ → PMF (Option δ)) (afterNone : after none = PMF.pure none) :
    (optBind distribution next).bind after = optBind distribution fun value => (next value).bind after := by
  unfold optBind
  rw [PMF.bind_bind]
  congr 1
  funext result
  cases result with
  | none => rw [PMF.pure_bind, afterNone]
  | some value => rfl

/-- A digit-indexed function read at a natural index (reduced mod 91). -/
def atFin {α : Type} (f : Fin 91 → α) (d : Nat) : α := f ⟨d % 91, Nat.mod_lt _ (by norm_num)⟩

theorem atFin_of_lt {α : Type} (f : Fin 91 → α) (d : Nat) (small : d < 91) : atFin f d = f ⟨d, small⟩ := by
  unfold atFin
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt small)

theorem atFin_val {α : Type} (f : Fin 91 → α) (d : Fin 91) : atFin f d.val = f d :=
  atFin_of_lt f d.val d.isLt

/-! ### Oracle-free and deterministic blocks -/

theorem noOracle_of_det : ∀ program : Prog, program.OpsSatisfy Op.Det → program.NoOracle
  | .op operation, det => by
      cases operation <;> first | exact (det : False).elim | rfl
  | .popBit _ _, _ => trivial
  | .skip _, _ => trivial
  | .abort _, _ => trivial
  | .seq first second, ⟨one, two⟩ => ⟨noOracle_of_det first one, noOracle_of_det second two⟩
  | .ite _ whenSet whenClear, ⟨one, two⟩ => ⟨noOracle_of_det whenSet one, noOracle_of_det whenClear two⟩

/-- The collector solve is deterministic. -/
theorem det_solve : Solve.solve.OpsSatisfy Op.Det :=
  det_rep _ _ fun d _ => by
    simp only [Solve.solveDigit, Solve.solvePrefix, Solve.rowX, Solve.rowY, Solve.rowZ, Solve.addRowScaled,
      Solve.addRow, Solve.addConstScaled, Solve.finishMask, Solve.finishMaskOver, Prog.seqList,
      Prog.OpsSatisfy, loadAt, storeAt, ar, cst, Op.Det, and_self]

/-- The rows program makes no oracle call (release-r1's tail points, Horner and head clamp, randomisers and lifts). -/
theorem rows_noOracle : Design.rowsProgram.NoOracle := by
  unfold Design.rowsProgram
  simp only [Prog.seqList]
  have curveRoot (source : Register) : (Opening.curveRoot source).NoOracle := by
    unfold Opening.curveRoot
    simp only [Prog.seqList]
    exact ⟨rfl, rfl, rfl, rfl, rfl, noOracle_rep _ _ (fun _ _ => by
      unfold Opening.sqrtRound
      exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
  have betaMul : Opening.betaMul.NoOracle := by
    unfold Opening.betaMul Opening.copyPoint Opening.clearP
    simp only [Prog.seqList]
    exact ⟨⟨rfl, rfl, rfl, trivial⟩, ⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
      unfold Opening.betaRound
      exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.tailOne
      simp only [Prog.seqList]
      refine ⟨noOracle_bounded _ _ _ _ ?_ ?_, noOracle_zeroRegs _, trivial⟩
      · unfold Opening.testCurveX
        simp only [Prog.seqList]
        exact ⟨rfl, rfl, curveRoot _, rfl, rfl, rfl, rfl, rfl, trivial⟩
      · unfold Opening.storeCurvePoint
        simp only [Prog.seqList]
        exact ⟨curveRoot _, ⟨rfl, trivial⟩, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, trivial⟩
  · unfold Opening.horner Opening.clearP Opening.head Opening.storePoint
    simp only [Prog.seqList]
    exact ⟨⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
        unfold Opening.hornerStep Opening.loadPoint
        simp only [Prog.seqList]
        exact ⟨betaMul, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, trivial⟩),
      ⟨betaMul, ⟨⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, noOracle_zeroRegs _, trivial⟩, trivial⟩,
        trivial⟩, trivial⟩
  · exact noOracle_rep _ _ fun _ _ =>
      ⟨⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩,
        ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.liftOne Opening.loadPoint
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, noOracle_zeroRegs _, trivial⟩

section Sem

variable [FieldCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

theorem sem_seq_free (first second : Prog) (free : first.NoOracle) (memory : Memory) (oracle : OState FI EI) :
    (Prog.seq first second).sem memory oracle =
      optBind (first.memSem memory) fun next => second.sem next oracle := by
  show andThen first.sem second.sem memory oracle = _
  unfold andThen optBind
  rw [sem_noOracle first free memory oracle, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun result => ?_)
  cases result <;> rfl

theorem sem_seq_exec (first second : Prog) (det : first.OpsSatisfy Op.Det) (memory after : Memory)
    (run : first.exec memory = some after) (oracle : OState FI EI) :
    (Prog.seq first second).sem memory oracle = second.sem after oracle := by
  rw [sem_seq_free first second (noOracle_of_det first det), memSem_eq_exec first det memory, run]
  exact PMF.pure_bind _ _

theorem sem_seq_assoc (first second third : Prog) (memory : Memory) (oracle : OState FI EI) :
    (Prog.seq first (Prog.seq second third)).sem memory oracle =
      (Prog.seq (Prog.seq first second) third).sem memory oracle := by
  show andThen first.sem (andThen second.sem third.sem) memory oracle =
    andThen (andThen first.sem second.sem) third.sem memory oracle
  unfold andThen
  rw [PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun result => ?_)
  rcases result with _ | ⟨next, updated⟩
  · show PMF.pure none = (PMF.pure none).bind _
    simp only [PMF.pure_bind]
  · rfl

omit [FieldCertificate] in
theorem labelVector_of (ram : Word → Word) (labels : LamportSignature)
    (cells : ∀ (i : Nat) (bound : i < 508), ram (word (labelBase + i)) = blockWord (labels[i]'bound)) :
    labelVector ram = labels := by
  apply Vector.ext
  intro i bound
  simp only [labelVector, Vector.getElem_ofFn]
  rw [cells i bound, blockWord_block]

/-- **The emission and the parse**: the labels in RAM are what the protocol reads. -/
theorem emit_finish (after : Memory) (labels : LamportSignature) (vector : labelVector after.ram = labels)
    (empty : after.bits 3 = []) (updated : OState FI EI) :
    ((Prog.seq Request.emitLabels (.skip 0)).sem after updated).bind finishK =
      PMF.pure (some (labels, updated)) := by
  obtain ⟨last, runEmit, _, bitsEmit, _⟩ := memSem_emitLabels after
  rw [sem_seq_free Request.emitLabels (.skip 0) invalid_noOracle, runEmit]
  unfold optBind
  rw [PMF.pure_bind]
  show (PMF.pure (some (last, updated))).bind finishK = _
  rw [PMF.pure_bind]
  show PMF.pure ((SimulatorProtocol.words 128 508 (last.bits 3)).map fun labels => (labels, updated)) = _
  rw [bitsEmit, empty, List.append_nil, labelRuns_words, vector]
  rfl

end Sem

/-! ### Addresses -/

section Addresses

variable [FieldCertificate]

omit [FieldCertificate] in
/-- A cell above the opening's region is not one of its cells. -/
theorem notOpen_high (x : Nat) (low : openBase + 2 ^ 12 ≤ x) (fits : x < 2 ^ 256) : ¬ OpenCell (word x) := by
  unfold OpenCell
  rw [word_toNat fits]
  rintro (⟨_, above⟩ | same)
  · omega
  · have same' := word_inj fits (by unfold tmpM tmpBase; norm_num) same
    simp only [tmpM, tmpBase, openBase] at same' low
    omega

omit [FieldCertificate] in
theorem notOpen_encCell (e : Privacy.BMR.Enc) : ¬ OpenCell (word (OutCells.encCell e)) := by
  cases e with
  | inl e =>
      have := (Privacy.BMR.xFlat e).isLt
      show ¬ OpenCell (word (Layout.decodedCell 0 (Privacy.BMR.xFlat e).val))
      apply notOpen_high <;> simp only [Layout.decodedCell, openBase] <;> omega
  | inr e =>
      have := (Privacy.BMR.yFlat e).isLt
      show ¬ OpenCell (word (Layout.decodedCell 1 (Privacy.BMR.yFlat e).val))
      apply notOpen_high <;> simp only [Layout.decodedCell, openBase] <;> omega

omit [FieldCertificate] in
theorem notOpen_rowMaskCell (r : Privacy.BMR.NonCollector) : ¬ OpenCell (word (OutCells.rowMaskCell r)) := by
  obtain ⟨⟨d, e⟩, _⟩ := r
  cases e with
  | inl x =>
      have := (PlanB.xElementIndex d x).isLt
      have count : PlanB.pointElementCountX = 364 := rfl
      show ¬ OpenCell (word (Layout.maskCell 0 (PlanB.xElementIndex d x).val))
      apply notOpen_high <;> simp only [Layout.maskCell, openBase] <;> omega
  | inr y =>
      have := (PlanB.yElementIndex d y).isLt
      have count : PlanB.pointElementCountY = 273 := rfl
      show ¬ OpenCell (word (Layout.maskCell 1 (PlanB.yElementIndex d y).val))
      apply notOpen_high <;> simp only [Layout.maskCell, openBase] <;> omega

omit [FieldCertificate] in
theorem notOpen_keyCell : ¬ OpenCell (word Layout.keyCell) :=
  notOpen_high _ (by unfold Layout.keyCell openBase; norm_num) (by unfold Layout.keyCell; norm_num)

omit [FieldCertificate] in
/-- The replay writes nothing below `2 ^ 56`. -/
theorem replayWrites_low (x : Nat) (small : x < 2 ^ 56) : ¬ Machine.replayWrites (word x) := by
  have count : nonCollectorCount PlanB.digitCount = 364 := rfl
  rintro (((inX | inY) | key) | (⟨b, bb, same⟩ | ⟨n, nb, same⟩))
  · exact Machine.coordWrites_high 0 Entry.xCount (by norm_num) (by decide) x small inX
  · exact Machine.coordWrites_high 1 Entry.yCount (by norm_num) (by decide) x small inY
  · have := word_inj (by omega) (by unfold Layout.keyCell; norm_num) key
    unfold Layout.keyCell at this
    omega
  · dsimp only [entryMaskCells] at bb same
    have fits := Machine.maskScratch_fits
    have low := Machine.maskScratch_low
    have := word_inj (by omega) (by omega) same
    omega
  · rw [count] at nb
    have mn : maskCellOf PlanB.digitCount n < 2 ^ 58 := by rw [maskCellOf_digitCount]; split_ifs <;> omega
    dsimp only [entryMaskCells] at same
    have := word_inj (by omega) (by omega) same
    rw [maskCellOf_digitCount] at this
    split_ifs at this <;> omega

omit [FieldCertificate] in
/-- The preimages and the programs write nothing below the opening's region other than `tmpM`. -/
theorem notWrites_low (x : Nat) (low : x < openBase) (notM : x ≠ tmpM) :
    ¬ (Preimages.preimagesWrites.union Programs.programsWrites) (word x) := by
  have fits : x < 2 ^ 256 := by unfold openBase at low; omega
  rintro ((same | ⟨index, bound, block, inside, same⟩ | ⟨index, bound, same⟩) | never)
  · exact notM (word_inj fits (by unfold tmpM tmpBase; norm_num) same)
  · have := word_inj fits (by unfold Layout.limbCell openBase; omega) same
    unfold Layout.limbCell at this
    omega
  · have := word_inj fits (by unfold Layout.fourthCell; omega) same
    unfold Layout.fourthCell openBase at *
    omega
  · exact never

omit [FieldCertificate] in
theorem label_ne_openTarget (i : Nat) (small : i < 508) (d c : Nat) (dSmall : d < 91) (cSmall : c < 3) :
    word (labelBase + i) ≠ word (openTarget d c) :=
  word_ne (by unfold labelBase; omega) (by unfold openTarget openBase; omega)
    (by unfold labelBase openTarget openBase; omega)

omit [FieldCertificate] in
theorem keyCell_ne_openTarget (d c : Nat) (dSmall : d < 91) (cSmall : c < 3) :
    word Layout.keyCell ≠ word (openTarget d c) :=
  word_ne (by unfold Layout.keyCell; norm_num) (by unfold openTarget openBase; omega)
    (by unfold Layout.keyCell openTarget openBase; omega)

end Addresses

/-! ### The rows -/

section Rows

variable [FieldCertificate] [GroupCertificate]

/-- What the rows leave: the target rows at `openRow d`, the stacks, and every cell off the opening's region. -/
structure RowsPost (memory next : Memory) (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) : Prop where
  bits : next.bits = memory.bits
  same : SameOff memory.ram next.ram
  rows : ∀ d : Fin 91, next.ram (word (openRow d)) = fieldWord (targets d).x ∧
    next.ram (word (openRow d + 1)) = fieldWord (targets d).y ∧
    next.ram (word (openRow d + 2)) = fieldWord (targets d).z

/-- **The rows**: release-r1's tail, Horner and head clamp, randomisers and lifts, followed by a continuation that
reads only what the rows leave, are `CrtBounded.rows` followed by the matching abstract continuation. -/
theorem rows_bind (memory : Memory) (u : AffineInput) (target : Point)
    (request : readWords (memory.ram (word reqTag0), memory.ram (word reqQX), memory.ram (word reqQY)) =
      some target)
    {γ : Type} (C : Memory → PMF (Option γ)) (H : (Fin 91 → FieldMacToECMac.HomogeneousValue) → PMF (Option γ))
    (agree : ∀ next targets, RowsPost memory next targets → C next = H targets) :
    optBind (Design.rowsProgram.memSem memory) C = optBind (CrtBounded.rows u target) H := by
  unfold Design.rowsProgram optBind CrtBounded.rows tailLaw
  simp only [Prog.seqList]
  rw [memSem_seq, memSem_tail, PMF.bind_map, PMF.bind_map, PMF.bind_bind, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun drawn => ?_)
  cases drawn with
  | none => simp [kleisli]
  | some points =>
      simp only [Function.comp_apply, Option.map_some, kleisli, Option.bind_some]
      have request' : readWords ((tailFold memory points).ram (word reqTag0),
          (tailFold memory points).ram (word reqQX), (tailFold memory points).ram (word reqQY)) =
            some target := by
        rw [tailFold_sameOff memory points _ (not_openCell _ (by addr_arith) (by addr_arith)),
          tailFold_sameOff memory points _ (not_openCell _ (by addr_arith) (by addr_arith)),
          tailFold_sameOff memory points _ (not_openCell _ (by addr_arith) (by addr_arith)), request]
      rw [memSem_seq, memSem_horner _ points target (tailFold_at memory points) request']
      by_cases clamp : FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0
      · rw [if_pos clamp, if_pos clamp, PMF.pure_bind]
        simp [kleisli]
      · rw [if_neg clamp, if_neg clamp, PMF.pure_bind]
        simp only [kleisli]
        rw [memSem_seq, memSem_lambdas_digit, PMF.bind_map, PMF.bind_bind, PMF.bind_bind]
        refine congrArg (PMF.bind _) (funext fun drawnLams => ?_)
        cases drawnLams with
        | none => simp [kleisli]
        | some lams =>
            simp only [Function.comp_apply, Option.map_some, kleisli]
            set pointsN : Nat → Point := fun digit =>
              if inside : digit < 91 then digitPoints target (Vector.ofFn points) ⟨digit, inside⟩ else 0
              with pointsDef
            set lamsN : Nat → BaseField := fun digit =>
              if inside : digit < 91 then (lams ⟨digit, inside⟩).1.value else 0 with lamsDef
            set tausN : Nat → BaseField := fun digit =>
              if inside : digit < 91 then (lams ⟨digit, inside⟩).2.value else 0 with tausDef
            obtain ⟨lifted, runLifts, bitsLifted, sameLifted, rowsLifted, _⟩ :=
              memSem_lifts (foldStore lamMem 91 (headMem memory target points) lams) pointsN lamsN tausN
                (fun digit inside => by
                  simp only [lamsDef, dif_pos inside]
                  exact (lamFold_at (headMem memory target points) lams ⟨digit, inside⟩).1)
                (fun digit inside => by
                  simp only [tausDef, dif_pos inside]
                  exact (lamFold_at (headMem memory target points) lams ⟨digit, inside⟩).2)
                (fun digit inside => by
                  simp only [pointsDef, dif_pos inside]
                  exact pointCells_after memory target points lams ⟨digit, inside⟩) 91 le_rfl
            have runLifts' : Opening.lifts.memSem (foldStore lamMem 91 (headMem memory target points) lams) =
                PMF.pure (some lifted) := runLifts
            rw [memSem_pure_seq runLifts', memSem_skip, PMF.pure_bind, PMF.pure_bind]
            have sameHead : SameOff (tailFold memory points).ram (headMem memory target points).ram := by
              rw [headMem_ram]
              exact sameOff_putPoint _ 0 (by norm_num) _
            refine agree lifted _ ⟨?_, ?_, fun d => ⟨?_, ?_, ?_⟩⟩
            · exact bitsLifted.trans ((lamFold_bits _ lams).trans (headMem_bits memory target points))
            · exact (((tailFold_sameOff memory points).trans sameHead).trans
                (lamFold_sameOff _ lams)).trans sameLifted
            · have row := rowsLifted d.val d.isLt 0 (by norm_num)
              rw [Nat.add_zero] at row
              rw [row]
              simp only [pointsDef, lamsDef, tausDef, dif_pos d.isLt]
              rfl
            · rw [rowsLifted d.val d.isLt 1 (by norm_num)]
              simp only [pointsDef, lamsDef, tausDef, dif_pos d.isLt]
              rfl
            · rw [rowsLifted d.val d.isLt 2 (by norm_num)]
              simp only [pointsDef, lamsDef, tausDef, dif_pos d.isLt]
              rfl

end Rows

/-! ### After the rows: the solve, the preimages, the programs, the emission -/

section After

variable [FieldCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The machine after the rows. -/
abbrev afterRowsProg : Prog :=
  Prog.seq Solve.solve (Prog.seq Preimages.preimages (Prog.seq (Programs.programs Preimages.programCells)
    (Prog.seq Request.emitLabels (.skip 0))))

/-- The abstract simulator after the rows (route M's `drawAll` of the bounded preimages and the exact fourth block,
then `programHashAll`). -/
def abstractAfterRows (u : AffineInput) (out : ReplayOut) (gamma : Fin 91 → RowGamma) (labels : LamportSignature)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) (oracle : OState FI EI) :
    PMF (Option (LamportSignature × OState FI EI)) :=
  (drawAll (fun c => Preimages.siteSample (collectorMasks u out gamma targets c)) collectorList).map fun drawn =>
    match drawn with
    | none => none
    | some drawn => (programHashAll (programRequests out.key drawn) oracle).map fun updated => (labels, updated)

/-- **After the rows**: from a memory that holds the replay's outputs, the request, the row constants and the labels,
and after the rows (`RowsPost`), the rest of the valid arm with the parse is the abstract continuation. -/
theorem afterRows_law (out : ReplayOut) (u : AffineInput) (gamma : Fin 91 → RowGamma) (labels : LamportSignature)
    (memory next : Memory) (targets : Fin 91 → FieldMacToECMac.HomogeneousValue)
    (post : RowsPost memory next targets) (holds : OutCells.OutHolds out memory)
    (reqXCell : memory.ram (word reqX) = fieldWord u.x) (reqYCell : memory.ram (word reqY) = fieldWord u.y)
    (rowCells : ∀ d : Fin 91, memory.ram (word (Opening.rowCell d 0)) = fieldWord (gamma d).xC0 ∧
      memory.ram (word (Opening.rowCell d 1)) = fieldWord (gamma d).yC4 ∧
      memory.ram (word (Opening.rowCell d 2)) = fieldWord (gamma d).zC0)
    (labelCells : ∀ (i : Nat) (bound : i < 508), memory.ram (word (labelBase + i)) = blockWord (labels[i]'bound))
    (empty : memory.bits 3 = []) (oracle : OState FI EI) :
    (afterRowsProg.sem next oracle).bind finishK = abstractAfterRows u out gamma labels targets oracle := by
  -- the cells, carried over the rows
  have holdsN : OutCells.OutHolds out next :=
    ⟨fun e => (post.same _ (notOpen_encCell e)).trans (holds.delivered e),
      fun r => (post.same _ (notOpen_rowMaskCell r)).trans (holds.masks r),
      (post.same _ notOpen_keyCell).trans holds.key⟩
  have hx : next.ram (word reqX) = fieldWord u.x :=
    (post.same _ (not_openCell _ (by addr_arith) (by addr_arith))).trans reqXCell
  have hy : next.ram (word reqY) = fieldWord u.y :=
    (post.same _ (not_openCell _ (by addr_arith) (by addr_arith))).trans reqYCell
  have rowsN : ∀ d : Fin 91, next.ram (word (Opening.rowCell d 0)) = fieldWord (gamma d).xC0 ∧
      next.ram (word (Opening.rowCell d 1)) = fieldWord (gamma d).yC4 ∧
      next.ram (word (Opening.rowCell d 2)) = fieldWord (gamma d).zC0 := fun d => by
    have := d.isLt
    refine ⟨?_, ?_, ?_⟩
    · exact (post.same _ (not_openCell _ (by addr_arith) (by addr_arith))).trans (rowCells d).1
    · exact (post.same _ (not_openCell _ (by addr_arith) (by addr_arith))).trans (rowCells d).2.1
    · exact (post.same _ (not_openCell _ (by addr_arith) (by addr_arith))).trans (rowCells d).2.2
  have labelsN : ∀ (i : Nat) (bound : i < 508), next.ram (word (labelBase + i)) = blockWord (labels[i]'bound) :=
    fun i bound => (post.same _ (not_openCell _ (by unfold labelBase openBase; omega)
      (by unfold labelBase tmpM tmpBase; omega))).trans (labelCells i bound)
  -- the solve
  obtain ⟨after, runSolve, written, frameSolve, bitsSolve, _⟩ := Solve.exec_solve next u.x u.y (atFin gamma)
    (atFin targets) (OutCells.dxOf out) (OutCells.pxOf out) (OutCells.dyOf out) (OutCells.pyOf out)
    (fun d small => by
      rw [atFin_of_lt gamma d small, atFin_of_lt targets d small]
      exact OutCells.digitCells_of_out out next u gamma targets holdsN hx hy rowsN post.rows ⟨d, small⟩)
  rw [sem_seq_exec Solve.solve _ det_solve next after runSolve, sem_seq_assoc]
  -- the preimages and the programs
  have cells : ∀ (d : Fin 91) (c : Fin 3), after.ram (word (openTarget d c)) =
      fieldWord (collectorMasks u out gamma targets (Programs.collectorAt d c)) := fun d c => by
    rw [written d.val c d.isLt, atFin_val gamma d, atFin_val targets d,
      OutCells.maskFormula_eq u out gamma targets d c]
  have keyCell : after.ram (word Layout.keyCell) = blockWord out.key :=
    (frameSolve _ fun d c dSmall cSmall => keyCell_ne_openTarget d c dSmall cSmall).trans holdsN.key
  obtain ⟨finalMem, frames, law⟩ :=
    Preimages.sem_preimagesPrograms (FI := FI) (EI := EI) after (collectorMasks u out gamma targets) out.key cells
      keyCell
  have vector : ∀ values, labelVector (finalMem values).ram = labels := fun values =>
    labelVector_of _ labels fun i bound => by
      rw [(frames values).ram _ (notWrites_low (labelBase + i) (by unfold labelBase openBase; omega)
          (by unfold labelBase tmpM tmpBase; omega)),
        frameSolve _ fun d c dSmall cSmall => label_ne_openTarget i bound d c dSmall cSmall, labelsN i bound]
  have emptyF : ∀ values, (finalMem values).bits 3 = [] := fun values => by
    rw [(frames values).bits, bitsSolve, post.bits, empty]
  show (andThen (Prog.seq Preimages.preimages (Programs.programs Preimages.programCells)).sem
    (Prog.seq Request.emitLabels (.skip 0)).sem after oracle).bind finishK = _
  unfold andThen abstractAfterRows
  rw [law oracle, PMF.bind_map, PMF.bind_bind, Preimages.drawAll_sites (collectorMasks u out gamma targets),
    PMF.map_comp,
    ← PMF.bind_pure_comp]
  refine congrArg (PMF.bind _) (funext fun drawn => ?_)
  cases drawn with
  | none =>
      show (PMF.pure none).bind finishK = PMF.pure none
      rw [PMF.pure_bind]
      rfl
  | some values =>
      simp only [Function.comp_apply, Option.map_some, Option.bind_some]
      rw [Preimages.drawn_eq (collectorMasks u out gamma targets) values]
      cases programHashAll (programRequests out.key
          (collectorList.map fun c => (c, Preimages.drawsOf (collectorMasks u out gamma targets) values c)))
          oracle with
      | none =>
          show (PMF.pure none).bind finishK = PMF.pure none
          rw [PMF.pure_bind]
          rfl
      | some updated =>
          exact emit_finish (finalMem values) labels (vector values) (emptyF values) updated

end After

/-! ### Everything after the replay -/

section Continuation

variable [FieldCertificate] [GroupCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI]
  [DecidableEq EI]

/-- The machine after the replay: the rows, the solve, the preimages, the programs, the emission. -/
abbrev restProg : Prog :=
  Prog.seqList [Design.rowsProgram, Solve.solve, Preimages.preimages, Programs.programs Preimages.programCells,
    Request.emitLabels]

/-- The abstract simulator after the replay, at the machine's bounded samplers. -/
def afterReplay (u : AffineInput) (target : Point) (gamma : Fin 91 → RowGamma) (labels : LamportSignature)
    (ran : ReplayOut × OState FI EI) : PMF (Option (LamportSignature × OState FI EI)) :=
  optBind (CrtBounded.rows u target) fun targets => abstractAfterRows u ran.1 gamma labels targets ran.2

/-- **The continuation law**: from the replay's outputs in RAM, the request, the output cells, the row constants,
the labels and an empty response stack, the rest of the valid arm with the parse is route M's stage 2 after its
replay, with the bounded rows, the bounded preimages and the exact fourth block. -/
theorem continuation_law (out : ReplayOut) (u : AffineInput) (target : Point) (gamma : Fin 91 → RowGamma)
    (labels : LamportSignature) (memory : Memory) (holds : OutCells.OutHolds out memory)
    (reqXCell : memory.ram (word reqX) = fieldWord u.x) (reqYCell : memory.ram (word reqY) = fieldWord u.y)
    (request : readWords (memory.ram (word reqTag0), memory.ram (word reqQX), memory.ram (word reqQY)) =
      some target)
    (rowCells : ∀ d : Fin 91, memory.ram (word (Opening.rowCell d 0)) = fieldWord (gamma d).xC0 ∧
      memory.ram (word (Opening.rowCell d 1)) = fieldWord (gamma d).yC4 ∧
      memory.ram (word (Opening.rowCell d 2)) = fieldWord (gamma d).zC0)
    (labelCells : ∀ (i : Nat) (bound : i < 508), memory.ram (word (labelBase + i)) = blockWord (labels[i]'bound))
    (empty : memory.bits 3 = []) (oracle : OState FI EI) :
    (restProg.sem memory oracle).bind finishK = afterReplay u target gamma labels (out, oracle) := by
  show ((Prog.seq Design.rowsProgram afterRowsProg).sem memory oracle).bind finishK = _
  rw [sem_seq_free _ _ rows_noOracle, optBind_bind _ _ finishK rfl]
  exact rows_bind memory u target request _ _ fun next targets post =>
    afterRows_law out u gamma labels memory next targets post holds reqXCell reqYCell rowCells labelCells empty
      oracle

end Continuation

/-! ### The valid arm -/

/-- **What the valid arm reads at its start**, from the stage-1 source and the stage-2 prefix: the two coordinates'
reads of `Machine.agree_replay` (the coordinate value, the label cells, the hint cells), the request, the curve
constants, the output cells, the row constants, the label cells and an empty response stack. -/
structure ValidStart [FieldCertificate] (pub : Entry.Public) (input : AffineInput) (labels : LamportSignature)
    (target : Point) (middle : Memory) : Prop where
  readsX : Machine.CoordReads 0 Entry.xCount (Entry.convOf pub.crtX) (fun e => (pub.recX.get e).val)
    input.x.val (Entry.labelX labels) middle
  readsY : Machine.CoordReads 1 Entry.yCount (Entry.convOf pub.crtY) (fun e => (pub.recY.get e).val)
    input.y.val (Entry.labelY labels) middle
  reqXCell : middle.ram (word reqX) = fieldWord input.x
  reqYCell : middle.ram (word reqY) = fieldWord input.y
  c0Cell : middle.ram (word fieldBase) = fieldWord pub.curve.1
  c1Cell : middle.ram (word (fieldBase + 1)) = fieldWord pub.curve.2.1
  c2Cell : middle.ram (word (fieldBase + 2)) = fieldWord pub.curve.2.2
  outputCells : (middle.ram (word reqTag0), middle.ram (word reqQX), middle.ram (word reqQY)) = outputWords target
  rowCells : ∀ d : Fin 91, middle.ram (word (Opening.rowCell d 0)) = fieldWord (Entry.gammaOf pub d).xC0 ∧
    middle.ram (word (Opening.rowCell d 1)) = fieldWord (Entry.gammaOf pub d).yC4 ∧
    middle.ram (word (Opening.rowCell d 2)) = fieldWord (Entry.gammaOf pub d).zC0
  labelCells : ∀ (i : Nat) (bound : i < 508), middle.ram (word (labelBase + i)) = blockWord (labels[i]'bound)
  empty : middle.bits 3 = []

section Valid

variable [FieldCertificate] [GroupCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI]
  [DecidableEq EI]

/-- The valid arm (`CrtTop.validArm Machine.replay`). -/
abbrev validProg : Prog :=
  Prog.seqList [Machine.replay, Design.rowsProgram, Solve.solve, Preimages.preimages,
    Programs.programs Preimages.programCells, Request.emitLabels]

omit [GroupCertificate] in
/-- The valid arm is the replay's tree followed by the rest. -/
theorem valid_machine (middle : Memory) (oracle : OState FI EI) :
    (validProg.sem middle oracle).bind finishK =
      (runT (Machine.replay.tree middle) oracle).bind fun result => match result.1 with
        | none => PMF.pure none
        | some memory => (restProg.sem memory result.2).bind finishK := by
  show (andThen Machine.replay.sem restProg.sem middle oracle).bind finishK = _
  unfold andThen
  rw [sem_eq_runT Machine.replay TreeOps.treeOps_replay middle oracle, PMF.bind_map, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun result => ?_)
  rcases result with ⟨_ | memory, updated⟩
  · show (PMF.pure none).bind finishK = PMF.pure none
    rw [PMF.pure_bind]
    rfl
  · rfl

omit [Fintype FI] [Fintype EI] in
/-- Route M's stage 2 at a defined output, with the bounded samplers, is the replay followed by `afterReplay`. -/
theorem stage2_some (source : Entry.Source) (input : AffineInput) (target : Point) (oracle : OState FI EI) :
    (LawShape.routeMWith (Privacy.Instance.crtEntry.view inferInstance inferInstance)
        (CrtBounded.samplers inferInstance inferInstance) lazyReader).stage2 source input (some target) oracle =
      (routeMReplay Privacy.Instance.view lazyReader (Entry.publish source) input (Entry.labels source input)
          oracle).bind
        (afterReplay input target (Entry.gammaOf (Entry.publish source)) (Entry.labels source input)) := by
  unfold LawShape.routeMWith
  dsimp only
  refine congrArg (PMF.bind _) (funext fun ran => ?_)
  unfold afterReplay optBind
  refine congrArg (PMF.bind _) (funext fun drawnRows => ?_)
  cases drawnRows with
  | none => rfl
  | some targets =>
      dsimp only
      unfold abstractAfterRows
      rfl

/-- **The valid arm of Stage2Law**: from `ValidStart`, the machine's valid arm followed by the protocol's parse is
route M's stage 2 at the defined output `target`, with the bounded samplers and the lazy reader. -/
theorem valid_law (source : Entry.Source) (input : AffineInput) (target : Point) (middle : Memory)
    (start : ValidStart (Entry.publish source) input (Entry.labels source input) target middle)
    (oracle : OState FI EI) :
    (validProg.sem middle oracle).bind finishK =
      (LawShape.routeMWith (Privacy.Instance.crtEntry.view inferInstance inferInstance)
        (CrtBounded.samplers inferInstance inferInstance) lazyReader).stage2 source input (some target) oracle := by
  rw [stage2_some, valid_machine, ← Lazy.runT_replayRouteM, PMF.bind_map]
  refine agree_run (fun memory o => (restProg.sem memory o).bind finishK)
    (fun out o => afterReplay input target (Entry.gammaOf (Entry.publish source)) (Entry.labels source input)
      (routeView out, o)) (fun out after o post => ?_)
    (Machine.agree_replay (FixedIndex := FI) (EncIndex := EI) (Entry.publish source) input
      (Entry.labels source input) middle start.readsX start.readsY start.reqXCell start.reqYCell start.c0Cell
      start.c1Cell start.c2Cell) oracle
  obtain ⟨holds, frame⟩ := post
  have keep : ∀ x, x < 2 ^ 56 → after.ram (word x) = middle.ram (word x) := fun x small =>
    frame.ram _ (replayWrites_low x small)
  exact continuation_law (routeView out) input target (Entry.gammaOf (Entry.publish source))
    (Entry.labels source input) after holds
    ((keep _ (by addr_arith)).trans start.reqXCell) ((keep _ (by addr_arith)).trans start.reqYCell)
    (by
      rw [keep _ (by addr_arith), keep _ (by addr_arith), keep _ (by addr_arith), start.outputCells,
        readWords_outputWords])
    (fun d => by
      have := d.isLt
      refine ⟨?_, ?_, ?_⟩
      · exact (keep _ (by addr_arith)).trans (start.rowCells d).1
      · exact (keep _ (by addr_arith)).trans (start.rowCells d).2.1
      · exact (keep _ (by addr_arith)).trans (start.rowCells d).2.2)
    (fun i bound => (keep _ (by unfold labelBase; omega)).trans (start.labelCells i bound))
    (by rw [frame.bits]; exact start.empty) o

end Valid

end CrtValid

end

end Kriterion.CRT.SimMachine
