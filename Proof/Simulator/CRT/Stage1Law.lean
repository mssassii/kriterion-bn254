/-
**Stage1Law for the CRT machine**.

The machine's stage-1 kernel (`LawShape.machineAbstract … (CrtTop.machine s1 r replay within)`, stage 1) is the
abstract stage 1 of `routeMWith` at the bounded samplers (`CrtBounded.samplers`, source
`CrtDraws.drawLaw` mapped by `CrtSource.sourceOf`), with the retained configuration read back by
`CrtSource.extract` (release-r1's `stage1Law`, ported).

* `stage1_noOracle`: stage 1 makes no oracle call, so its semantics is its memory law;
* `FinalSpec`: what the deterministic tail leaves after the draws `d` (in the support): the run, the response stack,
  every cell off the record limbs and the true labels, and the draws' word bounds; `CrtStage1Final.finalOf` provides it;
* `readDraw_final`, `extract_final`, `parse_final`: the final memory reads back as `CrtSource.sourceOf d`, and the protocol's
  parse of its response stack is `Entry.publish (CrtSource.sourceOf d)`;
* `stage1_run_form`: the machine's stage-1 run is `drawLaw` mapped to the halted configuration;
* `stage1_form`, `mem_support_stage1`: the kernel;
* `stage1Law_of`: `LawShape.Stage1Law` for the generic machine, with `extract = CrtSource.extract ·.ram`.
-/

import Proof.Simulator.CRT.Runs
import Proof.Simulator.CRT.Stage1Tail
import Proof.Simulator.CRT.Bounded
import Proof.Simulator.Stage1Bits

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit
open Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open CrtStage1 CrtDraws CrtStored CrtRecord CrtSerial CrtSource CrtTail
open Kriterion.ArgoMAC.PlanB.SimMachine.Top (afterTag)

noncomputable section

namespace CrtStage1Law

/-! ### Stage 1 makes no oracle call -/

theorem noOracle_of_det : ∀ program : Prog, program.OpsSatisfy Op.Det → program.NoOracle
  | .op operation, det => by
      cases operation <;> first | exact (det : False).elim | rfl
  | .popBit _ _, _ => trivial
  | .skip _, _ => trivial
  | .abort _, _ => trivial
  | .seq first second, ⟨one, two⟩ => ⟨noOracle_of_det first one, noOracle_of_det second two⟩
  | .ite _ whenSet whenClear, ⟨one, two⟩ => ⟨noOracle_of_det whenSet one, noOracle_of_det whenClear two⟩

theorem noOracle_fieldCell (address : Nat) : (Stage1.fieldCell address).NoOracle :=
  ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩

theorem noOracle_wordCell (width address : Nat) : (Stage1.wordCell width address).NoOracle :=
  ⟨noOracle_sampleWord _, ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩

theorem noOracle_digitCell (m address : Nat) : (digitCell m address).NoOracle :=
  ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩

theorem noOracle_pieceProg : ∀ piece : Piece, (pieceProg piece).NoOracle
  | .word address width => noOracle_emitWord address width
  | .record κ e => ⟨noOracle_of_det _ det_clearLimbs, noOracle_of_det _ (det_horner κ e),
      ⟨noOracle_emitWord _ _, noOracle_emitWord _ _, noOracle_emitWord _ _, noOracle_emitWord _ _,
        noOracle_emitWord _ _, trivial⟩, trivial⟩

theorem noOracle_fields : CrtStage1.fields.NoOracle := by
  unfold CrtStage1.fields
  refine noOracle_rep _ _ fun _ _ => ?_
  exact noOracle_fieldCell _

theorem noOracle_bytes : CrtStage1.bytes.NoOracle := by
  unfold CrtStage1.bytes Stage1.bytes
  refine noOracle_rep _ _ fun _ _ => ?_
  exact noOracle_wordCell _ _

theorem noOracle_joins : CrtStage1.joins.NoOracle := by
  unfold CrtStage1.joins
  refine noOracle_rep _ _ fun _ _ => ?_
  exact noOracle_wordCell _ _

theorem noOracle_pins : CrtStage1.pins.NoOracle := by
  unfold CrtStage1.pins
  refine noOracle_rep _ _ fun _ _ => ?_
  exact noOracle_wordCell _ _

theorem noOracle_digits : CrtStage1.digits.NoOracle := by
  unfold CrtStage1.digits
  refine noOracle_rep _ _ fun _ _ => ?_
  exact noOracle_digitCell _ _

theorem noOracle_zeros : CrtStage1.zeros.NoOracle := by
  unfold CrtStage1.zeros
  refine noOracle_rep _ _ fun _ _ => ?_
  exact noOracle_wordCell _ _

theorem noOracle_deltas : CrtStage1.deltas.NoOracle := by
  unfold CrtStage1.deltas
  refine noOracle_rep _ _ fun _ _ => ?_
  exact noOracle_wordCell _ _

theorem noOracle_serializeList (list : List Piece) :
    (Prog.rep list.length fun n => pieceProg (list.getD (list.length - 1 - n) default)).NoOracle :=
  noOracle_rep _ _ fun n _ => noOracle_pieceProg (list.getD (list.length - 1 - n) default)

theorem noOracle_serialize : CrtStage1.serialize.NoOracle := noOracle_serializeList pieces

/-- **Stage 1 has no oracle instruction.** -/
theorem stage1_noOracle : CrtStage1.program.NoOracle := by
  unfold CrtStage1.program
  simp only [Prog.seqList]
  exact ⟨noOracle_fields, noOracle_bytes, noOracle_joins, noOracle_pins, noOracle_digits, noOracle_zeros,
    noOracle_deltas, noOracle_serialize, noOracle_of_det _ det_keyTrue, noOracle_of_det _ det_clearLimbs,
    noOracle_zeroRegs _, trivial⟩

/-! ### The protocol's stage-1 request -/

/-- The initial stage-1 memory of the protocol (`machineAbstract`'s, at `crtEntry.bytes`). -/
abbrev stage1Memory (parameter : Nat) : Memory :=
  { bits := fun stack => if stack = 0 then
      [false, false] ++ SimulatorProtocol.natural parameter ++ SimulatorProtocol.natural Privacy.Instance.crtEntry.bytes
    else [] }

/-- The request after the two tag bits. -/
def stage1Rest (parameter : Nat) : List Bool :=
  SimulatorProtocol.natural parameter ++ SimulatorProtocol.natural Privacy.Instance.crtEntry.bytes

/-- The memory stage 1's program starts from. -/
def stage1Start (parameter : Nat) : Memory := afterTag (stage1Memory parameter) (stage1Rest parameter)

theorem stage1Memory_request (parameter : Nat) :
    (stage1Memory parameter).bits 0 = false :: false :: stage1Rest parameter := by
  simp [stage1Rest]

theorem stage1Start_stack3 (parameter : Nat) : (stage1Start parameter).bits 3 = [] := by
  simp [stage1Start, afterTag]

/-! ### The stored draws and the tail -/

variable [FieldCertificate]

omit [FieldCertificate] in
theorem wordStore_bits (address : Nat) (memory : Memory) (value : Nat) :
    (wordStore address memory value).bits = memory.bits := by
  simp only [wordStore, (clearRegs_other _ _).2, storeRam]

omit [FieldCertificate] in
theorem cellStore_bits (address : Nat) (memory : Memory) (value : Nat) :
    (cellStore address memory value).bits = memory.bits := by
  simp only [cellStore, (clearRegs_other _ _).2, storeRam]

theorem storedMem_bits (memory : Memory) (d : Draw) : (storedMem memory d).bits = memory.bits := by
  unfold storedMem
  rw [foldStore_bits (fun n => wordStore (Layout.deltaCell n)) (fun _ _ _ => wordStore_bits _ _ _),
    foldStore_bits (fun n => wordStore (keyBase + 2 * n)) (fun _ _ _ => wordStore_bits _ _ _),
    foldStore_bits (fun n => cellStore (digitAddr n)) (fun _ _ _ => cellStore_bits _ _ _),
    foldStore_bits (fun n => wordStore (pinAddr n)) (fun _ _ _ => wordStore_bits _ _ _),
    foldStore_bits (fun n => wordStore (joinAddr n)) (fun _ _ _ => wordStore_bits _ _ _),
    foldStore_bits (wordStep exceptionBase) (fun _ _ _ => wordStep_bits _ _ _ _),
    foldStore_bits (cellStep fieldBase) (fun _ _ _ => cellStep_bits _ _ _ _)]

omit [FieldCertificate] in
/-- A cell away from the record limbs and the true labels. -/
theorem notTrue_away (x : Nat) (fits : x < 2 ^ 256) (away : x < keyBase ∨ keyBase + 2 ^ 11 ≤ x) :
    ¬ TrueCell (word x) := by
  rintro ⟨j, small, same⟩
  have := word_inj fits (by unfold trueCell keyBase labelCount at *; omega) same
  unfold trueCell keyBase labelCount at *
  omega

omit [FieldCertificate] in
theorem notTrue_even (j : Nat) (small : j < labelCount) : ¬ TrueCell (word (keyBase + 2 * j)) := by
  rintro ⟨i, smallI, same⟩
  have := word_inj (by unfold keyBase labelCount at *; omega) (by unfold trueCell keyBase labelCount at *; omega) same
  unfold trueCell at this
  omega

section Read

variable {stored final : Memory}
  (off : ∀ address, ¬ LimbCell address → ¬ TrueCell address → final.ram address = stored.ram address)

include off

theorem off_far (x : Nat) (fits : x < 2 ^ 256) (awayLimb : x < tmpBase ∨ tmpBase + 2 ^ 20 ≤ x)
    (awayTrue : x < keyBase ∨ keyBase + 2 ^ 11 ≤ x) : final.ram (word x) = stored.ram (word x) :=
  off _ (not_limbCell x fits awayLimb) (notTrue_away x fits awayTrue)

/-- **The draws read the same** after the tail, which writes only the record limbs and the true labels. -/
theorem readDraw_final : readDraw final.ram = readDraw stored.ram := by
  simp only [readDraw, Draw.mk.injEq]
  refine ⟨funext fun n => ?_, funext fun n => ?_, funext fun n => ?_, funext fun n => ?_, funext fun n => ?_,
    funext fun n => ?_, funext fun n => ?_⟩
  · have := n.isLt
    rw [off_far off (fieldBase + n.val) (by unfold fieldCount curveCellCount rowCellCount fieldBase at *; omega)
      (Or.inl (by unfold fieldCount curveCellCount rowCellCount fieldBase tmpBase at *; omega))
      (Or.inl (by unfold fieldCount curveCellCount rowCellCount fieldBase keyBase at *; omega))]
  · have := n.isLt
    rw [off_far off (exceptionBase + n.val) (by unfold exceptionByteCount exceptionBase at *; omega)
      (Or.inl (by unfold exceptionByteCount exceptionBase tmpBase at *; omega))
      (Or.inl (by unfold exceptionByteCount exceptionBase keyBase at *; omega))]
  · have := joinAddr_range n.val n.isLt
    rw [off_far off (joinAddr n.val) (by omega) (Or.inr (by unfold tmpBase; omega))
      (Or.inr (by unfold keyBase; omega))]
  · have := pinAddr_range n.val n.isLt
    rw [off_far off (pinAddr n.val) (by omega) (Or.inr (by unfold tmpBase; omega))
      (Or.inr (by unfold keyBase; omega))]
  · have := digitAddr_range n.val n.isLt
    rw [off_far off (digitAddr n.val) (by omega) (Or.inr (by unfold tmpBase; omega))
      (Or.inr (by unfold keyBase; omega))]
  · have := n.isLt
    rw [off _ (even_not_limb n.val n.isLt) (notTrue_even n.val n.isLt)]
  · have := n.isLt
    rw [off_far off (Layout.deltaCell n.val) (by unfold Layout.deltaCell; omega)
      (Or.inr (by unfold Layout.deltaCell tmpBase; omega)) (Or.inr (by unfold Layout.deltaCell keyBase; omega))]

end Read

/-- **What the tail leaves after the draws**, on the support of the draw law (`CrtStage1Final.finalOf` satisfies it). -/
structure FinalSpec (start : Memory) (fin : Draw → Memory) : Prop where
  run : ∀ d, some d ∈ drawLaw.support → tail.memSem (storedMem start d) = PMF.pure (some (fin d))
  bits : ∀ d, some d ∈ drawLaw.support → (fin d).bits 3 =
    byteBits (Entry.Wire.encoding.encode (Entry.publish (extract (storedMem start d).ram))) ++
      (storedMem start d).bits 3
  off : ∀ d, some d ∈ drawLaw.support → ∀ address, ¬ LimbCell address → ¬ TrueCell address →
    (fin d).ram address = (storedMem start d).ram address
  small : ∀ d, some d ∈ drawLaw.support → DrawSmall d

theorem extract_stored (start : Memory) (d : Draw) (small : DrawSmall d) :
    extract (storedMem start d).ram = CrtSource.sourceOf d := by
  unfold extract
  rw [readDraw_stored start d small]

/-- **The final memory reads back as the drawn source.** -/
theorem extract_final (start : Memory) (fin : Draw → Memory) (spec : FinalSpec start fin) (d : Draw)
    (member : some d ∈ drawLaw.support) : extract (fin d).ram = CrtSource.sourceOf d := by
  unfold extract
  rw [readDraw_final (spec.off d member), readDraw_stored start d (spec.small d member)]

/-- **The protocol's parse of the final response stack** is the drawn source's public value. -/
theorem parse_final (start : Memory) (empty : start.bits 3 = []) (fin : Draw → Memory) (spec : FinalSpec start fin)
    (d : Draw) (member : some d ∈ drawLaw.support) :
    SimulatorProtocol.publicValue Entry.Wire.encoding Entry.ciphertextBytes ((fin d).bits 3) =
      some (Entry.publish (CrtSource.sourceOf d)) := by
  rw [spec.bits d member, storedMem_bits, empty, List.append_nil, extract_stored start d (spec.small d member)]
  exact publicValue_encode _ _ _ (Entry.Wire.encoding_length _)

/-! ### The machine's stage-1 run and kernel -/

section Machine

variable {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
  (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)
  (size1 : s1.size = CrtStage1.program.size) (cost1 : s1.cost = CrtStage1.program.cost)

include size1 cost1 in
/-- **The machine's stage-1 run**: the draws, mapped to the halted configuration. -/
theorem stage1_run_form (parameter : Nat) (fin : Draw → Memory) (spec : FinalSpec (stage1Start parameter) fin)
    (oracle : OState FI EI) :
    (CrtTop.machine s1 r replay within).run (Design.firstFuel (CrtTop.blocks s1 r)) ⟨0, stage1Memory parameter⟩
        oracle =
      drawLaw.map (Option.map fun d => (atPc (CrtTop.machine s1 r replay within)
        (Design.stage1Halt (CrtTop.blocks s1 r)) (fin d), oracle, Design.firstFuel (CrtTop.blocks s1 r))) := by
  rw [CrtTop.stage1_run s1 r replay within size1 cost1 (stage1Memory parameter) (stage1Rest parameter)
      (stage1Memory_request parameter) oracle]
  rw [sem_noOracle _ stage1_noOracle, program_law]
  unfold CrtDraws.optBind
  rw [PMF.map_bind, PMF.bind_bind, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro drawn member
  cases drawn with
  | none => simp [PMF.pure_map]
  | some d =>
      show ((tail.memSem (storedMem (stage1Start parameter) d)).map _).bind _ = _
      rw [spec.run d member, PMF.pure_map, PMF.pure_bind]
      rfl

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] [FieldCertificate] in
theorem optionT_mk_pure_some {α : Type} (value : α) :
    (OptionT.mk (PMF.pure (some value)) : OptionT PMF α) = pure value := rfl

include size1 cost1 in
/-- **The machine's stage-1 kernel**: the draws, mapped to the drawn source's public value and the halted
configuration. -/
theorem stage1_form_of (parameter : Nat) (fin : Draw → Memory) (spec : FinalSpec (stage1Start parameter) fin)
    (oracle : OState FI EI) :
    (LawShape.machineAbstract (FI := FI) (EI := EI) Privacy.Instance.crtEntry.encoding
        Privacy.Instance.crtEntry.bytes (CrtTop.machine s1 r replay within)).stage1 parameter oracle =
      drawLaw.map (Option.map (β := Privacy.Instance.crtEntry.Public ×
          Configuration ((CrtTop.machine s1 r replay within).size + 1) × OState FI EI) fun d =>
        (Entry.publish (CrtSource.sourceOf d),
          atPc (CrtTop.machine s1 r replay within) (Design.stage1Halt (CrtTop.blocks s1 r)) (fin d), oracle)) := by
  unfold LawShape.machineAbstract
  dsimp only
  rw [CrtTop.machine_firstFuel, stage1_run_form s1 r replay within size1 cost1 parameter fin spec oracle,
    Phase3.Glue.optionT_mk_map, bind_assoc]
  simp only [pure_bind]
  conv_rhs => rw [← OptionT.run_mk (drawLaw.map _), Phase3.Glue.optionT_mk_map]
  refine congrArg OptionT.run (Phase3.Glue.optionT_bind_congr _ _ _ fun d member => ?_)
  have parse : SimulatorProtocol.publicValue Privacy.Instance.crtEntry.encoding Privacy.Instance.crtEntry.bytes
      ((atPc (CrtTop.machine s1 r replay within) (Design.stage1Halt (CrtTop.blocks s1 r)) (fin d)).memory.bits 3) =
        some (Entry.publish (CrtSource.sourceOf d)) :=
    parse_final (stage1Start parameter) (stage1Start_stack3 parameter) fin spec d member
  rw [parse]
  exact pure_bind _ _

include size1 cost1 in
/-- **The support of the machine's stage-1 kernel.** -/
theorem mem_support_stage1 (parameter : Nat) (fin : Draw → Memory) (spec : FinalSpec (stage1Start parameter) fin)
    (oracle : OState FI EI)
    (result : Privacy.Instance.crtEntry.Public × Configuration ((CrtTop.machine s1 r replay within).size + 1) × OState FI EI)
    (member : some result ∈ ((LawShape.machineAbstract (FI := FI) (EI := EI) Privacy.Instance.crtEntry.encoding
        Privacy.Instance.crtEntry.bytes (CrtTop.machine s1 r replay within)).stage1 parameter oracle).support) :
    ∃ d, some d ∈ drawLaw.support ∧ result = (Entry.publish (CrtSource.sourceOf d),
      atPc (CrtTop.machine s1 r replay within) (Design.stage1Halt (CrtTop.blocks s1 r)) (fin d), oracle) := by
  rw [stage1_form_of s1 r replay within size1 cost1 parameter fin spec oracle] at member
  obtain ⟨drawn, drawnMember, same⟩ := (PMF.mem_support_map_iff _ _ _).1 member
  cases drawn with
  | none => cases same
  | some d =>
      injection same with same
      exact ⟨d, drawnMember, same.symm⟩

end Machine

/-! ### The law -/

omit [FieldCertificate] in
/-- Two composed maps agree when their composites agree on the support. -/
theorem map_map_eq {α β β' γ : Type} (p : PMF α) (f : α → β) (g : β → γ) (f' : α → β') (g' : β' → γ)
    (same : ∀ a ∈ p.support, g (f a) = g' (f' a)) : (p.map f).map g = (p.map f').map g' := by
  rw [PMF.map_comp, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro a member
  simp only [Function.comp_apply, same a member]

section Law

variable (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)
  (size1 : s1.size = CrtStage1.program.size) (cost1 : s1.cost = CrtStage1.program.cost)

omit [FieldCertificate] in
include size1 cost1 in
/-- **`Stage1Law` for the CRT machine**: the machine's stage-1 kernel is route M's stage 1 at the bounded samplers,
with the retained configuration read back by `CrtSource.extract`; given a final memory of the tail for each draw
(`CrtStage1Final.finalOf`). -/
theorem stage1Law_of (fin : ∀ _ : FieldCertificate, Nat → Draw → Memory)
    (spec : ∀ (field : FieldCertificate) (parameter : Nat), FinalSpec (stage1Start parameter) (fin field parameter)) :
    LawShape.Stage1Law Privacy.Instance.crtEntry (CrtTop.machine s1 r replay within) CrtBounded.samplers
      (fun _ _ memory => CrtSource.extract memory.ram) := by
  intro field group parameter
  dsimp only
  rw [@stage1_form_of field Empty Empty (Fintype.ofFinite Empty) (Fintype.ofFinite Empty) (Classical.decEq Empty)
    (Classical.decEq Empty) s1 r replay within size1 cost1 parameter (fin field parameter) (spec field parameter)
    LazyOracle.empty]
  unfold LawShape.routeMWith
  dsimp only
  rw [show (CrtBounded.samplers field group).source = drawLaw.map
      (Option.map (β := (Privacy.Instance.crtEntry.view field group).Source) CrtSource.sourceOf) from rfl]
  refine map_map_eq drawLaw _ _ _ _ fun drawn member => ?_
  cases drawn with
  | none => rfl
  | some d =>
      have back : CrtSource.extract (atPc (CrtTop.machine s1 r replay within) (Design.stage1Halt (CrtTop.blocks s1 r))
          (fin field parameter d)).memory.ram = CrtSource.sourceOf d :=
        extract_final (stage1Start parameter) (fin field parameter) (spec field parameter) d member
      exact congrArg (fun source => some (Entry.publish (CrtSource.sourceOf d), source,
        (LazyOracle.empty : LazyOracle.State Empty Empty))) back.symm

end Law

end CrtStage1Law

end

end Kriterion.CRT.SimMachine
