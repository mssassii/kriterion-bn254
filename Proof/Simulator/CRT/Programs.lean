/-
**Route M's hash programs, against the abstract simulator** (M6).

* `progSem_eq_exec`: a deterministic block's law on (memory, lazy oracle) is the point mass on its execution, the
  oracle unchanged (generic in the index types);
* `sem_programHash`: one program is `LazyOracle.program (.hash (collectorPoint K k j)) (a, b)`, with the frame of
  the programs;
* `sem_programs`: the 546 programs are `programHashAll (programRequests K drawn)` for the list `drawn` of the
  abstract simulator (`Proof/Privacy/CRT/AbstractSimulator.lean`), whenever the site cells hold `drawn`'s blocks.

Every statement is generic in the index types `FI`, `EI` (the CRT entry uses `Empty`).
-/

import Proof.Simulator.ReplayBase
import Proof.Simulator.CRT.Exec
import Proof.Privacy.CRT.AbstractSimulator
import Construction.Simulator.CRT.Programs

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

noncomputable section

namespace Programs

variable [FieldCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-! ### Deterministic blocks -/

/-- **A deterministic block's law is the point mass on its execution**, the oracle unchanged. -/
theorem progSem_eq_exec : ∀ (program : Prog), program.OpsSatisfy Op.Det → ∀ (memory : Memory)
    (oracle : OState FI EI),
    program.sem memory oracle = PMF.pure ((program.exec memory).map fun after => (after, oracle))
  | .op operation, det, memory, oracle => by
      cases operation
      all_goals first
        | exact (det : False).elim
        | rfl
  | .popBit _ _, _, _, _ => rfl
  | .skip _, _, _, _ => rfl
  | .abort _, _, _, _ => rfl
  | .seq first second, det, memory, oracle => by
      simp only [Prog.sem, Prog.exec]
      unfold andThen
      rw [progSem_eq_exec first det.1 memory oracle, PMF.pure_bind]
      cases first.exec memory with
      | none => rfl
      | some middle => exact progSem_eq_exec second det.2 middle oracle
  | .ite source whenSet whenClear, det, memory, oracle => by
      simp only [Prog.sem, Prog.exec]
      split
      · exact progSem_eq_exec whenClear det.2 memory oracle
      · exact progSem_eq_exec whenSet det.1 memory oracle

/-- A hash request decodes its input and ignores the index. -/
theorem query_hash_generic (index input : Word) :
    queryFromRegisters (FixedIndex := FI) (EncIndex := EI) 4 index input =
      some (.hash (input.toNat : BaseField)) := by
  unfold queryFromRegisters
  rfl

/-! ### One program -/

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem prefix_det (cells : ProgramCells) (k j : Nat) : (programPrefix cells k j).OpsSatisfy Op.Det := by
  unfold programPrefix
  exact ⟨⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- The tag of a mask answer is below `2^40`. -/
theorem tagCode_mask_lt (k j : Nat) (kSmall : k < 2 ^ 16) (jSmall : j < 64) :
    tagCode Family.mask 0 0 0 0 k j < 2 ^ 40 := by
  unfold tagCode Family.mask
  omega

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- **The prefix of one program**: the hash input and the two answer words in their registers. -/
theorem exec_programPrefix (cells : ProgramCells) (k j : Nat) (memory : Memory) (key a b : Block)
    (keyCell : memory.ram (word cells.key) = blockWord key)
    (firstCell : memory.ram (word (cells.half k (2 * j))) = blockWord a)
    (secondCell : memory.ram (word (cells.half k (2 * j + 1))) = blockWord b)
    (tagSmall : tagCode Family.mask 0 0 0 0 k j < 2 ^ 40) :
    ∃ after, (programPrefix cells k j).exec memory = some after ∧
      Frame programsWrites programsClobbers memory after ∧
      after.registers rInput = word (hashInput key (tagCode Family.mask 0 0 0 0 k j)) ∧
      after.registers rFirst = blockWord a ∧ after.registers rSecond = blockWord b := by
  have keySmall : key.toNat < 2 ^ 128 := key.isLt
  refine ⟨_, rfl, ⟨fun _ _ => rfl, rfl, fun register outside => ?_⟩, ?_, ?_, ?_⟩
  · simp only [programsClobbers, Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at outside
    obtain ⟨n1, n2, n3, n4, n5⟩ := outside
    simp only [setReg, Function.update_apply, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5]
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false]
    rw [keyCell]
    apply BitVec.eq_of_toNat_eq
    have tagLt : 2 ^ 128 * tagCode Family.mask 0 0 0 0 k j < 2 ^ 256 := by omega
    simp only [Arithmetic.eval, BitVec.toNat_add, blockWord_toNat, word, BitVec.toNat_ofNat, tagWord,
      hashInput, Nat.mod_eq_of_lt tagLt]
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false]
    exact firstCell
  · simp (config := {decide := true}) only [setReg, Function.update_apply, if_true, if_false]
    exact secondCell

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem hashInput_lt (key : Block) (tag : Nat) (tagSmall : tag < 2 ^ 40) :
    hashInput key tag < 2 ^ 256 := by
  have := key.isLt
  unfold hashInput
  omega

/-- **One program**: `K + 2^128 · tag(k, j) ↦ (a, b)`, memory kept up to the programs' frame. -/
theorem sem_programHash (cells : ProgramCells) (k j : Nat) (memory : Memory) (key a b : Block)
    (keyCell : memory.ram (word cells.key) = blockWord key)
    (firstCell : memory.ram (word (cells.half k (2 * j))) = blockWord a)
    (secondCell : memory.ram (word (cells.half k (2 * j + 1))) = blockWord b)
    (tagSmall : tagCode Family.mask 0 0 0 0 k j < 2 ^ 40) :
    ∃ after, Frame programsWrites programsClobbers memory after ∧ ∀ oracle : OState FI EI,
      (programHash cells k j).sem memory oracle =
        PMF.pure ((LazyOracle.program (.hash (Privacy.collectorPoint key k j)) (a, b) oracle).map
          fun updated => (after, updated)) := by
  obtain ⟨after, run, frame, input, first, second⟩ :=
    exec_programPrefix cells k j memory key a b keyCell firstCell secondCell tagSmall
  refine ⟨after, frame, fun oracle => ?_⟩
  unfold programHash
  simp only [Prog.sem]
  unfold andThen
  rw [progSem_eq_exec _ (prefix_det cells k j) memory oracle, run, Option.map_some, PMF.pure_bind]
  simp only [Op.sem]
  rw [query_hash_generic, input, first, second]
  simp only [answerFromWords, blockWord_block]
  rw [word_toNat (hashInput_lt key _ tagSmall)]
  rfl

/-! ### The batch -/

omit [FieldCertificate] [Fintype FI] [Fintype EI] in
theorem programHashAll_append (first second : List (BaseField × (Block × Block))) (oracle : OState FI EI) :
    Privacy.programHashAll (first ++ second) oracle =
      (Privacy.programHashAll first oracle).bind (Privacy.programHashAll second) := by
  induction first generalizing oracle with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨point, answer⟩ := head
      simp only [List.cons_append, Privacy.programHashAll]
      rw [Option.bind_assoc]
      congr 1
      funext updated
      exact ih updated

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem finRange_flatMap_succ' {β : Type} (count : Nat) (f : Nat → List β) :
    (List.finRange (count + 1)).flatMap (fun index => f index.val) =
      (List.finRange count).flatMap (fun index => f index.val) ++ f count := by
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem union_self_writes {W : Writes} : ∀ address, W.union W address → W address :=
  fun _ holds => holds.elim id id

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem union_self_clobbers {C : Clobbers} : ∀ register, C.union C register → C register :=
  fun _ holds => holds.elim id id

/-- **A `rep` whose steps are hash programs is the concatenated request list**, with the frame of its steps. -/
theorem sem_rep_programHash {W : Writes} {C : Clobbers} (count : Nat) (body : Nat → Prog)
    (requests : Nat → List (BaseField × (Block × Block))) (start : Memory)
    (step : ∀ index memory, index < count → Frame W C start memory →
      ∃ after, Frame W C memory after ∧ ∀ oracle : OState FI EI,
        (body index).sem memory oracle =
          PMF.pure ((Privacy.programHashAll (requests index) oracle).map fun updated => (after, updated))) :
    ∀ done, done ≤ count → ∃ after, Frame W C start after ∧ ∀ oracle : OState FI EI,
      (Prog.rep done body).sem start oracle =
        PMF.pure ((Privacy.programHashAll ((List.finRange done).flatMap fun index => requests index.val)
          oracle).map fun updated => (after, updated))
  | 0, _ => ⟨start, Frame.refl W C start, fun oracle => by rw [Prog.rep]; rfl⟩
  | done + 1, bound => by
      obtain ⟨middle, middleFrame, run⟩ := sem_rep_programHash count body requests start step done (by omega)
      obtain ⟨after, afterFrame, run'⟩ := step done middle (by omega) middleFrame
      refine ⟨after, (middleFrame.trans afterFrame).mono union_self_writes union_self_clobbers,
        fun oracle => ?_⟩
      rw [Prog.rep]
      simp only [Prog.sem]
      unfold andThen
      rw [run, PMF.pure_bind, finRange_flatMap_succ', programHashAll_append]
      cases Privacy.programHashAll ((List.finRange done).flatMap fun index => requests index.val) oracle with
      | none => rfl
      | some updated =>
          simp only [Option.map_some, Option.bind_some]
          exact run' updated

/-- The two requests of site `k` with preimage limbs and fourth block `drawn` (the abstract simulator's
`programRequests` on one entry). -/
def siteRequests (key : Block) (k : Nat) (drawn : (Block × Block × Block) × Block) :
    List (BaseField × (Block × Block)) :=
  [(Privacy.collectorPoint key k 0, (drawn.1.1, drawn.1.2.1)),
    (Privacy.collectorPoint key k 1, (drawn.1.2.2, drawn.2))]

/-- The site's cells hold its four halves. -/
def SiteHolds (cells : ProgramCells) (memory : Memory) (k : Nat) (drawn : (Block × Block × Block) × Block) :
    Prop :=
  memory.ram (word (cells.half k 0)) = blockWord drawn.1.1 ∧
    memory.ram (word (cells.half k 1)) = blockWord drawn.1.2.1 ∧
    memory.ram (word (cells.half k 2)) = blockWord drawn.1.2.2 ∧
    memory.ram (word (cells.half k 3)) = blockWord drawn.2

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem frame_ram_none {C : Clobbers} {start after : Memory} (frame : Frame programsWrites C start after)
    (address : Word) : after.ram address = start.ram address :=
  frame.ram address fun holds => holds

/-- **One site**: its two programs. -/
theorem sem_programSite (cells : ProgramCells) (k : Nat) (kSmall : k < 2 ^ 16) (memory : Memory) (key : Block)
    (drawn : (Block × Block × Block) × Block) (keyCell : memory.ram (word cells.key) = blockWord key)
    (holds : SiteHolds cells memory k drawn) :
    ∃ after, Frame programsWrites programsClobbers memory after ∧ ∀ oracle : OState FI EI,
      (programSite cells k).sem memory oracle =
        PMF.pure ((Privacy.programHashAll (siteRequests key k drawn) oracle).map
          fun updated => (after, updated)) := by
  obtain ⟨h0, h1, h2, h3⟩ := holds
  obtain ⟨middle, middleFrame, run0⟩ := sem_programHash (FI := FI) (EI := EI) cells k 0 memory key
    drawn.1.1 drawn.1.2.1 keyCell h0 h1 (tagCode_mask_lt k 0 kSmall (by omega))
  obtain ⟨after, afterFrame, run1⟩ := sem_programHash (FI := FI) (EI := EI) cells k 1 middle key
    drawn.1.2.2 drawn.2 (by rw [frame_ram_none middleFrame, keyCell])
    (by rw [frame_ram_none middleFrame]; exact h2) (by rw [frame_ram_none middleFrame]; exact h3)
    (tagCode_mask_lt k 1 kSmall (by omega))
  refine ⟨after, (middleFrame.trans afterFrame).mono union_self_writes union_self_clobbers,
    fun oracle => ?_⟩
  unfold programSite
  simp only [Prog.sem]
  unfold andThen
  rw [run0 oracle, PMF.pure_bind]
  simp only [siteRequests, Privacy.programHashAll]
  cases LazyOracle.program (.hash (Privacy.collectorPoint key k 0)) (drawn.1.1, drawn.1.2.1) oracle with
  | none => rfl
  | some updated =>
      simp only [Option.map_some, Option.bind_some]
      rw [run1 updated]
      cases LazyOracle.program (.hash (Privacy.collectorPoint key k 1)) (drawn.1.2.2, drawn.2) updated with
      | none => rfl
      | some final => rfl

/-! ### The 546 programs against `programRequests` -/

/-- Collector `c` of digit `d`, in `collectorList`'s order. -/
def collectorAt (d : Fin 91) : Fin 3 → Privacy.BMR.Collector
  | 0 => ⟨(d, .inl .rowX_x9), Or.inl rfl⟩
  | 1 => ⟨(d, .inl .rowY_x9), Or.inr (Or.inl rfl)⟩
  | 2 => ⟨(d, .inl .rowZ_x9), Or.inr (Or.inr rfl)⟩

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem collectorList_eq :
    Privacy.collectorList = (List.finRange 91).flatMap fun d =>
      [collectorAt d 0, collectorAt d 1, collectorAt d 2] := rfl

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem collectorIndex_at (d : Fin 91) (c : Fin 3) : Privacy.collectorIndex (collectorAt d c) = 3 * d.val + c.val := by
  fin_cases c <;> rfl

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- The abstract request list, digit by digit. -/
theorem programRequests_eq (key : Block) (draws : Privacy.BMR.Collector → (Block × Block × Block) × Block) :
    Privacy.programRequests key (Privacy.collectorList.map fun c => (c, draws c)) =
      (List.finRange 91).flatMap fun d => (List.finRange 3).flatMap fun c =>
        siteRequests key (3 * d.val + c.val) (draws (collectorAt d c)) := by
  rw [collectorList_eq]
  unfold Privacy.programRequests
  rw [List.flatMap_map, List.flatMap_assoc]
  congr 1

/-- The site cells of every collector hold its draws. -/
def AllHold (cells : ProgramCells) (memory : Memory) (draws : Privacy.BMR.Collector → (Block × Block × Block) × Block) :
    Prop :=
  ∀ (d : Fin 91) (c : Fin 3), SiteHolds cells memory (3 * d.val + c.val) (draws (collectorAt d c))

omit [FieldCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem siteHolds_frame (cells : ProgramCells) {start memory : Memory} {C : Clobbers}
    (frame : Frame programsWrites C start memory) (k : Nat) (drawn : (Block × Block × Block) × Block)
    (holds : SiteHolds cells start k drawn) : SiteHolds cells memory k drawn := by
  obtain ⟨h0, h1, h2, h3⟩ := holds
  exact ⟨(frame_ram_none frame _).trans h0, (frame_ram_none frame _).trans h1,
    (frame_ram_none frame _).trans h2, (frame_ram_none frame _).trans h3⟩

/-- **The 546 programs** are the abstract simulator's `programHashAll (programRequests K drawn)` for the draws the
site cells hold, in `collectorList`'s order. -/
theorem sem_programs (cells : ProgramCells) (memory : Memory) (key : Block)
    (draws : Privacy.BMR.Collector → (Block × Block × Block) × Block)
    (keyCell : memory.ram (word cells.key) = blockWord key) (holds : AllHold cells memory draws) :
    ∃ after, Frame programsWrites programsClobbers memory after ∧ ∀ oracle : OState FI EI,
      (programs cells).sem memory oracle =
        PMF.pure ((Privacy.programHashAll
          (Privacy.programRequests key (Privacy.collectorList.map fun c => (c, draws c))) oracle).map
            fun updated => (after, updated)) := by
  let digitRequests : Nat → List (BaseField × (Block × Block)) := fun d =>
    if inside : d < 91 then (List.finRange 3).flatMap fun c =>
      siteRequests key (3 * d + c.val) (draws (collectorAt ⟨d, inside⟩ c)) else []
  have digitStep : ∀ d memory', d < 91 → Frame programsWrites programsClobbers memory memory' →
      ∃ after, Frame programsWrites programsClobbers memory' after ∧ ∀ oracle : OState FI EI,
        (Prog.rep 3 fun c => programSite cells (3 * d + c)).sem memory' oracle =
          PMF.pure ((Privacy.programHashAll (digitRequests d) oracle).map fun updated => (after, updated)) := by
    intro d memory' inside frame
    let siteReq : Nat → List (BaseField × (Block × Block)) := fun c =>
      if small : c < 3 then siteRequests key (3 * d + c) (draws (collectorAt ⟨d, inside⟩ ⟨c, small⟩)) else []
    obtain ⟨after, afterFrame, run⟩ := sem_rep_programHash (FI := FI) (EI := EI) 3
      (fun c => programSite cells (3 * d + c)) siteReq memory'
      (fun c memory'' small frame' => by
        have site := sem_programSite (FI := FI) (EI := EI) cells (3 * d + c) (by omega) memory'' key
          (draws (collectorAt ⟨d, inside⟩ ⟨c, small⟩))
          (by rw [frame_ram_none frame', frame_ram_none frame, keyCell])
          (siteHolds_frame cells frame' _ _ (siteHolds_frame cells frame _ _ (holds ⟨d, inside⟩ ⟨c, small⟩)))
        simp only [siteReq, dif_pos small]
        exact site) 3 le_rfl
    refine ⟨after, afterFrame, fun oracle => ?_⟩
    rw [run oracle]
    congr 3
    simp only [digitRequests, dif_pos inside, siteReq]
    congr 1
    funext c
    rw [dif_pos c.isLt]
  obtain ⟨after, afterFrame, run⟩ := sem_rep_programHash (FI := FI) (EI := EI) 91
    (fun d => Prog.rep 3 fun c => programSite cells (3 * d + c)) digitRequests memory
    (fun d memory' small frame => digitStep d memory' small frame) 91 le_rfl
  refine ⟨after, afterFrame, fun oracle => ?_⟩
  unfold programs
  rw [run oracle, programRequests_eq]
  congr 3

end Programs

end

end Kriterion.CRT.SimMachine
