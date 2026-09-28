/-
**The serializer** (M2): `serialize` runs the pieces from the last to the first and leaves on the response stack
exactly `pieceListBits ram pieces` (the wire, `Stage1Pieces.pieces_bits`), changing RAM only in the five record
limbs.

* `pieces_safe`: every word piece reads a cell outside the limbs with at most 256 bits, every record piece names an
  encoding of a coordinate (the index bounds come from the table facts of `Stage1Conv`);
* `memSem_pieceProg`: one piece;
* `memSem_serialize`: all of them.
-/

import Proof.Simulator.CRT.Stage1Record

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.CRT.Entry (joinCount pinCount chunkJoinBase modJoinBase modPinBase)
open CrtStage1 CrtConv CrtRecord

namespace CrtSerial

/-! ### Safe pieces -/

/-- A piece the serializer can run: a word outside the limbs of at most 256 bits, or a record of a coordinate. -/
def PieceSafe : Piece → Prop
  | .word address width => address < 2 ^ 256 ∧ (address < tmpBase ∨ tmpBase + 2 ^ 20 ≤ address) ∧ width ≤ 256
  | .record κ e => κ < 2 ∧ e < encCount κ

theorem pinWidthAt_le (k : Nat) : pinWidthAt k ≤ 14 := by
  by_cases inside : k < 200
  · exact pinWidth_small ⟨k, inside⟩
  · unfold pinWidthAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [← pinCount_eq] at *; unfold pinCount at *; omega)]
    simp

theorem joinPieces_safe (κ start count : Nat) (small : κ < 2) (inRange : start + count ≤ joinCount) :
    ∀ p ∈ joinPieces κ start count, PieceSafe p := by
  intro p member
  simp only [joinPieces, List.mem_map, List.mem_range] at member
  obtain ⟨n, bound, same⟩ := member
  subst same
  have joins : joinCount ≤ 2 ^ 20 := by decide +kernel
  exact ⟨by unfold Layout.sourceJoin; omega, Or.inr (by unfold Layout.sourceJoin tmpBase; omega), by norm_num⟩

theorem pinPieces_safe (κ k : Nat) (small : κ < 2) (inside : k < pinCount) :
    ∀ p ∈ pinPieces κ k, PieceSafe p := by
  intro p member
  simp only [pinPieces, List.mem_map, List.mem_range] at member
  obtain ⟨lane, bound, same⟩ := member
  subst same
  have pins : pinCount = 200 := pinCount_eq
  have active : laneCount = 104 := rfl
  exact ⟨by unfold Layout.sourcePin; omega, Or.inr (by unfold Layout.sourcePin tmpBase; omega),
    le_trans (pinWidthAt_le k) (by norm_num)⟩

theorem convPieces_safe (κ : Nat) (small : κ < 2) : ∀ p ∈ convPieces κ, PieceSafe p := by
  intro p member
  simp only [convPieces, List.mem_append, List.mem_flatMap, List.mem_range] at member
  rcases member with ⟨c, bound, inPart⟩ | ⟨i, _, inPart⟩
  · have c32 : c < 32 := by rw [← chunkCount_eq]; exact bound
    obtain ⟨joinsIn, pinIn, _⟩ := chunkFacts ⟨c, c32⟩
    rcases inPart with inJoins | inPin
    · exact joinPieces_safe κ _ _ small joinsIn p inJoins
    · exact pinPieces_safe κ c small pinIn p inPin
  · revert inPart
    split
    · simp
    · rename_i row odd
      obtain ⟨joinsIn, pinIn, _, _⟩ := modFacts_of i row odd
      intro inPart
      simp only [List.mem_append] at inPart
      rcases inPart with ((((inPart | inPart) | inPart) | inPart) | inPart) | inPart
      · exact joinPieces_safe κ _ _ small (by omega) p inPart
      · exact pinPieces_safe κ _ small (by omega) p inPart
      · exact joinPieces_safe κ _ _ small (by omega) p inPart
      · exact pinPieces_safe κ _ small pinIn p inPart
      · exact joinPieces_safe κ _ _ small (by omega) p inPart
      · exact joinPieces_safe κ _ _ small (by omega) p inPart

theorem pieces_safe : ∀ p ∈ pieces, PieceSafe p := by
  intro p member
  simp only [pieces, List.mem_append] at member
  rcases member with (((((inFields | inRows) | inBytes) | inConv0) | inConv1) | inRec0) | inRec1
  · simp only [List.mem_map, List.mem_range] at inFields
    obtain ⟨index, bound, same⟩ := inFields
    subst same
    have : index < 3 := bound
    exact ⟨by unfold fieldBase; omega, Or.inl (by unfold fieldBase tmpBase; omega), le_rfl⟩
  · simp only [rowPieces, List.mem_flatten, List.mem_map, List.mem_range] at inRows
    obtain ⟨list, ⟨d, bound, rfl⟩, inList⟩ := inRows
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inList
    rcases inList with same | same <;> subst same
    · exact ⟨by unfold fieldBase; omega, Or.inl (by unfold fieldBase tmpBase; omega), le_rfl⟩
    · exact ⟨by unfold Layout.signCell fieldBase; omega, Or.inl (by unfold Layout.signCell fieldBase tmpBase; omega),
        by norm_num⟩
  · simp only [List.mem_map, List.mem_range] at inBytes
    obtain ⟨index, bound, same⟩ := inBytes
    subst same
    have : index < 182 := bound
    exact ⟨by unfold exceptionBase; omega, Or.inl (by unfold exceptionBase tmpBase; omega), by norm_num⟩
  · exact convPieces_safe 0 (by decide) p inConv0
  · exact convPieces_safe 1 (by decide) p inConv1
  · simp only [recordPieces, List.mem_map, List.mem_range] at inRec0
    obtain ⟨e, bound, same⟩ := inRec0
    subst same
    exact ⟨by decide, bound⟩
  · simp only [recordPieces, List.mem_map, List.mem_range] at inRec1
    obtain ⟨e, bound, same⟩ := inRec1
    subst same
    exact ⟨by decide, bound⟩

theorem encCount_le (κ : Nat) : encCount κ ≤ 367 := by
  unfold encCount
  split <;> decide

theorem residue_not_limb (κ e i : Nat) (hκ : κ < 2) (he : e < encCount κ) (hi : i < moduliCount) :
    ¬ LimbCell (word (Layout.residueCell κ i e)) := by
  have := encCount_le κ
  have : i < 85 := hi
  exact not_limbCell _ (by unfold Layout.residueCell; omega) (Or.inr (by unfold Layout.residueCell tmpBase; omega))

/-- Every stored digit is below its modulus. -/
def DigitsSmall (ram : Word → Word) : Prop :=
  ∀ κ e i, κ < 2 → e < encCount κ → i < moduliCount →
    (ram (word (Layout.residueCell κ i e))).toNat < modulusAt i

theorem pieceBits_congr (p : Piece) (safe : PieceSafe p) (ram ram' : Word → Word)
    (same : ∀ address, ¬ LimbCell address → ram' address = ram address) :
    pieceBits ram' p = pieceBits ram p := by
  cases p with
  | word address width =>
      simp only [pieceBits]
      rw [same _ (not_limbCell address safe.1 safe.2.1)]
  | record κ e =>
      have value : recordValue ram' κ e = recordValue ram κ e :=
        Finset.sum_congr rfl fun i member => by
          rw [same _ (residue_not_limb κ e i safe.1 safe.2 (Finset.mem_range.mp member))]
      simp only [pieceBits]
      rw [value]

theorem word_toNat_self (value : Word) : word value.toNat = value := by
  apply BitVec.eq_of_toNat_eq
  simp

variable [FieldCertificate]

/-- **One piece.** -/
theorem memSem_pieceProg (p : Piece) (safe : PieceSafe p) (memory : Memory) (digits : DigitsSmall memory.ram) :
    ∃ after, (pieceProg p).memSem memory = PMF.pure (some after) ∧
      (∀ address, ¬ LimbCell address → after.ram address = memory.ram address) ∧
      after.bits 3 = pieceBits memory.ram p ++ memory.bits 3 ∧
      ∀ stack, stack ≠ 3 → after.bits stack = memory.bits stack := by
  cases p with
  | word address width =>
      obtain ⟨after, run, emits⟩ := memSem_emitWord address width safe.2.2 memory
      exact ⟨after, run, fun address _ => by rw [emits.1], emits.2.1, emits.2.2⟩
  | record κ e =>
      obtain ⟨after, run, off, bitsIs, others⟩ := memSem_recordProg κ e memory
        (fun i => (memory.ram (word (Layout.residueCell κ i e))).toNat)
        (fun i inside => digits κ e i safe.1 safe.2 inside)
        (fun i inside => (word_toNat_self _).symm)
        (fun i inside => residue_not_limb κ e i safe.1 safe.2 inside)
      refine ⟨after, run, off, ?_, others⟩
      rw [bitsIs, hornerSuffix_zero]
      rfl

/-- A deterministic loop under an invariant. -/
theorem memSem_rep_inv (body : Nat → Prog) (Inv : Nat → Memory → Prop) :
    ∀ count : Nat, (∀ index, index < count → ∀ memory, Inv index memory →
      ∃ after, (body index).memSem memory = PMF.pure (some after) ∧ Inv (index + 1) after) →
      ∀ memory, Inv 0 memory → ∃ after, (Prog.rep count body).memSem memory = PMF.pure (some after) ∧
        Inv count after
  | 0, _, memory, start => ⟨memory, by rw [Prog.rep]; rfl, start⟩
  | count + 1, step, memory, start => by
      obtain ⟨middle, run, holds⟩ := memSem_rep_inv body Inv count
        (fun index bound => step index (by omega)) memory start
      obtain ⟨after, last, final⟩ := step count (by omega) middle holds
      refine ⟨after, ?_, final⟩
      rw [Prog.rep, memSem_seq, run, PMF.pure_bind]
      exact last

/-- **A serializer over a list of safe pieces.** -/
theorem memSem_serializeList (list : List Piece) (safeAll : ∀ p ∈ list, PieceSafe p) (memory : Memory)
    (digits : DigitsSmall memory.ram) :
    ∃ after, (Prog.rep list.length fun n => pieceProg (list.getD (list.length - 1 - n) default)).memSem memory =
        PMF.pure (some after) ∧
      (∀ address, ¬ LimbCell address → after.ram address = memory.ram address) ∧
      after.bits 3 = pieceListBits memory.ram list ++ memory.bits 3 ∧
      ∀ stack, stack ≠ 3 → after.bits stack = memory.bits stack := by
  obtain ⟨after, run, off, bitsIs, others⟩ := memSem_rep_inv
    (fun n => pieceProg (list.getD (list.length - 1 - n) default))
    (fun n current => (∀ address, ¬ LimbCell address → current.ram address = memory.ram address) ∧
      current.bits 3 = pieceListBits memory.ram (list.drop (list.length - n)) ++ memory.bits 3 ∧
      ∀ stack, stack ≠ 3 → current.bits stack = memory.bits stack)
    list.length
    (fun n bound current ⟨off, bitsIs, others⟩ => by
      have index : list.length - 1 - n < list.length := by omega
      have safe := safeAll _ (List.getElem_mem index)
      have digitsNow : DigitsSmall current.ram := fun κ e i hκ he hi => by
        rw [off _ (residue_not_limb κ e i hκ he hi)]
        exact digits κ e i hκ he hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index, Option.getD_some]
      obtain ⟨after, run, offNext, bitsNext, othersNext⟩ := memSem_pieceProg _ safe current digitsNow
      refine ⟨after, run, fun address outside => by rw [offNext address outside, off address outside], ?_,
        fun stack other => by rw [othersNext stack other, others stack other]⟩
      rw [bitsNext, bitsIs, pieceBits_congr _ safe memory.ram current.ram off,
        show list.length - (n + 1) = list.length - 1 - n by omega, List.drop_eq_getElem_cons index,
        show list.length - 1 - n + 1 = list.length - n by omega]
      simp [pieceListBits])
    memory ⟨fun _ _ => rfl, by rw [Nat.sub_zero, List.drop_length]; rfl, fun _ _ => rfl⟩
  refine ⟨after, run, off, ?_, others⟩
  rw [bitsIs, Nat.sub_self, List.drop_zero]

/-- **The serializer**: the wire's bits on the response stack, RAM unchanged outside the limbs. -/
theorem memSem_serialize (memory : Memory) (digits : DigitsSmall memory.ram) :
    ∃ after, serialize.memSem memory = PMF.pure (some after) ∧
      (∀ address, ¬ LimbCell address → after.ram address = memory.ram address) ∧
      after.bits 3 = pieceListBits memory.ram pieces ++ memory.bits 3 ∧
      ∀ stack, stack ≠ 3 → after.bits stack = memory.bits stack :=
  memSem_serializeList pieces pieces_safe memory digits

end CrtSerial

end Kriterion.CRT.SimMachine
