/-
**Stage 2's start, as the CRT machine reads it** (`Proof/Simulator/CRT/Stage2Start.lean`, `ValidStart.lean`,
`Stage1Final.lean`): values of an `optionProduct` and of a coin word (`optionProduct_support`, `wordLaw_support`), the
request's output tags (`outTags`), and the prefix of a valid request (`prefixStart`, `prefix_middle`: the flag is set,
the response stack is empty, the parse is in RAM and the labels are the selected key words).
-/

import Proof.Simulator.OpeningLaw

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### The support of the draws -/

/-- A value of an `optionProduct` is a value of every factor. -/
theorem optionProduct_support {α : Type} :
    ∀ (count : Nat) (sample : Fin count → PMF (Option α)) (values : Fin count → α),
      some values ∈ (optionProduct count sample).support →
        ∀ index, some (values index) ∈ (sample index).support
  | 0, _, _, _, index => index.elim0
  | count + 1, sample, values, member, index => by
      simp only [optionProduct, PMF.mem_support_bind_iff] at member
      obtain ⟨head, headMember, rest⟩ := member
      cases head with
      | none => simp at rest
      | some head =>
          simp only [PMF.mem_support_map_iff] at rest
          obtain ⟨tail, tailMember, same⟩ := rest
          cases tail with
          | none => simp at same
          | some tail =>
              simp only [Option.map_some, Option.some.injEq] at same
              subst same
              refine Fin.cases ?_ (fun later => ?_) index
              · simpa using headMember
              · simpa using optionProduct_support count (fun index => sample index.succ) tail
                  tailMember later

theorem wordLaw_support (width value : Nat)
    (member : some value ∈ ((wordLaw width).map some).support) : value < 2 ^ width := by
  simp only [PMF.mem_support_map_iff, wordLaw, Option.some.injEq] at member
  obtain ⟨drawn, drawnMember, same⟩ := member
  obtain ⟨index, _, rfl⟩ := drawnMember
  exact same ▸ index.isLt

section Prefix

variable [FieldCertificate]

/-- The request's output tags and `Q` for a defined output. -/
def outTags : Point → Bool × Bool × Nat × Nat
  | .zero => (false, true, 0, 0)
  | .some (x := x) (y := y) _ => (true, false, x.val, y.val)

theorem outTags_bits (target : Point) :
    OutBits (SimulatorProtocol.output (some target)) (outTags target).1 (outTags target).2.1
      (outTags target).2.2.1 (outTags target).2.2.2 := by
  cases target with
  | zero => simp [OutBits, outTags, SimulatorProtocol.output]
  | some nonsingular =>
      simp only [OutBits, outTags, ↓reduceIte]
      refine ⟨?_, coord_small _, coord_small _⟩
      simp only [SimulatorProtocol.output, SimulatorProtocol.affine, bits_eq_lsbs]
      rfl

theorem outTags_flag (target : Point) :
    bitWord (outTags target).1 + bitWord (outTags target).2.1 ≠ 0 := by
  cases target with
  | zero =>
      show bitWord false + bitWord true ≠ 0
      decide
  | some nonsingular =>
      show bitWord true + bitWord false ≠ 0
      decide

theorem outTags_words (target : Point) :
    outputWords target = (bitWord (outTags target).1, word (outTags target).2.2.1,
      word (outTags target).2.2.2) := by
  cases target <;> rfl

/-- The memory stage 2's prefix starts from. -/
def prefixStart (memory : Memory) (input : AffineInput) (target : Point) : Memory :=
  Top.afterTag (stage2Memory memory input (some target)) (stage2Rest input (some target))

/-- **The prefix of a valid request**: the flag is set, the response stack is empty, the cells
below the label region read as the parse, and the labels are the selected key words. -/
theorem prefix_middle (memory : Memory) (input : AffineInput) (target : Point) :
    ∃ middle, Request.prefixProgram.memSem (prefixStart memory input target) =
        PMF.pure (some middle) ∧
      middle.registers rFlag ≠ 0 ∧ middle.bits 3 = [] ∧
      (∀ value, value < 2 ^ 44 → middle.ram (word value) =
        parsedRam memory.ram input.x.val input.y.val (outTags target).1 (outTags target).2.1
          (outTags target).2.2.1 (outTags target).2.2.2 (word value)) ∧
      (∀ i, i < 508 → middle.ram (word (labelBase + i)) =
        memory.ram (word (keyBase + 2 * i + inputBit input.x.val input.y.val i))) := by
  obtain ⟨middle, run, bitsAfter, labels, away, flag⟩ := memSem_prefix
    (prefixStart memory input target) input.x.val input.y.val (coord_small _) (coord_small _)
    (SimulatorProtocol.output (some target)) (outTags target).1 (outTags target).2.1
    (outTags target).2.2.1 (outTags target).2.2.2 (outTags_bits target)
    (afterTag_request memory input (some target))
  refine ⟨middle, run, by rw [flag]; exact outTags_flag target, ?_, fun value small => ?_,
    fun i bound => labels i bound⟩
  · rw [bitsAfter, Function.update_of_ne (by decide)]
    exact afterTag_response memory input (some target)
  · rw [away _ fun position bound => word_ne (by omega) (labelCell_lt position bound)
      (by unfold labelBase; omega)]
    rfl

end Prefix

end

end Kriterion.ArgoMAC.PlanB.SimMachine
