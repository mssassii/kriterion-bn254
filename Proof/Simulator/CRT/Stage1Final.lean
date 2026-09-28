/-
**What stage 1 leaves** (M7).

* `DrawValid`: what every draw in the support of `CrtDraws.drawLaw` satisfies (`drawValid_of_support`); it
  gives `DrawSmall` (`DrawValid.small`) and in-range cells after the stores (`cellsValid_stored`).
* `finalOf memory d`: the memory the deterministic tail leaves after the stores of `d`, with `finalOf_spec`
  (the conjuncts of `CrtTail.memSem_tail`).
* `stored_off`, `final_off`: the cells the stores and the tail leave alone.
-/

import Proof.Simulator.CRT.Stage1Tail
import Proof.Simulator.CutoffSamplers
import Proof.Simulator.Stage2Start

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open CrtStage1 CrtDraws CrtStored CrtRecord CrtSource CrtTail

namespace CrtStage1Final

noncomputable section

/-! ### The support of the draws -/

/-- **What a drawn value satisfies.** -/
structure DrawValid (d : Draw) : Prop where
  bytes : ∀ n, d.bytes n < 2 ^ 4
  joins : ∀ n, d.joins n < 2 ^ labelBits
  pins : ∀ n, d.pins n < 2 ^ pinWidthAt (pinOf n.val)
  digits : ∀ n, d.digits n < modulusAt (n.val % moduliCount)
  zeros : ∀ n, d.zeros n < 2 ^ 128
  deltas : ∀ n, d.deltas n < 2 ^ 128
  signs : ∀ n, d.signs n < 2 ^ 1

/-- A value of an `optBind` is a value of the continuation at a value of the first law. -/
theorem mem_optBind {α β : Type} (law : PMF (Option α)) (next : α → PMF (Option β)) (value : β)
    (member : some value ∈ (optBind law next).support) :
    ∃ drawn, some drawn ∈ law.support ∧ some value ∈ (next drawn).support := by
  simp only [optBind, PMF.mem_support_bind_iff] at member
  obtain ⟨drawn, drawnMember, rest⟩ := member
  cases drawn with
  | none => simp at rest
  | some drawn => exact ⟨drawn, drawnMember, rest⟩

variable [FieldCertificate]

omit [FieldCertificate] in
/-- **Every draw in the support is valid.** -/
theorem drawValid_of_support (d : Draw) (member : some d ∈ drawLaw.support) : DrawValid d := by
  unfold drawLaw at member
  obtain ⟨f, _, m1⟩ := mem_optBind _ _ _ member
  obtain ⟨b, bm, m2⟩ := mem_optBind _ _ _ m1
  obtain ⟨j, jm, m3⟩ := mem_optBind _ _ _ m2
  obtain ⟨p, pm, m4⟩ := mem_optBind _ _ _ m3
  obtain ⟨g, gm, m5⟩ := mem_optBind _ _ _ m4
  obtain ⟨z, zm, m6⟩ := mem_optBind _ _ _ m5
  obtain ⟨dl, dlm, m7⟩ := mem_optBind _ _ _ m6
  obtain ⟨sg, sgm, m8⟩ := mem_optBind _ _ _ m7
  rw [PMF.mem_support_pure_iff, Option.some.injEq] at m8
  subst m8
  unfold bytesLaw at bm
  unfold joinsLaw at jm
  unfold pinsLaw at pm
  unfold digitsLaw at gm
  unfold zerosLaw at zm
  unfold deltasLaw at dlm
  unfold signsLaw at sgm
  exact
    { bytes := fun n => wordLaw_support 4 _ (optionProduct_support _ _ b bm n)
      joins := fun n => wordLaw_support labelBits _ (optionProduct_support _ _ j jm n)
      pins := fun n => wordLaw_support _ _ (optionProduct_support _ _ p pm n)
      digits := fun n => by
        have accepted := (rejectLaw_support _ _ _ _ (optionProduct_support _ _ g gm n)).1
        exact of_decide_eq_true accepted
      zeros := fun n => wordLaw_support 128 _ (optionProduct_support _ _ z zm n)
      deltas := fun n => wordLaw_support 128 _ (optionProduct_support _ _ dl dlm n)
      signs := fun n => wordLaw_support 1 _ (optionProduct_support _ _ sg sgm n) }

omit [FieldCertificate] in
theorem pow_le_256 {width : Nat} (small : width ≤ 256) : 2 ^ width ≤ 2 ^ 256 :=
  Nat.pow_le_pow_right (by norm_num) small

/-- A valid draw fits the words. -/
theorem DrawValid.small {d : Draw} (valid : DrawValid d) : DrawSmall d where
  bytes n := lt_of_lt_of_le (valid.bytes n) (pow_le_256 (by norm_num))
  joins n := lt_of_lt_of_le (valid.joins n) (pow_le_256 (by norm_num))
  pins n := lt_of_lt_of_le (valid.pins n) (pow_le_256 (pinWidthAt_small _))
  digits n := lt_trans (valid.digits n) (digitWidth_small n.val).2
  zeros n := lt_of_lt_of_le (valid.zeros n) (pow_le_256 (by norm_num))
  deltas n := lt_of_lt_of_le (valid.deltas n) (pow_le_256 (by norm_num))
  signs n := lt_of_lt_of_le (valid.signs n) (pow_le_256 (by norm_num))

/-- **The stores of a valid draw leave every source cell in range.** -/
theorem cellsValid_stored (memory : Memory) (d : Draw) (valid : DrawValid d) :
    CellsValid (storedMem memory d).ram where
  fields index inside := by
    have cell := stored_fields memory d ⟨index, inside⟩
    dsimp only at cell
    have below := (d.fields ⟨index, inside⟩).val_lt
    rw [cell, toNat_ofNat_small _ (lt_trans below (by unfold baseFieldModulus; norm_num))]
    exact below
  bytes n inside := by
    have cell := stored_bytes memory d ⟨n, inside⟩
    dsimp only at cell
    rw [cell, toNat_ofNat_small _ (valid.small.bytes _)]
    exact valid.bytes _
  joins n inside := by
    have cell := stored_joins memory d ⟨n, inside⟩
    dsimp only at cell
    rw [cell, toNat_ofNat_small _ (valid.small.joins _)]
    exact valid.joins _
  pins n inside := by
    have cell := stored_pins memory d ⟨n, inside⟩
    dsimp only at cell
    rw [cell, toNat_ofNat_small _ (valid.small.pins _)]
    exact valid.pins ⟨n, inside⟩
  digits n inside := by
    have cell := stored_digits memory d ⟨n, inside⟩
    dsimp only at cell
    rw [cell, toNat_ofNat_small _ (valid.small.digits _)]
    exact valid.digits ⟨n, inside⟩
  signs n inside := by
    have cell := stored_signs memory d ⟨n, inside⟩
    dsimp only at cell
    rw [cell, toNat_ofNat_small _ (valid.small.signs _)]
    exact valid.signs ⟨n, inside⟩

/-! ### Cells the stores and the tail leave alone -/

/-- A cell outside every stage-1 region keeps its value through the stores. -/
theorem stored_off (memory : Memory) (d : Draw) (target : Nat) (small : target < 2 ^ 256)
    (offDeltas : target < 2 ^ 55 ∨ 2 ^ 55 + 2 ≤ target)
    (offZeros : target < keyBase ∨ keyBase + 2 * labelCount ≤ target)
    (offDigits : target < 2 ^ 53 ∨ 2 ^ 53 + 2 ^ 25 ≤ target)
    (offPins : target < 2 ^ 52 ∨ 2 ^ 52 + 2 ^ 25 ≤ target)
    (offJoins : target < 2 ^ 51 ∨ 2 ^ 51 + 2 ^ 25 ≤ target)
    (offBytes : target < exceptionBase ∨ exceptionBase + exceptionCellCount ≤ target)
    (offFields : target < fieldBase ∨ fieldBase + fieldCount ≤ target)
    (offSigns : target < fieldBase + 276 ∨ fieldBase + 276 + 91 ≤ target) :
    (storedMem memory d).ram (word target) = memory.ram (word target) := by
  rw [stored_ram_upto_joins memory d target small offDeltas offZeros offDigits offPins offSigns,
    foldStore_ram_off _ (fun n => word (joinAddr n)) _ (fun n => wordStore_ram _) (2 * Entry.joinCount) _ _ _
      (fun k bound => by
        have := joinAddr_range k bound
        exact word_ne small (by omega) (by omega)),
    foldStore_ram_off _ (fun n => word (exceptionBase + n)) _ (fun n => wordStep_ram exceptionBase n)
      exceptionCellCount _ _ _
      (fun k bound => word_ne small (by unfold exceptionBase exceptionCellCount at *; omega)
        (by unfold exceptionBase exceptionCellCount at *; omega)),
    foldStore_ram_off _ (fun n => word (fieldBase + n)) _ (fun n => cellStep_ram fieldBase n) fieldCount _ _ _
      (fun k bound => word_ne small (by unfold fieldBase fieldCount curveCellCount rowCellCount at *; omega)
        (by unfold fieldBase fieldCount curveCellCount rowCellCount at *; omega))]

omit [FieldCertificate] in
/-- A cell away from the true labels is not one. -/
theorem not_trueCell (target : Nat) (small : target < 2 ^ 256)
    (away : target < keyBase ∨ keyBase + 2 * labelCount ≤ target ∨ target % 2 = keyBase % 2) :
    ¬ TrueCell (word target) := by
  rintro ⟨j, jb, same⟩
  have := word_inj small (by unfold trueCell keyBase labelCount at *; omega) same
  unfold trueCell at this
  unfold keyBase labelCount at *
  omega

omit [FieldCertificate] in
/-- A cell away from the limbs and the true labels keeps its value through the tail. -/
theorem final_off (final memory : Memory)
    (same : ∀ address, ¬ LimbCell address → ¬ TrueCell address → final.ram address = memory.ram address)
    (target : Nat) (small : target < 2 ^ 256) (offLimbs : target < tmpBase ∨ tmpBase + 2 ^ 20 ≤ target)
    (offKeys : target < keyBase ∨ keyBase + 2 * labelCount ≤ target ∨ target % 2 = keyBase % 2) :
    final.ram (word target) = memory.ram (word target) :=
  same _ (not_limbCell _ small offLimbs) (not_trueCell _ small offKeys)

/-! ### The memory the tail leaves -/

/-- The memory the tail leaves, from a memory whose cells are in range. -/
def tailFinal (memory : Memory) (valid : CellsValid memory.ram) : Memory :=
  Classical.choose (memSem_tail memory valid)

/-- **The memory stage 1 leaves**, after the stores of `d` and the tail (the stores themselves when the cells
are out of range, which no draw in the support produces). The memory argument of `memSem_tail` is explicit:
left to unification it comes out eta-expanded, and the kernel then evaluates the stores. -/
def finalOf (memory : Memory) (d : Draw) : Memory :=
  haveI := Classical.propDecidable (CellsValid (storedMem memory d).ram)
  if valid : CellsValid (storedMem memory d).ram then tailFinal (storedMem memory d) valid else storedMem memory d

theorem finalOf_eq (memory : Memory) (d : Draw) (valid : CellsValid (storedMem memory d).ram) :
    finalOf memory d = tailFinal (storedMem memory d) valid := by
  unfold finalOf
  rw [dif_pos valid]

/-- **The tail's run and effect**, at `tailFinal` (generic in the memory: instantiated at `storedMem memory d`
directly, the kernel check of `Classical.choose_spec` evaluates the stores). -/
theorem tailFinal_spec (memory : Memory) (valid : CellsValid memory.ram) :
    tail.memSem memory = PMF.pure (some (tailFinal memory valid)) ∧
      (tailFinal memory valid).bits 3 = byteBits (Entry.Wire.encoding.encode
        (Entry.publish (extract memory.ram))) ++ memory.bits 3 ∧
      (∀ stack, stack ≠ 3 → (tailFinal memory valid).bits stack = memory.bits stack) ∧
      (∀ register, (tailFinal memory valid).registers register = 0) ∧
      (∀ k, k < recordLimbCount → (tailFinal memory valid).ram (word (recordLimb k)) = word 0) ∧
      (∀ j, j < labelCount → (tailFinal memory valid).ram (word (trueCell j)) =
        memory.ram (word (keyBase + 2 * j)) ^^^ memory.ram (word (Layout.deltaCell (j / 254)))) ∧
      (∀ address, ¬ LimbCell address → ¬ TrueCell address → (tailFinal memory valid).ram address = memory.ram address) :=
  Classical.choose_spec (memSem_tail memory valid)

/-- **The tail's run and effect**, at `finalOf`. -/
theorem finalOf_spec (memory : Memory) (d : Draw) (valid : CellsValid (storedMem memory d).ram) :
    tail.memSem (storedMem memory d) = PMF.pure (some (finalOf memory d)) ∧
      (finalOf memory d).bits 3 = byteBits (Entry.Wire.encoding.encode
        (Entry.publish (extract (storedMem memory d).ram))) ++ (storedMem memory d).bits 3 ∧
      (∀ stack, stack ≠ 3 → (finalOf memory d).bits stack = (storedMem memory d).bits stack) ∧
      (∀ register, (finalOf memory d).registers register = 0) ∧
      (∀ k, k < recordLimbCount → (finalOf memory d).ram (word (recordLimb k)) = word 0) ∧
      (∀ j, j < labelCount → (finalOf memory d).ram (word (trueCell j)) =
        (storedMem memory d).ram (word (keyBase + 2 * j)) ^^^
          (storedMem memory d).ram (word (Layout.deltaCell (j / 254)))) ∧
      (∀ address, ¬ LimbCell address → ¬ TrueCell address →
        (finalOf memory d).ram address = (storedMem memory d).ram address) := by
  rw [finalOf_eq memory d valid]
  exact tailFinal_spec (storedMem memory d) valid

end

end CrtStage1Final

end Kriterion.CRT.SimMachine
