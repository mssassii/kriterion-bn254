/-
**The opening's head and randomisers, as the CRT machine's rows read them** (`Proof/Simulator/CRT/Stage2Valid.lean`,
`rows_bind`): the output cells the head clamp reads (`outputWords`, `readWords_outputWords`), the cells the opening
writes (`not_openCell`), the memory after the tail and the head clamp (`headMem`, `headMem_ram`, `headMem_bits`),
where the digit points sit after the randomisers (`pointCells_after`), and the randomisers indexed by
`Fin digitCount` (`memSem_lambdas_digit`).
-/

import Proof.Simulator.OpeningLift

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- The output cells the head clamp reads, `(tag₀, Q.x, Q.y)`: `(0, 0, 0)` for `O`. -/
def outputWords : Point → Word × Word × Word
  | .zero => (bitWord false, word 0, word 0)
  | .some (x := x) (y := y) _ => (bitWord true, fieldWord x, fieldWord y)

theorem readWords_outputWords (target : Point) : readWords (outputWords target) = some target := by
  cases target with
  | zero => rfl
  | some x y valid =>
      rw [← readWords_pointWords (.some x y valid)]
      rfl

/-- A cell below the opening's region, other than `tmpM`, is not one of the opening's cells. -/
theorem not_openCell (address : Nat) (below : address < openBase) (notM : address ≠ tmpM) :
    ¬ OpenCell (word address) := by
  unfold OpenCell
  rw [word_small (by unfold openBase at below; omega)]
  intro inside
  rcases inside with inside | same
  · omega
  · exact notM (word_injective (by unfold openBase at below; omega)
      (by unfold tmpM tmpBase; omega) same)

variable [GroupCertificate]

/-- The head clamp's point. -/
abbrev headPoint (target : Point) (points : Fin 90 → FieldMacToECMac.AffineOffset) : Point :=
  target - radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints (Vector.ofFn points))

/-- The memory after the tail and the head clamp. -/
abbrev headMem (memory : Memory) (target : Point) (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    Memory :=
  clearRegs (withRam (tailFold memory points) (putPoint (tailFold memory points).ram (openPoint 0)
    (pointWords (headPoint target points)))) headScratch

omit [FieldCertificate] [GroupCertificate] in
theorem wordAt_eq_triple (words : Word × Word × Word) (first second third : Word)
    (h0 : first = wordAt words 0) (h1 : second = wordAt words 1) (h2 : third = wordAt words 2) :
    (first, second, third) = words := by
  rw [h0, h1, h2]; rfl

/-- The digit points sit at `openPoint d` after the tail, the head and the randomisers. -/
theorem pointCells_after (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset)
    (lams : Fin digitCount → NonZeroBase × NonZeroBase)
    (digit : Fin digitCount) :
    ((foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit)),
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + 1)),
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + 2))) =
        pointWords (digitPoints target (Vector.ofFn points) digit) := by
  have digitSmall : digit.val < 91 := digit.isLt
  have lamOff : ∀ position, position < 3 →
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + position)) =
        putPoint (tailFold memory points).ram (openPoint 0) (pointWords (headPoint target points))
          (word (openPoint digit + position)) := by
    intro position inside
    refine (lamFold_off (headMem memory target points) lams (word (openPoint digit + position))
      (fun index bound => ⟨word_ne (by unfold openPoint openBase; omega)
          (by unfold openLambda openBase; omega) (by unfold openPoint openLambda; omega),
        word_ne (by unfold openPoint openBase; omega)
          (by unfold openTau openBase; omega) (by unfold openPoint openTau; omega)⟩)).trans ?_
    unfold headMem
    rw [(clearRegs_other _ _).1, withRam_ram]
  have atCell : ∀ position, position < 3 →
      putPoint (tailFold memory points).ram (openPoint 0) (pointWords (headPoint target points))
          (word (openPoint digit + position)) =
        wordAt (pointWords (digitPoints target (Vector.ofFn points) digit)) position := by
    intro position inside
    by_cases head : digit.val = 0
    · rw [head, putPoint_at _ _ _ _ (by unfold openPoint openBase; omega) inside]
      unfold digitPoints
      rw [dif_pos head]
    · rw [putPoint_off _ _ _ _ (fun position' inside' => word_ne
          (by unfold openPoint openBase; omega) (by unfold openPoint openBase; omega)
          (by unfold openPoint; omega))]
      have tailCell := tailFold_at memory points ⟨digit.val - 1, by omega⟩ position inside
      have digitIs : (⟨digit.val - 1, by omega⟩ : Fin 90).val + 1 = digit.val := by
        show digit.val - 1 + 1 = digit.val; omega
      rw [digitIs, offsetWords_eq] at tailCell
      rw [tailCell]
      unfold digitPoints
      rw [dif_neg head]
      have getIs : (Vector.ofFn points).get ⟨digit.val - 1, by omega⟩ =
          points ⟨digit.val - 1, by omega⟩ := Vector.get_ofFn _ _
      rw [getIs]
  apply wordAt_eq_triple
  · have := lamOff 0 (by omega)
    rw [Nat.add_zero] at this
    rw [this, ← Nat.add_zero (openPoint digit), atCell 0 (by omega)]
  · rw [lamOff 1 (by omega), atCell 1 (by omega)]
  · rw [lamOff 2 (by omega), atCell 2 (by omega)]

theorem headMem_ram (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    (headMem memory target points).ram = putPoint (tailFold memory points).ram (openPoint 0)
      (pointWords (headPoint target points)) := by
  unfold headMem
  rw [(clearRegs_other _ _).1, withRam_ram]

theorem headMem_bits (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    (headMem memory target points).bits = memory.bits := by
  unfold headMem
  rw [(clearRegs_other _ _).2, withRam_bits, tailFold_bits]

omit [GroupCertificate] in
/-- `memSem_lambdas` with the randomisers indexed by `Fin digitCount` (as `liftLaw` draws them). -/
theorem memSem_lambdas_digit (memory : Memory) :
    Opening.lambdas.memSem memory =
      liftLaw.map (Option.map fun lams : Fin digitCount → NonZeroBase × NonZeroBase =>
        foldStore lamMem 91 memory lams) :=
  memSem_lambdas memory

end

end Kriterion.ArgoMAC.PlanB.SimMachine
