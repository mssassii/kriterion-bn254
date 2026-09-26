/-
**The replay's outputs in RAM, and the collector solve against the abstract simulator** (M6/M7 interface).

* `encCell`, `rowMaskCell`, `OutHolds`: where the replay leaves the abstract `ReplayOut` (the non-collector masks at `Layout.maskCell κ e` with `e` the
  element index, the key at `Layout.keyCell`). the M5b post concludes `OutHolds`.
* `dxOf`, `pxOf`, `dyOf`, `pyOf`: the cell contents as functions of the flat index;
* `digitCells_of_out`: `OutHolds` and the request, row and target cells give `Solve.DigitCells`;
* `maskFormula_eq`: the machine's mask formula is the abstract simulator's `collectorMasks`.
-/

import Proof.Simulator.CRT.Solve
import Proof.Simulator.CRT.Programs
import Proof.Privacy.CRT.Core.EncIndex

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB (RowGamma XElement YElement xElementIndex yElementIndex)
open Kriterion.CRT.Privacy (ReplayOut)

noncomputable section

namespace OutCells

/-- The delivered-value cell of an encoding. -/
def encCell : Privacy.BMR.Enc → Nat
  | .inl e => Layout.decodedCell 0 (Privacy.BMR.xFlat e).val
  | .inr e => Layout.decodedCell 1 (Privacy.BMR.yFlat e).val

/-- The mask cell of a row encoding (its element index). -/
def rowMaskCell (r : Privacy.BMR.NonCollector) : Nat :=
  match r.1 with
  | (d, .inl x) => Layout.maskCell 0 (xElementIndex d x).val
  | (d, .inr y) => Layout.maskCell 1 (yElementIndex d y).val

/-- **The replay's outputs in RAM.** -/
structure OutHolds (out : ReplayOut) (memory : Memory) : Prop where
  delivered : ∀ e, memory.ram (word (encCell e)) = fieldWord (out.delivered e)
  masks : ∀ r : Privacy.BMR.NonCollector, memory.ram (word (rowMaskCell r)) = fieldWord (out.masks r)
  key : memory.ram (word Layout.keyCell) = blockWord out.key

/-! ### The cells as functions of the flat index -/

/-- The delivered value of `x` encoding `e`. -/
def dxOf (out : ReplayOut) (e : Nat) : BaseField :=
  out.delivered (.inl (Privacy.BMR.xEncEquiv.symm ⟨e % 458, Nat.mod_lt _ (by omega)⟩))

/-- The delivered value of `y` encoding `e`. -/
def dyOf (out : ReplayOut) (e : Nat) : BaseField :=
  out.delivered (.inr (Privacy.BMR.yEncEquiv.symm ⟨e % 275, Nat.mod_lt _ (by omega)⟩))

/-- The mask of `x` encoding `e` (`0` at a collector or a curve encoding). -/
def pxOf (out : ReplayOut) (e : Nat) : BaseField :=
  match Privacy.BMR.xEncEquiv.symm ⟨e % 458, Nat.mod_lt _ (by omega)⟩ with
  | .inl (d, x) => if plain : Privacy.BMR.IsCollector (.inl x) then 0 else out.masks ⟨(d, .inl x), plain⟩
  | .inr _ => 0

/-- The mask of `y` encoding `e` (`0` at a curve encoding). -/
def pyOf (out : ReplayOut) (e : Nat) : BaseField :=
  match Privacy.BMR.yEncEquiv.symm ⟨e % 275, Nat.mod_lt _ (by omega)⟩ with
  | .inl (d, y) => if plain : Privacy.BMR.IsCollector (.inr y) then 0 else out.masks ⟨(d, .inr y), plain⟩
  | .inr _ => 0

theorem xSymm (d : Fin 91) (x : XElement) :
    Privacy.BMR.xEncEquiv.symm ⟨(5 * d.val + x.slot.val) % 458, Nat.mod_lt _ (by decide)⟩ = .inl (d, x) := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  have : x.slot.val < 5 := x.slot.isLt
  have := d.isLt
  show (5 * d.val + x.slot.val) % 458 = (xElementIndex d x).val
  rw [Nat.mod_eq_of_lt (by omega)]
  rfl

theorem ySymm (d : Fin 91) (y : YElement) :
    Privacy.BMR.yEncEquiv.symm ⟨(3 * d.val + y.slot.val) % 275, Nat.mod_lt _ (by decide)⟩ = .inl (d, y) := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  have : y.slot.val < 3 := y.slot.isLt
  have := d.isLt
  show (3 * d.val + y.slot.val) % 275 = (yElementIndex d y).val
  rw [Nat.mod_eq_of_lt (by omega)]
  rfl

theorem dxOf_eq (out : ReplayOut) (d : Fin 91) (x : XElement) :
    dxOf out (5 * d.val + x.slot.val) = out.delivered (Privacy.BMR.rowEnc (d, .inl x)) := by
  unfold dxOf
  rw [xSymm]
  rfl

theorem dyOf_eq (out : ReplayOut) (d : Fin 91) (y : YElement) :
    dyOf out (3 * d.val + y.slot.val) = out.delivered (Privacy.BMR.rowEnc (d, .inr y)) := by
  unfold dyOf
  rw [ySymm]
  rfl

theorem pxOf_eq (out : ReplayOut) (d : Fin 91) (x : XElement) (plain : ¬ Privacy.BMR.IsCollector (.inl x)) :
    pxOf out (5 * d.val + x.slot.val) = out.masks ⟨(d, .inl x), plain⟩ := by
  unfold pxOf
  rw [xSymm]
  simp only [plain, dite_false]

theorem yPlain (y : YElement) : ¬ Privacy.BMR.IsCollector (.inr y) := by
  simp [Privacy.BMR.IsCollector]

theorem pyOf_eq (out : ReplayOut) (d : Fin 91) (y : YElement) :
    pyOf out (3 * d.val + y.slot.val) = out.masks ⟨(d, .inr y), yPlain y⟩ := by
  unfold pyOf
  rw [ySymm]
  simp only [yPlain y, dite_false]

/-! ### The machine's mask formula is the abstract simulator's -/

variable [FieldCertificate]

/-- **The collector masks agree**: `Solve.maskFormula` on the replay's cells is `collectorMasks`. -/
theorem maskFormula_eq (u : AffineInput) (out : ReplayOut) (gamma : Fin 91 → RowGamma)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) (d : Fin 91) (c : Fin 3) :
    Solve.maskFormula u.x u.y (gamma d) (targets d) (dxOf out) (pxOf out) (dyOf out) (pyOf out) d.val c =
      Privacy.collectorMasks u out gamma targets (Programs.collectorAt d c) := by
  have x7 : dxOf out (5 * d.val) = out.delivered (Privacy.BMR.rowEnc (d, .inl .rowX_x7)) :=
    dxOf_eq out d .rowX_x7
  have x9 : dxOf out (5 * d.val + 1) = out.delivered (Privacy.BMR.rowEnc (d, .inl .rowX_x9)) :=
    dxOf_eq out d .rowX_x9
  have x7y : dxOf out (5 * d.val + 2) = out.delivered (Privacy.BMR.rowEnc (d, .inl .rowY_x7)) :=
    dxOf_eq out d .rowY_x7
  have x9y : dxOf out (5 * d.val + 3) = out.delivered (Privacy.BMR.rowEnc (d, .inl .rowY_x9)) :=
    dxOf_eq out d .rowY_x9
  have x9z : dxOf out (5 * d.val + 4) = out.delivered (Privacy.BMR.rowEnc (d, .inl .rowZ_x9)) :=
    dxOf_eq out d .rowZ_x9
  have p7 : pxOf out (5 * d.val) = out.masks ⟨(d, .inl .rowX_x7), by simp [Privacy.BMR.IsCollector]⟩ :=
    pxOf_eq out d .rowX_x7 _
  have p7y : pxOf out (5 * d.val + 2) = out.masks ⟨(d, .inl .rowY_x7), by simp [Privacy.BMR.IsCollector]⟩ :=
    pxOf_eq out d .rowY_x7 _
  have y10 : dyOf out (3 * d.val) = out.delivered (Privacy.BMR.rowEnc (d, .inr .rowX_y10)) :=
    dyOf_eq out d .rowX_y10
  have y8 : dyOf out (3 * d.val + 1) = out.delivered (Privacy.BMR.rowEnc (d, .inr .rowY_y8)) :=
    dyOf_eq out d .rowY_y8
  have y10y : dyOf out (3 * d.val + 2) = out.delivered (Privacy.BMR.rowEnc (d, .inr .rowY_y10)) :=
    dyOf_eq out d .rowY_y10
  have q10 : pyOf out (3 * d.val) = out.masks ⟨(d, .inr .rowX_y10), yPlain _⟩ := pyOf_eq out d .rowX_y10
  have q8 : pyOf out (3 * d.val + 1) = out.masks ⟨(d, .inr .rowY_y8), yPlain _⟩ := pyOf_eq out d .rowY_y8
  have q10y : pyOf out (3 * d.val + 2) = out.masks ⟨(d, .inr .rowY_y10), yPlain _⟩ := pyOf_eq out d .rowY_y10
  fin_cases c
  · simp only [Solve.maskFormula, x7, x9, p7, y10, q10]
    simp [Privacy.collectorMasks, Programs.collectorAt, Privacy.BMR.collectorSolve,
      Privacy.replayRowValues, Privacy.BMR.IsCollector]
  · simp only [Solve.maskFormula, x7y, x9y, p7y, y8, q8, y10y, q10y]
    simp [Privacy.collectorMasks, Programs.collectorAt, Privacy.BMR.collectorSolve,
      Privacy.replayRowValues, Privacy.BMR.IsCollector, sq]
  · simp only [Solve.maskFormula, x9z]
    simp [Privacy.collectorMasks, Programs.collectorAt, Privacy.BMR.collectorSolve]

/-! ### The solve's cells from the replay's outputs -/

omit [FieldCertificate] in
theorem decodedX_holds (out : ReplayOut) (memory : Memory) (holds : OutHolds out memory) (e : Nat)
    (small : e < 458) : memory.ram (word (Solve.decX e)) = fieldWord (dxOf out e) := by
  have cell := holds.delivered (.inl (Privacy.BMR.xEncEquiv.symm ⟨e, small⟩))
  have flat : (Privacy.BMR.xFlat (Privacy.BMR.xEncEquiv.symm ⟨e, small⟩)).val = e :=
    congrArg Fin.val (Privacy.BMR.xEncEquiv.apply_symm_apply ⟨e, small⟩)
  simp only [encCell, flat] at cell
  unfold dxOf
  simp only [Nat.mod_eq_of_lt small]
  exact cell

omit [FieldCertificate] in
theorem decodedY_holds (out : ReplayOut) (memory : Memory) (holds : OutHolds out memory) (e : Nat)
    (small : e < 275) : memory.ram (word (Solve.decY e)) = fieldWord (dyOf out e) := by
  have cell := holds.delivered (.inr (Privacy.BMR.yEncEquiv.symm ⟨e, small⟩))
  have flat : (Privacy.BMR.yFlat (Privacy.BMR.yEncEquiv.symm ⟨e, small⟩)).val = e :=
    congrArg Fin.val (Privacy.BMR.yEncEquiv.apply_symm_apply ⟨e, small⟩)
  simp only [encCell, flat] at cell
  unfold dyOf
  simp only [Nat.mod_eq_of_lt small]
  exact cell

omit [FieldCertificate] in
theorem maskX_holds (out : ReplayOut) (memory : Memory) (holds : OutHolds out memory) (d : Fin 91)
    (x : XElement) (plain : ¬ Privacy.BMR.IsCollector (.inl x)) :
    memory.ram (word (Solve.maskX (5 * d.val + x.slot.val))) = fieldWord (pxOf out (5 * d.val + x.slot.val)) := by
  rw [pxOf_eq out d x plain]
  exact holds.masks ⟨(d, .inl x), plain⟩

omit [FieldCertificate] in
theorem maskY_holds (out : ReplayOut) (memory : Memory) (holds : OutHolds out memory) (d : Fin 91)
    (y : YElement) :
    memory.ram (word (Solve.maskY (3 * d.val + y.slot.val))) = fieldWord (pyOf out (3 * d.val + y.slot.val)) := by
  rw [pyOf_eq]
  exact holds.masks ⟨(d, .inr y), yPlain y⟩

omit [FieldCertificate] in
/-- **The solve's cells**, from the replay's outputs, the request, the row constants and the target rows. -/
theorem digitCells_of_out (out : ReplayOut) (memory : Memory) (u : AffineInput) (gamma : Fin 91 → RowGamma)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) (holds : OutHolds out memory)
    (hx : memory.ram (word reqX) = fieldWord u.x) (hy : memory.ram (word reqY) = fieldWord u.y)
    (rows : ∀ d : Fin 91, memory.ram (word (Opening.rowCell d 0)) = fieldWord (gamma d).xC0 ∧
      memory.ram (word (Opening.rowCell d 1)) = fieldWord (gamma d).yC0 ∧
      memory.ram (word (Opening.rowCell d 2)) = fieldWord (gamma d).yC4 ∧
      memory.ram (word (Opening.rowCell d 3)) = fieldWord (gamma d).zC0)
    (rowTargets : ∀ d : Fin 91, memory.ram (word (openRow d)) = fieldWord (targets d).x ∧
      memory.ram (word (openRow d + 1)) = fieldWord (targets d).y ∧
      memory.ram (word (openRow d + 2)) = fieldWord (targets d).z)
    (d : Fin 91) :
    Solve.DigitCells memory u.x u.y (gamma d) (targets d) (dxOf out) (pxOf out) (dyOf out) (pyOf out) d.val where
  reqXCell := hx
  reqYCell := hy
  row0 := (rows d).1
  row1 := (rows d).2.1
  row2 := (rows d).2.2.1
  row3 := (rows d).2.2.2
  decXCell k small := decodedX_holds out memory holds _ (by have := d.isLt; omega)
  maskX0 := maskX_holds out memory holds d .rowX_x7 (by simp [Privacy.BMR.IsCollector])
  maskX2 := maskX_holds out memory holds d .rowY_x7 (by simp [Privacy.BMR.IsCollector])
  decYCell k small := decodedY_holds out memory holds _ (by have := d.isLt; omega)
  maskYCell k small := by
    interval_cases k
    · exact maskY_holds out memory holds d .rowX_y10
    · exact maskY_holds out memory holds d .rowY_y8
    · exact maskY_holds out memory holds d .rowY_y10
  targetX := (rowTargets d).1
  targetY := (rowTargets d).2.1
  targetZ := (rowTargets d).2.2

end OutCells

end

end Kriterion.CRT.SimMachine
