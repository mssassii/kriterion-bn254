/-
**Route M's replay on the machine agrees with `Entry.replayRouteM`**
(`agree_entryReplay`), posting `OutHolds` (`OutCells.lean`) for the replay's
output read in the tier-2 index (`routeView`, as `EntryInstance.view_replayProgram_eval` reads it).
-/

import Proof.Simulator.CRT.ReplayCoord
import Proof.Simulator.CRT.ReplayKey
import Proof.Simulator.CRT.ReplayMasks
import Proof.Simulator.CRT.OutCells
import Construction.Simulator.CRT.ReplayEntry

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB BN254

/-! ### Reading replay results independently of the privacy instance -/

namespace ReplayView

/-- The non-collector answers in the entry's mask representation. -/
def nonCollectorValues (rest : (Fin (pairSites digitCount) → BaseField × BaseField) × BaseField) :
    MaskValues digitCount :=
  { collector := fun _ => 0, pair := rest.1, single := rest.2 }

/-- Delivered values indexed by the abstract simulator's encoding index. -/
def toDelivered (conv : Entry.ConvOut) : Privacy.BMR.Enc → BaseField
  | .inl x => conv.deliveredX (Privacy.BMR.xFlat x)
  | .inr y => conv.deliveredY (Privacy.BMR.yFlat y)

/-- Non-collector masks indexed by the abstract simulator's row index. -/
def toMasks (masks : Entry.RowEncoding → BaseField) : Privacy.BMR.NonCollector → BaseField
  | ⟨(d, .inl x), _⟩ => masks (.inl (xElementIndex d x))
  | ⟨(d, .inr y), _⟩ => masks (.inr (yElementIndex d y))

end ReplayView

/-! ### The curve check's output -/

theorem curveOutput_eq [FieldCertificate] (pub : Entry.Public) (input : AffineInput) (conv : Entry.ConvOut) :
    Entry.curveOutput pub input conv =
      curvePoly input.x input.y pub.curve.1 pub.curve.2.1 pub.curve.2.2
        (conv.deliveredX ⟨364, by decide⟩) (conv.deliveredY ⟨273, by decide⟩)
        (conv.deliveredX ⟨365, by decide⟩) (conv.deliveredY ⟨274, by decide⟩)
        (conv.deliveredX ⟨366, by decide⟩) := by
  unfold Entry.curveOutput CurveMembership.evaluate curvePoly Entry.curveValuesOf Pipeline.curveValues
    Entry.curvePartX Entry.curvePartY curveXElementIndex curveYElementIndex
  rfl

/-! ### The mask cells -/

theorem maskCellOf_eq (n : Nat) :
    maskCellOf 91 n = if n < 91 then 2 ^ 57 + 4 * n else 2 ^ 57 + 2 ^ 10 + (n - 91) := by
  unfold maskCellOf nonCollectorEntry Layout.maskCell
  split_ifs <;> simp

theorem maskCellOf_digitCount (n : Nat) :
    maskCellOf digitCount n = if n < 91 then 2 ^ 57 + 4 * n else 2 ^ 57 + 2 ^ 10 + (n - 91) :=
  maskCellOf_eq n

/-- The layout of the entry's mask stage, with its answer scratch at or above `2 ^ 59`. -/
theorem entryMaskLayout (maskScratch : Nat) (low : 2 ^ 59 ≤ maskScratch)
    (fits : maskScratch + 6 < 2 ^ 256) :
    MaskLayout (entryMaskCells maskScratch) (nonCollectorCount digitCount) := by
  have count : nonCollectorCount digitCount = 364 := rfl
  have key : Layout.keyCell = 2 ^ 58 := rfl
  refine ⟨by show Layout.keyCell < 2 ^ 256; rw [key]; norm_num, fits,
    fun b bb => by show Layout.keyCell ≠ maskScratch + b; rw [key]; omega, fun n nb => ?_, fun n nb b bb => ?_,
    fun n nb => ?_, fun n nb n' nb' ne => ?_⟩ <;>
    simp only [entryMaskCells, digitCount, count, key] at * <;>
    rw [maskCellOf_eq] <;> (try rw [maskCellOf_eq]) <;> split_ifs <;> omega

/-- **The masks by non-collector entry**: from the mask stage's post, entry `n`'s cell holds
`nonCollectorMask` of the replay's mask values (the `364` entries are `182` pairs; there is no single site). -/
theorem maskCells_of_post (pairs : Fin (pairSites digitCount) → BaseField × BaseField) (single : BaseField)
    (memory : Memory)
    (pairCells : ∀ k (kb : k < pairSites digitCount),
      memory.ram (word (maskCellOf digitCount (2 * k))) = fieldWord (pairs ⟨k, kb⟩).1 ∧
        memory.ram (word (maskCellOf digitCount (2 * k + 1))) = fieldWord (pairs ⟨k, kb⟩).2)
    (n : Nat) (nb : n < 364) :
    memory.ram (word (maskCellOf digitCount n)) =
      fieldWord (nonCollectorMask (ReplayView.nonCollectorValues (pairs, single)) n) := by
  have pairsEq : pairSites digitCount = 182 := rfl
  have inPairs : n / 2 < pairSites digitCount := by rw [pairsEq]; omega
  unfold nonCollectorMask
  rw [dif_pos inPairs]
  by_cases even : n % 2 = 0
  · rw [if_pos even]
    have := (pairCells (n / 2) inPairs).1
    rw [show 2 * (n / 2) = n by omega] at this
    exact this
  · rw [if_neg even]
    have := (pairCells (n / 2) inPairs).2
    rw [show 2 * (n / 2) + 1 = n by omega] at this
    exact this

/-- `maskOf` at the plain `x` slot `0` of digit `d` is non-collector entry `d`. -/
theorem maskOf_x (values : MaskValues digitCount) (d : Nat) (dLt : d < 91) :
    maskOf values 0 (4 * d + 0) = nonCollectorMask values d := by
  have dc : 4 * d + 0 < 4 * digitCount := by unfold digitCount; omega
  unfold maskOf
  rw [if_pos rfl, if_pos dc, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show (4 * d + 0) / 4 = d by omega]

/-- `maskOf` at a `y` point encoding is non-collector entry `91 + e`. -/
theorem maskOf_y (values : MaskValues digitCount) (e : Nat) (eLt : e < 273) :
    maskOf values 1 e = nonCollectorMask values (digitCount + e) := by
  unfold maskOf
  have lt : e < 3 * digitCount := by unfold digitCount; omega
  simp [lt]

/-- **The masks of `OutHolds`** from the masks by non-collector entry. -/
theorem outMasks_of (values : MaskValues digitCount) (memory : Memory)
    (cells : ∀ n, n < 364 → memory.ram (word (maskCellOf digitCount n)) = fieldWord (nonCollectorMask values n))
    (nc : Privacy.BMR.NonCollector) :
    memory.ram (word (OutCells.rowMaskCell nc)) =
      fieldWord (ReplayView.toMasks (Entry.maskFunction values) nc) := by
  obtain ⟨⟨d, element⟩, plain⟩ := nc
  have dLt := d.isLt
  cases element with
  | inl x =>
      cases x
      · have cell := cells d.val (by omega)
        rw [maskCellOf_digitCount, if_pos (by omega)] at cell
        show memory.ram (word (Layout.maskCell 0 (4 * d.val + 0))) = fieldWord (maskOf values 0 (4 * d.val + 0))
        rw [maskOf_x values d.val dLt]
        unfold Layout.maskCell
        simpa using cell
      · exact absurd (Or.inl rfl) plain
      · exact absurd (Or.inr (Or.inl rfl)) plain
      · exact absurd (Or.inr (Or.inr rfl)) plain
  | inr y =>
      have slotLt := y.slot.isLt
      have cell := cells (91 + (3 * d.val + y.slot.val)) (by
        have : y.slot.val < 3 := slotLt
        omega)
      rw [maskCellOf_digitCount, if_neg (by omega)] at cell
      show memory.ram (word (Layout.maskCell 1 (3 * d.val + y.slot.val))) =
        fieldWord (maskOf values 1 (3 * d.val + y.slot.val))
      rw [maskOf_y values _ (by have : y.slot.val < 3 := slotLt; omega)]
      unfold Layout.maskCell
      rw [show 91 + (3 * d.val + y.slot.val) - 91 = 3 * d.val + y.slot.val by omega] at cell
      simpa [digitCount] using cell

/-! ### The composition -/

/-- The replay's output in the tier-2 index (as `EntryInstance.view_replayProgram_eval` reads it). -/
def routeView (out : Entry.RouteMOut) : Privacy.ReplayOut where
  delivered := ReplayView.toDelivered out.conv
  masks := ReplayView.toMasks
    (Entry.maskFunction (ReplayView.nonCollectorValues (out.pairs, out.single)))
  key := out.key

theorem pure_bind' {spec : Cryptography.OracleSpec.{0, 0}} {α β : Type} (a : α) (f : α → FreeQuery spec β) :
    FreeQuery.bind (FreeQuery.pure a) f = f a := rfl

theorem decoded_not_mask (maskScratch : Nat) (low : 2 ^ 59 ≤ maskScratch)
    (fits : maskScratch + 6 < 2 ^ 256) (κ e : Nat) (κLe : κ ≤ 1) (eLt : e < 1024) :
    ¬ maskWrites (entryMaskCells maskScratch) (nonCollectorCount digitCount)
      (word (Layout.decodedCell κ e)) := by
  have count : nonCollectorCount digitCount = 364 := rfl
  unfold Layout.decodedCell
  rintro (⟨b, bb, same⟩ | ⟨n, nb, same⟩)
  · dsimp only [entryMaskCells] at bb same
    have := word_inj (by omega) (by omega) same
    omega
  · rw [count] at nb
    have mn : maskCellOf digitCount n < 2 ^ 58 := by rw [maskCellOf_digitCount]; split_ifs <;> omega
    dsimp only [entryMaskCells] at same
    have := word_inj (by omega) (by omega) same
    rw [maskCellOf_digitCount] at this
    split_ifs at this <;> omega

theorem maskTag_small (site part : Nat) (siteLe : site ≤ 182) (partLt : part < 3) :
    maskTag 1 site part < 2 ^ 127 := by
  unfold maskTag tagCode Family.mask
  have : (2 : Nat) ^ 60 < 2 ^ 127 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have : (2 : Nat) ^ 60 = 1152921504606846976 := by norm_num
  omega

section Composition

variable [FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **Route M's replay**: given the two coordinates' agreements (the `y` one for any memory the `x`
coordinate leaves outside its writes), the machine asks what `Entry.replayRouteM` asks and leaves
`OutHolds` of the output, with the frame of its four phases. -/
theorem agree_entryReplay (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) (coordX coordY : Prog) (maskScratch : Nat)
    (low : 2 ^ 59 ≤ maskScratch) (fits : maskScratch + 6 < 2 ^ 256)
    (WX WY : Writes) (CX CY : Clobbers) (memory : Memory)
    (hx : Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (ex : CoordEval Entry.table Entry.xCount) after =>
        (∀ e : Fin Entry.xCount, after.ram (word (Layout.decodedCell 0 e.val)) =
          fieldWord ((ex.decoded e : Nat) : BaseField)) ∧ Frame WX CX memory after)
      (coordX.tree memory)
      (liftHash (coordEvalM Entry.table Entry.xCount 0 (Entry.convOf pub.crtX) (fun e => (pub.recX.get e).val)
        input.x.val (fun j => clip (Entry.labelX labels j)))))
    (hy : ∀ m1 : Memory, (∀ address, ¬ WX address → m1.ram address = memory.ram address) →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
        (fun (ey : CoordEval Entry.table Entry.yCount) after =>
          (∀ e : Fin Entry.yCount, after.ram (word (Layout.decodedCell 1 e.val)) =
            fieldWord ((ey.decoded e : Nat) : BaseField)) ∧ Frame WY CY m1 after)
        (coordY.tree m1)
        (liftHash (coordEvalM Entry.table Entry.yCount 1 (Entry.convOf pub.crtY)
          (fun e => (pub.recY.get e).val) input.y.val (fun j => clip (Entry.labelY labels j)))))
    (xSafe : ∀ e : Fin Entry.xCount, ¬ WY (word (Layout.decodedCell 0 e.val)))
    (reqXCell : memory.ram (word reqX) = fieldWord input.x)
    (reqYCell : memory.ram (word reqY) = fieldWord input.y)
    (c0Cell : memory.ram (word fieldBase) = fieldWord pub.curve.1)
    (c1Cell : memory.ram (word (fieldBase + 1)) = fieldWord pub.curve.2.1)
    (c2Cell : memory.ram (word (fieldBase + 2)) = fieldWord pub.curve.2.2)
    (inputsSafe : ∀ x, (x = reqX ∨ x = reqY ∨ x = fieldBase ∨ x = fieldBase + 1 ∨ x = fieldBase + 2) →
      ¬ WX (word x) ∧ ¬ WY (word x)) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (out : Entry.RouteMOut) after =>
        OutCells.OutHolds (routeView out) after ∧
          Frame (((WX.union WY).union (Writes.cell Layout.keyCell)).union
              (maskWrites (entryMaskCells maskScratch) (nonCollectorCount digitCount)))
            (((CX.union CY).union keyClobbers).union maskClobbers) memory after)
      ((entryReplay coordX coordY maskScratch).tree memory)
      (liftHash (Entry.replayRouteM pub input labels)) := by
  have keyEq : Layout.keyCell = 2 ^ 58 := rfl
  unfold entryReplay Entry.replayRouteM Entry.replayConv
  rw [tree_seq, TreeLaws.monad_bind, TreeLaws.monad_bind, TreeLaws.bind_assoc, liftHash_bind]
  refine Agree.bindOpt (fun ex m1 post1 => ?_) hx
  obtain ⟨xCells, frame1⟩ := post1
  rw [tree_seq, TreeLaws.monad_bind, TreeLaws.bind_assoc, liftHash_bind]
  refine Agree.bindOpt (fun ey m2 post2 => ?_) (hy m1 frame1.ram)
  obtain ⟨yCells, frame2⟩ := post2
  rw [TreeLaws.monad_pure, pure_bind']
  have inputNow : ∀ x, (x = reqX ∨ x = reqY ∨ x = fieldBase ∨ x = fieldBase + 1 ∨ x = fieldBase + 2) →
      m2.ram (word x) = memory.ram (word x) := fun x hx => by
    rw [frame2.ram _ (inputsSafe x hx).2, frame1.ram _ (inputsSafe x hx).1]
  have xNow : ∀ e : Fin Entry.xCount, m2.ram (word (Layout.decodedCell 0 e.val)) =
      fieldWord ((ex.decoded e : Nat) : BaseField) := fun e => by
    rw [frame2.ram _ (xSafe e)]
    exact xCells e
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind, curveOutput_eq]
  refine Agree.bindOpt (fun key m3 post3 => ?_)
    (agree_keyBlock entryKeyCells m2 _ _ _ _ _ _ _ _ _ _
      ⟨by show m2.ram (word reqX) = _; rw [inputNow _ (Or.inl rfl)]; exact reqXCell,
        by show m2.ram (word reqY) = _; rw [inputNow _ (Or.inr (Or.inl rfl))]; exact reqYCell,
        by show m2.ram (word fieldBase) = _; rw [inputNow _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c0Cell,
        by show m2.ram (word (fieldBase + 1)) = _; rw [inputNow _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c1Cell,
        by show m2.ram (word (fieldBase + 2)) = _; rw [inputNow _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c2Cell,
        xNow ⟨364, by decide⟩, yCells ⟨273, by decide⟩, xNow ⟨365, by decide⟩,
        yCells ⟨274, by decide⟩, xNow ⟨366, by decide⟩⟩)
  obtain ⟨keyCell3, frame3⟩ := post3
  rw [TreeLaws.monad_bind, liftHash_bind,
    ← bindOpt_pure_right ((maskStage (entryMaskCells maskScratch) digitCount).tree m3)]
  refine Agree.bindOpt (fun rest m4 post4 => ?_)
    (agree_maskStage (entryMaskCells maskScratch) digitCount (entryMaskLayout maskScratch low fits) key m3
      keyCell3 fun site part siteLe partLt => maskTag_small site part siteLe partLt)
  obtain ⟨pairCells, singleCell, frame4⟩ := post4
  have notKey : ∀ κ e, κ ≤ 1 → e < 1024 → word (Layout.decodedCell κ e) ≠ word Layout.keyCell :=
    fun κ e κLe eLt same => by
      unfold Layout.decodedCell at same
      rw [keyEq] at same
      have := word_inj (by omega) (by norm_num) same
      omega
  refine .leaf ⟨⟨fun e => ?_, fun nc => ?_, ?_⟩, ((frame1.trans frame2).trans frame3).trans frame4⟩
  · cases e with
    | inl x =>
        have xb := (Privacy.BMR.xFlat x).isLt
        show m4.ram (word (Layout.decodedCell 0 (Privacy.BMR.xFlat x).val)) = _
        rw [frame4.ram _ (decoded_not_mask maskScratch low fits 0 _ (by norm_num) (by omega)),
          frame3.ram _ (notKey 0 _ (by norm_num) (by omega)), xNow]
        rfl
    | inr y =>
        have yb := (Privacy.BMR.yFlat y).isLt
        show m4.ram (word (Layout.decodedCell 1 (Privacy.BMR.yFlat y).val)) = _
        rw [frame4.ram _ (decoded_not_mask maskScratch low fits 1 _ le_rfl (by omega)),
          frame3.ram _ (notKey 1 _ le_rfl (by omega)), yCells]
        rfl
  · exact outMasks_of _ m4 (maskCells_of_post rest.1 rest.2 m4 pairCells) nc
  · show m4.ram (word Layout.keyCell) = blockWord key
    rw [frame4.ram (word Layout.keyCell)
      (MaskLayout.not_writes _ _ (entryMaskLayout maskScratch low fits) _ le_rfl)]
    exact keyCell3

end Composition

end Kriterion.CRT.SimMachine
