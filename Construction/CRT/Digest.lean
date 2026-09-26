/-
The exception gadget of configuration E with the per-label hash digest (D9).

* Digest labels: `h(κ, i, b) = (H(hashInput (Z_{κ,i} ⊕ b·Δ_κ) (tagCode 8 κ 0 0 0 i b))).1`. The garbler hashes both
  bits of every input position (`digestTableM`, coordinate, then position, then bit 0 and 1: `4 * bits` answers); the
  evaluator hashes its own label at its own bit (`digestKeyM`, `2 * bits` answers) and XORs them into its key.
* The key of digit `o` is `key_o = ⊕_{κ,i} h(κ, i, exc_o[κ, i])` (`garblerKey`), with `exc_o` the digit's
  exceptional input (`release-r1`'s `Exception.exceptionalInput`) and `exc_o[κ, i]` bit `i` of its coordinate `κ`.
* The mask byte of digit `o` at key `k` is the low 8 bits of `(H(hashInput k (tagCode 9 0 0 0 0 o 0))).1`
  (`finalMask`). The garbler asks it only for a nonzero digit (a zero digit has no exceptional input and publishes its
  pad, as `release-r1`'s `garbleEntryM`); the evaluator asks it for every digit.
* The 6-byte entry is `release-r1`'s: the coins' pad with `digitCode d ⊕ mask` written at `exceptionIndex exc_o`
  (`Exception.writeEntry`); the evaluator unlocks with `Exception.unlock`.

Budgets (`digestGarbleBudget`, `digestEvalBudget`): garbler `4 * bits + digits` (a bound: the count is
`4 * bits + (nonzero digits)`), evaluator `2 * bits + digits` exactly; 1,107 and 599 at 254 bits and 91 digits.
-/

import Construction.CRT.Tree
import Construction.ArgoMAC.Exception

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC BN254

/-! ### Tags and bits -/

/-- The tag of the digest label of coordinate `coord`, position `position`, bit `bit`. -/
def digestLabelTag (coord position bit : Nat) : Nat := tagCode Family.digestLabel coord 0 0 0 position bit

/-- The tag of digit `digit`'s final hash. -/
def digestFinalTag (digit : Nat) : Nat := tagCode Family.digestFinal 0 0 0 0 digit 0

/-- The coordinate `coord` (`0` is `x`, `1` is `y`) of a point, as a natural. -/
def coordNat (u : AffineInput) (coord : Fin 2) : Nat := if coord = 0 then u.x.val else u.y.val

/-- Bit `position` of coordinate `coord` of a point (little-endian bits of the canonical value). -/
def coordBit (u : AffineInput) (coord : Fin 2) (position : Nat) : Nat :=
  if (coordNat u coord).testBit position then 1 else 0

/-! ### Pure functions of the hash -/

/-- The garbler's digest table: both digest labels of every position, `(h(κ, i, 0), h(κ, i, 1))`. -/
def digestTable (H : HashN) (bits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block) :
    Fin 2 → Fin bits → Block × Block :=
  fun coord position =>
    (h128 H (zero coord position) (digestLabelTag coord.val position.val 0),
      h128 H (zero coord position ^^^ delta coord) (digestLabelTag coord.val position.val 1))

/-- The garbler's key of an input point: the XOR of the table entries at the point's bits. -/
def garblerKey {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (u : AffineInput) : Block :=
  xorFold fun coord : Fin 2 => xorFold fun position : Fin bits =>
    if coordBit u coord position.val = 1 then (table coord position).2 else (table coord position).1

/-- The evaluator's key: the XOR of the digest labels of its own labels at its own bits. -/
def digestKey (H : HashN) (bits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput) : Block :=
  xorFold fun coord : Fin 2 => xorFold fun position : Fin bits =>
    h128 H (labels coord position) (digestLabelTag coord.val position.val (coordBit u coord position.val))

/-- The mask byte of digit `digit` at key `key`: the low 8 bits of the final hash's first block. -/
def finalMask (H : HashN) (key : Block) (digit : Nat) : BitVec 8 :=
  Exception.lowByte (h128 H key (digestFinalTag digit))

/-- The garbler's entry of one digit: the pad, with the masked digit code at the exceptional input's slot for a
nonzero digit (`release-r1`'s `FieldMacToECMac.garbleEntry` with the digest's mask). -/
def garbleEntry (H : HashN) {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (index : Nat)
    (digit : Digit) (offset : AffineInput) (pad : Exception.Entry) : Exception.Entry :=
  match digitEndomorphismBase digit with
  | none => pad
  | some phi =>
      let exceptional := Exception.exceptionalInput phi offset
      Exception.writeEntry pad (Exception.exceptionIndex exceptional)
        (finalMask H (garblerKey table exceptional) index ^^^ Exception.digitCode digit)

/-- The garbler's entries of all digits. -/
def digestEntries (H : HashN) (bits digits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput) (padOf : Fin digits → Exception.Entry) :
    Fin digits → Exception.Entry :=
  fun o => garbleEntry H (digestTable H bits zero delta) o.val (digitOf o) (offsetOf o) (padOf o)

/-- The evaluator's unlocked digits at its input `u`. -/
def digestUnlock (H : HashN) (bits digits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (entries : Fin digits → Exception.Entry) : Fin digits → Digit :=
  fun o => Exception.unlock (finalMask H (digestKey H bits labels u) o.val) (entries o) u

/-! ### Programs -/

/-- The garbler's digest labels, coordinate, then position, then bit 0 and 1. -/
def digestTableM (bits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block) :
    CM (Fin 2 → Fin bits → Block × Block) :=
  tableM 2 fun coord => tableM bits fun position =>
    h128M (zero coord position) (digestLabelTag coord.val position.val 0) >>= fun first =>
      h128M (zero coord position ^^^ delta coord) (digestLabelTag coord.val position.val 1) >>= fun second =>
        pure (first, second)

/-- The evaluator's digest labels and key, coordinate, then position. -/
def digestKeyM (bits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput) : CM Block :=
  tableM 2 (fun coord => tableM bits fun position =>
      h128M (labels coord position) (digestLabelTag coord.val position.val (coordBit u coord position.val)))
    >>= fun hashes => pure (xorFold fun coord => xorFold (hashes coord))

/-- One final hash as a mask byte. -/
def finalMaskM (key : Block) (digit : Nat) : CM (BitVec 8) :=
  h128M key (digestFinalTag digit) >>= fun block => pure (Exception.lowByte block)

/-- The garbler's entry of one digit (no query for a zero digit). -/
def garbleEntryM {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (index : Nat) (digit : Digit)
    (offset : AffineInput) (pad : Exception.Entry) : CM Exception.Entry :=
  match digitEndomorphismBase digit with
  | none => pure pad
  | some phi =>
      let exceptional := Exception.exceptionalInput phi offset
      finalMaskM (garblerKey table exceptional) index >>= fun mask =>
        pure (Exception.writeEntry pad (Exception.exceptionIndex exceptional) (mask ^^^ Exception.digitCode digit))

/-- **The garbler's gadget**: the digest table (`4 * bits` answers), then one final per nonzero digit. -/
def digestGarbleM (bits digits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput) (padOf : Fin digits → Exception.Entry) :
    CM (Fin digits → Exception.Entry) :=
  digestTableM bits zero delta >>= fun table =>
    tableM digits fun o => garbleEntryM table o.val (digitOf o) (offsetOf o) (padOf o)

/-- **The evaluator's gadget**: its key (`2 * bits` answers), then every digit's final. -/
def digestEvalM (bits digits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (entries : Fin digits → Exception.Entry) : CM (Fin digits → Digit) :=
  digestKeyM bits labels u >>= fun key =>
    tableM digits fun o => finalMaskM key o.val >>= fun mask => pure (Exception.unlock mask (entries o) u)

/-! ### Evaluation -/

theorem eval_digestTableM (H : HashN) (bits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block) :
    (digestTableM bits zero delta).eval H = digestTable H bits zero delta := by
  funext coord position
  simp [digestTableM, digestTable]

theorem eval_digestKeyM (H : HashN) (bits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput) :
    (digestKeyM bits labels u).eval H = digestKey H bits labels u := by
  simp [digestKeyM, digestKey]

@[simp] theorem eval_finalMaskM (H : HashN) (key : Block) (digit : Nat) :
    (finalMaskM key digit).eval H = finalMask H key digit := rfl

theorem eval_garbleEntryM (H : HashN) {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (index : Nat)
    (digit : Digit) (offset : AffineInput) (pad : Exception.Entry) :
    (garbleEntryM table index digit offset pad).eval H = garbleEntry H table index digit offset pad := by
  unfold garbleEntryM garbleEntry
  cases digitEndomorphismBase digit with
  | none => rfl
  | some phi => rfl

theorem eval_digestGarbleM (H : HashN) (bits digits : Nat) (zero : Fin 2 → Fin bits → Block)
    (delta : Fin 2 → Block) (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput)
    (padOf : Fin digits → Exception.Entry) :
    (digestGarbleM bits digits zero delta digitOf offsetOf padOf).eval H
      = digestEntries H bits digits zero delta digitOf offsetOf padOf := by
  funext o
  simp only [digestGarbleM, FreeQuery.eval_bind, eval_digestTableM, eval_tableM, eval_garbleEntryM,
    digestEntries]

theorem eval_digestEvalM (H : HashN) (bits digits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (entries : Fin digits → Exception.Entry) :
    (digestEvalM bits digits labels u entries).eval H = digestUnlock H bits digits labels u entries := by
  funext o
  simp only [digestEvalM, FreeQuery.eval_bind, eval_digestKeyM, eval_tableM, eval_finalMaskM,
    FreeQuery.eval_pure, digestUnlock]

/-! ### Budgets -/

/-- The garbler's budget: every digest label and one final per digit (a bound; zero digits ask none). -/
def digestGarbleBudget (bits digits : Nat) : Nat := 4 * bits + digits

/-- The evaluator's count: its own digest labels and every final. -/
def digestEvalBudget (bits digits : Nat) : Nat := 2 * bits + digits

theorem digestGarbleBudget_real : digestGarbleBudget 254 91 = 1107 := by decide

theorem digestEvalBudget_real : digestEvalBudget 254 91 = 599 := by decide

theorem bounded_digestTableM (bits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block) :
    (digestTableM bits zero delta).Bounded (4 * bits) :=
  (bounded_tableM (budget := fun _ => bits * 2) fun _ =>
    (bounded_tableM (budget := fun _ => 1 + (1 + 0)) fun _ =>
      FreeQuery.Bounded.bind (bounded_h128M _ _) fun _ =>
        FreeQuery.Bounded.bind (bounded_h128M _ _) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq
      (by simp)).of_eq (by simp; ring)

theorem bounded_digestKeyM (bits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput) :
    (digestKeyM bits labels u).Bounded (2 * bits) := by
  unfold digestKeyM
  refine (FreeQuery.Bounded.bind (first := 2 * bits) (second := 0) ?_ fun _ =>
    FreeQuery.Bounded.pure' _ 0).of_eq (by simp)
  refine (bounded_tableM (budget := fun _ => bits) fun coord => ?_).of_eq (by simp; try ring)
  exact (bounded_tableM (budget := fun _ => 1) fun _ => bounded_h128M _ _).of_eq (by simp)

theorem bounded_finalMaskM (key : Block) (digit : Nat) : (finalMaskM key digit).Bounded 1 :=
  FreeQuery.Bounded.bind (bounded_h128M _ _) fun _ => FreeQuery.Bounded.pure' _ 0

theorem bounded_garbleEntryM {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (index : Nat)
    (digit : Digit) (offset : AffineInput) (pad : Exception.Entry) :
    (garbleEntryM table index digit offset pad).Bounded 1 := by
  unfold garbleEntryM
  cases digitEndomorphismBase digit with
  | none => exact FreeQuery.Bounded.pure' _ 1
  | some phi =>
      exact FreeQuery.Bounded.bind (bounded_finalMaskM _ _) fun _ => FreeQuery.Bounded.pure' _ 0

/-- **The garbler's gadget asks at most `4 * bits + digits` answers** (1,107). -/
theorem bounded_digestGarbleM (bits digits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput) (padOf : Fin digits → Exception.Entry) :
    (digestGarbleM bits digits zero delta digitOf offsetOf padOf).Bounded (digestGarbleBudget bits digits) := by
  unfold digestGarbleM
  refine (FreeQuery.Bounded.bind (first := 4 * bits) (second := digits) (bounded_digestTableM bits zero delta)
    fun table => ?_).of_eq (by simp [digestGarbleBudget])
  exact (bounded_tableM (budget := fun _ => 1) fun o =>
    bounded_garbleEntryM table o.val (digitOf o) (offsetOf o) (padOf o)).of_eq (by simp)

/-- **The evaluator's gadget asks `2 * bits + digits` answers** (599). -/
theorem bounded_digestEvalM (bits digits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (entries : Fin digits → Exception.Entry) :
    (digestEvalM bits digits labels u entries).Bounded (digestEvalBudget bits digits) := by
  unfold digestEvalM
  refine (FreeQuery.Bounded.bind (first := 2 * bits) (second := digits) (bounded_digestKeyM bits labels u)
    fun key => ?_).of_eq (by simp [digestEvalBudget])
  exact (bounded_tableM (budget := fun _ => 1 + 0) fun o =>
    FreeQuery.Bounded.bind (bounded_finalMaskM key o.val) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq
    (by simp)

end Kriterion.CRT
