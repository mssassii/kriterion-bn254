/-
The exception gadget of configuration E with the per-label hash digest (D9).

* Digest labels: `h(κ, i, b) = (H(hashInput (Z_{κ,i} ⊕ b·Δ_κ) (tagCode 8 κ 0 0 0 i b))).1`. The garbler hashes both
  bits of every input position (`digestTableM`, coordinate, then position, then bit 0 and 1: `4 * bits` answers); the
  evaluator hashes its own label at its own bit (`digestKeyM`, `2 * bits` answers) and XORs them into its key.
* The key of digit `o` is `key_o = ⊕_{κ,i} h(κ, i, exc_o[κ, i])` (`garblerKey`), with `exc_o` the digit's
  exceptional input (`release-r1`'s `Exception.exceptionalInput`) and `exc_o[κ, i]` bit `i` of its coordinate `κ`.
* A nonzero digit has two exceptional inputs: `Q = K` (kind 0, `Exception.exceptionalInput`, where the `X` and `Z`
  rows vanish) and `Q = 2K` (kind 1, `Exception.tripleInput`, where the sign row vanishes). Kind `k` of digit `o` is
  the **final site** `s = 2 o + k`.
* The four-bit mask of site `s` at key `key` is the low 4 bits of `(H(hashInput key (tagCode 9 0 0 0 0 s 0))).1`
  (`finalMask`). The garbler asks it at the key of each exceptional input of a nonzero digit (a zero digit has no
  exceptional input and publishes its pad); the evaluator asks both sites of every digit at its own key. The two
  sites have distinct tags, so the garbler's hash inputs stay tag-injective.
* The one-byte entry: the coins' pad with `digitCode d ⊕ mask₀` written at `slotOf false exc_o` and
  `digitCode d ⊕ mask₁` at `slotOf true triple_o` (`Exception.writeEntry`); the evaluator unlocks both slots with
  `Exception.unlock`.

Budgets (`digestGarbleBudget`, `digestEvalBudget`): garbler `4 * bits + 2 * digits` (a bound: the count is
`4 * bits + 2 · (nonzero digits)`), evaluator `2 * bits + 2 * digits` exactly; 1,198 and 690 at 254 bits and 91
digits.
-/

import Construction.CRT.Tree
import Construction.ArgoMAC.Exception

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC BN254

/-! ### Tags and bits -/

/-- The tag of the digest label of coordinate `coord`, position `position`, bit `bit`. -/
def digestLabelTag (coord position bit : Nat) : Nat := tagCode Family.digestLabel coord 0 0 0 position bit

/-- The tag of final site `site` (`2 o + k` for digit `o`, kind `k`; kind 0 is `Q = K`, kind 1 is `Q = 2K`). -/
def digestFinalTag (site : Nat) : Nat := tagCode Family.digestFinal 0 0 0 0 site 0

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

/-- The four-bit mask of final site `site` at key `key`: the low 4 bits of the final hash's first block. -/
def finalMask (H : HashN) (key : Block) (site : Nat) : BitVec 4 :=
  Exception.lowNibble (h128 H key (digestFinalTag site))

/-- The garbler's entry of one digit: the pad, with the masked digit code at the slots of its two exceptional
inputs for a nonzero digit, each masked by the final at that input's key. -/
def garbleEntry (H : HashN) {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (index : Nat)
    (digit : Digit) (offset : AffineInput) (pad : Exception.Entry) : Exception.Entry :=
  match digitEndomorphismBase digit with
  | none => pad
  | some phi =>
      let first := Exception.exceptionalInput phi offset
      let second := Exception.tripleInput phi offset
      Exception.writeEntry
        (Exception.writeEntry pad (Exception.slotOf false first)
          (finalMask H (garblerKey table first) (2 * index) ^^^ Exception.digitCode digit))
        (Exception.slotOf true second)
        (finalMask H (garblerKey table second) (2 * index + 1) ^^^ Exception.digitCode digit)

/-- The garbler's entries of all digits. -/
def digestEntries (H : HashN) (bits digits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput) (padOf : Fin digits → Exception.Entry) :
    Fin digits → Exception.Entry :=
  fun o => garbleEntry H (digestTable H bits zero delta) o.val (digitOf o) (offsetOf o) (padOf o)

/-- The evaluator's unlocked digits at its input `u`, both kinds. -/
def digestUnlock (H : HashN) (bits digits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (entries : Fin digits → Exception.Entry) : Fin digits → Digit × Digit :=
  fun o => (Exception.unlock (finalMask H (digestKey H bits labels u) (2 * o.val)) (entries o) false u,
    Exception.unlock (finalMask H (digestKey H bits labels u) (2 * o.val + 1)) (entries o) true u)

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

/-- One final hash as a four-bit mask. -/
def finalMaskM (key : Block) (site : Nat) : CM (BitVec 4) :=
  h128M key (digestFinalTag site) >>= fun block => pure (Exception.lowNibble block)

/-- The garbler's entry of one digit (no query for a zero digit, two for a nonzero one). -/
def garbleEntryM {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (index : Nat) (digit : Digit)
    (offset : AffineInput) (pad : Exception.Entry) : CM Exception.Entry :=
  match digitEndomorphismBase digit with
  | none => pure pad
  | some phi =>
      let first := Exception.exceptionalInput phi offset
      let second := Exception.tripleInput phi offset
      finalMaskM (garblerKey table first) (2 * index) >>= fun mask =>
        finalMaskM (garblerKey table second) (2 * index + 1) >>= fun mask' =>
          pure (Exception.writeEntry
            (Exception.writeEntry pad (Exception.slotOf false first) (mask ^^^ Exception.digitCode digit))
            (Exception.slotOf true second) (mask' ^^^ Exception.digitCode digit))

/-- **The garbler's gadget**: the digest table (`4 * bits` answers), then two finals per nonzero digit. -/
def digestGarbleM (bits digits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput) (padOf : Fin digits → Exception.Entry) :
    CM (Fin digits → Exception.Entry) :=
  digestTableM bits zero delta >>= fun table =>
    tableM digits fun o => garbleEntryM table o.val (digitOf o) (offsetOf o) (padOf o)

/-- **The evaluator's gadget**: its key (`2 * bits` answers), then both finals of every digit. -/
def digestEvalM (bits digits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (entries : Fin digits → Exception.Entry) : CM (Fin digits → Digit × Digit) :=
  digestKeyM bits labels u >>= fun key =>
    tableM digits fun o => finalMaskM key (2 * o.val) >>= fun mask => finalMaskM key (2 * o.val + 1) >>= fun mask' =>
      pure (Exception.unlock mask (entries o) false u, Exception.unlock mask' (entries o) true u)

/-! ### Evaluation -/

theorem eval_digestTableM (H : HashN) (bits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block) :
    (digestTableM bits zero delta).eval H = digestTable H bits zero delta := by
  funext coord position
  simp [digestTableM, digestTable]

theorem eval_digestKeyM (H : HashN) (bits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput) :
    (digestKeyM bits labels u).eval H = digestKey H bits labels u := by
  simp [digestKeyM, digestKey]

@[simp] theorem eval_finalMaskM (H : HashN) (key : Block) (site : Nat) :
    (finalMaskM key site).eval H = finalMask H key site := rfl

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

/-- The garbler's budget: every digest label and two finals per digit (a bound; zero digits ask none). -/
def digestGarbleBudget (bits digits : Nat) : Nat := 4 * bits + 2 * digits

/-- The evaluator's count: its own digest labels and both finals of every digit. -/
def digestEvalBudget (bits digits : Nat) : Nat := 2 * bits + 2 * digits

theorem digestGarbleBudget_real : digestGarbleBudget 254 91 = 1198 := by decide

theorem digestEvalBudget_real : digestEvalBudget 254 91 = 690 := by decide

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

theorem bounded_finalMaskM (key : Block) (site : Nat) : (finalMaskM key site).Bounded 1 :=
  FreeQuery.Bounded.bind (bounded_h128M _ _) fun _ => FreeQuery.Bounded.pure' _ 0

theorem bounded_garbleEntryM {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (index : Nat)
    (digit : Digit) (offset : AffineInput) (pad : Exception.Entry) :
    (garbleEntryM table index digit offset pad).Bounded 2 := by
  unfold garbleEntryM
  cases digitEndomorphismBase digit with
  | none => exact FreeQuery.Bounded.pure' _ 2
  | some phi =>
      exact FreeQuery.Bounded.bind (bounded_finalMaskM _ _) fun _ =>
        FreeQuery.Bounded.bind (bounded_finalMaskM _ _) fun _ => FreeQuery.Bounded.pure' _ 0

/-- **The garbler's gadget asks at most `4 * bits + 2 * digits` answers** (1,198). -/
theorem bounded_digestGarbleM (bits digits : Nat) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput) (padOf : Fin digits → Exception.Entry) :
    (digestGarbleM bits digits zero delta digitOf offsetOf padOf).Bounded (digestGarbleBudget bits digits) := by
  unfold digestGarbleM
  refine (FreeQuery.Bounded.bind (first := 4 * bits) (second := 2 * digits) (bounded_digestTableM bits zero delta)
    fun table => ?_).of_eq (by simp [digestGarbleBudget])
  exact (bounded_tableM (budget := fun _ => 2) fun o =>
    bounded_garbleEntryM table o.val (digitOf o) (offsetOf o) (padOf o)).of_eq (by simp [mul_comm])

/-- **The evaluator's gadget asks `2 * bits + 2 * digits` answers** (690). -/
theorem bounded_digestEvalM (bits digits : Nat) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (entries : Fin digits → Exception.Entry) :
    (digestEvalM bits digits labels u entries).Bounded (digestEvalBudget bits digits) := by
  unfold digestEvalM
  refine (FreeQuery.Bounded.bind (first := 2 * bits) (second := 2 * digits) (bounded_digestKeyM bits labels u)
    fun key => ?_).of_eq (by simp [digestEvalBudget])
  exact (bounded_tableM (budget := fun _ => 1 + (1 + 0)) fun o =>
    FreeQuery.Bounded.bind (bounded_finalMaskM key (2 * o.val)) fun _ =>
      FreeQuery.Bounded.bind (bounded_finalMaskM key (2 * o.val + 1)) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq
    (by simp [mul_comm])

end Kriterion.CRT
