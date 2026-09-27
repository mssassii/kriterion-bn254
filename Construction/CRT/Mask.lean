/-
The Embryo masks of the row encodings (configuration E, D8).

The evaluator reads the curve check's output `t'`, asks the key `K = (H (hashInput (t' mod 2 ^ 128) keyTag)).1`
(`keyM`; one labelled query, tag `tagCode Family.key 0 0 0 0 0 0`), and reads every row encoding's mask
from hash answers at `K + 2 ^ 128 * tag`, tag `tagCode 7 0 0 stage 0 site part`:

* **collector sites** (stage 0): the `x` slots 1, 2, 3 of each digit (`rowX_x9`, `rowY_cubic`, `rowZ_x9`), site
  `c = 3 * digit + k`, two answers each; the mask is `sampleFp a₀.1 a₀.2 a₁.1` (`a₁.2` unused);
* **non-collector sites** (stage 1): the list of the `x` encodings with slot 0 (digit-major), then the `y` point
  encodings `0 .. 3 * digits - 1`; entries `2k` and `2k + 1` share site `k` (three answers; masks
  `sampleFp a₀.1 a₀.2 a₁.1` and `sampleFp a₁.2 a₂.1 a₂.2`); an odd last entry has its own site with two answers.

`sampleFp` is `release-r1`'s Rule S reader (`Construction/PGS/Sampler.lean`). With 91 digits: 273 collector sites
(546 answers), 182 pairs (546) and no single site, 1,092 answers (`maskBudget_real`). Route M's replay asks only
the non-collector answers (`nonCollectorMasksM`, 546 answers), whose values are the full program's non-collector part
(`eval_nonCollectorMasksM`). The encoding order is `release-r1`'s: `x` encoding `e < 4 * digits` has digit `e / 4` and
slot `e % 4` (`rowX_x7, rowX_x9, rowY_cubic, rowZ_x9`), `y` encoding `e < 3 * digits` digit `e / 3`; the curve
encodings after them carry no mask (`maskOf` gives 0).
-/

import Construction.CRT.Query
import Construction.PGS.Sampler

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC
open Kriterion.ArgoMAC.PlanB (sampleFp)

/-! ### The site layout -/

/-- The tag of answer `part` of mask site `site` at stage `stage` (0 collectors, 1 non-collectors). -/
def maskTag (stage site part : Nat) : Nat := tagCode Family.mask 0 0 stage 0 site part

/-- Collector sites: three per digit. -/
def collectorSites (digits : Nat) : Nat := 3 * digits

/-- Non-collector encodings: one `x` slot and three `y` slots per digit. -/
def nonCollectorCount (digits : Nat) : Nat := 4 * digits

/-- Pair sites of the non-collector list. -/
def pairSites (digits : Nat) : Nat := nonCollectorCount digits / 2

/-- Single sites (0 or 1): the odd last entry of the non-collector list. -/
def singleSites (digits : Nat) : Nat := nonCollectorCount digits % 2

/-- The `x` slot of collector `k < 3` of a digit: `rowX_x9`, `rowY_cubic`, `rowZ_x9`. -/
def collectorSlot (k : Nat) : Nat := k + 1

/-- Entry `n` of the non-collector list, as (coordinate, encoding index). -/
def nonCollectorEntry (digits n : Nat) : Nat × Nat :=
  if n < digits then (0, 4 * n) else (1, n - digits)

/-! ### Reading -/

/-- The three-block reading of a two-answer site. -/
def readSingle (answers : Fin 2 → Block × Block) : BN254.BaseField :=
  sampleFp (answers 0).1 (answers 0).2 (answers 1).1

/-- The two masks of a three-answer pair site. -/
def readPair (answers : Fin 3 → Block × Block) : BN254.BaseField × BN254.BaseField :=
  (sampleFp (answers 0).1 (answers 0).2 (answers 1).1, sampleFp (answers 1).2 (answers 2).1 (answers 2).2)

/-- All masks of one garbling: collectors by site, pairs by site, and the single site (0 if there is none). -/
structure MaskValues (digits : Nat) where
  /-- The collector masks, by collector number `3 * digit + k`. -/
  collector : Fin (collectorSites digits) → BN254.BaseField
  /-- The pair masks, by pair site. -/
  pair : Fin (pairSites digits) → BN254.BaseField × BN254.BaseField
  /-- The mask of the single site (0 when the non-collector count is even). -/
  single : BN254.BaseField

/-! ### Pure functions of the hash -/

/-- The key's tag: family `Family.key`, every other field 0. -/
def maskKeyTag : Nat := tagCode Family.key 0 0 0 0 0 0

/-- The key's hash input: the low 128 bits of the curve check's output as the label, at the key's tag. -/
def maskKeyInput (t : BN254.BaseField) : Nat := hashInput (BitVec.ofNat 128 t.val) maskKeyTag

/-- The key `K = (H (hashInput (t' mod 2 ^ 128) maskKeyTag)).1` at the curve check's output. -/
def maskKey (H : HashN) (t : BN254.BaseField) : Block := (H (maskKeyInput t)).1

/-- The answers of one site at the key. -/
def siteAnswers (H : HashN) (K : Block) (stage site count : Nat) : Fin count → Block × Block :=
  fun part => H (hashInput K (maskTag stage site part.val))

/-- The masks of one garbling at key `K`. -/
def maskValues (H : HashN) (K : Block) (digits : Nat) : MaskValues digits where
  collector := fun c => readSingle (siteAnswers H K 0 c.val 2)
  pair := fun k => readPair (siteAnswers H K 1 k.val 3)
  single := if singleSites digits = 1 then readSingle (siteAnswers H K 1 (pairSites digits) 2) else 0

/-- The mask of non-collector entry `n` (the pair's first or second mask, or the single site's). -/
def nonCollectorMask {digits : Nat} (values : MaskValues digits) (n : Nat) : BN254.BaseField :=
  if inRange : n / 2 < pairSites digits then
    if n % 2 = 0 then (values.pair ⟨n / 2, inRange⟩).1 else (values.pair ⟨n / 2, inRange⟩).2
  else values.single

/-- **The mask of an encoding**: `x` encoding `e` of digit `e / 4` and slot `e % 4`, or `y` point encoding `e`;
curve encodings (and indices beyond the point encodings) carry no mask. -/
def maskOf {digits : Nat} (values : MaskValues digits) (coord e : Nat) : BN254.BaseField :=
  if coord = 0 then
    if e < 4 * digits then
      if e % 4 = 1 then atNat values.collector 0 (3 * (e / 4))
      else if e % 4 = 2 then atNat values.collector 0 (3 * (e / 4) + 1)
      else if e % 4 = 3 then atNat values.collector 0 (3 * (e / 4) + 2)
      else nonCollectorMask values (e / 4)
    else 0
  else if e < 3 * digits then nonCollectorMask values (digits + e) else 0

/-- The row value of an encoding: the delivered value minus its mask. -/
def unmask {digits : Nat} (values : MaskValues digits) (coord e : Nat) (delivered : BN254.BaseField) :
    BN254.BaseField :=
  delivered - maskOf values coord e

/-! ### Programs -/

/-- The key program: one query at the curve check's output. -/
def keyM (t : BN254.BaseField) : CM Block := askN (maskKeyInput t) >>= fun answer => pure answer.1

/-- One site's answers, parts ascending. -/
def siteAnswersM (K : Block) (stage site count : Nat) : CM (Fin count → Block × Block) :=
  tableM count fun part => askN (hashInput K (maskTag stage site part.val))

/-- The collector masks, sites ascending. -/
def collectorMasksM (K : Block) (digits : Nat) : CM (Fin (collectorSites digits) → BN254.BaseField) :=
  tableM (collectorSites digits) fun c => siteAnswersM K 0 c.val 2 >>= fun answers => pure (readSingle answers)

/-- The pair masks, sites ascending. -/
def pairMasksM (K : Block) (digits : Nat) :
    CM (Fin (pairSites digits) → BN254.BaseField × BN254.BaseField) :=
  tableM (pairSites digits) fun k => siteAnswersM K 1 k.val 3 >>= fun answers => pure (readPair answers)

/-- The single site's mask, if there is one. -/
def singleMaskM (K : Block) (digits : Nat) : CM BN254.BaseField :=
  if singleSites digits = 1 then
    siteAnswersM K 1 (pairSites digits) 2 >>= fun answers => pure (readSingle answers)
  else pure 0

/-- **Route M's replay**: the non-collector masks only (the collector answers are programmed, not asked). -/
def nonCollectorMasksM (K : Block) (digits : Nat) :
    CM ((Fin (pairSites digits) → BN254.BaseField × BN254.BaseField) × BN254.BaseField) :=
  pairMasksM K digits >>= fun pairs => singleMaskM K digits >>= fun single => pure (pairs, single)

/-- **Every mask answer, in site order** (collectors, then pairs, then the single site). -/
def maskAnswersM (K : Block) (digits : Nat) : CM (MaskValues digits) :=
  collectorMasksM K digits >>= fun collector => nonCollectorMasksM K digits >>= fun rest =>
    pure { collector, pair := rest.1, single := rest.2 }

/-! ### Evaluation -/

@[simp] theorem eval_keyM (H : HashN) (t : BN254.BaseField) : (keyM t).eval H = maskKey H t := rfl

@[simp] theorem eval_siteAnswersM (H : HashN) (K : Block) (stage site count : Nat) :
    (siteAnswersM K stage site count).eval H = siteAnswers H K stage site count := by
  simp only [siteAnswersM, eval_tableM, eval_askN]
  rfl

theorem eval_collectorMasksM (H : HashN) (K : Block) (digits : Nat) :
    (collectorMasksM K digits).eval H = (maskValues H K digits).collector := by
  simp [collectorMasksM, maskValues]

theorem eval_pairMasksM (H : HashN) (K : Block) (digits : Nat) :
    (pairMasksM K digits).eval H = (maskValues H K digits).pair := by
  simp [pairMasksM, maskValues]

theorem eval_singleMaskM (H : HashN) (K : Block) (digits : Nat) :
    (singleMaskM K digits).eval H = (maskValues H K digits).single := by
  unfold singleMaskM maskValues
  split <;> simp

/-- The replay's masks are the full program's non-collector part. -/
theorem eval_nonCollectorMasksM (H : HashN) (K : Block) (digits : Nat) :
    (nonCollectorMasksM K digits).eval H
      = ((maskValues H K digits).pair, (maskValues H K digits).single) := by
  simp only [nonCollectorMasksM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_pairMasksM,
    eval_singleMaskM]

theorem eval_maskAnswersM (H : HashN) (K : Block) (digits : Nat) :
    (maskAnswersM K digits).eval H = maskValues H K digits := by
  simp only [maskAnswersM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_collectorMasksM,
    eval_nonCollectorMasksM]

/-! ### Budgets -/

/-- Mask answers of one side: two per collector site, three per pair site, two for the single site. -/
def maskBudget (digits : Nat) : Nat :=
  2 * collectorSites digits + 3 * pairSites digits + 2 * singleSites digits

/-- Answers of route M's replay: the pairs and the single site. -/
def nonCollectorBudget (digits : Nat) : Nat := 3 * pairSites digits + 2 * singleSites digits

theorem maskBudget_real : maskBudget 91 = 1092 := by decide

theorem nonCollectorBudget_real : nonCollectorBudget 91 = 546 := by decide

theorem bounded_keyM (t : BN254.BaseField) : (keyM t).Bounded 1 :=
  FreeQuery.Bounded.bind (bounded_askN _) fun _ => FreeQuery.Bounded.pure' _ 0

theorem bounded_siteAnswersM (K : Block) (stage site count : Nat) :
    (siteAnswersM K stage site count).Bounded count :=
  (bounded_tableM (budget := fun _ => 1) fun _ => bounded_askN _).of_eq (by simp)

theorem bounded_collectorMasksM (K : Block) (digits : Nat) :
    (collectorMasksM K digits).Bounded (2 * collectorSites digits) :=
  (bounded_tableM (budget := fun _ => 2 + 0) fun c =>
    FreeQuery.Bounded.bind (bounded_siteAnswersM K 0 c.val 2) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq
    (by simp [mul_comm])

theorem bounded_pairMasksM (K : Block) (digits : Nat) :
    (pairMasksM K digits).Bounded (3 * pairSites digits) :=
  (bounded_tableM (budget := fun _ => 3 + 0) fun k =>
    FreeQuery.Bounded.bind (bounded_siteAnswersM K 1 k.val 3) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq
    (by simp [mul_comm])

theorem bounded_singleMaskM (K : Block) (digits : Nat) :
    (singleMaskM K digits).Bounded (2 * singleSites digits) := by
  unfold singleMaskM
  refine FreeQuery.Bounded.ite (fun one => ?_) (fun _ => FreeQuery.Bounded.pure' _ _)
  exact (FreeQuery.Bounded.bind (bounded_siteAnswersM K 1 (pairSites digits) 2) fun _ =>
    FreeQuery.Bounded.pure' _ 0).of_eq (by rw [one])

theorem bounded_nonCollectorMasksM (K : Block) (digits : Nat) :
    (nonCollectorMasksM K digits).Bounded (nonCollectorBudget digits) :=
  (FreeQuery.Bounded.bind (bounded_pairMasksM K digits) fun _ =>
    FreeQuery.Bounded.bind (bounded_singleMaskM K digits) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq
    (by simp [nonCollectorBudget])

/-- **The mask program asks exactly `maskBudget digits` answers** (1,092 with 91 digits). -/
theorem bounded_maskAnswersM (K : Block) (digits : Nat) :
    (maskAnswersM K digits).Bounded (maskBudget digits) :=
  (FreeQuery.Bounded.bind (bounded_collectorMasksM K digits) fun _ =>
    FreeQuery.Bounded.bind (bounded_nonCollectorMasksM K digits) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq
    (by simp [maskBudget, nonCollectorBudget]; omega)

end Kriterion.CRT
