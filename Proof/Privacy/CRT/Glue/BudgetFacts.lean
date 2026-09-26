/-
Names for the large closed numerals of `BudgetData`, stated **without Mathlib** so that `2 ^ 4352` keeps
core's `instPowNat`. Under Mathlib, `2 ^ 4352 : ℕ` elaborates through `Monoid.npow`, and checking it against core's
form unfolds `Nat.pow` 4,352 times (maximum recursion depth; verified in `Scratch/BudgetProbe.lean`).
`Budget.lean` uses only these names, never the numerals; they are irreducible for the elaborator and the two facts
are checked by the kernel (`decide +kernel`), which unfolds them with its GMP arithmetic.
-/

import Proof.Privacy.CRT.Glue.BudgetData

namespace Kriterion.CRT.BudgetData

/-- The numerator of one pad-and-mask swap over `padSwapDenom`. -/
@[irreducible] def padSwapNumer : Nat := padSwapNum + 728 * (2 ^ 384 % p) * 2 ^ 3968

/-- The common denominator `2^4352` of the pad terms. -/
@[irreducible] def padSwapDenom : Nat := 2 ^ 4352

theorem padSwap_share : Nat.ble (padSwapNumer * 2 ^ 100 * 1000) padSwapDenom = true := by decide +kernel

theorem padSwapDenom_pos : 0 < padSwapDenom := by decide +kernel

end Kriterion.CRT.BudgetData
