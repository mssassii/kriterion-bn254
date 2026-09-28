/-
The configuration-E budgets as numerals (C6 rows, selected width-8/9 extraction schedule), closed by kernel evaluation
(`decide +kernel`): the pad counts `⌈(bitlen(m ^ S) + 120) / 256⌉` of the 85 moduli are computed by the
kernel's GMP-backed `Nat.pow` and `Nat.log2`, never by the elaborator.
-/

import Construction.CRT.Entry

namespace Kriterion.CRT.Entry

set_option maxRecDepth 100000 in
theorem coordGarbleBudget_x : coordGarbleBudget table xCount = 555519 := by decide +kernel

set_option maxRecDepth 100000 in
theorem coordGarbleBudget_y : coordGarbleBudget table yCount = 504212 := by decide +kernel

set_option maxRecDepth 100000 in
theorem coordEvalBudget_x : coordEvalBudget table xCount = 552221 := by decide +kernel

set_option maxRecDepth 100000 in
theorem coordEvalBudget_y : coordEvalBudget table yCount = 501140 := by decide +kernel

/-- **The garbler asks 1,062,022 queries** (gate 1,759,967). -/
theorem garbleBudget_eq : garbleBudget = 1062022 := by
  rw [garbleBudget, garbleBudgetOf, coordGarbleBudget_x, coordGarbleBudget_y]
  decide +kernel

/-- **The evaluator asks 1,055,144 queries** (gate 1,055,879). -/
theorem evaluateBudget_eq : evaluateBudget = 1055144 := by
  rw [evaluateBudget, evaluateBudgetOf, coordEvalBudget_x, coordEvalBudget_y]
  decide +kernel

/-- Both budgets are within the challenge's gates. -/
theorem budgets_within_gates : garbleBudget ≤ 1759967 ∧ evaluateBudget ≤ 1055879 := by
  rw [garbleBudget_eq, evaluateBudget_eq]
  decide

set_option maxRecDepth 100000 in
/-- The published conversion vector of one coordinate has 2,906 blocks (no chunk joins). -/
theorem convBlocks_table : table.convBlocks = convCount := by decide +kernel

end Kriterion.CRT.Entry
