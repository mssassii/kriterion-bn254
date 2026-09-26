/-
**P6a2 for the concrete entry**: `ViewEntriesPerm crtEntry Entry.table` from its four primitive facts
(`crtEntry_garbler_small`, `crtEntry_garbler_distinct`, `crtEntry_viewOnce`, `crtEntry_sameVisible`), and
`CrtUpperFactor crtEntry Entry.table` by `crtUpperFactor_of`.
-/

import Proof.Privacy.CRT.Paths.SameVisible

namespace Kriterion.CRT.Paths

open Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws

/-- **The view's entries are the garbler's visible entries**, for the concrete entry at its table. -/
theorem crtEntry_viewEntriesPerm : ViewEntriesPerm Instance.crtEntry Kriterion.CRT.Entry.table :=
  viewEntriesPerm_of (E := Instance.crtEntry) Kriterion.CRT.Entry.table crtEntry_garbler_small
    crtEntry_garbler_distinct (crtEntry_viewOnce _) crtEntry_sameVisible

/-- **P6a2 (`CrtUpperFactor`) for the concrete entry at its table.** The instances are passed explicitly: the
statement has two `[Fintype Empty]` (and two `[DecidableEq Empty]`) binders, and letting the elaborator synthesize
them picks one local instance for both positions, so the two sides differ in their instances and the defeq check
evaluates the garbler. -/
theorem crtEntry_upperFactor : H8.CrtUpperFactor Instance.crtEntry Kriterion.CRT.Entry.table := by
  intro field group fintypeFI fintypeEI decFI decEI
  have upper := @crtUpperFactor_of _ _ Instance.crtEntry Kriterion.CRT.Entry.table crtEntry_viewEntriesPerm
  exact @upper field group fintypeFI fintypeEI decFI decEI

end Kriterion.CRT.Paths
