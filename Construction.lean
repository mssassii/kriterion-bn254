/-
The construction root of the CRT entry: the CRT layer and the entry (`Construction/CRT/`: the
residue lanes, the conversion blocks, the records, the entry's scheme and query programs, the
stage-1 source layout and the budget numerals) and the CRT simulator machine
(`Construction/Simulator/CRT/`). The switch-system entry's modules that these import (the scheme,
the garbling, the Lamport encoding, the simulator blocks the CRT machine reuses) are built through
them.
-/

import Construction.CRT.Entry
import Construction.CRT.Layout
import Construction.CRT.BudgetFacts
import Construction.Simulator.CRT.Simulator
