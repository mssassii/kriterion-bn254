/-
The release-r1 stage-1 samplers the CRT machine's stage 1 is built from (`Construction/Simulator/CRT/Stage1.lean`):

* `fieldCell address`: one field cell by constant-time bounded rejection over `254` coins with `attempts = 256` tries,
  aborting on exhaustion;
* `wordCell width address`: one uniform word of `width` fair coins;
* `bytes`: the `91 · 12` exception bytes, `8` coins each.

Stage 1 contains no oracle instruction at all.
-/

import Construction.Simulator.Blocks

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks

namespace Stage1

/-- One uniform field cell at `address`. -/
def fieldCell (address : Nat) : Prog :=
  .seq (bounded fieldWidth (testBelow pNat) attempts (storeAt address rOut)) (zeroRegs samplerScratch)

/-- One uniform word of `width` coins at `address`. -/
def wordCell (width address : Nat) : Prog :=
  .seq (sampleWord width) (.seq (storeAt address rAcc) (zeroRegs [rAcc, rBit, rAddr]))

/-- All exception bytes. -/
def bytes : Prog := Prog.rep exceptionByteCount fun index => wordCell 8 (exceptionBase + index)

/-! ### Sizes and costs -/

theorem size_fieldCell (address : Nat) : (fieldCell address).size = 457231 := by
  simp only [fieldCell, Prog.size]
  rw [size_bounded _ _ _ _ (by rw [cost_storeAt]; omega), size_zeroRegs]
  rfl

theorem cost_fieldCell (address : Nat) : (fieldCell address).cost = 327180 := by
  simp only [fieldCell, Prog.cost]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeAt]; omega), cost_zeroRegs]
  rfl

theorem size_wordCell (width address : Nat) : (wordCell width address).size = 6 + 7 * width := by
  simp only [wordCell, Prog.size, size_sampleWord, size_storeAt, size_zeroRegs, List.length_cons,
    List.length_nil]
  omega

theorem cost_wordCell (width address : Nat) : (wordCell width address).cost = 6 + 5 * width := by
  simp only [wordCell, Prog.cost, cost_sampleWord, cost_storeAt, cost_zeroRegs, List.length_cons,
    List.length_nil]
  omega

theorem size_bytes : bytes.size = exceptionByteCount * 62 :=
  Prog.size_rep _ _ _ fun _ _ => size_wordCell _ _

theorem cost_bytes : bytes.cost = exceptionByteCount * 46 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_wordCell _ _

end Stage1

end Kriterion.ArgoMAC.PlanB.SimMachine
