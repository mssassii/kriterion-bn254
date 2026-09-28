/-
**The replay of the conversion of one odd modulus** (package M5b, the conversion part), against the evaluator `conversionEvalM`
(`Construction/CRT/Coord.lean`), in its order:

1. the two stage values `σ mod 2 ^ w0` and `(σ / 2 ^ w0) mod 2 ^ w1` from the value cell `σ`;
2. extraction stage 0 on the truth word (`stageReplay`, `ReplayExtract.lean`);
3. extraction stage 1 on stage 0's next remainder;
4. the free stage-2 bit label `laneBit e1.next 0` (`lanePack`);
5. the copy of stage 0's `2 ^ w0` leaves to the growth region (`saveLeaves`);
6. the growth to `2 ^ keep` labels (`growEval`);
7. the reindex modulo `m` (`reindexBlock`) and the first hot index (`hotInit`);
8. the folds at bit positions `keep .. ell - 1` (`foldsLoop`).

The bit label of position `j` is read where it lies (`convBit`): stage 0's bit cells for
`j < w0`, stage 1's for `w0 ≤ j < w0 + w1`, the stage-2 cell otherwise.

**Placement**, inside the modulus window `W` that the composer assigns. The inputs are the truth word's active lanes at `W + j` (`j < 104`) and `σ` at `W + 128`; the joins
and pins stay in the source regions (below `W`). The block writes only cells of
`[W + 256, W + 2 ^ 18)`:

| cells | offset from `W` |
|---|---|
| stage values, stage-2 bit | `256`, `257`, `258` |
| fold vector (`m ≤ 2 ^ 11` cells), hot index | `2 ^ 12`, `2 ^ 12 + 2 ^ 11` |
| fold materials | `2 ^ 13` |
| stage 0 chain, stage 1 chain (each below `2 ^ 14` cells for `w ≤ 12`) | `2 ^ 14`, `2 ^ 15` |
| growth levels, growth materials (`2 ^ keep ≤ 2 ^ 16` each) | `2 ^ 16`, `2 ^ 17` |
-/

import Construction.Simulator.CRT.ReplayExtract
import Construction.Simulator.CRT.ReplayFold
import Construction.Simulator.CRT.ReplayChunks
import Construction.CRT.Coord

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! ### Placement -/

/-- The cells of one extraction stage laid out from `S` (scratch and outputs), with the given
inputs. -/
def stageChain (S w rb value remBase joinBase pinBase : Nat) : StageCells where
  value := value
  remBase := remBase
  joinBase := joinBase
  pinBase := pinBase
  subBase := S
  nodeBase := S + 128
  matBase := S + 128 + 2 ^ w
  levelSumBase := S + 128 + 2 ^ w + 2 ^ w
  classBase := S + 128 + 2 ^ w + 2 ^ w + w
  castSumBase := S + 128 + 2 ^ w + 2 ^ w + w + 128 * (w + 1)
  ansBase := S + 128 + 2 ^ w + 2 ^ w + w + 128 * (w + 1) + 128 * (w + 1)
  laneBase := S + 128 + 2 ^ w + 2 ^ w + w + 128 * (w + 1) + 128 * (w + 1) + 2 * Kriterion.CRT.castAnswers rb
  active := S + 128 + 2 ^ w + 2 ^ w + w + 128 * (w + 1) + 128 * (w + 1) +
    2 * Kriterion.CRT.castAnswers rb + 128
  slot := S + 128 + 2 ^ w + 2 ^ w + w + 128 * (w + 1) + 128 * (w + 1) +
    2 * Kriterion.CRT.castAnswers rb + 129
  bitBase := S + 128 + 2 ^ w + 2 ^ w + w + 128 * (w + 1) + 128 * (w + 1) +
    2 * Kriterion.CRT.castAnswers rb + 130
  nextBase := S + 128 + 2 ^ w + 2 ^ w + w + 128 * (w + 1) + 128 * (w + 1) +
    2 * Kriterion.CRT.castAnswers rb + 130 + w

/-- Stage 0's cells: the truth word at `W`, the value at `W + 256`. -/
def convStage0 (row : Kriterion.CRT.OddRow) (W joinBase pinBase : Nat) : StageCells :=
  stageChain (W + 2 ^ 14) row.width0 row.ell (W + 256) W joinBase pinBase

/-- Stage 1's cells: stage 0's next remainder, the value at `W + 257`. -/
def convStage1 (row : Kriterion.CRT.OddRow) (W joinBase0 pinBase0 joinBase pinBase : Nat) : StageCells :=
  stageChain (W + 2 ^ 15) row.width1 (row.ell - row.width0) (W + 257)
    (convStage0 row W joinBase0 pinBase0).nextBase joinBase pinBase

/-- The cell of the bit label of word position `j` (the construction's `wordBit`). -/
def convBit (row : Kriterion.CRT.OddRow) (W : Nat) (joinBase pinBase : Nat → Nat) (j : Nat) : Nat :=
  if j < row.width0 then (convStage0 row W (joinBase 0) (pinBase 0)).bitBase + j
  else if j < row.width0 + row.width1 then
    (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).bitBase + (j - row.width0)
  else W + 258

/-- The growth's tree cells. -/
def convGrowCells (row : Kriterion.CRT.OddRow) (W : Nat) (joinBase pinBase : Nat → Nat)
    (growJoin : Nat → Nat) : TreeCells :=
  ⟨W + 2 ^ 16, W + 2 ^ 17, W + 128, growJoin, convBit row W joinBase pinBase⟩

/-- The folds' cells. -/
def convFoldCells (row : Kriterion.CRT.OddRow) (W : Nat) (joinBase pinBase : Nat → Nat)
    (foldJoin : Nat → Nat) : FoldCells :=
  ⟨W + 2 ^ 12, W + 2 ^ 13, W + 2 ^ 12 + 2 ^ 11, W + 128, foldJoin, convBit row W joinBase pinBase⟩

/-! ### The blocks -/

/-- `value0 := σ mod 2 ^ w0` (clobbers `rA`, `rB`, `rAddr`). -/
def stageValue0 (W w0 : Nat) : Prog :=
  .seq (loadAt rA (W + 128))
    (.seq (cst rB (2 ^ w0 - 1))
    (.seq (ar .and rA rA rB) (storeAt (W + 256) rA)))

/-- `value1 := (σ >> w0) mod 2 ^ w1` (clobbers `rA`, `rB`, `rAddr`). -/
def stageValue1 (W w0 w1 : Nat) : Prog :=
  .seq (loadAt rA (W + 128))
    (.seq (cst rB w0)
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB (2 ^ w1 - 1))
    (.seq (ar .and rA rA rB) (storeAt (W + 257) rA)))))

/-- The stage-2 bit label `laneBit e1.next 0` into `W + 258` (clobbers `rB`, `rD`, `rE`, `rAddr`). -/
def lastBitProg (W nextBase : Nat) : Prog :=
  .seq (lanePack nextBase 0) (storeAt (W + 258) rD)

/-- **The conversion of odd modulus `i`** of coordinate `coord` (row `row`, modulus `m`) in the
window `W`; `joinBase q` and `pinBase q` place stage `q`'s joins and pin lanes, `growJoin j` and
`foldJoin j` the growth and fold joins of bit position `j`. -/
def conversionReplay (coord i : Nat) (row : Kriterion.CRT.OddRow) (m W : Nat)
    (joinBase pinBase : Nat → Nat) (growJoin foldJoin : Nat → Nat) : Prog :=
  .seq (stageValue0 W row.width0)
    (.seq (stageValue1 W row.width0 row.width1)
    (.seq (stageReplay (convStage0 row W (joinBase 0) (pinBase 0)) row.width0 row.ell
      (fun level => Kriterion.CRT.extTreeTag coord i 0 level 0) (Kriterion.CRT.extCastTag coord i 0 0 0) 64)
    (.seq (stageReplay (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)) row.width1
      (row.ell - row.width0) (fun level => Kriterion.CRT.extTreeTag coord i 1 level 0)
      (Kriterion.CRT.extCastTag coord i 1 0 0) 64)
    (.seq (lastBitProg W (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).nextBase)
    (.seq (saveLeaves (convStage0 row W (joinBase 0) (pinBase 0)).nodeBase (W + 2 ^ 16) row.width0 0)
    (.seq (growEval (convGrowCells row W joinBase pinBase growJoin) (Kriterion.CRT.growTag coord i)
      row.width0 (row.keep - row.width0))
    (.seq (reindexBlock (W + 2 ^ 16) (W + 2 ^ 12) (row.width0 + (row.keep - row.width0)) m)
    (.seq (hotInit (convFoldCells row W joinBase pinBase foldJoin) row.keep m)
      (foldsLoop (convFoldCells row W joinBase pinBase foldJoin) m row.keep (row.ell - row.keep)
        (Kriterion.CRT.foldTag coord i))))))))))

/-- The conversion writes only the cells `[W + 256, W + 2 ^ 18)`. -/
def convWrites (W : Nat) : Writes := Writes.region ⟨W + 256, 2 ^ 18 - 256⟩

/-- The conversion's registers. -/
def convClobbers : Clobbers :=
  Clobbers.ofList [rA, rB, rC, rD, rE, rF, rAddr, rInput, rFirst, rSecond, rAcc, rOut]

end Kriterion.CRT.SimMachine
