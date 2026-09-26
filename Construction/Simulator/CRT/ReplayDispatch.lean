/-
**The per-modulus programs of a coordinate** (the dispatch of `modEvalM` on the table's kind).
Modulus `i` owns the window of `2 ^ 20` cells from `W = modBase + 2 ^ 20 · i`: an odd modulus keeps
its truth-word lanes at `W`, its word value `σ` at `W + 128`, the conversion's cells in
`[W + 256, W + 2 ^ 18)`, and every modulus keeps its body's cells from
`W + 2 ^ 18` (`windowBody`), the residues at `windowOut W`.
-/

import Construction.Simulator.CRT.ReplayMod
import Construction.Simulator.CRT.ReplayWords
import Construction.Simulator.CRT.ReplayOdd
import Construction.Simulator.CRT.ReplayCoord

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The body cells of a modulus in its window `W`, with the one-hot at `vecBase`, the hot index at
`hot` and the residue joins at `joinBase`. -/
def windowBody (W vecBase hot joinBase : Nat) : BodyCells :=
  ⟨vecBase, hot, W + 2 ^ 18, W + 2 ^ 18 + 1024, W + 2 ^ 18 + 2048, W + 2 ^ 18 + 2560, joinBase,
    W + 2 ^ 18 + 3072⟩

/-- The residue cells of the modulus whose window starts at `W`. -/
def windowOut (W : Nat) : Nat := W + 2 ^ 18 + 3072

/-- The modulus-256 path in window `W`: the hot index at `W`, the one-hot at `leafBase`. -/
def modZeroProg (coordCell leafBase W joinBase m width S q : Nat) (tagOf : Nat → Nat → Nat) : Prog :=
  mod256Block coordCell (windowBody W leafBase W joinBase) m width S q tagOf

/-- An odd modulus in window `W`: its truth-word lanes at `W`, `σ` at `W + 128`, the conversion
`convProg`, then the body on the conversion's one-hot at `vec` with the hot index at `hot`. -/
def modOddProg (coordCell castBase W joinBase m ell S q count : Nat) (truthOf : Nat → Nat → Nat)
    (offset width : Nat → Nat) (convProg : Prog) (vec hot : Nat) (tagOf : Nat → Nat → Nat) : Prog :=
  .seq (truthWordBlock castBase W truthOf width count ell)
    (.seq (sigmaBlock coordCell (W + 128) m count offset width)
    (.seq convProg (bodyBlock (windowBody W vec hot joinBase) m S q tagOf)))

/-- **The program of modulus `i`** of a coordinate, in the window `modBase + 2 ^ 20 · i`: the
modulus-256 path or an odd modulus's path (`convProgOf i`, leaving
its one-hot at `vecOf i` and its hot index at `hotOf i`). -/
def modProg (T : CrtTable) (S coord : Nat) (cc : CoordCells) (modBase : Nat) (joinBaseOf : Nat → Nat)
    (convProgOf : Nat → Prog) (vecOf hotOf : Nat → Nat) (i : Nat) : Prog :=
  if h : i < T.count then
    match T.kind ⟨i, h⟩ with
    | .chunkZero =>
        modZeroProg cc.coordCell cc.leafBase (modBase + 2 ^ 20 * i) (joinBaseOf i) (T.modulus ⟨i, h⟩)
          (T.chunkWidth 0) S (T.padAnswers S ⟨i, h⟩) (Kriterion.CRT.bodyTag coord i)
    | .odd row =>
        modOddProg cc.coordCell cc.castBase (modBase + 2 ^ 20 * i) (joinBaseOf i) (T.modulus ⟨i, h⟩)
          row.ell S (T.padAnswers S ⟨i, h⟩) T.chunkCount (T.truth (T.modulus ⟨i, h⟩)) T.chunkOffset
          T.chunkWidth (convProgOf i) (vecOf i) (hotOf i) (Kriterion.CRT.bodyTag coord i)
  else .skip 0

end Kriterion.CRT.SimMachine
