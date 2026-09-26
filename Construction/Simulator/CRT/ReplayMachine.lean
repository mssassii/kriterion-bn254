/-
**Route M's replay on the machine, on the global layout** (M5b's concrete program): the cells of
every block placed on the map (`Layout.lean`). Coordinate `κ` keeps its replay in
`replayScratch κ` (a window of `2 ^ 40` cells):

* `R + 0 .. R + 2 ^ 21`: the chunk loop's scratch (`alpha` at `R`, level, materials, answers), its
  casts (`R + 2 ^ 10`, `2 ^ 20` cells) and leaves (`R + 2 ^ 10 + 2 ^ 20`, `256 · 32` cells);
* `R + 2 ^ 21 + 2 ^ 20 · i`: modulus `i`'s window (`ReplayDispatch.lean`; the conversion of an odd
  modulus is `conversionReplay`);
* `R + 2 ^ 28`: the decoding's scratch (gathered residues, digits, limbs).

The inputs are read in place: the request, the labels at `labelBase + 254 κ + j`, the joins and
pins in the source regions (`sourceJoin`, `sourcePin`) at the flat indices, the residue
digits at `residueCell κ i e`, the hints at `hintCell κ e`. The mask stage's answer scratch is at
`replayScratch 0 + 2 ^ 30`.
-/

import Construction.Simulator.CRT.ReplayEntry
import Construction.Simulator.CRT.ReplayDispatch
import Construction.Simulator.CRT.ReplayConversion
import Construction.CRT.Layout

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

namespace Machine

/-- The coordinate's value cell: the request. -/
def coordCellOf (κ : Nat) : Nat := if κ = 0 then reqX else reqY

/-- The chunk loop's cells of coordinate `κ`. -/
def coordCells (κ : Nat) : CoordCells where
  coordCell := coordCellOf κ
  labelBase := labelBase + 254 * κ
  chunkJoin c n := Layout.sourceJoin κ (Entry.chunkJoinBase c + (n - 1))
  pinBase := Layout.sourcePin κ 0 0
  alpha := Layout.replayScratch κ
  levelBase := Layout.replayScratch κ + 1
  matBase := Layout.replayScratch κ + 257
  ansBase := Layout.replayScratch κ + 513
  castBase := Layout.replayScratch κ + 2 ^ 10
  leafBase := Layout.replayScratch κ + 2 ^ 10 + 2 ^ 20

/-- The first cell of the moduli's windows. -/
def modBase (κ : Nat) : Nat := Layout.replayScratch κ + 2 ^ 21

/-- Modulus `i`'s window. -/
def windowAt (κ i : Nat) : Nat := modBase κ + 2 ^ 20 * i

/-- The residue joins of modulus `i`. -/
def joinBaseOf (κ i : Nat) : Nat := Layout.residueCell κ i 0

/-- The decoding's cells of coordinate `κ`. -/
def decodeCells (κ : Nat) : DecodeCells :=
  ⟨fun i => windowOut (windowAt κ i), Layout.hintCell κ 0, Layout.decodedCell κ 0,
    Layout.replayScratch κ + 2 ^ 28, Layout.replayScratch κ + 2 ^ 28 + 128,
    Layout.replayScratch κ + 2 ^ 28 + 256⟩

/-- The stage joins of modulus `i` (stage `q`'s `J_n` at `stageJoin κ i q + n`, `n ≥ 1`). -/
def stageJoin (κ i q : Nat) : Nat :=
  if q = 0 then Layout.sourceJoin κ (Entry.modJoinBase i) - 1
  else Layout.sourceJoin κ (Entry.modJoinBase i + ((Entry.rowAt i).width0 - 1)) - 1

/-- The stage pins of modulus `i` (stage `q`'s lane `j` at `stagePin κ i q + j`). -/
def stagePin (κ i q : Nat) : Nat := Layout.sourcePin κ (Entry.modPinBase i + q) 0

/-- The growth join of modulus `i` at position `j` (the offset capped at 16, which no row reaches,
so that every cell lies in the source region). -/
def growJoin (κ i j : Nat) : Nat :=
  Layout.sourceJoin κ (Entry.modJoinBase i + ((Entry.rowAt i).width0 - 1) + ((Entry.rowAt i).width1 - 1)
    + min (j - (Entry.rowAt i).width0) 16)

/-- The fold join of modulus `i` at position `j` (the offset capped at 16). -/
def foldJoin (κ i j : Nat) : Nat :=
  Layout.sourceJoin κ (Entry.modJoinBase i + ((Entry.rowAt i).width0 - 1) + ((Entry.rowAt i).width1 - 1)
    + ((Entry.rowAt i).keep - (Entry.rowAt i).width0) + min (j - (Entry.rowAt i).keep) 16)

/-- The conversion of modulus `i` (odd moduli only). -/
def convProg (κ i : Nat) : Prog :=
  if h : i < Entry.table.count then
    match Entry.table.kind ⟨i, h⟩ with
    | .odd row =>
        conversionReplay κ i row (Entry.table.modulus ⟨i, h⟩) (windowAt κ i) (stageJoin κ i)
          (stagePin κ i) (growJoin κ i) (foldJoin κ i)
    | .chunkZero => .skip 0
  else .skip 0

/-- The replay of coordinate `κ` with `S` encodings. -/
def coordProg (κ S : Nat) : Prog :=
  coordReplay (coordCells κ) Entry.table κ
    (modProg Entry.table S κ (coordCells κ) (modBase κ) (joinBaseOf κ) (convProg κ)
      (fun i => windowAt κ i + 2 ^ 12) (fun i => windowAt κ i + 2 ^ 12 + 2 ^ 11))
    (decodeCells κ) 6 S

/-- The mask stage's answer scratch. -/
def maskScratch : Nat := Layout.replayScratch 0 + 2 ^ 30

/-- **Route M's replay on the machine.** -/
def replay : Prog :=
  entryReplay (coordProg 0 Entry.xCount) (coordProg 1 Entry.yCount) maskScratch

end Machine

end Kriterion.CRT.SimMachine
