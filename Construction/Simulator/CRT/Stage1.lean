/-
**Stage 1 of the CRT machine** (M2): draw `Entry.Source` into RAM, write the Lamport key, and emit
`Wire.encoding (publish source)`.

Sampling, in this order (every cell in `Layout.lean`'s regions):

| block | cells | sampler |
|---|---|---|
| `fields` | `fieldBase + index`, `index < 276`: the curve constants, then the row cells `3 + 3 d + slot` | release-r1's `fieldCell` (bounded rejection below `p`) |
| `bytes` | `exceptionBase + index`, `index < 182` | independent exception nibbles (4 coins each) |
| `joins` | `sourceJoin κ index`, `index < joinCount` | 104 coins (the chunk-join cells are drawn but neither serialized nor read) |
| `pins` | `sourcePin κ k lane`, `k < pinCount`, `lane < 104` | `pinWidth k` coins (one lane per word) |
| `digits` | `residueCell κ i e`, `e < encCount κ`, `i < 84` | bounded rejection below `m_i` over `digitWidth m_i` coins |
| `zeros` | `keyBase + 2 j`, `j < 508` (`Z_j`) | 128 coins |
| `deltas` | `deltaCell κ` | 128 coins |
| `signs` | `Layout.signCell d`, `d < 91` (the sign bits `ν`) | one coin |
| `keyTrue` | `keyBase + 2 j + 1 := Z_j ⊕ Δ_{j / 254}` (after the serializer) | deterministic |

The record of encoding `e` is the mixed-radix integer of its digits, `Σ_i J_i · Π_{i' < i} m_{i'}`; the digits are
independent and uniform below `m_i`, so the record is uniform below `M`.

Serialization (`serialize`): `pieces` lists what the wire carries, in wire order, as words of RAM (`Piece.word
address width`: the low `width` bits of the word, least significant first) and records (`Piece.record κ e`: the
record's 624 bits, computed by Horner's rule into five 128-bit limbs at `recordLimb`, then emitted). The machine
emits the pieces in reverse (the response stack is last in, first out), each piece's bits most significant first,
so the stack reads the wire from the top.
-/

import Construction.Simulator.Stage1
import Construction.Simulator.CRT.Layout
import Construction.Simulator.CRT.Arith
import Construction.CRT.Layout

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

namespace CrtStage1

/-! ### Counts and widths -/

/-- The field cells: the curve constants and the row constants. -/
def fieldCount : Nat := curveCellCount + rowCellCount

/-- The encodings of coordinate `κ`. -/
def encCount (κ : Nat) : Nat := if κ = 0 then Entry.xCount else Entry.yCount

/-- Modulus `i` (`1` off range). -/
def modulusAt (i : Nat) : Nat := bn254Moduli.getD i 1

/-- The coins of a digit below `m`: `2 ^ digitWidth m ≥ m > 2 ^ (digitWidth m - 1)`. -/
def digitWidth (m : Nat) : Nat := Nat.log2 (m - 1) + 1

/-- The width of pin `k` (`0` off range). -/
def pinWidthAt (k : Nat) : Nat := Entry.pinWidths.getD k 0

/-- The moduli. -/
def moduliCount : Nat := 84

/-- The limbs of a record under construction (five 128-bit limbs, `624` bits emitted; records are below
`2 M < 2 ^ 620`). -/
def recordLimb (k : Nat) : Nat := tmpBase + 64 + k

/-- Limbs of a record. -/
def recordLimbCount : Nat := 5

/-! ### Sampling -/

/-- One digit below `m` at `address`: release-r1's `fieldCell` with the width and bound of `m`. -/
def digitCell (m address : Nat) : Prog :=
  .seq (bounded (digitWidth m) (testBelow m) attempts (storeAt address rOut)) (zeroRegs samplerScratch)

/-- The sign bits `ν`, one coin each. -/
def signs : Prog := Prog.rep 91 fun d => Stage1.wordCell 1 (Layout.signCell d)

/-- The curve constants and the row cells. -/
def fields : Prog := Prog.rep fieldCount fun index => Stage1.fieldCell (fieldBase + index)

/-- The exception nibbles (two per digit). -/
def bytes : Prog := Stage1.bytes

/-- The joins of both coordinates, flat: `n = κ · joinCount + index`. -/
def joins : Prog :=
  Prog.rep (2 * Entry.joinCount) fun n =>
    Stage1.wordCell labelBits (Layout.sourceJoin (n / Entry.joinCount) (n % Entry.joinCount))

/-- The pin of lane word `n = (κ · pinCount + k) · 104 + lane`. -/
def pinOf (n : Nat) : Nat := n / laneCount % Entry.pinCount

/-- The coordinate of lane word `n`. -/
def pinCoord (n : Nat) : Nat := n / (Entry.pinCount * laneCount)

/-- The pins of both coordinates, one lane per word, flat. -/
def pins : Prog :=
  Prog.rep (2 * (Entry.pinCount * laneCount)) fun n =>
    Stage1.wordCell (pinWidthAt (pinOf n)) (Layout.sourcePin (pinCoord n) (pinOf n) (n % laneCount))

/-- The records, `x` then `y`. -/
def recordCount : Nat := Entry.xCount + Entry.yCount

/-- The coordinate of record `r`. -/
def recordCoord (r : Nat) : Nat := if r < Entry.xCount then 0 else 1

/-- The encoding of record `r` inside its coordinate. -/
def recordIndex (r : Nat) : Nat := if r < Entry.xCount then r else r - Entry.xCount

/-- The records' digits, record by record, flat: `n = r · 84 + i`. -/
def digits : Prog :=
  Prog.rep (recordCount * moduliCount) fun n =>
    digitCell (modulusAt (n % moduliCount))
      (Layout.residueCell (recordCoord (n / moduliCount)) (n % moduliCount) (recordIndex (n / moduliCount)))

/-- The zero labels `Z_j`. -/
def zeros : Prog := Prog.rep labelCount fun j => Stage1.wordCell 128 (keyBase + 2 * j)

/-- The offsets `Δ_κ`. -/
def deltas : Prog := Prog.rep 2 fun κ => Stage1.wordCell 128 (Layout.deltaCell κ)

/-- The true label of bit `j`: `Z_j ⊕ Δ`. -/
def keyXor (j : Nat) : Prog :=
  Prog.seqList [loadAt rA (keyBase + 2 * j), loadAt rB (Layout.deltaCell (j / 254)), ar .xor rA rA rB,
    storeAt (keyBase + 2 * j + 1) rA]

/-- The true labels. -/
def keyTrue : Prog := Prog.rep labelCount keyXor

/-! ### Serialization -/

/-- What the wire carries, piece by piece. -/
inductive Piece
  /-- The low `width` bits of `RAM[address]`. -/
  | word (address width : Nat)
  /-- The 624 bits of the record of encoding `e` of coordinate `κ`. -/
  | record (κ e : Nat)
deriving Inhabited

/-- `count` joins of coordinate `κ` from index `start`. -/
def joinPieces (κ start count : Nat) : List Piece :=
  (List.range count).map fun n => .word (Layout.sourceJoin κ (start + n)) labelBits

/-- Pin `k` of coordinate `κ`: its 104 active lanes (the reserved RAM stride remains 128). -/
def pinPieces (κ k : Nat) : List Piece :=
  (List.range laneCount).map fun lane => .word (Layout.sourcePin κ k lane) (pinWidthAt k)

/-- The conversion blocks of coordinate `κ`, in the order of `ConvPublic.flatten`: per chunk its pin only (no
chunk joins: the chunk-join source cells are drawn but never serialized), then per odd modulus its joins and pins. -/
def convPieces (κ : Nat) : List Piece :=
  ((List.range Entry.table.chunkCount).flatMap fun c => pinPieces κ c) ++
  ((List.finRange Entry.table.count).flatMap fun i => match Entry.table.kind i with
    | .chunkZero => []
    | .odd row =>
      joinPieces κ (Entry.modJoinBase i) (row.width0 - 1) ++
      pinPieces κ (Entry.modPinBase i) ++
      joinPieces κ (Entry.modJoinBase i + (row.width0 - 1)) (row.width1 - 1) ++
      pinPieces κ (Entry.modPinBase i + 1) ++
      joinPieces κ (Entry.modJoinBase i + (row.width0 - 1) + (row.width1 - 1)) (row.keep - row.width0) ++
      joinPieces κ (Entry.modJoinBase i + (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0))
        (row.ell - row.keep))

/-- The records of coordinate `κ`. -/
def recordPieces (κ : Nat) : List Piece := (List.range (encCount κ)).map fun e => .record κ e

/-- The rows: per digit its `X` constant (a field cell) and its flags byte, the sign bit's cell (both
normalization flags clear). -/
def rowPieces : List Piece :=
  ((List.range 91).map fun d => [.word (fieldBase + (3 + 3 * d)) 256, .word (Layout.signCell d) 8]).flatten

/-- **The wire, piece by piece**: curve, rows, exception, `crtX`, `crtY`, `recX`, `recY`. -/
def pieces : List Piece :=
  (List.range curveCellCount).map (fun index => .word (fieldBase + index) 256) ++ rowPieces ++
  (List.range exceptionCellCount).map (fun index => .word (exceptionBase + index) 4) ++
  convPieces 0 ++ convPieces 1 ++ recordPieces 0 ++ recordPieces 1

/-- Clear the record limbs. -/
def clearLimbs : Prog :=
  Prog.rep recordLimbCount fun k => .seq (cst rA 0) (storeAt (recordLimb k) rA)

/-- One Horner step: `X ← X · m_i + J_i`. -/
def hornerStep (κ e i : Nat) : Prog :=
  Prog.seqList [loadAt rC (Layout.residueCell κ i e), setupConsts (modulusAt i),
    mulSmallAdd (recordLimb 0) recordLimbCount]

/-- Emit the record's 624 bits: limb 4 (112 bits) first, limb 0 last. -/
def emitRecord : Prog :=
  Prog.seqList [emitWord (recordLimb 4) 112, emitWord (recordLimb 3) 128, emitWord (recordLimb 2) 128,
    emitWord (recordLimb 1) 128, emitWord (recordLimb 0) 128]

/-- The record of encoding `e` of coordinate `κ`: Horner from the top digit, then its bits. -/
def recordProg (κ e : Nat) : Prog :=
  Prog.seqList [clearLimbs, Prog.rep moduliCount (fun n => hornerStep κ e (moduliCount - 1 - n)), emitRecord]

/-- One piece. -/
def pieceProg : Piece → Prog
  | .word address width => emitWord address width
  | .record κ e => recordProg κ e

/-- **The serializer**: the pieces, the last first. -/
def serialize : Prog :=
  Prog.rep pieces.length fun n => pieceProg (pieces.getD (pieces.length - 1 - n) default)

/-- **Stage 1**: the draws, the wire, the true labels; then the record limbs and every register are cleared, so
the retained configuration is a function of the draws. -/
def program : Prog :=
  Prog.seqList [fields, bytes, joins, pins, digits, zeros, deltas, signs, serialize, keyTrue, clearLimbs,
    zeroRegs allRegisters]

end CrtStage1

end Kriterion.CRT.SimMachine
