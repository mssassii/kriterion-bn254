/-
The stage-1 source of configuration E: every published cell in source form, for the machine's
stage 1 and the abstract simulator.

Per coordinate the conversion material is a list of **joins** (single blocks, in the flat order of
`ConvPublic.flatten`) and a list of **pins** held as lanes, one lane per value (`Lanes w`, with
`w = L` for the chunk pins and `ell`, `ell - width0` for the two extraction stages of an odd
modulus); the dense packing into blocks happens only in `publish`. Records are held as naturals
below `M` (the ideal stage 1 publishes every record uniform below `M` with the hint 0) and embedded into `Record` by `publish`. The Lamport key is the zero labels and
the two offsets.

`Finite` instances only (computable): a `Fintype` for uniform sampling is
`Fintype.ofFinite`, which is noncomputable and so belongs in `Proof/`.
-/

import Construction.CRT.Entry

namespace Kriterion.CRT.Entry

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-! ### Counts of one coordinate's joins and pins -/

/-- Joins of one modulus: stage 0, stage 1, growth, folds. -/
def modJoins : Kind → Nat
  | .chunkZero => 0
  | .odd row => (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0) + (row.ell - row.keep)

/-- The pin widths of one modulus: stages 0 and 1. -/
def modPinWidths : Kind → List Nat
  | .chunkZero => []
  | .odd row => [row.ell, row.ell - row.width0]

/-- The pin widths of one coordinate in pin order: one per chunk, then two per odd modulus. -/
def pinWidths : List Nat :=
  List.replicate table.chunkCount table.castWidth ++
    (List.finRange table.count).flatMap fun i => modPinWidths (table.kind i)

/-- Joins per coordinate. -/
def joinCount : Nat :=
  (∑ c : Fin table.chunkCount, (table.chunkWidth c.val - 1)) +
    ∑ i : Fin table.count, modJoins (table.kind i)

/-- Pins per coordinate. -/
def pinCount : Nat := pinWidths.length

/-- The width of pin `k`. -/
def pinWidth (k : Fin pinCount) : Nat := pinWidths.get k

/-! ### Index maps from the layout to joins and pins -/

/-- The first join of chunk `c`. -/
def chunkJoinBase (c : Nat) : Nat := ∑ c' : Fin c, (table.chunkWidth c'.val - 1)

/-- The first join of modulus `i`. -/
def modJoinBase (i : Nat) : Nat :=
  chunkJoinBase table.chunkCount + ∑ i' : Fin i, (match table.kindAt i'.val with
    | some kind => modJoins kind
    | none => 0)

/-- The first pin of modulus `i` (after the chunk pins). -/
def modPinBase (i : Nat) : Nat :=
  table.chunkCount + ∑ i' : Fin i, (match table.kindAt i'.val with
    | some kind => (modPinWidths kind).length
    | none => 0)

/-- The row of modulus `i` (a zero row off range or for the power of two). -/
def rowAt (i : Nat) : OddRow :=
  match table.kindAt i with
  | some (.odd row) => row
  | _ => ⟨0, 0, 0, 0⟩

/-! ### The source -/

/-- Every published cell in source form, and the Lamport key.

`rows d` holds the digit's published `X` constant (`xC0`) and two cells that are never published
(`yC4`, `zC0`): the privacy proof's stand-ins for the offsets of the collectors `rowY_cubic` and
`rowZ_x9`, whose zero event is the normalization's bad event (`Rows.zeroFlag`). `signs d` is `ν`. -/
structure Source where
  curve : BaseField × BaseField × BaseField
  rows : Fin digitCount → RowGamma
  signs : Fin digitCount → Bool
  exception : Fin digitCount → Exception.Entry
  joins : Fin 2 → Fin joinCount → Label
  pins : Fin 2 → (k : Fin pinCount) → Lanes (pinWidth k)
  recX : Fin xCount → Fin table.product
  recY : Fin yCount → Fin table.product
  zeros : Fin 2 → Fin coordinateBitCount → Block
  deltas : Fin 2 → Block

/-- A join of the source as a total function of its index. -/
def Source.joinAt (source : Source) (coord : Fin 2) (index : Nat) : Label :=
  atNat (source.joins coord) 0 index

/-- Block `b` of the dense packing of pin `k` (`0` off range). -/
def Source.pinBlockAt (source : Source) (coord : Fin 2) (k b : Nat) : Label :=
  if inRange : k < pinCount then
    atNat (pinBlocks (source.pins coord ⟨k, inRange⟩)) 0 b
  else 0

/-- The conversion material of one coordinate, as the evaluator reads it. -/
def Source.conv (source : Source) (coord : Fin 2) : ConvPublic where
  chunkJoin c n := source.joinAt coord (chunkJoinBase c + (n - 1))
  chunkPin c k := source.pinBlockAt coord c k
  stageJoin i stage n :=
    if stage = 0 then source.joinAt coord (modJoinBase i + (n - 1))
    else source.joinAt coord (modJoinBase i + ((rowAt i).width0 - 1) + (n - 1))
  stagePin i stage k := source.pinBlockAt coord (modPinBase i + stage) k
  growJoin i j :=
    source.joinAt coord (modJoinBase i + ((rowAt i).width0 - 1) + ((rowAt i).width1 - 1)
      + (j - (rowAt i).width0))
  foldJoin i j :=
    source.joinAt coord (modJoinBase i + ((rowAt i).width0 - 1) + ((rowAt i).width1 - 1)
      + ((rowAt i).keep - (rowAt i).width0) + (j - (rowAt i).keep))

/-- The published row data of a source digit: its `X` constant, both normalization flags clear, its sign. -/
def Source.normRow (source : Source) (digit : Fin digitCount) : NormRow :=
  { xC0 := (source.rows digit).xC0, zFlag := false, sFlag := false, sign := source.signs digit }

/-- **Publish**: the dense packing of the pins, the flat layout, the records with hint 0. -/
def publish (source : Source) : Public where
  curve := source.curve
  rows := Vector.ofFn source.normRow
  exception := Vector.ofFn source.exception
  crtX := convVector (source.conv 0)
  crtY := convVector (source.conv 1)
  recX := Vector.ofFn fun e => toRecord (source.recX e).val
  recY := Vector.ofFn fun e => toRecord (source.recY e).val

/-- The evaluator's 508 Lamport blocks at an input: `Z_j ⊕ bit_j Δ`, `x` then `y`. -/
def labels (source : Source) (input : AffineInput) : GarbledCircuit.LamportSignature :=
  Vector.ofFn fun index =>
    if inRange : index.val < coordinateBitCount then
      let position : Fin coordinateBitCount := ⟨index.val, inRange⟩
      if input.x.val.testBit index.val then source.zeros 0 position ^^^ source.deltas 0
      else source.zeros 0 position
    else
      let position : Fin coordinateBitCount := ⟨index.val - coordinateBitCount, by
        have := index.isLt; simp only [coordinateBitCount] at *; omega⟩
      if input.y.val.testBit position.val then source.zeros 1 position ^^^ source.deltas 1
      else source.zeros 1 position

/-! ### Finiteness -/

instance rowGammaFinite : Finite RowGamma :=
  Finite.of_injective (fun gamma : RowGamma => (gamma.xC0, gamma.yC4, gamma.zC0)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance entryFinite : Finite Exception.Entry :=
  Finite.of_injective (fun entry : Exception.Entry => fun index : Fin 2 => entry[index]) (by
    intro first second equal
    apply Vector.ext
    intro index bound
    exact congrFun equal ⟨index, bound⟩)

instance lanesFinite (width : Nat) : Finite (Lanes width) := by
  haveI : NeZero (2 ^ width) := ⟨pow_ne_zero _ two_ne_zero⟩
  infer_instance

instance blockFinite : Finite Block :=
  Finite.of_injective (fun block : Block => (⟨block.toNat, block.isLt⟩ : Fin (2 ^ 128))) (by
    intro first second equal
    exact BitVec.eq_of_toNat_eq (congrArg Fin.val equal))

/-- Conversion labels form a finite type without importing privacy infrastructure. -/
instance labelFinite : Finite Label :=
  Finite.of_injective (fun label : Label => (⟨label.toNat, label.isLt⟩ : Fin (2 ^ labelBits))) (by
    intro first second equal
    exact BitVec.eq_of_toNat_eq (congrArg Fin.val equal))

/-- The data of a source. -/
abbrev SourceData :=
  (BaseField × BaseField × BaseField) × (Fin digitCount → RowGamma) × (Fin digitCount → Bool) ×
    (Fin digitCount → Exception.Entry) × (Fin 2 → Fin joinCount → Label) ×
    (Fin 2 → (k : Fin pinCount) → Lanes (pinWidth k)) × (Fin xCount → Fin table.product) ×
    (Fin yCount → Fin table.product) × (Fin 2 → Fin coordinateBitCount → Block) × (Fin 2 → Block)

/-- A source's data. -/
def Source.data (source : Source) : SourceData :=
  (source.curve, source.rows, source.signs, source.exception, source.joins, source.pins, source.recX,
    source.recY, source.zeros, source.deltas)

theorem Source.data_injective : Function.Injective Source.data := by
  intro first second equal
  cases first
  cases second
  simp only [Source.data, Prod.mk.injEq] at equal
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := equal
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

instance sourceFinite : Finite Source := Finite.of_injective Source.data Source.data_injective

/-- `M > 0`: every modulus is at least 17. -/
theorem table_product_pos : 0 < table.product := by
  unfold CrtTable.product
  apply Finset.prod_pos
  intro i _
  have large : ∀ j : Fin bn254Moduli.size, 17 ≤ bn254Moduli[j] := by decide
  have := large i
  show 0 < bn254Moduli[i]
  omega

instance sourceNonempty : Nonempty Source :=
  ⟨{ curve := (0, 0, 0)
     rows := fun _ => ⟨0, 0, 0⟩
     signs := fun _ => false
     exception := fun _ => Vector.ofFn fun _ => 0
     joins := fun _ _ => 0
     pins := fun _ _ => 0
     recX := fun _ => ⟨0, table_product_pos⟩
     recY := fun _ => ⟨0, table_product_pos⟩
     zeros := fun _ _ => 0
     deltas := fun _ => 0 }⟩

end Kriterion.CRT.Entry
