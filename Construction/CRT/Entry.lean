/-
The configuration-E entry: coins, garbler, the evaluator's replay prefix, the full evaluator and
the scheme.

Garbler order (queries): the CRT layer of `x` (`coordGarbleM table 367 0`), of `y`
(`coordGarbleM table 275 1`), the key `K = (H t.val).1` (`keyM`), the 1,092 mask answers
(`maskAnswersM`), the digest labels and finals (`digestGarbleM`, on the actual zero labels).

**No chunk joins** (ROUND2 §5). The coordinate garblers run on the coins' zero labels `Z_j` (clipped);
the chunk-tree joins `J_{c,n}` they return are not published but absorbed into the returned Lamport
key: the actual zero label of bit `j = 8 c + n` is `Z'_j = Z_j ⊕ embed(J_{c,n})` for `n ≥ 1` and
`Z_j` at each chunk's first bit (`keyZeroOf`, `absorbedOf`), with the pairs `(Z'_j, Z'_j ⊕ Δ)`
(`keyOfZeros`, the coins' full `Δ`). The digest hashes the actual labels. The evaluator runs the chunk
trees with zero joins; its active material `0 ⊕ clip(Z'_j ⊕ bΔ) ⊕ cold = J ⊕ clip(Z_j ⊕ bΔ) ⊕ cold`
is the joined one. Query counts are unchanged. Then the pure assembly
(release-r1's "offsets first, slopes derived from offsets, joins last"): the element offset of
a curve encoding is `O_e mod p`, of a row encoding `(O_e mod p) - π_e`; slopes by
`CurveMembership.slopes` and `Biquadratic.slopes`; row constants by
`FieldMacToECMac.garbleRow`; curve constants by `CurveMembership.garble`; records by
`CoordGarbled.records` with the slopes' values.

Evaluator: an off-curve input is refused before any query (`some none`). On the curve, the replay
prefix (`replay`: the CRT layer of `x` and `y` on the restored labels, the curve check from the
five curve encodings, the key at `t'`, the masks), then the rows (pure), the digest
(`digestEvalM`), and release-r1's `Garbling.decodeResult`.
-/

import Construction.CRT.Public
import Construction.CRT.Mask
import Construction.CRT.Digest
import Construction.CRT.Bounds
import Construction.Scheme

namespace Kriterion.CRT.Entry

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-! ### Oracle, coins, key -/

/-- Configuration E is hash-only (D2): both permutation index types are empty. -/
abbrev Oracle := PublicOracle Empty Empty

/-- The public query interface. -/
abbrev Spec := publicOracleSpec Empty Empty

/-- The private coins: release-r1's `Scheme.Coins` (the CRT layer needs none of its own; its pads
come from the hash). `bridgeKey` is `t`. -/
abbrev Coins := Kriterion.ArgoMAC.Scheme.Coins

/-- The encoding key: the 508 Lamport label pairs. -/
abbrev Key := InputMacKey

/-- The tape witness. -/
def witness : Coins := Scheme.witness

/-- The bridge input `t`; the key's hash input is `t.val`, with no tag. -/
def bridgeInput (coins : Coins) : BaseField := coins.bridgeKey

/-- The output keys of a garbling (release-r1). -/
def outputKeysOf (scalar : NonZeroScalar) (coins : Coins) : FieldMacToECMac.OutputKeys :=
  FieldMacToECMac.outputKeys construction scalar.value coins.offsets

/-- The exceptional input of final site `s = 2 o + k`: kind `k = 0` is digit `o`'s doubling input
(`Q = K`), kind `k = 1` its sign row's zero (`Q = 2K`); `none` for a zero digit or `o ≥ 91`. -/
def exceptional (scalar : NonZeroScalar) (coins : Coins) (s : Nat) : Option AffineInput :=
  if inRange : s / 2 < digitCount then
    let key := (outputKeysOf scalar coins).get ⟨s / 2, inRange⟩
    match digitEndomorphismBase key.digit with
    | none => none
    | some phi => some (if s % 2 = 0 then Exception.exceptionalInput phi key.offset.coordinates
        else Exception.tripleInput phi key.offset.coordinates)
  else none

/-- **The cases of an exceptional input**: site `s` names digit `s / 2`, which is nonzero, and the input is its
doubling input (`s` even) or its sign row's zero (`s` odd). -/
theorem exceptional_cases (scalar : NonZeroScalar) (coins : Coins) (s : Nat) (u : AffineInput)
    (hexc : exceptional scalar coins s = some u) :
    ∃ (inRange : s / 2 < digitCount) (phi : BaseField),
      digitEndomorphismBase ((outputKeysOf scalar coins).get ⟨s / 2, inRange⟩).digit = some phi ∧
      ((s % 2 = 0 ∧ u = Exception.exceptionalInput phi
          ((outputKeysOf scalar coins).get ⟨s / 2, inRange⟩).offset.coordinates) ∨
        (s % 2 = 1 ∧ u = Exception.tripleInput phi
          ((outputKeysOf scalar coins).get ⟨s / 2, inRange⟩).offset.coordinates)) := by
  unfold exceptional at hexc
  by_cases inRange : s / 2 < digitCount
  swap
  · rw [dif_neg inRange] at hexc
    cases hexc
  rw [dif_pos inRange] at hexc
  refine ⟨inRange, ?_⟩
  generalize hkey : (outputKeysOf scalar coins).get ⟨s / 2, inRange⟩ = key at hexc ⊢
  dsimp only at hexc
  cases hphi : digitEndomorphismBase key.digit with
  | none => rw [hphi] at hexc; cases hexc
  | some phi =>
    rw [hphi] at hexc
    dsimp only at hexc
    refine ⟨phi, rfl, ?_⟩
    by_cases kind : s % 2 = 0
    · rw [if_pos kind] at hexc
      exact Or.inl ⟨kind, (Option.some.inj hexc).symm⟩
    · rw [if_neg kind] at hexc
      exact Or.inr ⟨by omega, (Option.some.inj hexc).symm⟩

/-- Coordinate `κ` (`0` is `x`) of the coins' zero labels. -/
def zeroOf (coins : Coins) (coord : Fin 2) : Fin coordinateBitCount → Block :=
  if coord = 0 then coins.inputZero .x else coins.inputZero .y

/-- Coordinate `κ`'s `Δ`. -/
def deltaOf (coins : Coins) (coord : Fin 2) : Block :=
  if coord = 0 then coins.inputDelta .x else coins.inputDelta .y

/-! ### The actual Lamport key: chunk joins absorbed into the zero labels -/

/-- The chunk join absorbed into bit `j` of coordinate `coord` (`0` at each chunk's first bit),
lifted to a raw block. -/
def absorbedOf (gx : CoordGarbled table xCount) (gy : CoordGarbled table yCount) (coord : Fin 2)
    (j : Nat) : Block :=
  embed (table.chunkShift (if coord = 0 then gx.pub.chunkJoin else gy.pub.chunkJoin) j)

/-- **The actual zero labels**: the coins' zero label XOR the absorbed chunk join. -/
def keyZeroOf (coins : Coins) (absorbed : Fin 2 → Nat → Block) (coord : Fin 2)
    (position : Fin coordinateBitCount) : Block :=
  zeroOf coins coord position ^^^ absorbed coord position.val

/-- The Lamport key of zero labels and offsets: the pairs `(Z_j, Z_j ⊕ Δ)`. -/
def keyOfZeros (zero : Fin 2 → Fin coordinateBitCount → Block) (delta : Fin 2 → Block) : Key :=
  { x := Vector.ofFn fun position =>
      { falseLabel := zero 0 position
        trueLabel := zero 0 position ^^^ delta 0 }
    y := Vector.ofFn fun position =>
      { falseLabel := zero 1 position
        trueLabel := zero 1 position ^^^ delta 1 } }

/-! ### Element offsets, slopes, rows -/

/-- The field value of a natural (CRT offsets, decoded integers). -/
def toField (value : Nat) : BaseField := (value : BaseField)

/-- The element offsets of `x` (rows: `O mod p - π`; curve encodings carry no mask). -/
def offsetsX (offset : Fin xCount → Nat) (masks : MaskValues digitCount) (e : Fin xCount) :
    BaseField :=
  toField (offset e) - maskOf masks 0 e.val

/-- The element offsets of `y`. -/
def offsetsY (offset : Fin yCount → Nat) (masks : MaskValues digitCount) (e : Fin yCount) :
    BaseField :=
  toField (offset e) - maskOf masks 1 e.val

/-- The point part (`0 .. 363`) of an `x` vector. -/
def pointPartX (values : Fin xCount → BaseField) (e : Fin pointElementCountX) : BaseField :=
  values ⟨e.val, by have := e.isLt; simp only [pointElementCountX, pointElementCountY, xCount, yCount] at *; omega⟩

/-- The curve part (`364 .. 366`) of an `x` vector. -/
def curvePartX (values : Fin xCount → BaseField) (e : Fin curveElementCountX) : BaseField :=
  values ⟨pointElementCountX + e.val, by
    have := e.isLt; simp only [curveElementCountX, pointElementCountX, xCount] at *; omega⟩

/-- The point part (`0 .. 272`) of a `y` vector. -/
def pointPartY (values : Fin yCount → BaseField) (e : Fin pointElementCountY) : BaseField :=
  values ⟨e.val, by have := e.isLt; simp only [pointElementCountY, yCount] at *; omega⟩

/-- The curve part (`273 .. 274`) of a `y` vector. -/
def curvePartY (values : Fin yCount → BaseField) (e : Fin curveElementCountY) : BaseField :=
  values ⟨pointElementCountY + e.val, by
    have := e.isLt; simp only [curveElementCountY, pointElementCountY, yCount] at *; omega⟩

/-- An `x` vector from its point and curve parts. -/
def joinX (point : Fin pointElementCountX → BaseField) (curve : Fin curveElementCountX → BaseField)
    (e : Fin xCount) : BaseField :=
  if inRange : e.val < pointElementCountX then point ⟨e.val, inRange⟩
  else curve ⟨e.val - pointElementCountX, by
    have := e.isLt; simp only [pointElementCountX, curveElementCountX, xCount] at *; omega⟩

/-- A `y` vector from its point and curve parts. -/
def joinY (point : Fin pointElementCountY → BaseField) (curve : Fin curveElementCountY → BaseField)
    (e : Fin yCount) : BaseField :=
  if inRange : e.val < pointElementCountY then point ⟨e.val, inRange⟩
  else curve ⟨e.val - pointElementCountY, by
    have := e.isLt; simp only [pointElementCountY, curveElementCountY, yCount] at *; omega⟩

/-- The per-digit element values of the rows (release-r1's `digitValues`). -/
def digitValuesOf (xValues : Fin xCount → BaseField) (yValues : Fin yCount → BaseField) :
    FieldMacToECMac.DigitValues :=
  fun digit => Pipeline.digitValues (pointPartX xValues) (pointPartY yValues) digit

/-- The curve check's element values (release-r1's `curveValues`). -/
def curveValuesOf (xValues : Fin xCount → BaseField) (yValues : Fin yCount → BaseField) :
    CurveMembership.Values :=
  Pipeline.curveValues (curvePartX xValues) (curvePartY yValues)

/-- The row slopes of every digit. -/
def pointSlopes (rows : FieldMacToECMac.Rows) (randomness : FieldMacToECMac.Randomness)
    (K : FieldMacToECMac.DigitValues) : Fin digitCount → Biquadratic.Values :=
  fun digit =>
    Biquadratic.slopes (rows.get digit) (randomness.get digit).x (randomness.get digit).y
      (randomness.get digit).z (K digit)

/-- The slopes of `x` (point slopes, then the curve slopes). -/
def slopesX (point : Fin digitCount → Biquadratic.Values) (curve : CurveMembership.Values) :
    Fin xCount → BaseField :=
  joinX (Pipeline.pointXAssemble point) (Pipeline.curveXAssemble curve)

/-- The slopes of `y`. -/
def slopesY (point : Fin digitCount → Biquadratic.Values) (curve : CurveMembership.Values) :
    Fin yCount → BaseField :=
  joinY (Pipeline.pointYAssemble point) (Pipeline.curveYAssemble curve)

/-- A record natural as a 78-byte natural (honest records are below `2 M < 256 ^ 78`). -/
def toRecord (value : Nat) : Record :=
  ⟨value % 256 ^ recordBytes, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

/-- A flat conversion vector from the garbler's material. -/
def convVector (pub : ConvPublic) : Vector Label convCount :=
  let blocks := (pub.flatten table).toArray
  Vector.ofFn fun k => blocks.getD k.val 0

/-- **The pure assembly** of the public value from the CRT phase, the masks and the digest. -/
def assemble (scalar : NonZeroScalar) (coins : Coins) (gx : CoordGarbled table xCount)
    (gy : CoordGarbled table yCount) (masks : MaskValues digitCount)
    (entries : Fin digitCount → Exception.Entry) : Public :=
  let outputKeys := outputKeysOf scalar coins
  let rows := FieldMacToECMac.rowsForOutputKeys outputKeys coins.pointRandomness
  let offX := offsetsX gx.offset masks
  let offY := offsetsY gy.offset masks
  let K := digitValuesOf offX offY
  let curveK := curveValuesOf offX offY
  let point := pointSlopes rows coins.pointRandomness K
  let curve := CurveMembership.slopes coins.curveR1 coins.curveR2 curveK
  let recordsX := gx.records fun e => (slopesX point curve e).val
  let recordsY := gy.records fun e => (slopesY point curve e).val
  { curve := CurveMembership.garble coins.bridgeKey coins.curveMask.value coins.curveR1
      coins.curveR2 curveK
    rows := Vector.ofFn fun digit =>
      FieldMacToECMac.garbleRow (rows.get digit) (K digit)
    exception := Vector.ofFn entries
    crtX := convVector gx.pub
    crtY := convVector gy.pub
    recX := Vector.ofFn fun e => toRecord (recordsX e)
    recY := Vector.ofFn fun e => toRecord (recordsY e) }

/-! ### The garbler -/

/-- **The garbler program** over the layer's hash. The returned key and the digest use the actual
zero labels `keyZeroOf coins (absorbedOf gx gy)` (the chunk joins absorbed). -/
def garbleCM (scalar : NonZeroScalar) (coins : Coins) : CM (Public × Key) :=
  let outputKeys := outputKeysOf scalar coins
  coordGarbleM table xCount 0 (clip (coins.inputDelta .x))
      (fun j => clip (atNat (coins.inputZero .x) 0 j)) >>= fun gx =>
    coordGarbleM table yCount 1 (clip (coins.inputDelta .y))
        (fun j => clip (atNat (coins.inputZero .y) 0 j)) >>= fun gy =>
      keyM coins.bridgeKey >>= fun K =>
        maskAnswersM K digitCount >>= fun masks =>
          digestGarbleM coordinateBitCount digitCount (keyZeroOf coins (absorbedOf gx gy)) (deltaOf coins)
              (fun o => (outputKeys.get o).digit) (fun o => (outputKeys.get o).offset.coordinates)
              (fun o => coins.exceptionPad.get o) >>= fun entries =>
            pure (assemble scalar coins gx gy masks entries,
              keyOfZeros (keyZeroOf coins (absorbedOf gx gy)) (deltaOf coins))

/-- The garbler over the contest's public oracle. -/
def garbleM (scalar : NonZeroScalar) (coins : Coins) : FreeQuery Spec (Public × Key) :=
  liftHash (garbleCM scalar coins)

/-- The garbler's budget on a table, term by term. -/
def garbleBudgetOf (T : CrtTable) : Nat :=
  coordGarbleBudget T xCount + (coordGarbleBudget T yCount + (1 + (maskBudget digitCount +
    digestGarbleBudget coordinateBitCount digitCount)))

/-- The garbler's budget. It is stated through `garbleBudgetOf` so that its equation lemmas never
make the kernel compare the closed sum with the constant, which evaluates the 85-row sums. -/
def garbleBudget : Nat := garbleBudgetOf table

/-! ### The evaluator -/

/-- What the replay prefix produces. -/
structure ReplayOut where
  /-- The delivered value `v_e` of each `x` encoding (after the hint, mod `p`). -/
  deliveredX : Fin xCount → BaseField
  /-- The delivered value of each `y` encoding. -/
  deliveredY : Fin yCount → BaseField
  /-- The masks `π_e` as read at `K'`. -/
  masks : RowEncoding → BaseField
  /-- `K' = (H t'.val).1`. -/
  key : Block

/-- The evaluator's label of `x` bit `j` (Lamport blocks `0 .. 253`). -/
def labelX (labels : GarbledCircuit.LamportSignature) (j : Nat) : Block := labels.toArray.getD j 0

/-- The evaluator's label of `y` bit `j` (Lamport blocks `254 .. 507`). -/
def labelY (labels : GarbledCircuit.LamportSignature) (j : Nat) : Block :=
  labels.toArray.getD (coordinateBitCount + j) 0

/-- The evaluator's labels by coordinate, as the digest reads them. -/
def labelsOf (labels : GarbledCircuit.LamportSignature) (coord : Fin 2)
    (position : Fin coordinateBitCount) : Block :=
  if coord = 0 then labelX labels position.val else labelY labels position.val

/-- The delivered values of both coordinates. -/
structure ConvOut where
  /-- The delivered value `v_e` of each `x` encoding (after the hint, mod `p`). -/
  deliveredX : Fin xCount → BaseField
  /-- The delivered value of each `y` encoding. -/
  deliveredY : Fin yCount → BaseField

/-- **The conversion part of the replay**: the CRT layer of `x` and `y` on the restored
labels, every query labelled (chunk trees and casts, conversions, body pads). -/
def replayConv (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    CM ConvOut :=
  coordEvalM table xCount 0 (convOf pub.crtX) (fun e => (pub.recX.get e).val) input.x.val
      (fun j => clip (labelX labels j)) >>= fun ex =>
    coordEvalM table yCount 1 (convOf pub.crtY) (fun e => (pub.recY.get e).val) input.y.val
        (fun j => clip (labelY labels j)) >>= fun ey =>
      pure { deliveredX := fun e => toField (ex.decoded e)
             deliveredY := fun e => toField (ey.decoded e) }

/-- The curve check's output `t'` from the delivered values. -/
def curveOutput (pub : Public) (input : AffineInput) (conv : ConvOut) : BaseField :=
  CurveMembership.evaluate pub.curve input (curveValuesOf conv.deliveredX conv.deliveredY)

/-- The masks by row encoding. -/
def maskFunction (masks : MaskValues digitCount) : RowEncoding → BaseField
  | .inl e => maskOf masks 0 e.val
  | .inr e => maskOf masks 1 e.val

/-- **The replay prefix** (blocks chunkTree .. masks): `replayConv`, then the key
query at `t'.val`, then the 1,092 mask answers. -/
def replay (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    CM ReplayOut :=
  replayConv pub input labels >>= fun conv =>
    keyM (curveOutput pub input conv) >>= fun key =>
      maskAnswersM key digitCount >>= fun masks =>
        pure { deliveredX := conv.deliveredX, deliveredY := conv.deliveredY, key
               masks := maskFunction masks }

/-- What route M's replay produces: the delivered values, the key, the non-collector masks. -/
structure RouteMOut where
  conv : ConvOut
  key : Block
  pairs : Fin (pairSites digitCount) → BaseField × BaseField
  single : BaseField

/-- **Route M's replay**: `replayConv`, the key query, and only the 546 non-collector
mask answers (the 546 collector answers are programmed by the simulator, not asked). -/
def replayRouteM (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    CM RouteMOut :=
  replayConv pub input labels >>= fun conv =>
    keyM (curveOutput pub input conv) >>= fun key =>
      nonCollectorMasksM key digitCount >>= fun rest =>
        pure { conv, key, pairs := rest.1, single := rest.2 }

/-- The mask of an `x` encoding in the replay's output (curve encodings carry none). -/
def maskX (out : ReplayOut) (e : Fin xCount) : BaseField :=
  if inRange : e.val < pointElementCountX then out.masks (.inl ⟨e.val, inRange⟩) else 0

/-- The mask of a `y` encoding in the replay's output. -/
def maskY (out : ReplayOut) (e : Fin yCount) : BaseField :=
  if inRange : e.val < pointElementCountY then out.masks (.inr ⟨e.val, inRange⟩) else 0

/-- The row values of the replay's output: the delivered values minus the masks. -/
def rowValues (out : ReplayOut) : FieldMacToECMac.DigitValues :=
  digitValuesOf (fun e => out.deliveredX e - maskX out e) (fun e => out.deliveredY e - maskY out e)

/-- **The evaluator program**: refuse off the curve, else replay, rows, digest, decode. -/
def evaluateCM [FieldCertificate] [GroupCertificate] (pub : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) : CM (Option (Option Point)) :=
  match decodePoint input with
  | none => pure (some none)
  | some _ =>
      replay pub input labels >>= fun out =>
        digestEvalM coordinateBitCount digitCount (labelsOf labels) input
            (fun o => pub.exception.get o) >>= fun digits =>
          pure (some (Garbling.decodeResult
            { point := input
              pointMacs := FieldMacToECMac.evaluateHomogeneous (pub.rows, pub.exception)
                (rowValues out) input
              exceptionDigits := Vector.ofFn fun o => (digits o).1
              tripleDigits := Vector.ofFn fun o => (digits o).2 }))

/-- The evaluator over the contest's public oracle. -/
def evaluateM [FieldCertificate] [GroupCertificate] (pub : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) : FreeQuery Spec (Option (Option Point)) :=
  liftHash (evaluateCM pub input labels)

/-- The evaluator's budget on a table, term by term. -/
def evaluateBudgetOf (T : CrtTable) : Nat :=
  coordEvalBudget T xCount + (coordEvalBudget T yCount + (1 + (maskBudget digitCount +
    digestEvalBudget coordinateBitCount digitCount)))

/-- The evaluator's budget (through `evaluateBudgetOf`, as `garbleBudget`). -/
def evaluateBudget : Nat := evaluateBudgetOf table

/-! ### Query bounds and the challenge's programs -/

open FreeQuery (Bounded)

/-- Every T9 row has nonempty extraction stages (all moduli are at least 17). -/
theorem stagesNonempty_bn254TableOf (moduli : Array Nat) (large : ∀ i : Fin moduli.size, 17 ≤ moduli[i]) :
    (bn254TableOf moduli).StagesNonempty := by
  intro i row kind
  have atLeast := large i
  simp only [bn254TableOf, CrtTable.ofModuli, t9Kind] at kind
  split at kind
  · cases kind
  · cases kind
    refine ⟨by simp [t9Row], ?_⟩
    simp only [t9Row, bitLength]
    have nonzero : 32 * (moduli[i] - 1) ≠ 0 := by omega
    have eight : 8 ≤ Nat.log2 (32 * (moduli[i] - 1)) :=
      (Nat.le_log2 nonzero).mpr (by omega)
    omega

/-- The fallback's width-7/8 rows also have nonempty extraction stages. -/
theorem stagesNonempty_fallbackTableOf (moduli : Array Nat) (large : ∀ i : Fin moduli.size, 17 ≤ moduli[i]) :
    (fallbackTableOf moduli).StagesNonempty := by
  intro i row kind
  have atLeast := large i
  simp only [fallbackTableOf, CrtTable.ofModuli, fallbackKind] at kind
  split at kind
  · cases kind
  · cases kind
    have lower := fallbackWidth0_lower moduli[i]
    have upper := fallbackWidth0_upper moduli[i]
    have nonzero : 32 * (moduli[i] - 1) ≠ 0 := by omega
    have nine : 9 ≤ Nat.log2 (32 * (moduli[i] - 1)) :=
      (Nat.le_log2 nonzero).mpr (by omega)
    -- CHECK: the fallbackRow let-bindings must reduce before omega handles the two Nat subtractions.
    simp only [fallbackRow, bitLength]
    constructor <;> omega

/-- Every width-8 row has nonempty extraction stages for moduli at least 17. -/
theorem stagesNonempty_width8TableOf (moduli : Array Nat)
    (large : ∀ i : Fin moduli.size, 17 ≤ moduli[i]) :
    (width8TableOf moduli).StagesNonempty := by
  intro i row kind
  have atLeast := large i
  simp only [width8TableOf, CrtTable.ofModuli, width8Kind] at kind
  split at kind
  · cases kind
  · cases kind
    have nonzero : 32 * (moduli[i] - 1) ≠ 0 := by omega
    have nine : 9 ≤ Nat.log2 (32 * (moduli[i] - 1)) :=
      (Nat.le_log2 nonzero).mpr (by omega)
    simp only [width8Row, bitLength]
    constructor <;> omega

theorem stagesNonempty_table : table.StagesNonempty :=
  stagesNonempty_width8TableOf bn254Moduli (by decide)

theorem bounded_garbleCM (scalar : NonZeroScalar) (coins : Coins) :
    (garbleCM scalar coins).Bounded garbleBudget := by
  unfold garbleCM
  rw [garbleBudget, garbleBudgetOf]
  exact (Bounded.bind (bounded_coordGarbleM _ _ _ _ _) fun _ =>
    Bounded.bind (bounded_coordGarbleM _ _ _ _ _) fun _ =>
      Bounded.bind (bounded_keyM _) fun _ =>
        Bounded.bind (bounded_maskAnswersM _ _) fun _ =>
          Bounded.bind (bounded_digestGarbleM _ _ _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq
    (by rw [Nat.add_zero])

theorem bounded_garbleM (scalar : NonZeroScalar) (coins : Coins) :
    (garbleM scalar coins).Bounded garbleBudget :=
  bounded_liftHash (bounded_garbleCM scalar coins)

/-- The garbling program at its exact budget. -/
def garbleProgram (scalar : NonZeroScalar) (coins : Coins) :
    QueryProgram Spec (Public × Key) garbleBudget :=
  FreeQuery.toProgram (garbleM scalar coins) garbleBudget (bounded_garbleM scalar coins)

/-- The replay's conversion budget on a table. -/
def replayConvBudgetOf (T : CrtTable) : Nat := coordEvalBudget T xCount + coordEvalBudget T yCount

/-- The replay's conversion budget. -/
def replayConvBudget : Nat := replayConvBudgetOf table

/-- The replay prefix's budget on a table. -/
def replayBudgetOf (T : CrtTable) : Nat :=
  coordEvalBudget T xCount + (coordEvalBudget T yCount + (1 + maskBudget digitCount))

/-- The replay prefix's budget. -/
def replayBudget : Nat := replayBudgetOf table

/-- Route M's replay budget on a table. -/
def replayRouteMBudgetOf (T : CrtTable) : Nat := replayConvBudgetOf T + (1 + nonCollectorBudget digitCount)

/-- Route M's replay budget. -/
def replayRouteMBudget : Nat := replayRouteMBudgetOf table

theorem bounded_replayConv (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    (replayConv pub input labels).Bounded replayConvBudget := by
  unfold replayConv
  rw [replayConvBudget, replayConvBudgetOf]
  exact (Bounded.bind (bounded_coordEvalM _ stagesNonempty_table _ _ _ _ _ _) fun _ =>
    Bounded.bind (bounded_coordEvalM _ stagesNonempty_table _ _ _ _ _ _) fun _ =>
      Bounded.pure' _ 0).of_eq (by rw [Nat.add_zero])

theorem bounded_replay (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    (replay pub input labels).Bounded replayBudget := by
  unfold replay
  rw [replayBudget, replayBudgetOf]
  exact (Bounded.bind (bounded_replayConv pub input labels) fun _ =>
    Bounded.bind (bounded_keyM _) fun _ =>
      Bounded.bind (bounded_maskAnswersM _ _) fun _ => Bounded.pure' _ 0).of_eq
    (by rw [Nat.add_zero, replayConvBudget, replayConvBudgetOf, Nat.add_assoc])

theorem bounded_replayRouteM (pub : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    (replayRouteM pub input labels).Bounded replayRouteMBudget := by
  unfold replayRouteM
  rw [replayRouteMBudget, replayRouteMBudgetOf, ← replayConvBudget]
  exact (Bounded.bind (bounded_replayConv pub input labels) fun _ =>
    Bounded.bind (bounded_keyM _) fun _ =>
      Bounded.bind (bounded_nonCollectorMasksM _ _) fun _ => Bounded.pure' _ 0).of_eq
    (by rw [Nat.add_zero])

theorem bounded_evaluateCM [FieldCertificate] [GroupCertificate] (pub : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    (evaluateCM pub input labels).Bounded evaluateBudget := by
  unfold evaluateCM
  split
  · exact Bounded.pure' _ _
  · exact (Bounded.bind (bounded_replay pub input labels) fun _ =>
      Bounded.bind (bounded_digestEvalM _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq
      (by rw [Nat.add_zero, replayBudget, replayBudgetOf, evaluateBudget, evaluateBudgetOf, Nat.add_assoc,
        Nat.add_assoc, Nat.add_assoc])

theorem bounded_evaluateM [FieldCertificate] [GroupCertificate] (pub : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) : (evaluateM pub input labels).Bounded evaluateBudget :=
  bounded_liftHash (bounded_evaluateCM pub input labels)

/-- The evaluation program at its exact budget. -/
def evaluateProgram [FieldCertificate] [GroupCertificate] (pub : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    QueryProgram Spec (Option (Option Point)) evaluateBudget :=
  FreeQuery.toProgram (evaluateM pub input labels) evaluateBudget (bounded_evaluateM pub input labels)

/-! ### The evaluator's query path without the curve refusal (for the privacy side's reach) -/

/-- The row layer's result on the replay's output and the digest's digits. -/
def resultOf (pub : Public) (input : AffineInput) (out : ReplayOut)
    (digits : Fin digitCount → Digit × Digit) : FieldMacToECMac.Result :=
  { point := input
    pointMacs := FieldMacToECMac.evaluateHomogeneous (pub.rows, pub.exception) (rowValues out) input
    exceptionDigits := Vector.ofFn fun o => (digits o).1
    tripleDigits := Vector.ofFn fun o => (digits o).2 }

/-- **The reach program**: `evaluateCM`'s on-curve branch without the refusal and the decode (the
replay, the rows, the digest labels and finals). -/
def reachCM (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    CM FieldMacToECMac.Result :=
  replay pub input labels >>= fun out =>
    digestEvalM coordinateBitCount digitCount (labelsOf labels) input (fun o => pub.exception.get o)
      >>= fun digits => pure (resultOf pub input out digits)

/-- The reach program over the contest's public oracle. -/
def reachM (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    FreeQuery Spec FieldMacToECMac.Result :=
  liftHash (reachCM pub input labels)

theorem bounded_reachCM (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    (reachCM pub input labels).Bounded evaluateBudget :=
  (Bounded.bind (bounded_replay pub input labels) fun _ =>
    Bounded.bind (bounded_digestEvalM _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq
    (by rw [Nat.add_zero, replayBudget, replayBudgetOf, evaluateBudget, evaluateBudgetOf, Nat.add_assoc,
        Nat.add_assoc, Nat.add_assoc])

theorem bounded_reachM (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    (reachM pub input labels).Bounded evaluateBudget :=
  bounded_liftHash (bounded_reachCM pub input labels)

/-- The reach program at the evaluator's budget. -/
def reachProgram (pub : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    QueryProgram Spec FieldMacToECMac.Result evaluateBudget :=
  FreeQuery.toProgram (reachM pub input labels) evaluateBudget (bounded_reachM pub input labels)

/-- On the curve the evaluator is the reach program followed by the decode, for every hash. -/
theorem eval_evaluateCM_of_decode [FieldCertificate] [GroupCertificate] (H : HashN) (pub : Public)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) (point : Point)
    (decoded : decodePoint input = some point) :
    (evaluateCM pub input labels).eval H =
      some (Garbling.decodeResult ((reachCM pub input labels).eval H)) := by
  unfold evaluateCM reachCM
  rw [decoded]
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, resultOf]

/-! ### The scheme -/

/-- **The configuration-E scheme** at the challenge's interface. -/
def scheme [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) (Coins × Oracle) Public Key
      GarbledCircuit.LamportSignature Oracle where
  function scalar input := checkedScalarMultiplication scalar.value input
  garble _ scalar tape := (garbleCM scalar tape.1).eval (schemeHash tape.2)
  encode key input := Lamport.selectedLabels (key.encode (BitInput.ofAffine input))
  evaluate oracle pub input labels := (evaluateCM pub input labels).eval (schemeHash oracle)

end Kriterion.CRT.Entry
