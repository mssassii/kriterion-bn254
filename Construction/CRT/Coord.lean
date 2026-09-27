/-
One coordinate of the CRT delivery layer: the conversion of every modulus, the body, the CRT
offsets with the wrap hint, the records, the evaluator's reconstruction, and the flat layout of
the published conversion material, with the wrap hint and the per-encoding records.

Garbler order (per coordinate): chunks `c = 0, 1, ...` (tree, then casts); then for each modulus
index `i` ascending: for an odd row, extraction stage 0 (tree, casts), stage 1 (tree, casts),
growth, folds; then the body pads of all its slots. The garbler's phase is slope-free: it returns
the published conversion material, the residues `R_{e,i}`, the pad sums, the CRT offsets
`O_e = crt(R_{e,·}) < M` and the hints `h_e = [M - B < O_e]`; the records need the slopes and are a
pure function (`CoordGarbled.records`).

Evaluator order: chunk trees and casts per chunk; then for each
modulus index `i` ascending: extraction stage 0, stage 1 (round order), stage 2 (free), growth,
reindex (free), folds, body pads (cold slots ascending), residues. Reconstruction:
`w_e = crt(L_{e,·})`, hint `h_e = [M ≤ record_e]`, decoded integer `wrapDecode M B h_e w_e`, which
equals `a_e * v + O_e` (L16, L17, L18).
-/

import Construction.CRT.Body

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC

/-! ### Tags -/

/-- The tag of an extraction-tree material. -/
def extTreeTag (coord i stage level slot : Nat) : Nat :=
  tagCode Family.extTree coord i stage level slot 0

/-- The tag of part `part` of the cast of leaf `leaf` of an extraction stage. -/
def extCastTag (coord i stage leaf part : Nat) : Nat :=
  tagCode Family.extCast coord i stage 0 leaf part

/-- The tag of a growth material (`level` is the bit position). -/
def growTag (coord i level slot : Nat) : Nat := tagCode Family.grow coord i 0 level slot 0

/-- The tag of a fold material (`position` is the bit position, `residue` the slot). -/
def foldTag (coord i position residue : Nat) : Nat :=
  tagCode Family.fold coord i 0 position residue 0

/-! ### Table helpers -/

/-- The kind of modulus index `i` (`none` off range). -/
def CrtTable.kindAt (T : CrtTable) (i : Nat) : Option Kind :=
  if inRange : i < T.count then some (T.kind ⟨i, inRange⟩) else none

/-- CRT reconstruction from a product and stored idempotents; `T.crt r` is
`crtWith T.product T.idempotent r`. -/
def crtWith {count : Nat} (product : Nat) (idempotent : Fin count → Nat) (residues : Fin count → Nat) :
    Nat :=
  (∑ i : Fin count, residues i * idempotent i) % product

theorem crt_eq_crtWith (T : CrtTable) (residues : Fin T.count → Nat) :
    T.crt residues = crtWith T.product T.idempotent residues := rfl

/-! ### The published conversion material -/

/-- The published conversion material of one coordinate, as total functions of natural indices
(`0` off range). -/
structure ConvPublic where
  /-- Chunk `c`, tree level `n` (`1 ≤ n < w_c`). -/
  chunkJoin : Nat → Nat → Block
  /-- Chunk `c`, pin block `k` (`k < L`). -/
  chunkPin : Nat → Nat → Block
  /-- Modulus `i`, stage `q` (0 or 1), level `n` (`1 ≤ n < w_q`). -/
  stageJoin : Nat → Nat → Nat → Block
  /-- Modulus `i`, stage `q`, pin block `k`. -/
  stagePin : Nat → Nat → Nat → Block
  /-- Modulus `i`, growth join at bit position `j` (`width0 ≤ j < keep`). -/
  growJoin : Nat → Nat → Block
  /-- Modulus `i`, fold join at bit position `j` (`keep ≤ j < ell`). -/
  foldJoin : Nat → Nat → Block

/-! ### One odd modulus: the conversion -/

/-- What the garbler keeps of one odd modulus's conversion. -/
structure ConversionGarbled (m : Nat) where
  stageJoins : Nat → Nat → Block
  stagePins : Nat → Nat → Block
  growJoins : Nat → Block
  foldJoins : Nat → Block
  /-- The final one-hot over `Z_m`, hot at `v mod m`. -/
  final : Fin m → Block

/-- The bit labels (or masks) of the word, by bit position: stage 0 gives `0 .. width0 - 1`,
stage 1 `width0 .. width0 + width1 - 1`, stage 2 the last. -/
def wordBit (row : OddRow) (stage0 stage1 : Nat → Block) (last : Block) (position : Nat) : Block :=
  if position < row.width0 then stage0 position
  else if position < row.width0 + row.width1 then stage1 (position - row.width0)
  else last

/-- The garbler's conversion of an odd modulus `m` (index `i`, row `row`) from its word mask. -/
def conversionGarbleM (coord i : Nat) (row : OddRow) (m : Nat) (delta : Block)
    (word : Lanes row.ell) : CM (ConversionGarbled m) :=
  extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) delta word >>= fun g0 =>
    extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) delta g0.next
      >>= fun g1 =>
      let bitMask := wordBit row g0.bits g1.bits (laneBit g1.next 0)
      growGarbleM (growTag coord i) row.width0 (stored fun leaf => g0.leaves leaf.val)
          (row.keep - row.width0) >>= fun grown =>
        foldsGarbleM m (foldTag coord i) bitMask (row.ell - row.keep) row.keep
            (reindex _ grown.1 m) >>= fun folded =>
          let pin0 := stored (pinBlocks g0.pin)
          let pin1 := stored (pinBlocks g1.pin)
          pure { stageJoins := fun stage n => if stage = 0 then g0.joins n else g1.joins n
                 stagePins := fun stage k => if stage = 0 then atNat pin0 0 k else atNat pin1 0 k
                 growJoins := fun position => grown.2 position ^^^ bitMask position
                 foldJoins := folded.2
                 final := folded.1 }

/-- The evaluator's conversion of an odd modulus: from the word label and the word value `σ`, the
final one-hot and its hot index. -/
def conversionEvalM (coord i : Nat) (row : OddRow) (m : Nat) (value : Nat) (word : Lanes row.ell)
    (pub : ConvPublic) : CM ((Fin m → Block) × Nat) :=
  let value1 := value / 2 ^ row.width0
  extStageEvalM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) word
      (value % 2 ^ row.width0) (pub.stageJoin i 0)
      (pinOfBlocks row.ell fun k => pub.stagePin i 0 k.val) >>= fun e0 =>
    extStageEvalM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) e0.next
        (value1 % 2 ^ row.width1) (pub.stageJoin i 1)
        (pinOfBlocks (row.ell - row.width0) fun k => pub.stagePin i 1 k.val) >>= fun e1 =>
      let bitLabel := wordBit row e0.bits e1.bits (laneBit e1.next 0)
      growEvalM (growTag coord i) value bitLabel (pub.growJoin i) row.width0
          (stored fun leaf => e0.leaves leaf.val) (row.keep - row.width0) >>= fun grown =>
        foldsEvalM m (foldTag coord i) value bitLabel (pub.foldJoin i) (row.ell - row.keep) row.keep
          (value % 2 ^ row.keep % m) (reindex _ grown m)

/-! ### One modulus: conversion and body -/

/-- What the garbler keeps of one modulus. -/
structure ModGarbled (S : Nat) where
  stageJoins : Nat → Nat → Block
  stagePins : Nat → Nat → Block
  growJoins : Nat → Block
  foldJoins : Nat → Block
  body : BodyGarbled S

/-- An empty chunk record (off-range default). -/
def ChunkGarbled.empty (L : Nat) : ChunkGarbled L := ⟨fun _ => 0, fun _ => 0, fun _ => 0, 0⟩

/-- An empty chunk record (off-range default). -/
def ChunkEval.empty (L : Nat) : ChunkEval L := ⟨fun _ => 0, fun _ => 0⟩

/-- The garbler of modulus index `i`, given the chunks. -/
def modGarbleM (T : CrtTable) (S coord : Nat) (delta : Block)
    (chunks : Nat → ChunkGarbled T.castWidth) (i : Fin T.count) : CM (ModGarbled S) :=
  let m := T.modulus i
  let q := T.padAnswers S i
  match T.kind i with
  | .chunkZero =>
      bodyGarbleM m S q coord i.val (stored fun residue => (chunks 0).leaves residue.val)
        >>= fun body =>
          pure { stageJoins := fun _ _ => 0, stagePins := fun _ _ => 0, growJoins := fun _ => 0
                 foldJoins := fun _ => 0, body }
  | .odd row =>
      materializeM (truthWord T m row.ell fun c leaf => (chunks c).casts leaf) >>= fun word =>
      conversionGarbleM coord i.val row m delta word >>= fun conversion =>
          bodyGarbleM m S q coord i.val conversion.final >>= fun body =>
            pure { stageJoins := conversion.stageJoins, stagePins := conversion.stagePins
                   growJoins := conversion.growJoins, foldJoins := conversion.foldJoins, body }

/-- The evaluator of modulus index `i`: its residues `L_{e,i}`. -/
def modEvalM (T : CrtTable) (S coord : Nat) (pub : ConvPublic) (joins : Fin T.count → Fin S → Nat)
    (v : Nat) (chunks : Nat → ChunkEval T.castWidth) (i : Fin T.count) : CM (Fin S → Nat) :=
  let m := T.modulus i
  let q := T.padAnswers S i
  match T.kind i with
  | .chunkZero =>
      bodyEvalM m S q coord i.val (stored fun residue => (chunks 0).leaves residue.val) (v % m)
        (joins i)
  | .odd row =>
      materializeM (truthWord T m row.ell fun c leaf => (chunks c).casts leaf) >>= fun word =>
      conversionEvalM coord i.val row m (T.wordValue m v) word pub >>= fun conversion =>
        bodyEvalM m S q coord i.val conversion.1 conversion.2 (joins i)

/-! ### One coordinate -/

/-- What the garbler keeps of one coordinate (slope-free). -/
structure CoordGarbled (T : CrtTable) (S : Nat) where
  /-- The published conversion material. -/
  pub : ConvPublic
  /-- `R_{e,i}`. -/
  residue : Fin T.count → Fin S → Nat
  /-- `Σ_ρ V_ρ[e] mod m_i`. -/
  padSum : Fin T.count → Fin S → Nat
  /-- The CRT offset `O_e = crt(R_{e,·}) < M`. -/
  offset : Fin S → Nat
  /-- The wrap hint `h_e = [M - B < O_e]`. -/
  hint : Fin S → Bool

/-- **The garbler of one coordinate** (phase 1, slope-free): `zeroLabel j` is the zero label of
coordinate bit `j`, `delta` the coordinate's `Δ`. -/
def coordGarbleM (T : CrtTable) (S coord : Nat) (delta : Block) (zeroLabel : Nat → Block) :
    CM (CoordGarbled T S) :=
  tableM T.chunkCount (fun c => chunkGarbleM T coord delta zeroLabel c.val) >>= fun chunkTable =>
    let chunks : Nat → ChunkGarbled T.castWidth := atNat chunkTable (ChunkGarbled.empty _)
    let chunkPins : Fin T.chunkCount → Fin T.castWidth → Block :=
      stored fun c => stored (pinBlocks (chunkTable c).pin)
    tableM T.count (modGarbleM T S coord delta chunks) >>= fun mods =>
      let modAt : Nat → Option (ModGarbled S) := fun i =>
        if inRange : i < T.count then some (mods ⟨i, inRange⟩) else none
      let pub : ConvPublic :=
        { chunkJoin := fun c n => (chunks c).joins n
          chunkPin := fun c k =>
            if inRange : c < T.chunkCount then atNat (chunkPins ⟨c, inRange⟩) 0 k else 0
          stageJoin := fun i stage n => match modAt i with
            | some g => g.stageJoins stage n
            | none => 0
          stagePin := fun i stage k => match modAt i with
            | some g => g.stagePins stage k
            | none => 0
          growJoin := fun i j => match modAt i with
            | some g => g.growJoins j
            | none => 0
          foldJoin := fun i j => match modAt i with
            | some g => g.foldJoins j
            | none => 0 }
      let product := T.product
      let idempotent := stored T.idempotent
      let offset : Fin S → Nat := stored fun e => crtWith product idempotent fun i => (mods i).body.residue e
      pure { pub
             residue := fun i => (mods i).body.residue
             padSum := fun i => (mods i).body.padSum
             offset
             hint := stored fun e => wrapHint product T.wrapBound (offset e) }

/-- The residue join `J_{e,i} = (Σ_ρ V_ρ[e] + a_e) mod m_i`. -/
def CoordGarbled.join {T : CrtTable} {S : Nat} (garbled : CoordGarbled T S) (slopes : Fin S → Nat)
    (i : Fin T.count) (e : Fin S) : Nat :=
  (garbled.padSum i e + slopes e) % T.modulus i

/-- The records (phase 2, after the slopes): `h_e * M + Σ_i J_{e,i} * Π_{i' < i} m_{i'}`, below
`2 M`. -/
def CoordGarbled.records {T : CrtTable} {S : Nat} (garbled : CoordGarbled T S)
    (slopes : Fin S → Nat) : Fin S → Nat :=
  let product := T.product
  let radix := stored T.radix
  stored fun e =>
    (if garbled.hint e then product else 0) + ∑ i : Fin T.count, garbled.join slopes i e * radix i

/-- The residue join of modulus `i` read back from a record. -/
def recordJoin (T : CrtTable) (product : Nat) (radix : Fin T.count → Nat) (record : Nat)
    (i : Fin T.count) : Nat :=
  record % product / radix i % T.modulus i

/-- What the evaluator obtains for one coordinate. -/
structure CoordEval (T : CrtTable) (S : Nat) where
  /-- `L_{e,i}`. -/
  residue : Fin T.count → Fin S → Nat
  /-- `w_e = crt(L_{e,·})`. -/
  crtValue : Fin S → Nat
  /-- The decoded integer `wrapDecode M B h_e w_e` (`= a_e * v + O_e`). -/
  decoded : Fin S → Nat

/-- **The evaluator of one coordinate**: `pub` and `records` are the published material, `v` the
coordinate value and `labels j` the evaluator's label of coordinate bit `j`. -/
def coordEvalM (T : CrtTable) (S coord : Nat) (pub : ConvPublic) (records : Fin S → Nat) (v : Nat)
    (labels : Nat → Block) : CM (CoordEval T S) :=
  let product := T.product
  let radix := stored T.radix
  let joins : Fin T.count → Fin S → Nat :=
    stored fun i => stored fun e => recordJoin T product radix (records e) i
  tableM T.chunkCount (fun c =>
    chunkEvalM T coord labels v (pub.chunkJoin c.val)
      (pinOfBlocks T.castWidth fun k => pub.chunkPin c.val k.val) c.val) >>= fun chunkTable =>
    let chunks : Nat → ChunkEval T.castWidth := atNat chunkTable (ChunkEval.empty _)
    tableM T.count (modEvalM T S coord pub joins v chunks) >>= fun residue =>
      let idempotent := stored T.idempotent
      let crtValue : Fin S → Nat := stored fun e => crtWith product idempotent fun i => residue i e
      pure { residue
             crtValue
             decoded := stored fun e =>
               wrapDecode product T.wrapBound (decide (product ≤ records e)) (crtValue e) }

/-! ### The flat layout -/

/-- Published blocks of one modulus. -/
def modBlocks : Kind → Nat
  | .chunkZero => 0
  | .odd row => (row.width0 - 1) + row.ell + (row.width1 - 1) + (row.ell - row.width0)
      + (row.keep - row.width0) + (row.ell - row.keep)

/-- Published blocks of chunk `c`: its joins and its pin. -/
def CrtTable.chunkBlocks (T : CrtTable) (c : Nat) : Nat := (T.chunkWidth c - 1) + T.castWidth

/-- Published conversion blocks of one coordinate (3,412 for the real table). -/
def CrtTable.convBlocks (T : CrtTable) : Nat :=
  (∑ c : Fin T.chunkCount, T.chunkBlocks c.val) + ∑ i : Fin T.count, modBlocks (T.kind i)

/-- The flat layout: for each chunk its joins then its pin; then for each odd modulus stage 0's
joins and pin, stage 1's joins and pin, the growth joins and the fold joins. -/
def ConvPublic.flatten (T : CrtTable) (pub : ConvPublic) : List Block :=
  ((List.range T.chunkCount).flatMap fun c =>
    (List.range (T.chunkWidth c - 1)).map (fun n => pub.chunkJoin c (n + 1)) ++
      (List.range T.castWidth).map (pub.chunkPin c)) ++
  ((List.finRange T.count).flatMap fun i => match T.kind i with
    | .chunkZero => []
    | .odd row =>
      (List.range (row.width0 - 1)).map (fun n => pub.stageJoin i 0 (n + 1)) ++
      (List.range row.ell).map (pub.stagePin i 0) ++
      (List.range (row.width1 - 1)).map (fun n => pub.stageJoin i 1 (n + 1)) ++
      (List.range (row.ell - row.width0)).map (pub.stagePin i 1) ++
      (List.range (row.keep - row.width0)).map (fun n => pub.growJoin i (row.width0 + n)) ++
      (List.range (row.ell - row.keep)).map (fun n => pub.foldJoin i (row.keep + n)))

/-- The first flat index of chunk `c`. -/
def CrtTable.chunkBase (T : CrtTable) (c : Nat) : Nat :=
  ∑ c' : Fin c, T.chunkBlocks c'.val

/-- The first flat index of modulus `i`. -/
def CrtTable.modBase (T : CrtTable) (i : Nat) : Nat :=
  T.chunkBase T.chunkCount + ∑ i' : Fin i, (match T.kindAt i'.val with
    | some kind => modBlocks kind
    | none => 0)

/-- Read the published conversion material back from the flat blocks. -/
def ConvPublic.unflatten (T : CrtTable) (blocks : Array Block) : ConvPublic :=
  let at_ (index : Nat) : Block := blocks.getD index 0
  let row (i : Nat) : OddRow := match T.kindAt i with
    | some (.odd row) => row
    | _ => ⟨0, 0, 0, 0⟩
  { chunkJoin := fun c n => at_ (T.chunkBase c + (n - 1))
    chunkPin := fun c k => at_ (T.chunkBase c + (T.chunkWidth c - 1) + k)
    stageJoin := fun i stage n =>
      if stage = 0 then at_ (T.modBase i + (n - 1))
      else at_ (T.modBase i + ((row i).width0 - 1) + (row i).ell + (n - 1))
    stagePin := fun i stage k =>
      if stage = 0 then at_ (T.modBase i + ((row i).width0 - 1) + k)
      else at_ (T.modBase i + ((row i).width0 - 1) + (row i).ell + ((row i).width1 - 1) + k)
    growJoin := fun i j =>
      at_ (T.modBase i + ((row i).width0 - 1) + (row i).ell + ((row i).width1 - 1)
        + ((row i).ell - (row i).width0) + (j - (row i).width0))
    foldJoin := fun i j =>
      at_ (T.modBase i + ((row i).width0 - 1) + (row i).ell + ((row i).width1 - 1)
        + ((row i).ell - (row i).width0) + ((row i).keep - (row i).width0) + (j - (row i).keep)) }

/-! ### Budgets -/

/-- Garbler queries of one modulus's conversion. -/
def conversionGarbleBudget (m : Nat) : Kind → Nat
  | .chunkZero => 0
  | .odd row => extGarbleBudget row.ell row.width0 + extGarbleBudget (row.ell - row.width0) row.width1
      + growGarbleBudget row.width0 (row.keep - row.width0) + (row.ell - row.keep) * m

/-- Evaluator queries of one modulus's conversion. -/
def conversionEvalBudget (m : Nat) : Kind → Nat
  | .chunkZero => 0
  | .odd row => extEvalBudget row.ell row.width0 + extEvalBudget (row.ell - row.width0) row.width1
      + growEvalBudget row.width0 (row.keep - row.width0) + (row.ell - row.keep) * (m - 1)

/-- Garbler queries of one coordinate with `S` encodings. -/
def coordGarbleBudget (T : CrtTable) (S : Nat) : Nat :=
  (∑ c : Fin T.chunkCount, chunkGarbleBudget T c.val) +
    ∑ i : Fin T.count, (conversionGarbleBudget (T.modulus i) (T.kind i) + T.modulus i * T.padAnswers S i)

/-- Evaluator queries of one coordinate with `S` encodings. -/
def coordEvalBudget (T : CrtTable) (S : Nat) : Nat :=
  (∑ c : Fin T.chunkCount, chunkEvalBudget T c.val) +
    ∑ i : Fin T.count,
      (conversionEvalBudget (T.modulus i) (T.kind i) + (T.modulus i - 1) * T.padAnswers S i)

end Kriterion.CRT
