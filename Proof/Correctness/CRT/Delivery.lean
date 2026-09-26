/-
CRT slice, delivery part 4: L18 for one coordinate, on the programs
`coordGarbleM`/`coordEvalM` (`Construction/CRT/Coord.lean`) at `.eval H`, for every `H : HashN`:
the evaluator's decoded integer of every encoding is `slope_e · v + O_e`, with `O_e` the garbler's
CRT offset (the delivery fact), through the chunk step (L2, L3), the words (L4, L5), the conversions
(L14) or chunk 0's leaves (the power-of-two row), the body (L15), the record codec (L19, `records_roundtrip`), CRT (L16) and the wrap hint (L17).
-/

import Proof.Correctness.CRT.BodyStep
import Proof.Correctness.CRT.Record

namespace Kriterion.CRT.SliceC

open scoped BigOperators Function
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

/-- The table conditions under which one coordinate delivers correctly (C7 discharges them for
`bn254Table` row by row). -/
structure CorrectTable (T : CrtTable) : Prop where
  chunkBits_pos : 0 < T.chunkBits
  inputBits_pos : 0 < T.inputBits
  castWidth_pos : 0 < T.castWidth
  modulus_pos : ∀ i, 0 < T.modulus i
  coprime : Pairwise (Nat.Coprime on T.modulus)
  wrap : 2 * T.wrapBound ≤ T.product + 1
  chunkZero : ∀ i, T.kind i = .chunkZero → T.modulus i = 2 ^ T.chunkWidth 0
  odd : ∀ i row, T.kind i = .odd row →
    1 ≤ row.width0 ∧ 1 ≤ row.width1 ∧ row.width0 + row.width1 + 1 = row.ell ∧
      row.width0 ≤ row.keep ∧ row.keep ≤ row.ell ∧ row.ell ≤ T.castWidth ∧
      T.chunkCount * (T.modulus i - 1) < 2 ^ row.ell

/-! ### The garbler's coordinate, field by field -/

theorem coordGarbleM_fields (H : HashN) (T : CrtTable) (S coord : Nat) (Δ : Block)
    (Z : Nat → Block) :
    let chunkTableG : Fin T.chunkCount → ChunkGarbled T.castWidth :=
      fun c => (chunkGarbleM T coord Δ Z c.val).eval H
    let chunksG := atNat chunkTableG (ChunkGarbled.empty _)
    let modsG : Fin T.count → ModGarbled S := fun i => (modGarbleM T S coord Δ chunksG i).eval H
    let g := (coordGarbleM T S coord Δ Z).eval H
    (∀ c, g.pub.chunkJoin c = (chunksG c).joins) ∧
      (∀ c (hc : c < T.chunkCount),
        (fun k : Fin T.castWidth => g.pub.chunkPin c k.val) = pinBlocks (chunkTableG ⟨c, hc⟩).pin) ∧
      (∀ i : Fin T.count, g.pub.stageJoin i.val = (modsG i).stageJoins ∧
        g.pub.stagePin i.val = (modsG i).stagePins ∧ g.pub.growJoin i.val = (modsG i).growJoins ∧
        g.pub.foldJoin i.val = (modsG i).foldJoins) ∧
      (∀ i e, g.padSum i e = (modsG i).body.padSum e) ∧
      (∀ e, g.offset e = crtWith T.product T.idempotent (fun i => (modsG i).body.residue e)) ∧
      (∀ e, g.hint e = wrapHint T.product T.wrapBound (g.offset e)) := by
  intro chunkTableG chunksG modsG g
  simp only [g, coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq]
  refine ⟨fun c => by first | rfl | trivial, fun c hc => ?_, fun i => ?_, fun i e => by first | rfl | trivial,
    fun e => by first | rfl | trivial, fun e => by first | rfl | trivial⟩
  · funext k
    simp only [dif_pos hc]
    rw [atNat_of_lt _ _ k.isLt]
  · simp only [dif_pos i.isLt]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem chunkCount_pos (T : CrtTable) (hk : 0 < T.chunkBits) (hI : 0 < T.inputBits) :
    0 < T.chunkCount := by
  unfold CrtTable.chunkCount
  exact Nat.div_pos (by omega) hk

theorem chunkValue_zero (T : CrtTable) (v : Nat) : T.chunkValue v 0 = v % 2 ^ T.chunkWidth 0 := by
  unfold CrtTable.chunkValue CrtTable.chunkOffset
  rw [Nat.mul_zero, Nat.shiftRight_zero]

/-- One modulus: the evaluator's residue of every encoding is the garbler's plus `slope·v` modulo
`m_i`, given the chunk step's invariants, the garbler's published material and residue joins. -/
theorem mod_residue (H : HashN) (T : CrtTable) (S coord : Nat) (Δ : Block) (slopes : Fin S → Nat)
    (v : Nat) (hT : CorrectTable T) (hv : v < 2 ^ T.inputBits) (pub : ConvPublic)
    (joinsE : Fin T.count → Fin S → Nat) (chunksG : Nat → ChunkGarbled T.castWidth)
    (chunksE : Nat → ChunkEval T.castWidth)
    (hL : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunksG c).leaves α ^^^ (if α = T.chunkValue v c then Δ else 0))
    (hC : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunksG c).casts α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ else 0))
    (i : Fin T.count)
    (hpJ : pub.stageJoin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).stageJoins)
    (hpP : pub.stagePin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).stagePins)
    (hpG : pub.growJoin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).growJoins)
    (hpF : pub.foldJoin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).foldJoins)
    (hJ : ∀ e, joinsE i e = (((modGarbleM T S coord Δ chunksG i).eval H).body.padSum e + slopes e) %
      T.modulus i)
    (e : Fin S) :
    (modEvalM T S coord pub joinsE v chunksE i).eval H e ≡
      ((modGarbleM T S coord Δ chunksG i).eval H).body.residue e + slopes e * v [MOD T.modulus i] := by
  have hm := hT.modulus_pos i
  cases hk : T.kind i with
  | chunkZero =>
    have hmod : T.modulus i = 2 ^ T.chunkWidth 0 := hT.chunkZero i hk
    have hc0 := chunkCount_pos T hT.chunkBits_pos hT.inputBits_pos
    simp only [modEvalM, modGarbleM, hk, FreeQuery.eval_bind, FreeQuery.eval_pure] at hJ ⊢
    have hbody := body_correct H (T.modulus i) S (T.padAnswers S i) coord i.val hm
      (stored fun ρ : Fin (T.modulus i) => (chunksG 0).leaves ρ.val)
      (stored fun ρ : Fin (T.modulus i) => (chunksE 0).leaves ρ.val) Δ (v % T.modulus i)
      (Nat.mod_lt _ hm)
      (by
        intro ρ
        simp only [stored_eq]
        have hρ : ρ.val < 2 ^ T.chunkWidth 0 := hmod ▸ ρ.isLt
        rw [hL 0 hc0 ρ.val hρ, chunkValue_zero, ← hmod])
      slopes (joinsE i) hJ e
    exact hbody.trans (Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ (Nat.mod_modEq v _)))
  | odd row =>
    obtain ⟨h0, h1, hell, hk0, hk1, hcw, hcount⟩ := hT.odd i row hk
    have hσlt : T.wordValue (T.modulus i) v < 2 ^ row.ell :=
      wordValue_lt T (T.modulus i) v row.ell hm hcount
    have hσ : T.wordValue (T.modulus i) v ≡ v [MOD T.modulus i] :=
      wordValue_modEq T hT.chunkBits_pos (T.modulus i) v hv
    have hW := truthWord_label T (T.modulus i) row.ell hcw (fun c leaf => (chunksG c).casts leaf)
      (fun c leaf => (chunksE c).casts leaf) Δ v (fun c hc α hα => hC c hc α hα)
    simp only [modEvalM, modGarbleM, hk, FreeQuery.eval_bind, FreeQuery.eval_pure,
      eval_materializeM] at hJ hpJ hpP hpG hpF ⊢
    rw [hW]
    obtain ⟨hconv2, hconv1⟩ := conversion_final H coord i.val row (T.modulus i) Δ
      (truthWord T (T.modulus i) row.ell fun c leaf => (chunksG c).casts leaf)
      (T.wordValue (T.modulus i) v) pub h0 h1 hell hk0 hk1 hm hσlt hpJ hpP hpG hpF
    rw [hconv2]
    have hbody := body_correct H (T.modulus i) S (T.padAnswers S i) coord i.val hm _ _ Δ
      (T.wordValue (T.modulus i) v % T.modulus i) (Nat.mod_lt _ hm) hconv1 slopes (joinsE i) hJ e
    refine hbody.trans (Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ ?_))
    exact (Nat.mod_modEq _ _).trans hσ

theorem coord_delivery (H : HashN) (T : CrtTable) (S coord : Nat) (Δ : Block) (Z : Nat → Block)
    (slopes : Fin S → Nat) (v : Nat) (hT : CorrectTable T) (hv : v < 2 ^ T.inputBits)
    (hav : ∀ e, slopes e * v < T.wrapBound) :
    let g := (coordGarbleM T S coord Δ Z).eval H
    let ev := (coordEvalM T S coord g.pub (g.records slopes) v
      (fun j => Z j ^^^ (if v.testBit j then Δ else 0))).eval H
    ∀ e, ev.decoded e = slopes e * v + g.offset e := by
  intro g ev e
  obtain ⟨hdec_lt, hhint, hjoin⟩ := CrtTable.records_roundtrip T g slopes e hT.modulus_pos
  obtain ⟨fJ, fP, fM, fS, fO, fH⟩ := coordGarbleM_fields H T S coord Δ Z
  simp only at fJ fP fM fS fO fH
  simp only [ev, coordEvalM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq]
  rw [hhint, fH e, fO e, Nat.add_comm]
  have hmodspec : ∀ r j, crtWith T.product T.idempotent r % T.modulus j = r j % T.modulus j := by
    intro r j
    have := table_crt_mod T hT.modulus_pos hT.coprime r j
    rwa [stored_eq] at this
  have hltspec : ∀ r, crtWith T.product T.idempotent r < ∏ i, T.modulus i := by
    intro r
    have := table_crt_lt T hT.modulus_pos r
    rwa [stored_eq] at this
  have hwrap : 2 * T.wrapBound ≤ (∏ i, T.modulus i) + 1 := hT.wrap
  have key := wrapDecode_crt hT.modulus_pos hT.coprime (crtWith T.product T.idempotent) hmodspec
    hltspec (hav e) hwrap
  refine key _ _ (fun j => ?_)
  beta_reduce
  -- the chunk step, with the published chunk material
  have hchunk : ∀ c (hc : c < T.chunkCount),
      (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v (g.pub.chunkJoin c)
        (pinOfBlocks T.castWidth fun k => g.pub.chunkPin c k.val) c).eval H =
      (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v
        ((chunkGarbleM T coord Δ Z c).eval H).joins ((chunkGarbleM T coord Δ Z c).eval H).pin c).eval H := by
    intro c hc
    rw [fJ c, fP c hc, pinOfBlocks_pinBlocks hT.castWidth_pos, atNat_of_lt _ _ hc]
  set chunksG := atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z c.val).eval H)
    (ChunkGarbled.empty T.castWidth) with hchunksG
  set chunksE := atNat (fun index : Fin T.chunkCount =>
    (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v (g.pub.chunkJoin index.val)
      (pinOfBlocks T.castWidth fun k => g.pub.chunkPin index.val k.val) index.val).eval H)
    (ChunkEval.empty T.castWidth) with hchunksE
  have hL : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunksG c).leaves α ^^^ (if α = T.chunkValue v c then Δ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunksG, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    simp only
    rw [hchunk c hc]
    exact (chunk_correct H T coord Δ Z v c).1 α hα
  have hC : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunksG c).casts α +
        (if α = T.chunkValue v c then deltaLanes T.castWidth Δ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunksG, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    simp only
    rw [hchunk c hc]
    exact (chunk_correct H T coord Δ Z v c).2 α hα
  have hJ : ∀ e', recordJoin T T.product T.radix (g.records slopes e') j =
      (((modGarbleM T S coord Δ chunksG j).eval H).body.padSum e' + slopes e') % T.modulus j := by
    intro e'
    have := (CrtTable.records_roundtrip T g slopes e' hT.modulus_pos).2.2 j
    simp only [stored_eq] at this
    rw [this]
    unfold CoordGarbled.join
    rw [fS j e']
  exact mod_residue H T S coord Δ slopes v hT hv g.pub
    (fun i e => recordJoin T T.product T.radix (g.records slopes e) i) chunksG chunksE hL hC j
    (fM j).1 (fM j).2.1 (fM j).2.2.1 (fM j).2.2.2 hJ e

end Kriterion.CRT.SliceC
