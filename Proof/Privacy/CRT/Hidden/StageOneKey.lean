/-
**H6 for the CRT entry, family 10: the bridge key at stage one**.

The garbler's only input of family 10 is the key input `maskKeyInput t = hashInput (t mod 2^128) maskKeyTag`
(`key_input`), so the event is `t.val % 2^128 = ℓ`. On the tag table the published value reads `t` only through the
curve constant `c0 = 3·mask + t − K(y6) − K(x7)`. The symmetry: for a nonzero `m'`, move the curve coins
`(t, mask, r1, r2)` to `(t + 3δ, m', r1 + δ, r2 − δ)` with `δ = mask − m'`, and move the pads `V_0[x3]`, `V_0[y4]` so
that the residue joins of `x3` and `y4` (whose slopes are `−r1`, `−r2`) do not change. The readouts `Σ ρ·V_ρ` do not
see `V_0`, so the offsets, hints, curve offsets, row offsets and row constants do not change either
(`BmrMove.invariant`). The orbit of a point is parametrized by `m' ∈ F_p^*`, on which `t` is injective; so given the
published value at most `⌊(p − 1)/2^128⌋ + 1` of the `p − 1` orbit points have the key label (`orbit_count`), and the
bound is `2/2^128 + 1/(p − 1)` (`BmrOff.count_bound`).

The measure side (`keyCase`): under the swapped table the pads are uniform and independent of the rest of the table
(`swapped_pads_split`), and the published value is a function `Φ` of the coins, the pads and the rest (`pubT_eq_Φ`).
-/

import Proof.Privacy.CRT.Hidden.StageOneTable
import Proof.Privacy.CRT.Core.BmrReal
import Proof.Privacy.CRT.Core.BmrKeyOff
import Proof.Privacy.CRT.Swap.PadLaw

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.StageOneKey

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Privacy.StageTwo (gAsked)
open Kriterion.CRT.Privacy.StageOneProof (keyRun_congr tagHash_key family_tag40 entriesOf_tagHash pubT)
open scoped ENNReal

noncomputable section

attribute [local instance 2000] H8.tableModulusNeZero

/-! ### P1. The key input -/

/-- **The garbler's only input of family 10 is the key input.** -/
theorem key_input (scalar : NonZeroScalar) (coins : Entry.Coins) (A : TagTable) (N : ℕ)
    (inside : N ∈ asked (H8.tagHash A) (garbleCM scalar coins)) (fam : tagFamily (N / 2 ^ 128) = 10) :
    N = maskKeyInput coins.bridgeKey := by
  unfold garbleCM at inside
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table xCount 0 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _ inX
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_ofPred_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table yCount 1 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _ inY
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_ofPred_eq] at member
    omega
  · simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inKey
    exact inKey
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.maskAnswersM_tagged _ digitCount (by decide) (by decide)) _ _ inMask
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
      Set.mem_ofPred_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.digestGarbleM_tagged coordinateBitCount digitCount (by decide) (by decide) _ _ _ _ _) _ _ inDigest
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union,
      Set.mem_ofPred_eq] at member
    omega

/-- The key input's low part is the bridge key's. -/
theorem maskKeyInput_mod (t : BaseField) : maskKeyInput t % 2 ^ 128 = t.val % 2 ^ 128 := by
  unfold maskKeyInput hashInput
  rw [Nat.add_mul_mod_self_left, BitVec.toNat_ofNat, Nat.mod_mod]

/-- **A family-10 garbler input fixes the bridge key's low part.** -/
theorem key_low (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) (N : ℕ)
    (inside : N ∈ gAsked scalar tape) (fam : tagFamily (N / 2 ^ 128) = 10) :
    tape.1.bridgeKey.val % 2 ^ 128 = N % 2 ^ 128 := by
  rw [StageOneProof.gAsked_eq] at inside
  rw [key_input scalar tape.1 tape.2 N inside fam, maskKeyInput_mod]

/-! ### P7. The bound -/

/-- The bound of this case: `2/2^128 + 1/(p − 1)` (`BmrOff.keyError`, without its certificate argument). -/
def keyEps : ℝ≥0∞ := ENNReal.ofReal (2 / 2 ^ 128 + 1 / ((BN254.baseFieldModulus : ℝ) - 1))

theorem keyEps_le : keyEps ≤ ENNReal.ofReal crtHiddenCharge := by
  refine ENNReal.ofReal_le_ofReal ?_
  rw [crtHiddenCharge_eq]
  have two : (2 : ℝ) / 2 ^ 128 ≤ 4 / 2 ^ labelBits := by norm_num [labelBits]
  linarith

/-! ### P2. The pad positions and what reads them -/

/-- **Every pad position has family 6.** -/
theorem padPositions_family {p : Fin (2 ^ 40)} (member : p ∈ padPositions) : tagFamily p.val = 6 := by
  obtain ⟨site, pad, hmem⟩ := member
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  obtain ⟨κ', i, ρ, rfl, hκ', hi, hρ⟩ := Layout.mem_padSites pad
  obtain ⟨-, -, -, -, hm, hq⟩ := Layout.tableFacts κ' hκ' i hi
  simp only [siteTags, List.mem_map, List.mem_range] at ht
  obtain ⟨j, hj, rfl⟩ := ht
  have hj' : j < Layout.padCount κ' i := hj
  have hin : TagInRange κ' i 0 0 ρ j := ⟨hκ', by omega, by omega, by omega, by omega, by omega⟩
  rw [← heq]
  simp only [tagPos]
  rw [Nat.mod_eq_of_lt (Asks.tagCode_lt (by decide) hin), tagFamily_tagCode hin]
  rfl

/-- Two tables that agree off the pad positions. -/
def OffPads (T T' : TagTable) : Prop := ∀ p, p ∉ padPositions → T p = T' p

theorem OffPads.at {T T' : TagTable} (h : OffPads T T') (p : Fin (2 ^ 40)) (fam : tagFamily p.val ≠ 6) :
    T p = T' p :=
  h p fun member => fam (padPositions_family member)

/-- At a labelled input of a key of a family other than 6, two tables that agree off the pads agree. -/
theorem OffPads.key {T T' : TagTable} (h : OffPads T T') {k : Paths.TagKey} (range : k.InRange) (fam : k.fam ≠ 6)
    (label : Block) : H8.tagHash T (hashInput label k.code) = H8.tagHash T' (hashInput label k.code) := by
  rw [tagHash_key T range, tagHash_key T' range]
  exact h.at _ (by rw [family_tag40 range]; exact fam)

open Classical in
/-- The table with its pad positions cleared. -/
def restOff (T : TagTable) : TagTable := fun p => if p ∈ padPositions then (0, 0) else T p

theorem offPads_restOff (T : TagTable) : OffPads T (restOff T) := by
  intro p off
  unfold restOff
  rw [if_neg off]

theorem restOff_congr {T T' : TagTable} (h : OffPads T T') : restOff T = restOff T' := by
  funext p
  unfold restOff
  split_ifs with hp
  · rfl
  · exact h p hp

/-- **The masks read no pad position.** -/
theorem masks_congr {T T' : TagTable} (h : OffPads T T') :
    BmrEntry.bmrMasksOf T = BmrEntry.bmrMasksOf T' := by
  have maskFams : ∀ k ∈ Paths.maskKeys digitCount, k.fam ≠ 6 := by
    intro k member
    simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
      Set.mem_ofPred_eq] at member
    omega
  have tagged := Paths.maskAnswersM_tagged (0 : Block) digitCount (by decide) (by decide)
  have same := (keyRun_congr tagged (H8.tagHash T) (H8.tagHash T')
    fun k member range label => h.key range (maskFams k member) label).1
  have values : maskValues (H8.tagHash T) 0 digitCount = maskValues (H8.tagHash T') 0 digitCount := by
    rw [← eval_maskAnswersM, ← eval_maskAnswersM]
    exact same
  funext r
  rcases r with ⟨d, x | y⟩
  · simp only [BmrEntry.bmrMasksOf, values]
  · simp only [BmrEntry.bmrMasksOf, values]

/-- **The exception entries read no pad position.** -/
theorem entries_congr (scalar : NonZeroScalar) (c : Entry.Coins) {T T' : TagTable} (h : OffPads T T') :
    EntryCorrect.entriesOf (H8.tagHash T) scalar c = EntryCorrect.entriesOf (H8.tagHash T') scalar c := by
  funext o
  rw [entriesOf_tagHash, entriesOf_tagHash]
  have h0 : 2 * o.val < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  have h1 : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  rw [h.at _ (by rw [DigestSplit.family_final _ h0]; decide), h.at _ (by rw [DigestSplit.family_final _ h1]; decide)]

/-- **A coordinate's published conversion material reads no pad position.** -/
theorem convVector_congr (S coord : ℕ) (hc : coord < 2) (small : S ≤ 1000) (Δ : Label) (Z : ℕ → Label)
    {T T' : TagTable} (h : OffPads T T') :
    convVector ((coordGarbleM table S coord Δ Z).eval (H8.tagHash T)).pub =
      convVector ((coordGarbleM table S coord Δ Z).eval (H8.tagHash T')).pub := by
  have ranges := Paths.bn254_ranges S small
  have read : Conv.readPub table ((coordGarbleM table S coord Δ Z).eval (H8.tagHash T)).pub =
      Conv.readPub table ((coordGarbleM table S coord Δ Z).eval (H8.tagHash T')).pub := by
    refine Asks.readPub_congr table S coord Δ Z _ _ (fun c hcc => ?_) (fun i row hk W => ?_)
    · refine (keyRun_congr (Paths.chunkGarbleM_tagged table coord Δ Z c hc
        (lt_of_lt_of_le hcc ranges.chunkCount) (ranges.chunkWidth c hcc) ranges.castAnswers) _ _
        fun k member range label => h.key range ?_ label).1
      simp only [Paths.pairKeys, Set.mem_ofPred_eq] at member
      omega
    · refine (keyRun_congr (Paths.conversionGarbleM_tagged coord i.val row (table.modulus i) hc
        (lt_of_lt_of_le i.isLt ranges.count) (ranges.rows i row hk) (ranges.modulus i) Δ W) _ _
        fun k member range label => h.key range ?_ label).1
      simp only [Paths.convKeys, Set.mem_ofPred_eq] at member
      omega
  rw [Flat.convVector_eq_flatOf, Flat.convVector_eq_flatOf, read]

/-! ### P3. The published value from the coins, the pads and the rest of the table -/

/-- P45's coins from the scheme's coins, the pads and the rest of the table. -/
def bcOf (c : Entry.Coins) (P : BMR.Pads table) (R : TagTable) : BMR.Coins table :=
  (P, BmrEntry.bmrMasksOf R, (BmrEntry.bmrCoinsOf c R).2.2)

/-- **The published value from the coins, the pads and the rest of the table.** -/
def pubParts (scalar : NonZeroScalar) (c : Entry.Coins) (P : BMR.Pads table) (R : TagTable) : Entry.Public where
  curve := BMR.curveTable (bcOf c P R)
  rows := Vector.ofFn fun d => BMR.nGamma (BmrEntry.bmrContextOf scalar c) (bcOf c P R) d
  exception := Vector.ofFn (EntryCorrect.entriesOf (H8.tagHash R) scalar c)
  crtX := convVector (EntryCorrect.gxOf (H8.tagHash R) c).pub
  crtY := convVector (EntryCorrect.gyOf (H8.tagHash R) c).pub
  recX := Vector.ofFn fun e => Entry.toRecord (BmrSplit.recordOf (BMR.nJoin (BmrEntry.bmrContextOf scalar c)
    (bcOf c P R)) (BMR.hint (bcOf c P R)) (.inl (BMR.xEncEquiv.symm e)))
  recY := Vector.ofFn fun e => Entry.toRecord (BmrSplit.recordOf (BMR.nJoin (BmrEntry.bmrContextOf scalar c)
    (bcOf c P R)) (BMR.hint (bcOf c P R)) (.inr (BMR.yEncEquiv.symm e)))

/-- A published value is the structure of its fields. -/
theorem public_eta (p : Entry.Public) :
    p = ⟨p.curve, p.rows, p.exception, p.crtX, p.crtY, p.recX, p.recY⟩ := rfl

/-- P45's coins of a table tape are those of its pads and its rest. -/
theorem bmrCoinsOf_eq (c : Entry.Coins) (T : TagTable) :
    BmrEntry.bmrCoinsOf c T = bcOf c (padsOf T) (restOff T) := by
  show (BmrEntry.bmrPadsOf T, BmrEntry.bmrMasksOf T, (BmrEntry.bmrCoinsOf c T).2.2) =
    (padsOf T, BmrEntry.bmrMasksOf (restOff T), (BmrEntry.bmrCoinsOf c (restOff T)).2.2)
  rw [masks_congr (offPads_restOff T)]
  rfl

/-- **The published value on a tag table is `pubParts` of its coins, pads and rest.** -/
theorem pubT_eq [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (c : Entry.Coins) (T : TagTable) :
    pubT scalar c T = pubParts scalar c (padsOf T) (restOff T) := by
  have hcurve : (pubT scalar c T).curve = BMR.curveTable (bcOf c (padsOf T) (restOff T)) := by
    rw [← bmrCoinsOf_eq]
    exact BmrEntry.curve_eq scalar c T
  have hrows : (pubT scalar c T).rows =
      Vector.ofFn fun d => BMR.nGamma (BmrEntry.bmrContextOf scalar c) (bcOf c (padsOf T) (restOff T)) d := by
    rw [← bmrCoinsOf_eq]
    exact BmrReal.vector_eq_ofFn _ _ fun d => BmrEntry.rows_eq scalar c T d
  have hexc : (pubT scalar c T).exception = Vector.ofFn (EntryCorrect.entriesOf (H8.tagHash (restOff T)) scalar c) := by
    rw [← entries_congr scalar c (offPads_restOff T)]
    rfl
  have hX : (pubT scalar c T).crtX = convVector (EntryCorrect.gxOf (H8.tagHash (restOff T)) c).pub := by
    unfold pubT
    rw [EntryCorrect.pubOf_crtX]
    unfold EntryCorrect.gxOf
    exact convVector_congr _ 0 (by norm_num) (by decide) _ _ (offPads_restOff T)
  have hY : (pubT scalar c T).crtY = convVector (EntryCorrect.gyOf (H8.tagHash (restOff T)) c).pub := by
    unfold pubT
    rw [EntryCorrect.pubOf_crtY]
    unfold EntryCorrect.gyOf
    exact convVector_congr _ 1 (by norm_num) (by decide) _ _ (offPads_restOff T)
  have hrecX : (pubT scalar c T).recX = Vector.ofFn fun e => Entry.toRecord (BmrSplit.recordOf
      (BMR.nJoin (BmrEntry.bmrContextOf scalar c) (bcOf c (padsOf T) (restOff T)))
      (BMR.hint (bcOf c (padsOf T) (restOff T))) (.inl (BMR.xEncEquiv.symm e))) := by
    rw [← bmrCoinsOf_eq]
    exact BmrReal.recX_vec scalar c T
  have hrecY : (pubT scalar c T).recY = Vector.ofFn fun e => Entry.toRecord (BmrSplit.recordOf
      (BMR.nJoin (BmrEntry.bmrContextOf scalar c) (bcOf c (padsOf T) (restOff T)))
      (BMR.hint (bcOf c (padsOf T) (restOff T))) (.inr (BMR.yEncEquiv.symm e))) := by
    rw [← bmrCoinsOf_eq]
    exact BmrReal.recY_vec scalar c T
  rw [public_eta (pubT scalar c T), hcurve, hrows, hexc, hX, hY, hrecX, hrecY]
  rfl

/-! ### P4a. The move of the curve coins and the pads, at the P45 level -/

section Move

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- The pad correction at slot `0`: at `x3` and `y4` it undoes the change of the slopes `−r1`, `−r2`. -/
def shiftAdj (r1 r1' r2 r2' : BaseField) (i : Fin T.count) : BMR.Enc → ZMod (T.modulus i)
  | .inl (.inr .x3) => (((-r1).val : ℕ) : ZMod (T.modulus i)) - (((-r1').val : ℕ) : ZMod (T.modulus i))
  | .inr (.inr .y4) => (((-r2).val : ℕ) : ZMod (T.modulus i)) - (((-r2').val : ℕ) : ZMod (T.modulus i))
  | _ => 0

/-- The hypotheses of a move: the pads change only at slot `0` by `shiftAdj`, the masks and the row randomizers
do not change, and the three curve constants' coin parts do not change. -/
structure Moved (c c' : BMR.Coins T) : Prop where
  pads : ∀ i ρ e, c'.pads i ρ e = c.pads i ρ e + if ρ = 0 then shiftAdj c.r1 c'.r1 c.r2 c'.r2 i e else 0
  mask : c'.mask = c.mask
  r4 : c'.r4 = c.r4
  unused : c'.unused = c.unused
  c0 : 3 * c'.curveMask + c'.bridge = 3 * c.curveMask + c.bridge
  c1 : c'.curveMask + c'.r1 = c.curveMask + c.r1
  c2 : -c'.curveMask + c'.r2 = -c.curveMask + c.r2

namespace Moved

variable {c c' : BMR.Coins T} (h : Moved c c')
include h

theorem readout (e : BMR.Enc) (i : Fin T.count) : BMR.readout c' e i = BMR.readout c e i := by
  unfold BMR.readout
  have zero : ∑ ρ : ZMod (T.modulus i), ρ * (if ρ = 0 then shiftAdj c.r1 c'.r1 c.r2 c'.r2 i e else 0) = 0 :=
    Finset.sum_eq_zero fun ρ _ => by by_cases hρ : ρ = 0 <;> simp [hρ]
  simp only [h.pads, mul_add, Finset.sum_add_distrib, zero, add_zero]

theorem offset (e : BMR.Enc) : BMR.offset c' e = BMR.offset c e := by
  unfold BMR.offset
  simp only [h.readout]

theorem offsetF (e : BMR.Enc) : BMR.offsetF c' e = BMR.offsetF c e := by
  unfold BMR.offsetF
  rw [h.offset]

theorem curveK : BMR.curveK c' = BMR.curveK c := by
  funext element
  unfold BMR.curveK
  rw [h.offsetF]

theorem rowOffset (r : BMR.RowEnc) : BMR.rowOffset c' r = BMR.rowOffset c r := by
  unfold BMR.rowOffset
  rw [h.offsetF, h.mask]

theorem digitSlopes (ctx : BMR.Context) (d : Fin 91) : BMR.digitSlopes ctx c' d = BMR.digitSlopes ctx c d := by
  unfold BMR.digitSlopes
  simp only [h.r4, h.unused, h.rowOffset]

theorem hint : BMR.hint c' = BMR.hint c := by
  funext e
  unfold BMR.hint
  rw [h.offset]

theorem gamma (ctx : BMR.Context) : BMR.gamma ctx c' = BMR.gamma ctx c := by
  funext d
  unfold BMR.gamma
  simp only [h.r4, h.unused, h.rowOffset]

theorem curveTable : BMR.curveTable c' = BMR.curveTable c := by
  unfold BMR.curveTable CurveMembership.garble
  rw [h.curveK]
  have e0 := h.c0
  have e1 := h.c1
  have e2 := h.c2
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show 3 * c'.curveMask + c'.bridge - _ - _ = 3 * c.curveMask + c.bridge - _ - _
    rw [e0]
  · exact e1
  · exact e2

theorem padSum (i : Fin T.count) (e : BMR.Enc) :
    ∑ ρ : ZMod (T.modulus i), c'.pads i ρ e = (∑ ρ : ZMod (T.modulus i), c.pads i ρ e) +
      shiftAdj c.r1 c'.r1 c.r2 c'.r2 i e := by
  simp only [h.pads, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem join (ctx : BMR.Context) : BMR.join ctx c' = BMR.join ctx c := by
  funext e i
  unfold BMR.join
  rw [h.padSum]
  rcases e with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y))
  · show _ + 0 + ((BMR.digitSlopes ctx c' d (.inl x)).val : ZMod (T.modulus i)) =
      _ + ((BMR.digitSlopes ctx c d (.inl x)).val : ZMod (T.modulus i))
    rw [h.digitSlopes, add_zero]
  · cases x
    · show _ + ((((-c.r1).val : ℕ) : ZMod (T.modulus i)) - (((-c'.r1).val : ℕ) : ZMod (T.modulus i))) +
          (((-c'.r1).val : ℕ) : ZMod (T.modulus i)) = _ + (((-c.r1).val : ℕ) : ZMod (T.modulus i))
      ring
    · show _ + 0 + ((-(BMR.curveK c') (.inl .x3)).val : ZMod (T.modulus i)) =
        _ + ((-(BMR.curveK c) (.inl .x3)).val : ZMod (T.modulus i))
      rw [h.curveK, add_zero]
    · show _ + 0 + ((-(BMR.curveK c') (.inl .x5)).val : ZMod (T.modulus i)) =
        _ + ((-(BMR.curveK c) (.inl .x5)).val : ZMod (T.modulus i))
      rw [h.curveK, add_zero]
  · show _ + 0 + ((BMR.digitSlopes ctx c' d (.inr y)).val : ZMod (T.modulus i)) =
      _ + ((BMR.digitSlopes ctx c d (.inr y)).val : ZMod (T.modulus i))
    rw [h.digitSlopes, add_zero]
  · cases y
    · show _ + ((((-c.r2).val : ℕ) : ZMod (T.modulus i)) - (((-c'.r2).val : ℕ) : ZMod (T.modulus i))) +
          (((-c'.r2).val : ℕ) : ZMod (T.modulus i)) = _ + (((-c.r2).val : ℕ) : ZMod (T.modulus i))
      ring
    · show _ + 0 + ((-(BMR.curveK c') (.inr .y4)).val : ZMod (T.modulus i)) =
        _ + ((-(BMR.curveK c) (.inr .y4)).val : ZMod (T.modulus i))
      rw [h.curveK, add_zero]

theorem rowKey : BmrOff.rowKey c' = BmrOff.rowKey c := by
  funext d
  unfold BmrOff.rowKey
  rw [h.rowOffset, h.rowOffset]

theorem nGamma (nctx : BMR.NContext) : BMR.nGamma nctx c' = BMR.nGamma nctx c := by
  funext d
  rw [BmrOff.nGamma_key, BmrOff.nGamma_key, h.rowKey, h.gamma]

theorem nJoin (nctx : BMR.NContext) : BMR.nJoin nctx c' = BMR.nJoin nctx c := by
  rw [BmrOff.nJoin_key, BmrOff.nJoin_key, h.rowKey, h.join]

end Moved

end Move

/-! ### P4b. The move at the entry -/

/-- The nonzero field elements. -/
abbrev NZ := {m : BaseField // m ≠ 0}

/-- The curve mask of the coins, as a nonzero element. -/
def maskOf (c : Entry.Coins) : NZ := ⟨c.curveMask.value, c.curveMask.nonzero⟩

/-- **The move of the curve coins** to the curve mask `m`: `δ = mask − m`, `t + 3δ`, `r1 + δ`, `r2 − δ`. -/
def moveCoins (c : Entry.Coins) (m : NZ) : Entry.Coins :=
  { c with
    bridgeKey := c.bridgeKey + 3 * (c.curveMask.value - m.1)
    curveMask := ⟨m.1, m.2⟩
    curveR1 := c.curveR1 + (c.curveMask.value - m.1)
    curveR2 := c.curveR2 - (c.curveMask.value - m.1) }

/-- **The move of the pads**: slot `0` of `x3` and `y4` absorbs the change of their slopes. -/
def movePads (c : Entry.Coins) (m : NZ) (P : BMR.Pads table) : BMR.Pads table := fun i ρ e =>
  P i ρ e + if ρ = 0 then shiftAdj c.curveR1 (moveCoins c m).curveR1 c.curveR2 (moveCoins c m).curveR2 i e else 0

/-- The move of a point of `coins × pads`. -/
def move (x : Entry.Coins × BMR.Pads table) (m : NZ) : Entry.Coins × BMR.Pads table :=
  (moveCoins x.1 m, movePads x.1 m x.2)

theorem maskOf_move (x : Entry.Coins × BMR.Pads table) (m : NZ) : maskOf (move x m).1 = m := rfl

theorem bridge_move (x : Entry.Coins × BMR.Pads table) (m : NZ) :
    (move x m).1.bridgeKey = x.1.bridgeKey + 3 * ((maskOf x.1).1 - m.1) := rfl

theorem shiftAdj_self {T : CrtTable} [∀ i, NeZero (T.modulus i)] (r1 r2 : BaseField) (i : Fin T.count)
    (e : BMR.Enc) : shiftAdj r1 r1 r2 r2 i e = 0 := by
  rcases e with ((_ | x) | (_ | y))
  · rfl
  · cases x <;> simp [shiftAdj]
  · rfl
  · cases y <;> simp [shiftAdj]

theorem shiftAdj_add {T : CrtTable} [∀ i, NeZero (T.modulus i)] (a1 b1 c1 a2 b2 c2 : BaseField) (i : Fin T.count)
    (e : BMR.Enc) : shiftAdj a1 b1 a2 b2 i e + shiftAdj b1 c1 b2 c2 i e = shiftAdj a1 c1 a2 c2 i e := by
  rcases e with ((_ | x) | (_ | y))
  · show (0 : ZMod (T.modulus i)) + 0 = 0
    rw [add_zero]
  · cases x
    · show (_ - _) + (_ - _) = (_ - _ : ZMod (T.modulus i))
      ring
    · show (0 : ZMod (T.modulus i)) + 0 = 0
      rw [add_zero]
    · show (0 : ZMod (T.modulus i)) + 0 = 0
      rw [add_zero]
  · show (0 : ZMod (T.modulus i)) + 0 = 0
    rw [add_zero]
  · cases y
    · show (_ - _) + (_ - _) = (_ - _ : ZMod (T.modulus i))
      ring
    · show (0 : ZMod (T.modulus i)) + 0 = 0
      rw [add_zero]

theorem moveCoins_self (c : Entry.Coins) : moveCoins c (maskOf c) = c := by
  cases c with
  | mk offsets clamped pr pad t mk r1 r2 zero delta =>
    show Kriterion.ArgoMAC.Scheme.Coins.mk offsets clamped pr pad (t + 3 * (mk.value - mk.value))
        ⟨mk.value, mk.nonzero⟩ (r1 + (mk.value - mk.value)) (r2 - (mk.value - mk.value)) zero delta =
      Kriterion.ArgoMAC.Scheme.Coins.mk offsets clamped pr pad t mk r1 r2 zero delta
    rw [sub_self, mul_zero, add_zero, add_zero, sub_zero]

theorem moveCoins_move (c : Entry.Coins) (m m' : NZ) : moveCoins (moveCoins c m) m' = moveCoins c m' := by
  cases c with
  | mk offsets clamped pr pad t mk r1 r2 zero delta =>
    show Kriterion.ArgoMAC.Scheme.Coins.mk offsets clamped pr pad
        (t + 3 * (mk.value - m.1) + 3 * (m.1 - m'.1)) ⟨m'.1, m'.2⟩
        (r1 + (mk.value - m.1) + (m.1 - m'.1)) (r2 - (mk.value - m.1) - (m.1 - m'.1)) zero delta =
      Kriterion.ArgoMAC.Scheme.Coins.mk offsets clamped pr pad (t + 3 * (mk.value - m'.1)) ⟨m'.1, m'.2⟩
        (r1 + (mk.value - m'.1)) (r2 - (mk.value - m'.1)) zero delta
    rw [show t + 3 * (mk.value - m.1) + 3 * (m.1 - m'.1) = t + 3 * (mk.value - m'.1) by ring,
      show r1 + (mk.value - m.1) + (m.1 - m'.1) = r1 + (mk.value - m'.1) by ring,
      show r2 - (mk.value - m.1) - (m.1 - m'.1) = r2 - (mk.value - m'.1) by ring]

theorem move_self (x : Entry.Coins × BMR.Pads table) : move x (maskOf x.1) = x := by
  obtain ⟨c, P⟩ := x
  have pads : movePads c (maskOf c) P = P := by
    funext i ρ e
    unfold movePads
    rw [moveCoins_self, shiftAdj_self, ite_self, add_zero]
  show (moveCoins c (maskOf c), movePads c (maskOf c) P) = (c, P)
  rw [moveCoins_self, pads]

theorem move_move (x : Entry.Coins × BMR.Pads table) (m m' : NZ) : move (move x m) m' = move x m' := by
  obtain ⟨c, P⟩ := x
  have pads : movePads (moveCoins c m) m' (movePads c m P) = movePads c m' P := by
    funext i ρ e
    unfold movePads
    rw [moveCoins_move]
    by_cases hρ : ρ = 0
    · simp only [hρ, if_true]
      rw [add_assoc, shiftAdj_add]
    · simp only [hρ, if_false, add_zero]
  show (moveCoins (moveCoins c m) m', movePads (moveCoins c m) m' (movePads c m P)) =
    (moveCoins c m', movePads c m' P)
  rw [moveCoins_move, pads]

/-- **The move is a move at the P45 level.** -/
theorem moved (x : Entry.Coins × BMR.Pads table) (m : NZ) (R : TagTable) :
    Moved (bcOf x.1 x.2 R) (bcOf (move x m).1 (move x m).2 R) where
  pads _ _ _ := rfl
  mask := rfl
  r4 := rfl
  unused := rfl
  c0 := by
    show 3 * m.1 + (x.1.bridgeKey + 3 * (x.1.curveMask.value - m.1)) = 3 * x.1.curveMask.value + x.1.bridgeKey
    ring
  c1 := by
    show m.1 + (x.1.curveR1 + (x.1.curveMask.value - m.1)) = x.1.curveMask.value + x.1.curveR1
    ring
  c2 := by
    show -m.1 + (x.1.curveR2 - (x.1.curveMask.value - m.1)) = -x.1.curveMask.value + x.1.curveR2
    ring

theorem moveCoins_offsets (c : Entry.Coins) (m : NZ) : (moveCoins c m).offsets = c.offsets := rfl

theorem ctx_move (scalar : NonZeroScalar) (c : Entry.Coins) (m : NZ) :
    BmrEntry.bmrContextOf scalar (moveCoins c m) = BmrEntry.bmrContextOf scalar c := by
  unfold BmrEntry.bmrContextOf NormRows.nctxOf Kriterion.CRT.Entry.outputKeysOf
  rw [moveCoins_offsets]
theorem moveCoins_exceptionPad (c : Entry.Coins) (m : NZ) : (moveCoins c m).exceptionPad = c.exceptionPad := rfl
theorem moveCoins_inputZero (c : Entry.Coins) (m : NZ) : (moveCoins c m).inputZero = c.inputZero := rfl
theorem moveCoins_inputDelta (c : Entry.Coins) (m : NZ) : (moveCoins c m).inputDelta = c.inputDelta := rfl

theorem entries_move (H : HashN) (scalar : NonZeroScalar) (c : Entry.Coins) (m : NZ) :
    EntryCorrect.entriesOf H scalar (moveCoins c m) = EntryCorrect.entriesOf H scalar c := by
  -- the actual zero labels read the coins' zero labels and the coordinate garblings only
  have hz : EntryCorrect.keyZero H (moveCoins c m) = EntryCorrect.keyZero H c := rfl
  unfold EntryCorrect.entriesOf Entry.deltaOf Entry.outputKeysOf
  rw [hz, moveCoins_offsets, moveCoins_exceptionPad, moveCoins_inputDelta]

theorem gx_move (H : HashN) (c : Entry.Coins) (m : NZ) :
    EntryCorrect.gxOf H (moveCoins c m) = EntryCorrect.gxOf H c := rfl

theorem gy_move (H : HashN) (c : Entry.Coins) (m : NZ) :
    EntryCorrect.gyOf H (moveCoins c m) = EntryCorrect.gyOf H c := rfl

/-- **The published value does not change along a move.** -/
theorem pubParts_move (scalar : NonZeroScalar) (x : Entry.Coins × BMR.Pads table) (m : NZ) (R : TagTable) :
    pubParts scalar (move x m).1 (move x m).2 R = pubParts scalar x.1 x.2 R := by
  have mv : (move x m).1 = moveCoins x.1 m := rfl
  have h := moved x m R
  rw [mv] at h
  have e1 := h.curveTable
  have e2 := h.nGamma (BmrEntry.bmrContextOf scalar x.1)
  have e3 := h.nJoin (BmrEntry.bmrContextOf scalar x.1)
  have e4 := h.hint
  unfold pubParts
  rw [mv, ctx_move, entries_move, gx_move, gy_move, e1, e2, e3, e4]

/-! ### P5. Counting along the orbits -/

theorem tsum_indicator_one {α : Type} [Fintype α] (S : Set α) :
    ∑' a, S.indicator (1 : α → ℝ≥0∞) a = (Nat.card S : ℝ≥0∞) := by
  classical
  rw [tsum_fintype, Finset.sum_indicator_eq_sum_filter, Nat.card_eq_card_toFinset]
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext a
  simp

theorem three_ne_zero' [FieldCertificate] : (3 : BaseField) ≠ 0 := by
  have h : ((3 : ℕ) : BaseField) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 3 BN254.baseFieldModulus).not.mpr (by decide)
  exact_mod_cast h

/-- `⌊(p − 1)/2^128⌋ + 1 ≤ keyEps · (p − 1)` (`BmrOff.count_bound`). -/
theorem low_le_keyEps [FieldCertificate] :
    (((BN254.baseFieldModulus - 1) / 2 ^ 128 + 1 : ℕ) : ℝ≥0∞) ≤
      keyEps * ((BN254.baseFieldModulus - 1 : ℕ) : ℝ≥0∞) := by
  have h := BmrOff.count_bound
  have ne : ((BN254.baseFieldModulus - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]
    have two : 2 ≤ BN254.baseFieldModulus := (Fact.out : Nat.Prime BN254.baseFieldModulus).two_le
    omega
  rw [ENNReal.div_le_iff_le_mul (Or.inl ne) (Or.inl (ENNReal.natCast_ne_top _))] at h
  exact h

/-- The unit as a nonzero element. -/
def oneNZ : NZ := ⟨1, BMR.one_ne_zero_base⟩

/-- **Counting along the orbits**: if a map `ψ` moves every point along an orbit parametrized by the nonzero field
elements, keeps `Φ`, and moves the key by `3·(mask − m)`, then the points of a `Φ`-fibre whose key has a given low
part are at most a `keyEps` fraction of the fibre. -/
theorem orbit_count [FieldCertificate] {X V : Type} [Fintype X] (Φ : X → V) (key : X → BaseField)
    (mk : X → NZ) (ψ : X → NZ → X) (hmask : ∀ x m, mk (ψ x m) = m) (hself : ∀ x, ψ x (mk x) = x)
    (hcomp : ∀ x m m', ψ (ψ x m) m' = ψ x m') (hΦ : ∀ x m, Φ (ψ x m) = Φ x)
    (hkey : ∀ x m, key (ψ x m) = key x + 3 * ((mk x).1 - m.1)) (v : V) (ℓ : ℕ) :
    ∑' x, {x | Φ x = v ∧ (key x).val % 2 ^ 128 = ℓ}.indicator (1 : X → ℝ≥0∞) x ≤
      keyEps * ∑' x, {x | Φ x = v}.indicator (1 : X → ℝ≥0∞) x := by
  classical
  let e : {x : X // mk x = oneNZ} × NZ ≃ X :=
    { toFun := fun p => ψ p.1.1 p.2
      invFun := fun x => (⟨ψ x oneNZ, hmask x oneNZ⟩, mk x)
      left_inv := fun p => by
        refine Prod.ext (Subtype.ext ?_) (hmask _ _)
        show ψ (ψ p.1.1 p.2) oneNZ = p.1.1
        have back := hself p.1.1
        rw [p.1.2] at back
        rw [hcomp, back]
      right_inv := fun x => by
        show ψ (ψ x oneNZ) (mk x) = x
        rw [hcomp, hself] }
  rw [← e.tsum_eq, ← e.tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  show ∑' m, {x | Φ x = v ∧ (key x).val % 2 ^ 128 = ℓ}.indicator (1 : X → ℝ≥0∞) (ψ y.1 m) ≤
    keyEps * ∑' m, {x | Φ x = v}.indicator (1 : X → ℝ≥0∞) (ψ y.1 m)
  by_cases hv : Φ y.1 = v
  · have lhs : ∀ m, {x | Φ x = v ∧ (key x).val % 2 ^ 128 = ℓ}.indicator (1 : X → ℝ≥0∞) (ψ y.1 m) =
        {m : NZ | (key y.1 + 3 * ((mk y.1).1 - m.1)).val % 2 ^ 128 = ℓ}.indicator 1 m := by
      intro m
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hΦ, hkey, hv, true_and, Pi.one_apply]
    have rhs : ∀ m, {x | Φ x = v}.indicator (1 : X → ℝ≥0∞) (ψ y.1 m) = (Set.univ : Set NZ).indicator 1 m := by
      intro m
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hΦ, hv, Set.mem_univ, Pi.one_apply]
    rw [tsum_congr lhs, tsum_congr rhs, tsum_indicator_one, tsum_indicator_one]
    have inj : Function.Injective fun m : NZ => key y.1 + 3 * ((mk y.1).1 - m.1) := by
      intro m m' same
      have h3 := three_ne_zero'
      have e1 : 3 * ((mk y.1).1 - m.1) = 3 * ((mk y.1).1 - m'.1) := add_left_cancel same
      have e2 := mul_left_cancel₀ h3 e1
      apply Subtype.ext
      linear_combination -e2
    have few := BmrOff.natCard_low_le ℓ _ inj
    have all : Nat.card (Set.univ : Set NZ) = BN254.baseFieldModulus - 1 := by
      rw [Nat.card_univ, BmrOff.natCard_nonzero]
    calc ((Nat.card {m : NZ | (key y.1 + 3 * ((mk y.1).1 - m.1)).val % 2 ^ 128 = ℓ} : ℕ) : ℝ≥0∞)
        ≤ (((BN254.baseFieldModulus - 1) / 2 ^ 128 + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast few
      _ ≤ keyEps * ((BN254.baseFieldModulus - 1 : ℕ) : ℝ≥0∞) := low_le_keyEps
      _ = keyEps * (Nat.card (Set.univ : Set NZ) : ℝ≥0∞) := by rw [all]
  · have zero : ∀ m, {x | Φ x = v ∧ (key x).val % 2 ^ 128 = ℓ}.indicator (1 : X → ℝ≥0∞) (ψ y.1 m) = 0 := by
      intro m
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hΦ, hv, false_and, if_false]
    rw [tsum_congr zero, tsum_zero]
    exact zero_le

/-! ### P6. The measure -/

theorem bind_outer_le {R X : Type} (law : PMF R) (κ : R → PMF X) (A B : Set X) (ε : ℝ≥0∞)
    (each : ∀ r, (κ r).toOuterMeasure A ≤ ε * (κ r).toOuterMeasure B) :
    (law.bind κ).toOuterMeasure A ≤ ε * (law.bind κ).toOuterMeasure B := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun r => ?_
  rw [mul_left_comm]
  exact mul_le_mul' le_rfl (each r)

theorem uniform_outer_le {X : Type} [Fintype X] [Nonempty X] (A B : Set X) (ε : ℝ≥0∞)
    (count : ∑' x, A.indicator (1 : X → ℝ≥0∞) x ≤ ε * ∑' x, B.indicator (1 : X → ℝ≥0∞) x) :
    (PMF.uniformOfFintype X).toOuterMeasure A ≤ ε * (PMF.uniformOfFintype X).toOuterMeasure B := by
  have scale : ∀ S : Set X, (PMF.uniformOfFintype X).toOuterMeasure S =
      (Fintype.card X : ℝ≥0∞)⁻¹ * ∑' x, S.indicator (1 : X → ℝ≥0∞) x := by
    intro S
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, PMF.uniformOfFintype_apply, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  rw [scale, scale, mul_left_comm]
  exact mul_le_mul' le_rfl count

end

end Kriterion.CRT.Privacy.StageOneKey

namespace Kriterion.CRT.Privacy.StageOneProof

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.StageTwo (gAsked)
open Kriterion.CRT.Privacy.StageOneKey
open scoped ENNReal

noncomputable section

attribute [local instance 2000] H8.tableModulusNeZero

/-- The orbit count at the entry, for one rest of the table. -/
theorem count_at [FieldCertificate] [Fintype Instance.crtEntry.Coins] (scalar : NonZeroScalar) (R : TagTable)
    (view : Instance.crtEntry.Public) (ℓ : ℕ) :
    ∑' x : Instance.crtEntry.Coins × BMR.Pads table,
        {x : Instance.crtEntry.Coins × BMR.Pads table | pubParts scalar x.1 x.2 R = view ∧
          x.1.bridgeKey.val % 2 ^ 128 = ℓ}.indicator (1 : Instance.crtEntry.Coins × BMR.Pads table → ℝ≥0∞) x ≤
      keyEps * ∑' x : Instance.crtEntry.Coins × BMR.Pads table,
        {x : Instance.crtEntry.Coins × BMR.Pads table | pubParts scalar x.1 x.2 R = view}.indicator
          (1 : Instance.crtEntry.Coins × BMR.Pads table → ℝ≥0∞) x :=
  orbit_count (X := Instance.crtEntry.Coins × BMR.Pads table) (fun x => pubParts scalar x.1 x.2 R)
    (fun x => x.1.bridgeKey) (fun x => StageOneKey.maskOf x.1) move
    (fun x m => maskOf_move x m) move_self move_move (fun x m => pubParts_move scalar x m R)
    (fun x m => bridge_move x m) view ℓ

/-- **Family 10 (the bridge key) at stage one**: given the published value, the key label `t mod 2^128` has
conditional mass at most `2/2^128 + 1/(p − 1)`. -/
theorem keyCase : OneCase (fun τ => tagFamily τ = 10) keyEps := by
  intro field group parameter scalar view N fam
  have sub : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} ⊆
      {ω : TableTape Instance.crtEntry | pubT scalar ω.1 ω.2 = view ∧
        ω.1.bridgeKey.val % 2 ^ 128 = N % 2 ^ 128} := by
    intro tape member
    obtain ⟨hv, hN⟩ := member
    rw [stageOneView_pubT] at hv
    exact ⟨hv, key_low scalar tape N hN fam⟩
  refine le_trans (MeasureTheory.measure_mono sub) ?_
  let coinsFin : Fintype Instance.crtEntry.Coins := @Fintype.ofFinite _ Instance.crtEntry.coinsFinite
  have coinsNe : Nonempty Instance.crtEntry.Coins := ⟨Instance.crtEntry.coinWitness⟩
  let UC := PMF.uniformOfFintype Instance.crtEntry.Coins
  have tapeEq : swappedTableTape Instance.crtEntry =
      UC.bind fun c => (swappedTableLaw crtLayout).map fun T => ((c, T) : TableTape Instance.crtEntry) :=
    swappedTableTape_eq
  rw [viewSet_eq, tapeEq]
  let G : TableTape Instance.crtEntry → (Instance.crtEntry.Coins × BMR.Pads table) × TagTable :=
    fun ω => ((ω.1, padsOf ω.2), restOff ω.2)
  have hA : {ω : TableTape Instance.crtEntry | pubT scalar ω.1 ω.2 = view ∧
      ω.1.bridgeKey.val % 2 ^ 128 = N % 2 ^ 128} =
      G ⁻¹' {q | pubParts scalar q.1.1 q.1.2 q.2 = view ∧ q.1.1.bridgeKey.val % 2 ^ 128 = N % 2 ^ 128} := by
    ext ω
    show (pubT scalar ω.1 ω.2 = view ∧ _) ↔ (pubParts scalar ω.1 (padsOf ω.2) (restOff ω.2) = view ∧ _)
    rw [pubT_eq scalar ω.1 ω.2]
    exact Iff.rfl
  have hB : {ω : TableTape Instance.crtEntry | pubT scalar ω.1 ω.2 = view} =
      G ⁻¹' {q | pubParts scalar q.1.1 q.1.2 q.2 = view} := by
    ext ω
    show pubT scalar ω.1 ω.2 = view ↔ pubParts scalar ω.1 (padsOf ω.2) (restOff ω.2) = view
    rw [pubT_eq scalar ω.1 ω.2]
    exact Iff.rfl
  rw [hA, hB, ← PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_map_apply]
  let UP := PMF.uniformOfFintype (BMR.Pads table)
  let LR := (swappedTableLaw crtLayout).map restOff
  have left : (UC.bind fun c => (swappedTableLaw crtLayout).map fun T => ((c, T) : TableTape Instance.crtEntry)).map G =
      UC.bind fun c => UP.bind fun P => LR.map fun R => ((c, P), R) := by
    calc (UC.bind fun c => (swappedTableLaw crtLayout).map fun T => ((c, T) : TableTape Instance.crtEntry)).map G
        = UC.bind fun c => ((swappedTableLaw crtLayout).map fun T => (padsOf T, restOff T)).map
            fun q => ((c, q.1), q.2) := by
          rw [PMF.map_bind]
          refine congrArg (PMF.bind UC) (funext fun c => ?_)
          rw [PMF.map_comp, PMF.map_comp]
          rfl
      _ = UC.bind fun c => (UP.bind fun P => LR.map fun r => (P, r)).map fun q => ((c, q.1), q.2) := by
          rw [swapped_pads_split restOff fun T T' h => restOff_congr h]
      _ = UC.bind fun c => UP.bind fun P => LR.map fun R => ((c, P), R) := by
          refine congrArg (PMF.bind UC) (funext fun c => ?_)
          rw [PMF.map_bind]
          refine congrArg (PMF.bind UP) (funext fun P => ?_)
          rw [PMF.map_comp]
          rfl
  have right : (LR.bind fun R => (PMF.uniformOfFintype (Instance.crtEntry.Coins × BMR.Pads table)).map
      fun x => (x, R)) = UC.bind fun c => UP.bind fun P => LR.map fun R => ((c, P), R) := by
    calc (LR.bind fun R => (PMF.uniformOfFintype (Instance.crtEntry.Coins × BMR.Pads table)).map fun x => (x, R))
        = LR.bind fun R => UC.bind fun c => UP.map fun P => ((c, P), R) := by
          refine congrArg (PMF.bind LR) (funext fun R => ?_)
          rw [Kriterion.CRT.EntrySplit.uniform_prod_eq_bind, PMF.map_bind]
          refine congrArg (PMF.bind UC) (funext fun c => ?_)
          rw [PMF.map_comp]
          rfl
      _ = UC.bind fun c => LR.bind fun R => UP.map fun P => ((c, P), R) := PMF.bind_comm _ _ _
      _ = UC.bind fun c => UP.bind fun P => LR.map fun R => ((c, P), R) := by
          refine congrArg (PMF.bind UC) (funext fun c => ?_)
          simp only [← PMF.bind_pure_comp]
          exact PMF.bind_comm _ _ _
  rw [left, ← right]
  refine bind_outer_le _ _ _ _ _ fun R => ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine uniform_outer_le _ _ _ ?_
  exact count_at scalar R view (N % 2 ^ 128)

/-- The bound of `keyCase` is within H6's charge. -/
theorem keyCase_le : keyEps ≤ ENNReal.ofReal crtHiddenCharge := keyEps_le

end

end Kriterion.CRT.Privacy.StageOneProof
