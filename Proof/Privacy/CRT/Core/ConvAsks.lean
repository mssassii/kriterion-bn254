/-
**CRT privacy core: the garbler's conversion asks only small labelled inputs.**

The scheme runs the garbler on `schemeHash oracle`, which reads a natural hash input `n` as the field element
`(n : BaseField)`. On the chain's table oracle (`tableOracle A`) an input is answered by `A` at the tag
`((n mod p) / 2^128) mod 2^40`; the conversion laws (`ConvRead.lean`) read the table as `tableHash (tagRead A)`, which
answers `n` by `A` at `(n / 2^128) mod 2^40`. The two agree below `p`, and every conversion query is a labelled input
`hashInput label tag` with a tag below `2^40`, hence below `2^168 < p`.

* `AsksIn S P`: along every path, `P` asks only inputs in `S`; `eval_congr`: then `P.eval` depends on the hash only on
  `S`. Closure under `pure`, `bind`, `vector`, `tableM`, `h128M`, `hlongM`.
* The block lemmas: the tree, growth, cast, fold, extraction stage, chunk and conversion programs ask only small
  inputs when their tags are in range (`tagCode_lt`).
* `readPub_congr`: a coordinate's in-range published material depends on the hash only through its chunks and its
  conversions; `real_readPub`: on the real table, the scheme's reading of the table oracle gives the same material as
  `tableHash (tagRead A)`.
-/

import Proof.Privacy.CRT.Core.ConvRead
import Proof.Privacy.CRT.Hybrids

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Asks

open Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Conv (ConvVals rowOf readPub readMod RowWF ConvTagRange ConvTableWF tagRead castAnswers_le
  pow_le_pow15 coord_pub modGarbleM_odd bn254Table_wf bn254Table_range)

noncomputable section

/-! ### Programs that ask only inputs in a set -/

/-- **Along every path, `P` asks only inputs in `S`.** -/
def AsksIn (S : ℕ → Prop) {α : Type} : CM α → Prop
  | .pure _ => True
  | .query input next => S input ∧ ∀ answer, AsksIn S (next answer)

section Closure

variable {S : ℕ → Prop}

/-- A program that asks only inputs in `S` reads the hash only on `S`. -/
theorem eval_congr {α : Type} (P : CM α) (hP : AsksIn S P) {H H' : HashN} (agree : ∀ n, S n → H n = H' n) :
    P.eval H = P.eval H' := by
  induction P with
  | pure v => rfl
  | query input next ih =>
      obtain ⟨h1, h2⟩ := hP
      show (next (H input)).eval H = (next (H' input)).eval H'
      rw [agree input h1]
      exact ih _ (h2 _)

theorem asks_pure {α : Type} (a : α) : AsksIn S (Pure.pure a : CM α) := trivial

theorem asks_bind {α β : Type} {P : CM α} {f : α → CM β} (hP : AsksIn S P) (hf : ∀ a, AsksIn S (f a)) :
    AsksIn S (P >>= f) := by
  induction P with
  | pure v => exact hf v
  | query input next ih =>
      obtain ⟨h1, h2⟩ := hP
      exact ⟨h1, fun answer => ih answer (h2 answer)⟩

theorem asks_askN (input : ℕ) (h : S input) : AsksIn S (askN input) := ⟨h, fun _ => trivial⟩

theorem asks_vector {α : Type} (n : ℕ) (prog : Fin n → CM α) (h : ∀ i, AsksIn S (prog i)) :
    AsksIn S (FreeQuery.vector n prog) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      exact asks_bind (ih _ fun i => h _) fun _ => asks_bind (h _) fun _ => trivial

theorem asks_tableM {α : Type} (n : ℕ) (prog : Fin n → CM α) (h : ∀ i, AsksIn S (prog i)) :
    AsksIn S (tableM n prog) :=
  asks_bind (asks_vector n prog h) fun _ => trivial

end Closure

/-! ### Small inputs and in-range tags -/

/-- An input below `2 ^ 168` (so below `p`). -/
def Small (n : ℕ) : Prop := n < 2 ^ 168

theorem hashInput_small (label : Block) (tag : ℕ) (h : tag < 2 ^ 40) : Small (hashInput label tag) := by
  unfold Small hashInput
  have h1 : label.toNat < 2 ^ 128 := label.isLt
  have h2 : 2 ^ 128 * (tag + 1) ≤ 2 ^ 128 * 2 ^ 40 := Nat.mul_le_mul_left _ h
  calc label.toNat + 2 ^ 128 * tag < 2 ^ 128 + 2 ^ 128 * tag := Nat.add_lt_add_right h1 _
    _ = 2 ^ 128 * (tag + 1) := by ring
    _ ≤ 2 ^ 128 * 2 ^ 40 := h2
    _ = 2 ^ 168 := by norm_num

theorem tagCode_lt {fam coord idx stage level slot part : ℕ} (hf : fam < 16)
    (h : TagInRange coord idx stage level slot part) : tagCode fam coord idx stage level slot part < 2 ^ 40 := by
  have := h.coord; have := h.idx; have := h.stage; have := h.level; have := h.slot; have := h.part
  unfold tagCode
  omega

theorem asks_h128M (label : Block) (tag : ℕ) (h : tag < 2 ^ 40) : AsksIn Small (h128M label tag) :=
  asks_bind (asks_askN _ (hashInput_small label tag h)) fun _ => trivial

theorem asks_hlongM (label : Block) (tagOf : ℕ → ℕ) (count : ℕ) (h : ∀ j, j < count → tagOf j < 2 ^ 40) :
    AsksIn Small (hlongM label tagOf count) :=
  asks_bind (asks_vector _ _ fun j => asks_askN _ (hashInput_small label _ (h j.val j.isLt))) fun _ => trivial

/-! ### The blocks -/

theorem asks_castM (l : ℕ) (label : Block) (tagOf : ℕ → ℕ) (h : ∀ j, j < castAnswers l → tagOf j < 2 ^ 40) :
    AsksIn Small (castM l label tagOf) :=
  asks_bind (asks_hlongM label tagOf _ h) fun _ => trivial

theorem asks_garbleStepM (n : ℕ) (tagOf : ℕ → ℕ) (parent : Fin (2 ^ n) → Block)
    (h : ∀ s, s < 2 ^ n → tagOf s < 2 ^ 40) : AsksIn Small (garbleStepM n tagOf parent) :=
  asks_bind (asks_tableM _ _ fun slot => asks_h128M _ _ (h slot.val slot.isLt)) fun _ => trivial

theorem asks_treeGarbleM (tagOf : ℕ → ℕ → ℕ) (Δ b0 : Block) (levels : ℕ)
    (h : ∀ n s, n < levels → s < 2 ^ n → tagOf n s < 2 ^ 40) : AsksIn Small (treeGarbleM tagOf Δ b0 levels) := by
  induction levels with
  | zero => trivial
  | succ n ih =>
      rw [treeGarbleM]
      refine asks_bind (ih fun n' s hn hs => h n' s (by omega) hs) fun previous => ?_
      split
      · trivial
      · exact asks_bind (asks_garbleStepM n _ _ fun s hs => h n s (by omega) hs) fun _ => trivial

theorem asks_growGarbleM (tagOf : ℕ → ℕ → ℕ) (start : ℕ) (labels : Fin (2 ^ start) → Block) (count : ℕ)
    (h : ∀ n s, n < start + count → s < 2 ^ n → tagOf n s < 2 ^ 40) :
    AsksIn Small (growGarbleM tagOf start labels count) := by
  induction count with
  | zero => trivial
  | succ k ih =>
      rw [growGarbleM]
      exact asks_bind (ih fun n s hn hs => h n s (by omega) hs) fun _ =>
        asks_bind (asks_garbleStepM _ _ _ fun s hs => h _ s (by omega) hs) fun _ => trivial

theorem asks_foldGarbleM (m : ℕ) (tagOf : ℕ → ℕ) (shift : ℕ) (bitMask : Block) (labels : Fin m → Block)
    (h : ∀ r, r < m → tagOf r < 2 ^ 40) : AsksIn Small (foldGarbleM m tagOf shift bitMask labels) :=
  asks_bind (asks_tableM _ _ fun r => asks_h128M _ _ (h r.val r.isLt)) fun _ => trivial

theorem asks_foldsGarbleM (m : ℕ) (tagOf : ℕ → ℕ → ℕ) (bitMask : ℕ → Block) (count : ℕ) :
    ∀ (start : ℕ) (labels : Fin m → Block), (∀ pos r, pos < start + count → r < m → tagOf pos r < 2 ^ 40) →
      AsksIn Small (foldsGarbleM m tagOf bitMask count start labels) := by
  induction count with
  | zero => intro _ _ _; trivial
  | succ k ih =>
      intro start labels h
      rw [foldsGarbleM]
      exact asks_bind (asks_foldGarbleM _ _ _ _ _ fun r hr => h start r (by omega) hr) fun step =>
        asks_bind (ih (start + 1) step.1 fun pos r hp hr => h pos r (by omega) hr) fun _ => trivial

theorem asks_extStageGarbleM {rb : ℕ} (w : ℕ) (treeTag castTag : ℕ → ℕ → ℕ) (Δ : Block) (remainder : Lanes rb)
    (ht : ∀ n s, n < w → s < 2 ^ n → treeTag n s < 2 ^ 40)
    (hc : ∀ leaf j, leaf < 2 ^ w → j < castAnswers rb → castTag leaf j < 2 ^ 40) :
    AsksIn Small (extStageGarbleM w treeTag castTag Δ remainder) := by
  unfold extStageGarbleM
  dsimp only
  exact asks_bind (asks_treeGarbleM _ _ _ _ ht) fun _ =>
    asks_bind (asks_tableM _ _ fun leaf => asks_castM _ _ _ fun j hj => hc leaf.val j leaf.isLt hj) fun _ => trivial

/-! ### The tags of the conversion -/

theorem fam_lt : Family.chunkTree < 16 ∧ Family.chunkCast < 16 ∧ Family.extTree < 16 ∧ Family.extCast < 16 ∧
    Family.grow < 16 ∧ Family.fold < 16 := by
  decide

theorem slot_lt {n : ℕ} (hn : n ≤ 15) {s : ℕ} (hs : s < 2 ^ n) : s < 65536 :=
  lt_of_lt_of_le hs (le_trans (pow_le_pow15 hn) (by norm_num))

/-- **A chunk asks only small inputs.** -/
theorem asks_chunkGarbleM (tbl : CrtTable) (range : ConvTagRange tbl) (coord : ℕ) (hc : coord < 2) (Δ : Block)
    (Z : ℕ → Block) (c : ℕ) (hcc : c < tbl.chunkCount) : AsksIn Small (chunkGarbleM tbl coord Δ Z c) := by
  have hw := range.chunkWidth c hcc
  have hC := range.chunkCount
  have hL := castAnswers_le tbl.castWidth
  unfold chunkGarbleM
  dsimp only
  refine asks_bind (asks_treeGarbleM _ _ _ _ fun n s hn hs => ?_) fun tree =>
    asks_bind (asks_tableM _ _ fun leaf => asks_castM _ _ _ fun j hj => ?_) fun _ => trivial
  · exact tagCode_lt fam_lt.1 ⟨hc, by omega, by omega, by omega, slot_lt (by omega) hs, by omega⟩
  · exact tagCode_lt fam_lt.2.1 ⟨hc, by omega, by omega, by omega, slot_lt hw leaf.isLt, by omega⟩

/-- **An odd modulus's conversion asks only small inputs.** -/
theorem asks_conversionGarbleM (coord i : ℕ) (row : OddRow) (m : ℕ) (Δ : Block) (word : Lanes row.ell)
    (hc : coord < 2) (hi : i < 128) (hrow : RowWF row) (hell : row.ell ≤ 15) (hm : m ≤ 65536) :
    AsksIn Small (conversionGarbleM coord i row m Δ word) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrow
  have hL0 := castAnswers_le row.ell
  have hL1 := castAnswers_le (row.ell - row.width0)
  unfold conversionGarbleM
  dsimp only
  refine asks_bind (asks_extStageGarbleM _ _ _ _ _ (fun n s hn hs => ?_) (fun leaf j hl hj => ?_)) fun g0 =>
    asks_bind (asks_extStageGarbleM _ _ _ _ _ (fun n s hn hs => ?_) (fun leaf j hl hj => ?_)) fun g1 =>
      asks_bind (asks_growGarbleM _ _ _ _ fun n s hn hs => ?_) fun grown =>
        asks_bind (asks_foldsGarbleM _ _ _ _ _ _ fun pos r hp hr => ?_) fun _ => trivial
  · exact tagCode_lt fam_lt.2.2.1 ⟨hc, hi, by omega, by omega, slot_lt (by omega) hs, by omega⟩
  · exact tagCode_lt fam_lt.2.2.2.1 ⟨hc, hi, by omega, by omega, slot_lt (by omega) hl, by omega⟩
  · exact tagCode_lt fam_lt.2.2.1 ⟨hc, hi, by omega, by omega, slot_lt (by omega) hs, by omega⟩
  · exact tagCode_lt fam_lt.2.2.2.1 ⟨hc, hi, by omega, by omega, slot_lt (by omega) hl, by omega⟩
  · exact tagCode_lt fam_lt.2.2.2.2.1 ⟨hc, hi, by omega, by omega, slot_lt (by omega) hs, by omega⟩
  · exact tagCode_lt fam_lt.2.2.2.2.2 ⟨hc, hi, by omega, by omega, by omega, by omega⟩

/-! ### The in-range published material depends on the hash through the chunks and conversions -/

theorem modGarbleM_zero (H : HashN) (tbl : CrtTable) (S coord : ℕ) (Δ : Block)
    (chunks : ℕ → ChunkGarbled tbl.castWidth) (i : Fin tbl.count) (hk : tbl.kind i = .chunkZero) :
    let g := (modGarbleM tbl S coord Δ chunks i).eval H
    g.stageJoins = (fun _ _ => 0) ∧ g.stagePins = (fun _ _ => 0) ∧ g.growJoins = (fun _ => 0) ∧
      g.foldJoins = (fun _ => 0) := by
  intro g
  simp only [g, modGarbleM, hk, FreeQuery.eval_bind, FreeQuery.eval_pure]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- The conversion fields of a modulus depend on the hash only through its conversion. -/
theorem modFields_congr (tbl : CrtTable) (S coord : ℕ) (Δ : Block) (chunks : ℕ → ChunkGarbled tbl.castWidth)
    (H H' : HashN) (hconv : ∀ (i : Fin tbl.count) (row : OddRow), tbl.kind i = .odd row → ∀ W : Lanes row.ell,
      (conversionGarbleM coord i.val row (tbl.modulus i) Δ W).eval H =
        (conversionGarbleM coord i.val row (tbl.modulus i) Δ W).eval H') (i : Fin tbl.count) :
    let g := (modGarbleM tbl S coord Δ chunks i).eval H
    let g' := (modGarbleM tbl S coord Δ chunks i).eval H'
    g.stageJoins = g'.stageJoins ∧ g.stagePins = g'.stagePins ∧ g.growJoins = g'.growJoins ∧
      g.foldJoins = g'.foldJoins := by
  intro g g'
  cases hk : tbl.kind i with
  | chunkZero =>
      obtain ⟨a1, a2, a3, a4⟩ := modGarbleM_zero H tbl S coord Δ chunks i hk
      obtain ⟨b1, b2, b3, b4⟩ := modGarbleM_zero H' tbl S coord Δ chunks i hk
      exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm⟩
  | odd row =>
      obtain ⟨a1, a2, a3, a4⟩ := modGarbleM_odd H tbl S coord Δ chunks i row hk
      obtain ⟨b1, b2, b3, b4⟩ := modGarbleM_odd H' tbl S coord Δ chunks i row hk
      rw [hconv i row hk] at a1 a2 a3 a4
      exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm⟩

/-- **The in-range published material of a coordinate** depends on the hash only through its chunks and its odd
moduli's conversions. -/
theorem readPub_congr (tbl : CrtTable) (S coord : ℕ) (Δ : Block) (Z : ℕ → Block) (H H' : HashN)
    (hchunk : ∀ c, c < tbl.chunkCount → (chunkGarbleM tbl coord Δ Z c).eval H = (chunkGarbleM tbl coord Δ Z c).eval H')
    (hconv : ∀ (i : Fin tbl.count) (row : OddRow), tbl.kind i = .odd row → ∀ W : Lanes row.ell,
      (conversionGarbleM coord i.val row (tbl.modulus i) Δ W).eval H =
        (conversionGarbleM coord i.val row (tbl.modulus i) Δ W).eval H') :
    readPub tbl ((coordGarbleM tbl S coord Δ Z).eval H).pub = readPub tbl ((coordGarbleM tbl S coord Δ Z).eval H').pub := by
  have pH := coord_pub H tbl S coord Δ Z
  have pH' := coord_pub H' tbl S coord Δ Z
  dsimp only at pH pH'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pH
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := pH'
  have hchunks : atNat (fun c : Fin tbl.chunkCount => (chunkGarbleM tbl coord Δ Z c.val).eval H)
      (ChunkGarbled.empty _) = atNat (fun c : Fin tbl.chunkCount => (chunkGarbleM tbl coord Δ Z c.val).eval H')
      (ChunkGarbled.empty _) := by
    funext c
    unfold atNat
    split
    · exact hchunk c ‹_›
    · rfl
  rw [← hchunks] at d3 d4 d5 d6
  unfold readPub
  congr 1
  · congr 1
    · funext c k
      rw [c1 c.val c.isLt, d1 c.val c.isLt, hchunk c.val c.isLt]
    · funext c
      congr 1
      funext j
      rw [c2 c.val c.isLt, d2 c.val c.isLt, hchunk c.val c.isLt]
  · funext i
    obtain ⟨e1, e2, e3, e4⟩ := modFields_congr tbl S coord Δ _ H H' hconv i
    unfold readMod
    simp only [c3 i.val i.isLt, d3 i.val i.isLt, c4 i.val i.isLt, d4 i.val i.isLt, c5 i.val i.isLt,
      d5 i.val i.isLt, c6 i.val i.isLt, d6 i.val i.isLt]
    rw [e1, e2, e3, e4]

/-! ### The real table -/

theorem modulus_gt : 2 ^ 168 < BN254.baseFieldModulus := by
  unfold BN254.baseFieldModulus
  norm_num

/-- **Below `2 ^ 168` the scheme's reading of the table oracle is `tableHash (tagRead A)`.** -/
theorem schemeHash_small {FI EI : Type} (A : TagTable) (n : ℕ) (hn : Small n) :
    schemeHash (Kriterion.CRT.Privacy.tableOracle (FI := FI) (EI := EI) A) n = tableHash (tagRead A) n := by
  have hp : n < BN254.baseFieldModulus := lt_trans hn modulus_gt
  have hval : ((n : BN254.BaseField)).val = n := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hp]
  show A (tagOfInput (n : BN254.BaseField)) = A _
  congr 1
  apply Fin.ext
  show ((n : BN254.BaseField)).val / 2 ^ 128 % 2 ^ 40 = n / 2 ^ 128 % 2 ^ 40
  rw [hval]

/-- **On the real table the garbler's in-range conversion material reads the table oracle as
`tableHash (tagRead A)`.** -/
theorem real_readPub {FI EI : Type} (A : TagTable) (S coord : ℕ) (hc : coord < 2) (Δ : Block) (Z : ℕ → Block) :
    readPub bn254Table ((coordGarbleM bn254Table S coord Δ Z).eval
        (schemeHash (Kriterion.CRT.Privacy.tableOracle (FI := FI) (EI := EI) A))).pub =
      readPub bn254Table ((coordGarbleM bn254Table S coord Δ Z).eval (tableHash (tagRead A))).pub := by
  have agree : ∀ n, Small n → schemeHash (Kriterion.CRT.Privacy.tableOracle (FI := FI) (EI := EI) A) n = tableHash (tagRead A) n :=
    fun n hn => schemeHash_small A n hn
  apply readPub_congr
  · intro c hcc
    exact eval_congr _ (asks_chunkGarbleM bn254Table bn254Table_range coord hc Δ Z c hcc) agree
  · intro i row hk W
    obtain ⟨wf, _⟩ := bn254Table_wf.rows i row hk
    have hell : row.ell ≤ 15 := by
      have e := bn254Table_range.ell i
      rw [hk, Kriterion.CRT.Privacy.Conv.rowOf_odd row _ wf (bn254Table_wf.rows i row hk).2] at e
      exact e
    have hi : i.val < 128 := lt_of_lt_of_le i.isLt bn254Table_range.count
    exact eval_congr _ (asks_conversionGarbleM coord i.val row _ Δ W hc hi wf hell (bn254Table_range.modulus i)) agree

end

end Kriterion.CRT.Privacy.Asks
