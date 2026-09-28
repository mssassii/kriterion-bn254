/-
**The extraction-stage instance on the construction's own definition** (`Construction/CRT/ExtractSpec.lean`).

`ExtractSpec.StageParams rb` is one fused stage with its tree material `mat level slot label` and its leaf cast
`castF leaf label`; the garbler is `gNode`, `gJoin`, `gPin`. The hidden tuple `(y_1, ..., y_{w-1}, A_s)` of the
privacy core enters by overriding the stage's answers at the hot positions of the stage value `s`
(`overrideHot`): `mat n x _` becomes `y_n` at the hot slot `x = s mod 2 ^ n`, and `castF s _` becomes `A_s`. On
the answer-table reading (`mat n x lab = (clip (T (treeTag n x)).1)`, `Kriterion.CRT.tableHash`) this is exactly
`Function.update` of the table at the hot tags.

* `spec_publish_eq`: the published joins and pin of the overridden stage are `publish (specFrame sp R Δ) s h`, the
  map of `Proof.Privacy.CRT.Core.ExtractStage`;
* `spec_publish_injective`, `spec_stage_uniform`: hence the stage publishes an injective, uniform image of its
  hidden tuple, for every `mat`, `castF`, `R`, `Δ` (the instance of the left-inverse inversion lemma);
* `spec_garbler_eq_publish`: the garbler itself, not overridden, is the overridden stage at the hidden tuple it
  answers at its own hot positions (`hiddenOfSpec`), so the law statement applies to the real garbler.

Needs `1 ≤ sp.w` (the stages of table T9 have widths 7 and `ℓ − 8 ≥ 2`).
-/

import Construction.CRT.ExtractSpec
import Proof.Privacy.CRT.Core.ExtractStage
import Proof.Privacy.CRT.Core.LabelUniform

namespace Kriterion.CRT.Privacy.ExtractStage

open Cryptography
open Kriterion.CRT.ExtractSpec (StageParams stepMat gNode gBit0 gLeaf gCast gRes gBit gLevelSum gJoin gPin xsum)

variable {rb : ℕ}

/-! ### The shared definitions agree at 104 lanes -/

theorem laneBit_eq_crt {l : ℕ} (A : Lanes labelBits l) (n : ℕ) : laneBit A n = Kriterion.CRT.laneBit A n := rfl

theorem reduceTo_eq_crt {l : ℕ} (w : ℕ) (A : Lanes labelBits l) :
    reduceTo w A = Kriterion.CRT.reduceTo w A := rfl

theorem deltaLanes_eq_crt (l : ℕ) (Δ : Label) : deltaLanes l Δ = Kriterion.CRT.deltaLanes l Δ := rfl

theorem xsum_range_eq (f : ℕ → Label) : ∀ K, xsum (Finset.range K) f = xorUpTo f K
  | 0 => rfl
  | K + 1 => by
      have ih := xsum_range_eq f K
      unfold xsum at ih ⊢
      rw [Finset.range_add_one, Finset.fold_insert Finset.notMem_range_self, ih]
      show f K ^^^ xorUpTo f K = xorUpTo f K ^^^ f K
      exact BitVec.xor_comm _ _

theorem xorUpTo_congr {L : ℕ} (f g : ℕ → BitVec L) :
    ∀ K, (∀ i < K, f i = g i) → xorUpTo f K = xorUpTo g K
  | 0, _ => rfl
  | K + 1, same => by
      simp only [xorUpTo, xorUpTo_congr f g K (fun i hi => same i (Nat.lt_succ_of_lt hi)),
        same K (Nat.lt_succ_self K)]

/-- Below `2 ^ (i + 1)`, bit `i` is set exactly from `2 ^ i` on. -/
theorem testBit_top {x i : ℕ} (lt : x < 2 ^ (i + 1)) : x.testBit i = decide (2 ^ i ≤ x) := by
  by_cases ge : 2 ^ i ≤ x
  · have split : x = 2 ^ i + (x - 2 ^ i) := (Nat.add_sub_cancel' ge).symm
    have small : x - 2 ^ i < 2 ^ i := by rw [pow_succ] at lt; omega
    rw [split, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow small, decide_eq_true (by omega)]
    rfl
  · rw [Nat.testBit_lt_two_pow (by omega), decide_eq_false ge]

theorem mod_top {x i : ℕ} (lt : x < 2 ^ (i + 1)) :
    x % 2 ^ i = if x < 2 ^ i then x else x - 2 ^ i := by
  split_ifs with small
  · exact Nat.mod_eq_of_lt small
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by rw [pow_succ] at lt; omega)]

/-! ### The overridden stage and its frame -/

/-- The stage with its answers at the hot positions of `s` replaced by the hidden tuple. -/
def overrideHot (sp : StageParams rb) (s : ℕ) (h : Hidden labelBits sp.w rb) : StageParams rb where
  w := sp.w
  hw := sp.hw
  mat n x lab := if x = s % 2 ^ n then hot (w := sp.w) h.1 (n - 1) else sp.mat n x lab
  castF α lab := if α = s then h.2 else sp.castF α lab

/-- The frame of `ExtractStage` read from the stage: `sub = reduce_w R`, `Δ`, the cold answers `mat` and `castF`. -/
def specFrame (sp : StageParams rb) (R : Kriterion.CRT.Lanes rb) (Δ : Label) : Frame labelBits sp.w rb where
  sub := Kriterion.CRT.reduceTo sp.w R
  delta := Δ
  tree := sp.mat
  cast := sp.castF

section Override

variable (sp : StageParams rb) (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s : ℕ) (h : Hidden labelBits sp.w rb)

theorem gBit0_override : gBit0 (overrideHot sp s h) R = bit0 (specFrame sp R Δ) := rfl

/-- The garbler's nodes of the overridden stage are the labels of `ExtractStage.level`, on range. -/
theorem gNode_override :
    ∀ k, ∀ x < 2 ^ (k + 1),
      gNode (overrideHot sp s h) (gBit0 (overrideHot sp s h) R) Δ (k + 1) x
        = level (specFrame sp R Δ) s h.1 k x
  | 0, x, hx => by
      have hx' : x = 0 ∨ x = 1 := by omega
      rcases hx' with rfl | rfl
      · show (if Nat.testBit 0 0 = true then _ else _) = _
        simp only [Nat.testBit_zero, stepMat, gNode, level, if_true, gBit0_override sp R Δ s h]
        exact BitVec.xor_comm _ _
      · show (if Nat.testBit 1 0 = true then _ else _) = _
        simp only [Nat.testBit_zero, decide_true, if_true, stepMat, level, one_ne_zero, if_false,
          gBit0_override sp R Δ s h]
  | k + 1, x, hx => by
      have ih := gNode_override k
      have top := testBit_top hx
      have md := mod_top hx
      show (if x.testBit (k + 1) = true then _ else _) = level (specFrame sp R Δ) s h.1 (k + 1) x
      simp only [level]
      rw [top]
      by_cases small : x < 2 ^ (k + 1)
      · have nb : ¬ (2 ^ (k + 1) ≤ x) := by omega
        rw [md, if_pos small, if_pos small, decide_eq_false nb]
        simp only [Bool.false_eq_true, if_false, stepMat]
        rw [ih x small]
        simp only [overrideHot, material, specFrame, Nat.add_sub_cancel]
      · have nb : 2 ^ (k + 1) ≤ x := by omega
        have t_lt : x - 2 ^ (k + 1) < 2 ^ (k + 1) := by rw [pow_succ] at hx; omega
        rw [md, if_neg small, if_neg small, decide_eq_true nb]
        simp only [if_true, stepMat]
        rw [ih _ t_lt]
        simp only [overrideHot, material, specFrame, Nat.add_sub_cancel]

theorem gCast_override (hw1 : 1 ≤ sp.w) (α : ℕ) (hα : α < 2 ^ sp.w) :
    gCast (overrideHot sp s h) R Δ α = castAt (specFrame sp R Δ) s h α := by
  have e : sp.w - 1 + 1 = sp.w := Nat.sub_add_cancel hw1
  have node := gNode_override sp R Δ s h (sp.w - 1) α (by rw [e]; exact hα)
  rw [e] at node
  unfold gCast gLeaf castAt
  show (if α = s then h.2 else sp.castF α _) = (if α = s then h.2 else sp.castF α _)
  rw [show (overrideHot sp s h).w = sp.w from rfl, node]

/-- **The bridge.** The joins `J_1 .. J_{w-1}` and the pin of the overridden stage are `publish` of its frame at
the hidden tuple. -/
theorem spec_publish_eq (hw1 : 1 ≤ sp.w) :
    ((fun k : Fin (sp.w - 1) => gJoin (overrideHot sp s h) R Δ (k.val + 1)), gPin (overrideHot sp s h) R Δ)
      = publish (specFrame sp R Δ) s h := by
  have casts : ∀ α ∈ Finset.range (2 ^ sp.w),
      gCast (overrideHot sp s h) R Δ α = castAt (specFrame sp R Δ) s h α :=
    fun α hα => gCast_override sp R Δ s h hw1 α (Finset.mem_range.mp hα)
  have res : ∀ n, gRes (overrideHot sp s h) R Δ n = classSum (specFrame sp R Δ) s h n := by
    intro n
    unfold gRes classSum
    exact Finset.sum_congr rfl fun α hα => by rw [casts α hα]
  refine Prod.ext ?_ ?_
  · funext k
    show gLevelSum (overrideHot sp s h) R Δ (k.val + 1) ^^^ gBit (overrideHot sp s h) R Δ (k.val + 1)
      = levelSum (specFrame sp R Δ) s h k.val ^^^ bitMask (specFrame sp R Δ) s h (k.val + 1)
    have bits : gBit (overrideHot sp s h) R Δ (k.val + 1) = bitMask (specFrame sp R Δ) s h (k.val + 1) := by
      unfold gBit bitMask
      rw [if_neg (Nat.succ_ne_zero _), res]
      rfl
    have sums : gLevelSum (overrideHot sp s h) R Δ (k.val + 1) = levelSum (specFrame sp R Δ) s h k.val := by
      unfold gLevelSum levelSum
      rw [xsum_range_eq]
      refine xorUpTo_congr _ _ _ fun x hx => ?_
      rw [gNode_override sp R Δ s h k.val x hx]
      simp only [overrideHot, material, specFrame, Nat.add_sub_cancel]
    rw [bits, sums]
  · show ∑ α ∈ Finset.range (2 ^ sp.w), gCast (overrideHot sp s h) R Δ α + Kriterion.CRT.deltaLanes rb Δ
      = castSum (specFrame sp R Δ) s h + deltaLanes rb Δ
    unfold castSum
    rw [Finset.sum_congr rfl casts]
    rfl

end Override

/-! ### The instance of the inversion lemma, on the construction's stage -/

/-- The published tuple of a stage whose hot answers are the hidden tuple. -/
def specPublish (sp : StageParams rb) (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s : ℕ)
    (h : Hidden labelBits sp.w rb) : Published labelBits sp.w rb :=
  ((fun k : Fin (sp.w - 1) => gJoin (overrideHot sp s h) R Δ (k.val + 1)), gPin (overrideHot sp s h) R Δ)

/-- **The construction's stage is injective in its hidden tuple.** -/
theorem spec_publish_injective (sp : StageParams rb) (hw1 : 1 ≤ sp.w) (R : Kriterion.CRT.Lanes rb) (Δ : Label)
    (s : ℕ) (hs : s < 2 ^ sp.w) : Function.Injective (specPublish sp R Δ s) := by
  intro h h' same
  have e : ∀ h, specPublish sp R Δ s h = publish (specFrame sp R Δ) s h :=
    fun h => spec_publish_eq sp R Δ s h hw1
  rw [e, e] at same
  exact publish_injective (specFrame sp R Δ) s hs same

/-- A stage of width `w` built from its answers. -/
def stageOf (w : ℕ) (hw : w ≤ rb) (mat : ℕ → ℕ → Label → Label) (castF : ℕ → Label → Kriterion.CRT.Lanes rb) :
    StageParams rb :=
  { w := w, hw := hw, mat := mat, castF := castF }

/-- **The construction's stage publishes a uniform tuple, independent of the rest.** Draw the stage's answers
(`mat`, `castF`), the remainder `R` and `Δ` from any law and the hidden tuple uniformly: the published joins and pin
of the stage with its hot answers overridden by the hidden tuple are uniform and independent of the rest. -/
theorem spec_stage_uniform {Rest : Type*} (rest : PMF Rest) (w : ℕ) (hw : w ≤ rb) (hw1 : 1 ≤ w)
    (matOf : Rest → ℕ → ℕ → Label → Label) (castOf : Rest → ℕ → Label → Kriterion.CRT.Lanes rb)
    (remOf : Rest → Kriterion.CRT.Lanes rb) (deltaOf : Rest → Label) (s : ℕ) (hs : s < 2 ^ w) :
    (rest.bind fun r => (PMF.uniformOfFintype (Hidden labelBits w rb)).map fun h =>
        (r, specPublish (stageOf w hw (matOf r) (castOf r)) (remOf r) (deltaOf r) s h))
      = rest.bind fun r => (PMF.uniformOfFintype (Published labelBits w rb)).map fun b => (r, b) :=
  bind_map_uniform_of_injective rest _
    (fun r => spec_publish_injective (stageOf w hw (matOf r) (castOf r)) hw1 (remOf r) (deltaOf r) s hs) rfl

/-! ### The real garbler is the overridden stage at its own hot answers -/

/-- The hidden tuple the stage's own answers give at the hot positions of `s`. -/
def hiddenOfSpec (sp : StageParams rb) (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s : ℕ) : Hidden labelBits sp.w rb :=
  (fun k => sp.mat (k.val + 1) (s % 2 ^ (k.val + 1)) (gNode sp (gBit0 sp R) Δ (k.val + 1) (s % 2 ^ (k.val + 1))),
    gCast sp R Δ s)

section Self

variable (sp : StageParams rb) (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s : ℕ)

theorem mat_override_self (m : ℕ) (hm : m + 1 < sp.w) (t : ℕ) :
    (overrideHot sp s (hiddenOfSpec sp R Δ s)).mat (m + 1) t (gNode sp (gBit0 sp R) Δ (m + 1) t)
      = sp.mat (m + 1) t (gNode sp (gBit0 sp R) Δ (m + 1) t) := by
  show (if t = s % 2 ^ (m + 1) then hot (w := sp.w) (hiddenOfSpec sp R Δ s).1 (m + 1 - 1) else _) = _
  split_ifs with ht
  · rw [ht, Nat.add_sub_cancel]
    simp only [hot, dif_pos (show m < sp.w - 1 by omega), hiddenOfSpec]
  · rfl

theorem gNode_override_self :
    ∀ n, n ≤ sp.w → ∀ x,
      gNode (overrideHot sp s (hiddenOfSpec sp R Δ s)) (gBit0 sp R) Δ n x = gNode sp (gBit0 sp R) Δ n x
  | 0, _, _ => rfl
  | 0 + 1, _, x => rfl
  | m + 1 + 1, hn, x => by
      have ih := gNode_override_self (m + 1) (by omega)
      show (if x.testBit (m + 1) = true then _ else _) = (if x.testBit (m + 1) = true then _ else _)
      simp only [stepMat, ih]
      rw [mat_override_self sp R Δ s m (by omega)]

/-- **The real garbler.** For every stage (every `mat`, `castF`, `R`, `Δ`) and every stage value `s`, the stage's
published joins and pin are `publish` of its frame at the hidden tuple of its own hot answers. -/
theorem spec_garbler_eq_publish (hw1 : 1 ≤ sp.w) :
    ((fun k : Fin (sp.w - 1) => gJoin sp R Δ (k.val + 1)), gPin sp R Δ)
      = publish (specFrame sp R Δ) s (hiddenOfSpec sp R Δ s) := by
  rw [← spec_publish_eq sp R Δ s (hiddenOfSpec sp R Δ s) hw1]
  have casts : ∀ α, gCast (overrideHot sp s (hiddenOfSpec sp R Δ s)) R Δ α = gCast sp R Δ α := by
    intro α
    unfold gCast gLeaf
    show (if α = s then _ else sp.castF α _) = _
    rw [show (overrideHot sp s (hiddenOfSpec sp R Δ s)).w = sp.w from rfl,
      show gBit0 (overrideHot sp s (hiddenOfSpec sp R Δ s)) R = gBit0 sp R from rfl,
      gNode_override_self sp R Δ s sp.w le_rfl α]
    split_ifs with hα
    · rw [hα]; rfl
    · rfl
  have res : ∀ n, gRes (overrideHot sp s (hiddenOfSpec sp R Δ s)) R Δ n = gRes sp R Δ n := fun n =>
    Finset.sum_congr rfl fun α _ => by rw [casts α]
  refine Prod.ext ?_ ?_
  · funext k
    show gLevelSum sp R Δ (k.val + 1) ^^^ gBit sp R Δ (k.val + 1)
      = gLevelSum (overrideHot sp s (hiddenOfSpec sp R Δ s)) R Δ (k.val + 1)
        ^^^ gBit (overrideHot sp s (hiddenOfSpec sp R Δ s)) R Δ (k.val + 1)
    have bits : gBit (overrideHot sp s (hiddenOfSpec sp R Δ s)) R Δ (k.val + 1) = gBit sp R Δ (k.val + 1) := by
      unfold gBit
      rw [if_neg (Nat.succ_ne_zero _), if_neg (Nat.succ_ne_zero _), res]
      rfl
    have sums : gLevelSum (overrideHot sp s (hiddenOfSpec sp R Δ s)) R Δ (k.val + 1)
        = gLevelSum sp R Δ (k.val + 1) := by
      unfold gLevelSum
      congr 1
      funext x
      rw [show gBit0 (overrideHot sp s (hiddenOfSpec sp R Δ s)) R = gBit0 sp R from rfl,
        gNode_override_self sp R Δ s (k.val + 1) (by omega) x,
        mat_override_self sp R Δ s k.val (by omega) x]
    rw [bits, sums]
  · show ∑ α ∈ Finset.range (2 ^ sp.w), gCast sp R Δ α + _
      = ∑ α ∈ Finset.range (2 ^ sp.w), gCast (overrideHot sp s (hiddenOfSpec sp R Δ s)) R Δ α + _
    rw [Finset.sum_congr rfl fun α _ => casts α]

end Self

end Kriterion.CRT.Privacy.ExtractStage
