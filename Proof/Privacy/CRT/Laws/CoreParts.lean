/-
**The composition of H8's core row, the parts** (for `Core/CoreBelow.lean`).

A view of the CRT entry at `u` is determined by five parts: the conversion material of `x` and of `y`, the exception
entries, the rest (the labels and the table at the visible tags of families `0` to `5` and `8`) and the P45 part
`bmrPart` (curve and row constants, records, the table at the visible tags of families `6`, `7`, `10`): the visible
tags are exactly those two kinds (`visTag_families`).

* `viewParts`, `viewParts_injective`;
* `map_apply_eq_of_iff`: two pushforwards agree at two points with the same preimage;
* **`realCore_factor`**: the real view law at `some v` is the product of the four split parts' ideal laws and the real
  P45 marginal, from the four splits and the `ReadsOff` side conditions of the parts that remain after each split.
-/

import Proof.Privacy.CRT.Core.H8

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-! ### 1. The five parts of a view -/

/-- A visible tag is of family `0` to `8` or `10`, never `9` or above `10`. -/
theorem visTag_families (T : CrtTable) (u : AffineInput) (tag : ℕ) (visible : visTag T u tag = true) :
    (tagFamily tag ≤ 5 ∨ tagFamily tag = 8) ∨ (tagFamily tag = 6 ∨ tagFamily tag = 7 ∨ tagFamily tag = 10) := by
  unfold visTag at visible
  split at visible <;> first | omega | simp at visible

/-- The rest part of a view: the labels and the table at the rest tags. -/
abbrev RestPart (T : CrtTable) (u : AffineInput) := LamportSignature × (RestTags T u → Block × Block)

/-- The P45 part's type. -/
abbrev BmrPartT (T : CrtTable) (u : AffineInput) :=
  (BaseField × BaseField × BaseField) × Vector RowGamma digitCount ×
    Vector Kriterion.CRT.Entry.Record Kriterion.CRT.Entry.xCount ×
    Vector Kriterion.CRT.Entry.Record Kriterion.CRT.Entry.yCount × (BmrTags T u → Block × Block)

/-- The rest part of a view. -/
def restOf (T : CrtTable) (u : AffineInput) (v : CoreView crtEntry T u) : RestPart T u :=
  (v.2.1, fun tag => v.2.2 tag.1)

/-- **The five parts of a view.** -/
def viewParts (T : CrtTable) (u : AffineInput) (v : CoreView crtEntry T u) :
    Vector Block Kriterion.CRT.Entry.convCount × Vector Block Kriterion.CRT.Entry.convCount ×
      Vector Exception.Entry digitCount × RestPart T u × BmrPartT T u :=
  (v.1.crtX, v.1.crtY, v.1.exception, restOf T u v, bmrPart T u v)

theorem viewParts_injective (T : CrtTable) (u : AffineInput) : Function.Injective (viewParts T u) := by
  intro v w same
  have hx : v.1.crtX = w.1.crtX := congrArg (fun q => q.1) same
  have hy : v.1.crtY = w.1.crtY := congrArg (fun q => q.2.1) same
  have he : v.1.exception = w.1.exception := congrArg (fun q => q.2.2.1) same
  have hr : restOf T u v = restOf T u w := congrArg (fun q => q.2.2.2.1) same
  have hb : bmrPart T u v = bmrPart T u w := congrArg (fun q => q.2.2.2.2) same
  have hl : v.2.1 = w.2.1 := congrArg (fun q : RestPart T u => q.1) hr
  have hrest : (fun tag : RestTags T u => v.2.2 tag.1) = fun tag => w.2.2 tag.1 :=
    congrArg (fun q : RestPart T u => q.2) hr
  have hcurve : v.1.curve = w.1.curve := congrArg (fun q => q.1) hb
  have hrows : v.1.rows = w.1.rows := congrArg (fun q => q.2.1) hb
  have hrecX : v.1.recX = w.1.recX := congrArg (fun q => q.2.2.1) hb
  have hrecY : v.1.recY = w.1.recY := congrArg (fun q => q.2.2.2.1) hb
  have hbmr : (fun tag : BmrTags T u => v.2.2 tag.1) = fun tag => w.2.2 tag.1 := congrArg (fun q => q.2.2.2.2) hb
  obtain ⟨⟨c, r, e, x, y, rx, ry⟩, l, tb⟩ := v
  obtain ⟨⟨c', r', e', x', y', rx', ry'⟩, l', tb'⟩ := w
  simp only at hx hy he hl hcurve hrows hrecX hrecY
  subst hx hy he hl hcurve hrows hrecX hrecY
  refine Prod.ext rfl (Prod.ext rfl (funext fun tag => ?_))
  rcases visTag_families T u tag.1.val tag.2 with restTag | bmrTag
  · exact congrFun hrest ⟨tag, restTag⟩
  · exact congrFun hbmr ⟨tag, bmrTag⟩

theorem viewParts_eq_iff (T : CrtTable) (u : AffineInput) (v w : CoreView crtEntry T u) :
    v = w ↔ viewParts T u v = viewParts T u w :=
  ⟨congrArg _, fun h => viewParts_injective T u h⟩

/-- **Two pushforwards agree at two points with the same preimage.** -/
theorem map_apply_eq_of_iff {Ω A B : Type} (μ : PMF Ω) (f : Ω → A) (g : Ω → B) (a : A) (b : B)
    (h : ∀ ω, f ω = a ↔ g ω = b) : (μ.map f) a = (μ.map g) b := by
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun ω => ?_
  by_cases hω : f ω = a
  · rw [if_pos hω.symm, if_pos ((h ω).mp hω).symm]
  · rw [if_neg (fun e => hω e.symm), if_neg (fun e => hω ((h ω).mpr e.symm))]

/-! ### 2. The real side

Every statement below names the real garbling `realGarbled crtEntry parameter scalar tape` only as an opaque value:
its projections are never reduced (that would evaluate the garbler), and the facts about views are proved for an
arbitrary garbled value `g` and instantiated by unification. -/

/-- A view given as a triple has the parts of its components. -/
theorem tuple_eq_iff (T : CrtTable) (u : AffineInput) (g : crtEntry.Public × crtEntry.Key) (enc : LamportSignature)
    (tb : VisTags T u → Block × Block) (v : CoreView crtEntry T u) :
    ((g.1, enc, tb) : CoreView crtEntry T u) = v ↔
      g.1.crtX = v.1.crtX ∧ g.1.crtY = v.1.crtY ∧ g.1.exception = v.1.exception ∧
        ((enc, fun tag : RestTags T u => tb tag.1) : RestPart T u) = restOf T u v ∧
          ((g.1.curve, g.1.rows, g.1.recX, g.1.recY, fun tag : BmrTags T u => tb tag.1) : BmrPartT T u) =
            bmrPart T u v := by
  rw [viewParts_eq_iff]
  simp only [viewParts, restOf, bmrPart, Prod.mk.injEq]

theorem bmrPart_tuple (T : CrtTable) (u : AffineInput) (g : crtEntry.Public × crtEntry.Key) (enc : LamportSignature)
    (tb : VisTags T u → Block × Block) :
    bmrPart T u ((g.1, enc, tb) : CoreView crtEntry T u) =
      (g.1.curve, g.1.rows, g.1.recX, g.1.recY, fun tag : BmrTags T u => tb tag.1) := rfl

section Real

variable [FieldCertificate] [GroupCertificate]

/-- The real view as a triple (by definition). -/
theorem realView_def (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (tape : TableTape crtEntry) :
    realView crtEntry T parameter scalar u tape =
      ((realGarbled crtEntry parameter scalar tape).1,
        (crtEntry.scheme inferInstance inferInstance).encode (realGarbled crtEntry parameter scalar tape).2 u,
        fun tag => tape.2 tag.1) := rfl

/-- The real P45 part of a tape. -/
def realBmr (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape crtEntry) :
    BmrPartT T u :=
  ((realGarbled crtEntry parameter scalar tape).1.curve, (realGarbled crtEntry parameter scalar tape).1.rows,
    (realGarbled crtEntry parameter scalar tape).1.recX, (realGarbled crtEntry parameter scalar tape).1.recY,
    fun tag : BmrTags T u => tape.2 tag.1.1)

/-- The real rest part of a tape. -/
def realRest (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape crtEntry) :
    RestPart T u :=
  ((crtEntry.scheme inferInstance inferInstance).encode (realGarbled crtEntry parameter scalar tape).2 u,
    fun tag : RestTags T u => tape.2 tag.1.1)

theorem realView_eq_iff (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (tape : TableTape crtEntry) (v : CoreView crtEntry T u) :
    realView crtEntry T parameter scalar u tape = v ↔
      (realGarbled crtEntry parameter scalar tape).1.crtX = v.1.crtX ∧
        (realGarbled crtEntry parameter scalar tape).1.crtY = v.1.crtY ∧
        (realGarbled crtEntry parameter scalar tape).1.exception = v.1.exception ∧
        realRest T parameter scalar u tape = restOf T u v ∧ realBmr T parameter scalar u tape = bmrPart T u v := by
  rw [realView_def]
  exact tuple_eq_iff T u _ _ _ v

theorem bmrPart_realView (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (tape : TableTape crtEntry) :
    bmrPart T u (realView crtEntry T parameter scalar u tape) = realBmr T parameter scalar u tape := by
  rw [realView_def]
  exact bmrPart_tuple T u _ _ _

open Classical in
/-- The real P45 marginal is the law of the real P45 part off doubling. -/
theorem realBmr_marginal (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (b : BmrPartT T u) :
    ((realCore crtEntry T parameter scalar u).map (Option.map (bmrPart T u))) (some b) =
      ((swappedTableTape crtEntry).map fun tape =>
        if Doubling crtEntry scalar tape u then none else some (realBmr T parameter scalar u tape)) (some b) := by
  unfold realCore
  rw [PMF.map_comp]
  refine map_apply_eq_of_iff _ _ _ _ _ fun tape => ?_
  by_cases D : Doubling crtEntry scalar tape u
  · simp only [Function.comp_apply, if_pos D, Option.map_none, reduceCtorEq]
  · simp only [Function.comp_apply, if_neg D, Option.map_some, Option.some.injEq]
    rw [bmrPart_realView]

open Classical in
/-- **The real view law factors**: at `some v`, the real view law is the product of the ideal laws of the conversion
materials, the exception entries and the rest part, and the real P45 marginal. The side conditions are the reads of
the parts that remain after each split. -/
theorem realCore_factor (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (convX : CrtConvSplit T 0) (convY : CrtConvSplit T 1) (digest : CrtDigestSplit) (rest : CrtRestSplit T)
    (reads₁ : ReadsOff Eq (hotConvTag T u 0) fun tape =>
      if Doubling crtEntry scalar tape u then none
      else some ((realGarbled crtEntry parameter scalar tape).1.crtY,
        (realGarbled crtEntry parameter scalar tape).1.exception, realRest T parameter scalar u tape,
        realBmr T parameter scalar u tape))
    (reads₂ : ReadsOff Eq (hotConvTag T u 1) fun tape =>
      if Doubling crtEntry scalar tape u then none
      else some ((realGarbled crtEntry parameter scalar tape).1.exception, realRest T parameter scalar u tape,
        realBmr T parameter scalar u tape))
    (reads₃ : ReadsOff SameOffExceptionPad (hiddenDigestTag u) fun tape =>
      (realRest T parameter scalar u tape, realBmr T parameter scalar u tape))
    (reads₄ : ReadsOff SameOffLabels (fun tag => visTag T u tag.val = true ∧ (tagFamily tag.val ≤ 5 ∨
      tagFamily tag.val = 8)) fun tape => realBmr T parameter scalar u tape)
    (v : CoreView crtEntry T u) :
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    realCore crtEntry T parameter scalar u (some v) =
      ((PMF.uniformOfFintype (view).Source).map fun source =>
          if (0 : Fin 2) = 0 then ((view).publish source).crtX else ((view).publish source).crtY) v.1.crtX *
        (((PMF.uniformOfFintype (view).Source).map fun source =>
          if (1 : Fin 2) = 0 then ((view).publish source).crtX else ((view).publish source).crtY) v.1.crtY *
        (((PMF.uniformOfFintype (view).Source).map fun source => ((view).publish source).exception) v.1.exception *
        (((PMF.uniformOfFintype (view).Source).bind fun source =>
          (swappedTableLaw crtLayout).map fun table => ((view).labels source u, fun tag : RestTags T u => table tag.1.1))
            (restOf T u v) *
        ((realCore crtEntry T parameter scalar u).map (Option.map (bmrPart T u))) (some (bmrPart T u v))))) := by
  have e₁ := convX parameter scalar u _ reads₁ v.1.crtX (some (v.1.crtY, v.1.exception, restOf T u v, bmrPart T u v))
  have e₂ := convY parameter scalar u _ reads₂ v.1.crtY (some (v.1.exception, restOf T u v, bmrPart T u v))
  have e₃ := digest parameter scalar u _ reads₃ v.1.exception (restOf T u v, bmrPart T u v)
  have e₄ := rest parameter scalar u _ reads₄ (restOf T u v) (bmrPart T u v)
  rw [realBmr_marginal]
  unfold realCore
  refine (map_apply_eq_of_iff _ _ _ _ _ fun tape => ?_).trans (e₁.trans (congrArg _
    ((map_apply_eq_of_iff _ _ _ _ _ fun tape => ?_).trans (e₂.trans (congrArg _
      ((map_apply_eq_of_iff _ _ _ _ _ fun tape => ?_).trans (e₃.trans (congrArg _ e₄))))))))
  · by_cases D : Doubling crtEntry scalar tape u
    · simp only [if_pos D, reduceCtorEq, if_neg not_false, Option.some.injEq, Prod.mk.injEq, and_false]
    · simp only [if_neg D, if_neg not_false, Option.some.injEq, Prod.mk.injEq]
      rw [realView_eq_iff]
      simp only [↓reduceIte]
  · have ne : ¬ ((1 : Fin 2) = 0) := by decide
    by_cases D : Doubling crtEntry scalar tape u
    · simp only [if_pos D, reduceCtorEq, if_neg not_false, Option.some.injEq, Prod.mk.injEq, and_false]
    · simp only [if_neg D, if_neg not_false, if_neg ne, Option.some.injEq, Prod.mk.injEq]
  · by_cases D : Doubling crtEntry scalar tape u
    · simp only [if_pos D, reduceCtorEq, if_neg not_false, Option.some.injEq]
    · simp only [if_neg D, if_neg not_false, Option.some.injEq]

end Real

/-! ### 3. The composition from the factorizations -/

open Classical in
/-- **The real reads** (named input): the parts that remain after each split read the tape off that split's hidden
tags and coins. -/
def RealReads (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    (ReadsOff Eq (hotConvTag T u 0) fun tape =>
      if Doubling crtEntry scalar tape u then none
      else some ((realGarbled crtEntry parameter scalar tape).1.crtY,
        (realGarbled crtEntry parameter scalar tape).1.exception, realRest T parameter scalar u tape,
        realBmr T parameter scalar u tape)) ∧
    (ReadsOff Eq (hotConvTag T u 1) fun tape =>
      if Doubling crtEntry scalar tape u then none
      else some ((realGarbled crtEntry parameter scalar tape).1.exception, realRest T parameter scalar u tape,
        realBmr T parameter scalar u tape)) ∧
    (ReadsOff SameOffExceptionPad (hiddenDigestTag u) fun tape =>
      (realRest T parameter scalar u tape, realBmr T parameter scalar u tape)) ∧
    ReadsOff SameOffLabels (fun tag => visTag T u tag.val = true ∧ (tagFamily tag.val ≤ 5 ∨ tagFamily tag.val = 8))
      fun tape => realBmr T parameter scalar u tape

/-- **The ideal view law factors on the curve** (named input): the product of the same four ideal laws and the ideal
P45 marginal. -/
def IdealFactorOn (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
    (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q → ∀ v : CoreView crtEntry T u,
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    idealCore crtEntry T crtRevealOn scalar u Q (some v) =
      ((PMF.uniformOfFintype (view).Source).map fun source =>
          if (0 : Fin 2) = 0 then ((view).publish source).crtX else ((view).publish source).crtY) v.1.crtX *
        (((PMF.uniformOfFintype (view).Source).map fun source =>
          if (1 : Fin 2) = 0 then ((view).publish source).crtX else ((view).publish source).crtY) v.1.crtY *
        (((PMF.uniformOfFintype (view).Source).map fun source => ((view).publish source).exception) v.1.exception *
        (((PMF.uniformOfFintype (view).Source).bind fun source =>
          (swappedTableLaw crtLayout).map fun table => ((view).labels source u, fun tag : RestTags T u => table tag.1.1))
            (restOf T u v) *
        ((idealCore crtEntry T crtRevealOn scalar u Q).map (Option.map (bmrPart T u))) (some (bmrPart T u v)))))

/-- **The ideal view law factors off the curve** (named input). -/
def IdealFactorOff (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput),
    (crtEntry.scheme inferInstance inferInstance).function scalar u = none → ∀ v : CoreView crtEntry T u,
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    idealCoreOff crtEntry T crtRevealOff u (some v) =
      ((PMF.uniformOfFintype (view).Source).map fun source =>
          if (0 : Fin 2) = 0 then ((view).publish source).crtX else ((view).publish source).crtY) v.1.crtX *
        (((PMF.uniformOfFintype (view).Source).map fun source =>
          if (1 : Fin 2) = 0 then ((view).publish source).crtX else ((view).publish source).crtY) v.1.crtY *
        (((PMF.uniformOfFintype (view).Source).map fun source => ((view).publish source).exception) v.1.exception *
        (((PMF.uniformOfFintype (view).Source).bind fun source =>
          (swappedTableLaw crtLayout).map fun table => ((view).labels source u, fun tag : RestTags T u => table tag.1.1))
            (restOf T u v) *
        ((idealCoreOff crtEntry T crtRevealOff u).map (Option.map (bmrPart T u))) (some (bmrPart T u v)))))

/-- **The core row from the splits, P45 on and off the curve, the reads and the ideal factorizations.** -/
theorem coreBelow_of_factors (T : CrtTable) (convX : CrtConvSplit T 0) (convY : CrtConvSplit T 1)
    (digest : CrtDigestSplit) (bmr : CrtBmrSplit T) (bmrOff : CrtBmrSplitOff T) (rest : CrtRestSplit T)
    (reads : RealReads T) (on : IdealFactorOn T) (off : IdealFactorOff T) :
    CrtCoreBelow crtEntry T crtRevealOn crtRevealOff := by
  intro _ _ parameter scalar u v
  obtain ⟨r₁, r₂, r₃, r₄⟩ := reads parameter scalar u
  rw [realCore_factor T parameter scalar u convX convY digest rest r₁ r₂ r₃ r₄ v]
  unfold idealAt
  cases output : (crtEntry.scheme inferInstance inferInstance).function scalar u with
  | some Q =>
      dsimp only
      rw [on scalar u Q output v]
      gcongr
      exact bmr parameter scalar u Q output (bmrPart T u v)
  | none =>
      dsimp only
      rw [off scalar u output v]
      gcongr
      exact bmrOff parameter scalar u output (bmrPart T u v)

end

end Kriterion.CRT.Privacy.Laws
