/-
**`CrtBmrSplit` for the CRT entry, on the curve** (H8's P45 row).

The P45 part of a view (`H8.bmrPart`: curve and row constants, records, the answers at the visible body, mask and key
tags) is, on either side, a published part computed from a P45 output (`BMR.Out`), and answers drawn from the swapped
table's kernel given the visible targets (cold pads and masks). So `CrtBmrSplit` follows from four statements:

* `TableKernel` (`Swap/Product.lean`): the swapped table is uniform targets followed by a kernel; the
  kernel's answers at the visible P45 tags depend only on the visible targets.
* `RealReading K`: `G1U°`'s P45 part is, under uniform coins and targets, the published part of
  `BMR.realOut` at `bmrCoinsWith coins τ` with the kernel's answers, flagged on doubling (`BmrEntry`'s reading).
* `IdealReading K`: `M'`'s P45 part is, under uniform coins (for the rows kernel) and uniform P45
  cells, the published part of `BMR.idealOut` with the kernel's answers, flagged by the P45 reveal (doubling of the
  true rows, or a CRT value in the two-sided window).
* `CoinsSplit`: under uniform coins, the layer coins (`r4`, the unused randomizers, the curve coins)
  are uniform and independent of the context part (offsets and `ρ`).

`crtBmrSplit_of` composes them with `BMR.core_below` (the P45 core with the window flag, proved) and
`BmrEntry.rowsDoubling_of_doubling` (proved).
-/

import Proof.Privacy.CRT.Core.BmrEntry
import Proof.Privacy.CRT.Core.BmrNorm
import Proof.Privacy.CRT.Flags.Wrap

namespace Kriterion.CRT.Privacy.BmrSplit

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-- The entry's table. -/
abbrev Tb : CrtTable := Kriterion.CRT.Entry.table

/-! ### 1. Targets and the kernel of the swapped table -/

/-- The targets of the body and mask sites: every pad value and every mask. -/
abbrev Targets := BMR.Pads Tb × (BMR.RowEnc → BaseField)

/-- The answers a table shows at the visible P45 tags. -/
def restrictBmr (u : AffineInput) (table : TagTable) : H8.BmrTags Tb u → Block × Block := fun tag => table tag.1.1

/-- The cold pads of a pad vector at `u`. -/
def coldOfPads (u : AffineInput) (pads : BMR.Pads Tb) : BMR.Cold Tb u := fun i e ρ => pads i ρ.1 e

/-- **The swapped table as uniform targets and a kernel**. -/
structure TableKernel where
  given : Targets → PMF TagTable
  law : swappedTableLaw crtLayout = (PMF.uniformOfFintype Targets).bind given
  reads : ∀ τ, ∀ table ∈ (given τ).support, BmrEntry.bmrPadsOf table = τ.1 ∧ BmrEntry.bmrMasksOf table = τ.2
  visible : ∀ (u : AffineInput) (τ τ' : Targets), coldOfPads u τ.1 = coldOfPads u τ'.1 → τ.2 = τ'.2 →
    (given τ).map (restrictBmr u) = (given τ').map (restrictBmr u)

/-- The pads with the cold part given and `0` at the hot slots. -/
def padsOfCold (u : AffineInput) (cold : BMR.Cold Tb u) : BMR.Pads Tb := fun i ρ e =>
  if hot : ρ = BMR.hotRes Tb u e i then 0 else cold i e ⟨ρ, hot⟩

/-- The kernel's answers at the visible P45 tags, from the visible targets. -/
def bmrKernel (K : TableKernel) (u : AffineInput) (cold : BMR.Cold Tb u) (masks : BMR.RowEnc → BaseField) :
    PMF (H8.BmrTags Tb u → Block × Block) :=
  (K.given (padsOfCold u cold, masks)).map (restrictBmr u)

/-! ### 2. The P45 part of a view from a P45 output -/

/-- The record natural of an encoding from its joins and hint. -/
def recordOf (J : BMR.Joins Tb) (hints : BMR.Enc → Bool) (e : BMR.Enc) : ℕ :=
  (if hints e then Tb.product else 0) + ∑ i : Fin Tb.count, (J e i).val * Tb.radix i

/-- The type of `H8.bmrPart`. -/
abbrev BmrPart (u : AffineInput) :=
  (BaseField × BaseField × BaseField) × Vector NormRow digitCount ×
    Vector Kriterion.CRT.Entry.Record Kriterion.CRT.Entry.xCount ×
    Vector Kriterion.CRT.Entry.Record Kriterion.CRT.Entry.yCount × (H8.BmrTags Tb u → Block × Block)

/-- The P45 part of a view from a P45 output and the answers. -/
def bmrOf (u : AffineInput) (o : BMR.NOut Tb u) (answers : H8.BmrTags Tb u → Block × Block) : BmrPart u :=
  (o.1.1.2.2, Vector.ofFn fun d => o.1.1.2.1 d,
    Vector.ofFn fun e => Kriterion.CRT.Entry.toRecord (recordOf o.1.1.1 o.1.2 (.inl (BMR.xEncEquiv.symm e))),
    Vector.ofFn fun e => Kriterion.CRT.Entry.toRecord (recordOf o.1.1.1 o.1.2 (.inr (BMR.yEncEquiv.symm e))),
    answers)

/-- The visible targets of a P45 output: the cold pads and every mask. -/
def visTargets (u : AffineInput) (o : BMR.NOut Tb u) : BMR.Cold Tb u × (BMR.RowEnc → BaseField) :=
  (o.2.1.1, fun r => if h : BMR.IsCollector r.2 then o.2.2.1 ⟨r, h⟩ else o.2.1.2 ⟨r, h⟩)

/-- **The P45 part drawn from a P45 output.** -/
def bmrLaw (K : TableKernel) (u : AffineInput) (o : BMR.NOut Tb u) : PMF (BmrPart u) :=
  (bmrKernel K u (visTargets u o).1 (visTargets u o).2).map (bmrOf u o)

/-! ### 3. The coins -/

variable [FieldCertificate] [GroupCertificate]

/-- The uniform law of the scheme's coins. -/
def coinLaw : PMF Kriterion.ArgoMAC.Scheme.Coins :=
  @PMF.uniformOfFintype _ (@Fintype.ofFinite _ crtEntry.coinsFinite) ⟨crtEntry.coinWitness⟩

/-- The layer coins of P45 that the scheme's coins carry: `r4`, the unused randomizers, the curve coins. -/
abbrev BmrLayer := (Fin 91 → BaseField) × (Fin 91 → Fin 7 → BaseField) ×
  (BaseField × {m : BaseField // m ≠ 0} × BaseField × BaseField)

/-- The layer coins: the row randomizers `(ρ, τ)` (the rows kernel's scales, unused by the construction) and P45's
layer. -/
abbrev Layer := (Fin 91 → NonZeroBase × NonZeroBase) × BmrLayer

/-- The layer of the scheme's coins (as `BmrEntry.bmrCoinsOf` and `NormRows.scalesOf` read it). -/
def layerOf (coins : Kriterion.ArgoMAC.Scheme.Coins) : Layer :=
  (NormRows.scalesOf coins, ((BmrEntry.bmrCoinsOf coins fun _ => (0, 0)).2.2.1,
    (BmrEntry.bmrCoinsOf coins fun _ => (0, 0)).2.2.2.1, (BmrEntry.bmrCoinsOf coins fun _ => (0, 0)).2.2.2.2))

/-- P45's coins from targets and a layer. -/
def coinsOf (τ : Targets) (layer : Layer) : BMR.Coins Tb := (τ.1, τ.2, layer.2)

/-- The context part of the scheme's coins: the offsets. -/
def ctxPart (coins : Kriterion.ArgoMAC.Scheme.Coins) : FieldMacToECMac.SuccessfulOffsets := coins.offsets

/-- **The layer is uniform and independent of the context part**: for every weight on the scheme's
coins that reads only the context part and a layer, averaging the coins' own layer is averaging a uniform one. -/
def CoinsSplit : Prop :=
  ∀ (g : Kriterion.ArgoMAC.Scheme.Coins → Layer → ℝ≥0∞),
    (∀ coins coins' layer, ctxPart coins = ctxPart coins' → g coins layer = g coins' layer) →
      ∑' coins, coinLaw coins * g coins (layerOf coins) =
        ∑' coins, coinLaw coins * ∑' layer, PMF.uniformOfFintype Layer layer * g coins layer

/-! ### 4. The two readings -/

open Classical in
/-- **`G1U°`'s P45 part**. -/
def RealReading (K : TableKernel) : Prop :=
  ∀ (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    (H8.realCore crtEntry Tb parameter scalar u).map (Option.map (H8.bmrPart Tb u)) =
      coinLaw.bind fun coins => (PMF.uniformOfFintype Targets).bind fun τ =>
        if H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u then PMF.pure none
        else (bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u (coinsOf τ (layerOf coins)))).map some

/-- The P45 reveal at kernel scales: doubling of the corrected targets, a CRT value in the two-sided window, or the
normalization flag of the source's hidden cells. -/
def revealAt (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins)
    (scales : Fin 91 → NonZeroBase × NonZeroBase) (u : AffineInput) (cells : BMR.NSource Tb × BMR.Visible Tb u) :
    Prop :=
  H8.rowsDoubling (BMR.nTargets (BmrEntry.bmrContextOf scalar coins) u scales) ∨
    (∃ e, BMR.InWindow Tb (BMR.evalInt u cells.1.1 cells.2.1 e)) ∨ BMR.normBad cells.1

/-- The P45 reveal at the coins' own kernel scales. -/
abbrev revealP45 (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (cells : BMR.NSource Tb × BMR.Visible Tb u) : Prop :=
  revealAt scalar coins (NormRows.scalesOf coins) u cells

open Classical in
/-- **`M'`'s P45 part**. -/
def IdealReading (K : TableKernel) : Prop :=
  ∀ (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
    (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
      (H8.idealCore crtEntry Tb H8.crtRevealOn scalar u Q).map (Option.map (H8.bmrPart Tb u)) =
        coinLaw.bind fun coins => (PMF.uniformOfFintype (BMR.NSource Tb × BMR.Visible Tb u)).bind fun cells =>
          if revealP45 scalar coins u cells then PMF.pure none
          else (bmrLaw K u (BMR.nIdealOut (NormRows.normTrueRows scalar coins u) u cells)).map some

end

/-! ### 5. Sums against pushforwards, and the weighted P45 core -/

section Sums

/-- Summing a weight against the `some` part of a pushforward is summing it along the map. -/
theorem tsum_map_some {α β : Type*} (p : PMF α) (f : α → Option β) (F : β → ℝ≥0∞) :
    ∑' b, p.map f (some b) * F b = ∑' a, p a * (f a).elim 0 F := by
  classical
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rcases hfa : f a with _ | b0
  · simp
  · simp only [Option.elim, Option.some.injEq, ite_mul, zero_mul]
    rw [tsum_eq_single b0 fun b other => if_neg other]
    rw [if_pos rfl, mul_comm]

/-- **Pointwise domination of the `some` parts gives domination of every weighted sum.** -/
theorem weighted_le {α α' β : Type*} (p : PMF α) (q : PMF α') (f : α → Option β) (g : α' → Option β)
    (below : ∀ b, p.map f (some b) ≤ q.map g (some b)) (F : β → ℝ≥0∞) :
    ∑' a, p a * (f a).elim 0 F ≤ ∑' a, q a * (g a).elim 0 F := by
  rw [← tsum_map_some, ← tsum_map_some]
  exact ENNReal.tsum_le_tsum fun b => by gcongr; exact below b

/-- A uniform double sum through an equivalence is the uniform sum on the target. -/
theorem uniform_sum_equiv {A B C : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C]
    [Nonempty C] (e : A × B ≃ C) (f : C → ℝ≥0∞) :
    ∑' b, PMF.uniformOfFintype B b * ∑' a, PMF.uniformOfFintype A a * f (e (a, b)) =
      ∑' c, PMF.uniformOfFintype C c * f c := by
  have card : Fintype.card C = Fintype.card A * Fintype.card B := by
    rw [← Fintype.card_congr e, Fintype.card_prod]
  rw [← e.tsum_eq]
  simp only [PMF.uniformOfFintype_apply, card, Nat.cast_mul, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  ring

end Sums

section Composition

variable [FieldCertificate] [GroupCertificate]

/-- The scheme's function is defined only on the curve. -/
theorem onCurve_of_function {scalar : NonZeroScalar} {u : AffineInput} {Q : Point}
    (defined : (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q) : OnCurve u := by
  refine (decodePoint_defined u).mp fun none => ?_
  have : (crtEntry.scheme inferInstance inferInstance).function scalar u = (decodePoint u).map _ := rfl
  rw [this, none] at defined
  exact absurd defined (by simp)

/-- The context of the coins reads only their offsets. -/
theorem bmrContextOf_congr (scalar : NonZeroScalar) {coins coins' : Kriterion.ArgoMAC.Scheme.Coins}
    (same : ctxPart coins = ctxPart coins') :
    BmrEntry.bmrContextOf scalar coins = BmrEntry.bmrContextOf scalar coins' := by
  have offsets : coins.offsets = coins'.offsets := same
  unfold BmrEntry.bmrContextOf NormRows.nctxOf Kriterion.CRT.Entry.outputKeysOf
  rw [offsets]

/-- The doubling event on a table tape, as the entry's exceptional inputs. -/
theorem doubling_tape (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape crtEntry) :
    H8.Doubling crtEntry scalar tape u ↔ ∃ o, Kriterion.CRT.Entry.exceptional scalar tape.1 o = some u :=
  Iff.rfl

/-- The doubling event at a pair, as the entry's exceptional inputs of the coins. -/
theorem doubling_iff (scalar : NonZeroScalar) (u : AffineInput) (coins : Kriterion.ArgoMAC.Scheme.Coins)
    (table : TagTable) :
    H8.Doubling crtEntry scalar (coins, table) u ↔ ∃ o, Kriterion.CRT.Entry.exceptional scalar coins o = some u := by
  refine (doubling_tape scalar u (coins, table)).trans ?_
  dsimp only
  exact Iff.rfl

/-- The doubling event reads only the context part. -/
theorem doubling_congr (scalar : NonZeroScalar) (u : AffineInput) {coins coins' : Kriterion.ArgoMAC.Scheme.Coins}
    (table table' : TagTable) (same : ctxPart coins = ctxPart coins') :
    H8.Doubling crtEntry scalar (coins, table) u ↔ H8.Doubling crtEntry scalar (coins', table') u := by
  have offsets : coins.offsets = coins'.offsets := same
  have e : ∀ o, Kriterion.CRT.Entry.exceptional scalar coins o = Kriterion.CRT.Entry.exceptional scalar coins' o := by
    intro o
    unfold Kriterion.CRT.Entry.exceptional Kriterion.CRT.Entry.outputKeysOf
    rw [offsets]
  rw [doubling_iff, doubling_iff]
  simp only [e]

/-- `Targets × BmrLayer` is P45's coin space. -/
def coinsEquiv : Targets × BmrLayer ≃ BMR.Coins Tb where
  toFun x := (x.1.1, x.1.2, x.2)
  invFun c := ((c.1, c.2.1), c.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_some_apply {β : Type*} (X : PMF β) (w : β) : X.map some (some w) = X w := by
  rw [PMF.map_apply, tsum_eq_single w ?_]
  · rw [if_pos rfl]
  · intro b other
    exact if_neg fun same => other (Option.some.inj same).symm

/-- The corrected true rows of coins with another layer. -/
theorem normTrueRows_layer (scalar : NonZeroScalar) (u : AffineInput) (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    NormRows.normTrueRows scalar coins u = BMR.nTargets (BmrEntry.bmrContextOf scalar coins) u (layerOf coins).1 := rfl

/-- The nonzero-coordinate facts of the context. -/
theorem valid_ctx (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    (BmrEntry.bmrContextOf scalar coins).Valid := by
  intro d
  have z := Rows.z0_ne_zero ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).offset.coordinates
    (digitEndomorphismBase ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).digit)
    ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).offset.onCurve
  have s4 := Rows.s4_ne_zero ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).offset.coordinates
    (digitEndomorphismBase ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).digit)
    ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).offset.onCurve
    (fun phi => digitEndomorphismBasePowSix ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).digit phi)
  exact ⟨z, s4⟩

theorem sparse_ctx (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    (BmrEntry.bmrContextOf scalar coins).Sparse := fun d =>
  Rows.unscaledRows_sparse ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).offset.coordinates
    (digitEndomorphismBase ((Kriterion.CRT.Entry.outputKeysOf scalar coins).get d).digit)

open Classical in
/-- **`CrtBmrSplit` from the kernel, the two readings and the coin split.** -/
theorem crtBmrSplit_of (K : TableKernel) (real : ∀ [FieldCertificate] [GroupCertificate], RealReading K)
    (ideal : ∀ [FieldCertificate] [GroupCertificate], IdealReading K)
    (split : ∀ [FieldCertificate] [GroupCertificate], CoinsSplit) : H8.CrtBmrSplit Tb := by
  intro _ _ parameter scalar u Q defined w
  have onCurve : OnCurve u := onCurve_of_function defined
  rw [ideal scalar u Q defined, real parameter scalar u]
  simp only [PMF.bind_apply]
  -- the real side, as a weight of the context part and the layer
  let g : Kriterion.ArgoMAC.Scheme.Coins → Layer → ℝ≥0∞ := fun coins layer =>
    if H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u then 0
    else ∑' τ, PMF.uniformOfFintype Targets τ *
      bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u (coinsOf τ layer)) w
  -- the ideal side, likewise
  let h : Kriterion.ArgoMAC.Scheme.Coins → Layer → ℝ≥0∞ := fun coins layer =>
    ∑' cells, PMF.uniformOfFintype (BMR.NSource Tb × BMR.Visible Tb u) cells *
      (if revealAt scalar coins layer.1 u cells then PMF.pure none
        else (bmrLaw K u (BMR.nIdealOut (BMR.nTargets (BmrEntry.bmrContextOf scalar coins) u layer.1) u cells)).map
          some) (some w)
  have rhs : ∀ coins, (∑' τ, PMF.uniformOfFintype Targets τ *
      (if H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u then PMF.pure none
        else (bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u
          (coinsOf τ (layerOf coins)))).map some) (some w)) = g coins (layerOf coins) := by
    intro coins
    by_cases dbl : H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u
    · have zero : ∀ τ : Targets, PMF.uniformOfFintype Targets τ *
          (if H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u then PMF.pure none
            else (bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u
              (coinsOf τ (layerOf coins)))).map some) (some w) = 0 := by
        intro τ
        rw [if_pos dbl, PMF.pure_apply_of_ne _ _ (Option.some_ne_none w), mul_zero]
      rw [tsum_congr zero, tsum_zero]
      exact (if_pos dbl).symm
    · rw [show g coins (layerOf coins) = _ from if_neg dbl]
      refine tsum_congr fun τ => ?_
      rw [if_neg dbl, map_some_apply]
  have lhs : ∀ coins, (∑' cells, PMF.uniformOfFintype (BMR.NSource Tb × BMR.Visible Tb u) cells *
      (if revealP45 scalar coins u cells then PMF.pure none
        else (bmrLaw K u (BMR.nIdealOut (NormRows.normTrueRows scalar coins u) u cells)).map some) (some w)) =
      h coins (layerOf coins) := fun coins => rfl
  have R : (∑' coins, coinLaw coins * ∑' τ, PMF.uniformOfFintype Targets τ *
      (if H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u then PMF.pure none
        else (bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u
          (coinsOf τ (layerOf coins)))).map some) (some w)) =
      ∑' coins, coinLaw coins * g coins (layerOf coins) :=
    tsum_congr fun coins => by rw [rhs coins]
  have L : (∑' coins, coinLaw coins * ∑' cells, PMF.uniformOfFintype (BMR.NSource Tb × BMR.Visible Tb u) cells *
      (if revealP45 scalar coins u cells then PMF.pure none
        else (bmrLaw K u (BMR.nIdealOut (NormRows.normTrueRows scalar coins u) u cells)).map some) (some w)) =
      ∑' coins, coinLaw coins * h coins (layerOf coins) :=
    tsum_congr fun coins => by rw [lhs coins]
  have invariantG : ∀ coins coins' layer, ctxPart coins = ctxPart coins' → g coins layer = g coins' layer := by
    intro coins coins' layer same
    simp only [g, doubling_congr scalar u (fun _ => (0, 0)) (fun _ => (0, 0)) same, bmrContextOf_congr scalar same]
  have invariantH : ∀ coins coins' layer, ctxPart coins = ctxPart coins' → h coins layer = h coins' layer := by
    intro coins coins' layer same
    simp only [h, revealAt, bmrContextOf_congr scalar same]
  rw [L, R, split g invariantG, split h invariantH]
  refine ENNReal.tsum_le_tsum fun coins => ?_
  gcongr coinLaw coins * ?_
  -- per coins: the layer's scales against P45's layer
  rw [BMR.tsum_uniform_prod (fun layer : Layer => h coins layer),
    BMR.tsum_uniform_prod (fun layer : Layer => g coins layer)]
  by_cases dbl : H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u
  · -- doubling: the corrected rows vanish somewhere for every scale
    have zero : ∀ s : Fin 91 → NonZeroBase × NonZeroBase, ∀ old : BmrLayer, h coins (s, old) = 0 := by
      intro s old
      refine ENNReal.tsum_eq_zero.mpr fun cells => ?_
      have flagged := BmrEntry.rowsDoubling_nTargets scalar coins u ((doubling_iff scalar u _ _).mp dbl) s
      rw [if_pos (show revealAt scalar coins s u cells from Or.inl flagged),
        PMF.pure_apply_of_ne _ _ (Option.some_ne_none w), mul_zero]
    simp only [zero, mul_zero, tsum_zero]
    exact zero_le
  · -- no doubling: the normalized core
    have gval : ∀ s old, g coins (s, old) = ∑' τ, PMF.uniformOfFintype Targets τ *
        bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u (coinsEquiv (τ, old))) w :=
      fun s old => if_neg dbl
    have gconst : ∀ s, ∑' old, PMF.uniformOfFintype BmrLayer old * g coins (s, old) =
        ∑' c, PMF.uniformOfFintype (BMR.Coins Tb) c *
          bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u c) w := by
      intro s
      simp only [gval]
      exact uniform_sum_equiv coinsEquiv fun c => bmrLaw K u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u c) w
    have hval : ∀ s old, h coins (s, old) = ∑' cells, PMF.uniformOfFintype (BMR.NSource Tb × BMR.Visible Tb u) cells *
        (if revealAt scalar coins s u cells then 0
          else bmrLaw K u (BMR.nIdealOut (BMR.nTargets (BmrEntry.bmrContextOf scalar coins) u s) u cells) w) := by
      intro s old
      refine tsum_congr fun cells => ?_
      split_ifs
      · rw [PMF.pure_apply_of_ne _ _ (Option.some_ne_none w)]
      · rw [map_some_apply]
    simp only [gconst, hval, BMR.tsum_uniform_const]
    exact BMR.nCore_weighted Flags.Wrap.entryTableFacts (BmrEntry.bmrContextOf scalar coins) (valid_ctx scalar coins)
      (sparse_ctx scalar coins) u onCurve
      (fun s cells => revealAt scalar coins s u cells)
      (fun s cells flagged window => flagged (Or.inr (Or.inl window)))
      (fun s cells flagged bad => flagged (Or.inr (Or.inr bad)))
      (fun o => bmrLaw K u o w)

end Composition

end Kriterion.CRT.Privacy.BmrSplit
