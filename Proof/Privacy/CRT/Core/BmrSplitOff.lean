/-
**`CrtBmrSplitOff` for the CRT entry, off the curve** (H8's off-curve P45 row).

The P45 part of a view off the curve (`H8.bmrPart`: curve and row constants, records, the answers at the visible
body tags; no mask or key tag is visible off the curve) is, on either side, a published part computed from an
off-curve P45 output (`BMR.OutOff`) and answers drawn from the swapped table's kernel given the cold pads. The
composition uses the decomposition (`Core/BmrSplit.lean`): the kernel `TableKernel`, the real
reading `RealReading` (stated at every input) and the coin split `CoinsSplit`, plus:

* `KernelOff K`: off the curve the kernel's visible answers depend only on the cold pads, so the real
  masks can be replaced by `0` (`bmrLaw_realOut_off`);
* `idealReadingOff` (proved here): route M's off-curve middle view is, under uniform P45 cells and cold pads, the
  published part of `BMR.idealOutOff` with the kernel's answers, flagged by the window (`windowFlag`);
* `BmrOff.core_below_off` (`Core/BmrIdealOff.lean`): the P45 core off the curve with the window flag.

`crtBmrSplitOff_of` composes them; off the curve no tape doubles (`not_doubling_of_off`).
-/

import Proof.Privacy.CRT.Core.BmrIdealOff
import Proof.Privacy.CRT.Core.BmrSplit

namespace Kriterion.CRT.Privacy.BmrOff

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance
open Kriterion.CRT.Privacy.BmrSplit (TableKernel Targets restrictBmr coldOfPads padsOfCold bmrKernel recordOf BmrPart
  bmrOf visTargets bmrLaw coinLaw Layer layerOf coinsOf ctxPart CoinsSplit RealReading)
open scoped ENNReal

noncomputable section

/-! ### 1. The kernel off the curve -/

/-- **Off the curve the kernel's visible answers depend only on the cold pads**: no mask tag is visible
off the curve. -/
def KernelOff (K : TableKernel) : Prop :=
  ∀ (u : AffineInput) (τ τ' : Targets), validate u = false → coldOfPads u τ.1 = coldOfPads u τ'.1 →
    (K.given τ).map (restrictBmr u) = (K.given τ').map (restrictBmr u)

/-- An off-curve P45 output as an output with zero masks and key. -/
def offOut (u : AffineInput) (o : BMR.OutOff Tb u) : BMR.Out Tb u := (o.1, (o.2, fun _ => 0), fun _ => 0, 0)

/-- The cold pads of the pads with a given cold part. -/
theorem coldOfPads_padsOfCold (u : AffineInput) (cold : BMR.Cold Tb u) : coldOfPads u (padsOfCold u cold) = cold := by
  funext i e ρ
  show (if hot : ρ.1 = BMR.hotRes Tb u e i then 0 else cold i e ⟨ρ.1, hot⟩) = cold i e ρ
  rw [dif_neg ρ.2]

/-- Off the curve the kernel at the cold pads does not read the masks. -/
theorem bmrKernel_masks (K : TableKernel) (off : KernelOff K) (u : AffineInput) (hv : validate u = false)
    (cold : BMR.Cold Tb u) (masks masks' : BMR.RowEnc → BaseField) :
    bmrKernel K u cold masks = bmrKernel K u cold masks' :=
  off u _ _ hv rfl

/-- Off the curve the kernel's answers of any targets are the kernel's at their cold pads. -/
theorem given_restrict (K : TableKernel) (off : KernelOff K) (u : AffineInput) (hv : validate u = false)
    (τ : Targets) (masks : BMR.RowEnc → BaseField) :
    (K.given τ).map (restrictBmr u) = bmrKernel K u (coldOfPads u τ.1) masks :=
  off u _ _ hv (coldOfPads_padsOfCold u _).symm

/-- **Off the curve the real P45 part reads only the off-curve output.** -/
theorem bmrLaw_realOut_off (K : TableKernel) (off : KernelOff K) (u : AffineInput) (hv : validate u = false)
    [FieldCertificate] (ctx : BMR.Context) (c : BMR.Coins Tb) :
    bmrLaw K u (BMR.realOut ctx u c) = bmrLaw K u (offOut u (BMR.realOutOff ctx u c)) := by
  unfold bmrLaw
  rw [bmrKernel_masks K off u hv (visTargets u (BMR.realOut ctx u c)).1 (visTargets u (BMR.realOut ctx u c)).2
    (visTargets u (offOut u (BMR.realOutOff ctx u c))).2]
  rfl

/-! ### 2. The ideal reading off the curve -/

/-- A pushforward only reads the support. -/
theorem map_congr_support {α β : Type} (p : PMF α) (f g : α → β) (h : ∀ x ∈ p.support, f x = g x) :
    p.map f = p.map g := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact PMF.bind_congr _ _ _ fun x hx => by rw [Function.comp_apply, Function.comp_apply, h x hx]

/-- A pushforward through a flag that does not move. -/
theorem map_ite_const {α β γ : Type} (p : PMF α) (flag : Prop) [Decidable flag] (r : α → γ) (P : γ → β) :
    p.map (fun x => if flag then none else some (P (r x))) =
      if flag then PMF.pure none else ((p.map r).map fun a => some (P a)) := by
  by_cases h : flag
  · simp only [if_pos h]
    exact PMF.map_const _ _
  · simp only [if_neg h, PMF.map_comp]
    rfl

/-- The uniform targets' cold pads are uniform. -/
theorem uniform_targets_cold (u : AffineInput) :
    (PMF.uniformOfFintype Targets).map (fun τ => coldOfPads u τ.1) = PMF.uniformOfFintype (BMR.Cold Tb u) := by
  have factor : (fun τ : Targets => coldOfPads u τ.1) = Flags.Wrap.restrictCold u ∘ Prod.fst := rfl
  rw [factor, ← PMF.map_comp, BMR.uniform_map_fst]
  exact BMR.WrapMass.uniform_map_addHom _ (Flags.Wrap.restrictCold_surjective u)

section Ideal

variable [FieldCertificate] [GroupCertificate]

/-- **The P45 part of a middle view off the curve** is the published part of the ideal off-curve output of its
source and the table's cold pads, with the table's answers. -/
theorem bmrPart_middle (u : AffineInput) (s : Kriterion.CRT.Entry.Source) (labels : LamportSignature)
    (table : TagTable) (cold : BMR.Cold Tb u) :
    H8.bmrPart Tb u ((Kriterion.CRT.Entry.publish s, labels, fun tag => table tag.1) : H8.CoreView crtEntry Tb u) =
      bmrOf u (offOut u (BMR.idealOutOff u (srcOf s, cold))) (restrictBmr u table) := by
  unfold H8.bmrPart bmrOf offOut BMR.idealOutOff
  dsimp only
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · show Vector.ofFn s.rows = Vector.ofFn fun d => s.rows d
    rfl
  · refine Vector.ext fun e he => ?_
    have := publish_recX s ⟨e, he⟩
    rw [Vector.getElem_ofFn]
    exact this
  · refine Vector.ext fun e he => ?_
    have := publish_recY s ⟨e, he⟩
    rw [Vector.getElem_ofFn]
    exact this

open Classical in
/-- The off-curve ideal P45 law of cells: flagged by the window, else the published part and the kernel's answers. -/
def idealCellLaw (K : TableKernel) (u : AffineInput) (cells : BMR.Source Tb × BMR.Cold Tb u) :
    PMF (Option (BmrPart u)) :=
  if windowFlag u cells then PMF.pure none else (bmrLaw K u (offOut u (BMR.idealOutOff u cells))).map some

open Classical in
/-- **The ideal reading off the curve** (proved): `M'`'s off-curve P45 part is, under uniform P45 cells and cold pads,
the published part of `BMR.idealOutOff` with the kernel's answers, flagged by the window. -/
theorem idealReadingOff (K : TableKernel) (off : KernelOff K) (u : AffineInput) (hv : validate u = false) :
    (H8.idealCoreOff crtEntry Tb H8.crtRevealOff u).map (Option.map (H8.bmrPart Tb u)) =
      (PMF.uniformOfFintype (BMR.Source Tb × BMR.Cold Tb u)).bind (idealCellLaw K u) := by
  -- the middle view of a source, table by table
  have perTable : ∀ (s : (PublicFirst.viewHere crtEntry).Source) (τ : Targets),
      (K.given τ).map (fun table => Option.map (H8.bmrPart Tb u)
          (if H8.crtRevealOff s u table then none
            else some ((PublicFirst.viewHere crtEntry).publish s, (PublicFirst.viewHere crtEntry).labels s u,
              fun tag => table tag.1))) =
        idealCellLaw K u (srcOf s, coldOfPads u τ.1) := by
    intro s τ
    rw [map_congr_support (K.given τ) _
      (fun table => if windowFlag u (srcOf s, coldOfPads u τ.1) then none
        else some (bmrOf u (offOut u (BMR.idealOutOff u (srcOf s, coldOfPads u τ.1))) (restrictBmr u table)))]
    · rw [map_ite_const]
      unfold idealCellLaw bmrLaw
      by_cases flag : windowFlag u (srcOf s, coldOfPads u τ.1)
      · rw [if_pos flag, if_pos flag]
      · rw [if_neg flag, if_neg flag, given_restrict K off u hv τ
          (visTargets u (offOut u (BMR.idealOutOff u (srcOf s, coldOfPads u τ.1)))).2, PMF.map_comp]
        rfl
    · intro table member
      have cold : H8.bmrColdOf table u = coldOfPads u τ.1 := by
        rw [Flags.Wrap.bmrColdOf_eq, ← (K.reads τ table member).1]
        rfl
      have reveal : H8.crtRevealOff s u table ↔ windowFlag u (srcOf s, coldOfPads u τ.1) := by
        rw [← cold]
        exact replayWraps_iff s u table
      by_cases flag : windowFlag u (srcOf s, coldOfPads u τ.1)
      · rw [if_pos flag, if_pos (reveal.mpr flag)]
        rfl
      · rw [if_neg flag, if_neg (fun hit => flag (reveal.mp hit))]
        exact congrArg some (bmrPart_middle u s _ table (coldOfPads u τ.1))
  have perSource : ∀ s : (PublicFirst.viewHere crtEntry).Source,
      (swappedTableLaw crtEntry.layout).map (fun table => Option.map (H8.bmrPart Tb u)
          (if H8.crtRevealOff s u table then none
            else some ((PublicFirst.viewHere crtEntry).publish s, (PublicFirst.viewHere crtEntry).labels s u,
              fun tag => table tag.1))) =
        (PMF.uniformOfFintype Targets).bind fun τ => idealCellLaw K u (srcOf s, coldOfPads u τ.1) := by
    intro s
    rw [show crtEntry.layout = crtLayout from rfl, K.law, PMF.map_bind]
    exact congrArg _ (funext fun τ => perTable s τ)
  unfold H8.idealCoreOff
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  simp only [perSource]
  have prodLaw : (PMF.uniformOfFintype (BMR.Source Tb × BMR.Cold Tb u)).bind (idealCellLaw K u) =
      (PMF.uniformOfFintype (BMR.Source Tb)).bind fun src =>
        (PMF.uniformOfFintype (BMR.Cold Tb u)).bind fun cold => idealCellLaw K u (src, cold) := by
    rw [EntrySplit.uniform_prod_eq_bind, PMF.bind_bind]
    refine congrArg _ (funext fun src => ?_)
    rw [PMF.bind_map]
    rfl
  rw [prodLaw, ← uniform_srcOf, ← uniform_targets_cold u, PMF.bind_map]
  refine congrArg _ (funext fun s => ?_)
  show _ = (PMF.map (fun τ => coldOfPads u τ.1) (PMF.uniformOfFintype Targets)).bind fun cold =>
    idealCellLaw K u (srcOf s, cold)
  rw [PMF.bind_map]
  rfl

end Ideal

/-! ### 3. The composition -/

section Composition

variable [FieldCertificate] [GroupCertificate]

theorem map_some_apply' {β : Type} (X : PMF β) (w : β) : X.map some (some w) = X w := by
  rw [PMF.map_apply, tsum_eq_single w ?_]
  · rw [if_pos rfl]
  · intro b other
    exact if_neg fun same => other (Option.some.inj same).symm

open Classical in
/-- The ideal cell law at `some w`, as the weight of the flagged ideal output. -/
theorem idealCellLaw_some (K : TableKernel) (u : AffineInput) (cells : BMR.Source Tb × BMR.Cold Tb u)
    (w : BmrPart u) :
    idealCellLaw K u cells (some w) =
      (if windowFlag u cells then none else some (BMR.idealOutOff u cells)).elim 0
        fun o => bmrLaw K u (offOut u o) w := by
  unfold idealCellLaw
  by_cases flag : windowFlag u cells
  · rw [if_pos flag, if_pos flag, PMF.pure_apply_of_ne _ _ (Option.some_ne_none w)]
    rfl
  · rw [if_neg flag, if_neg flag, map_some_apply']
    rfl

open Classical in
/-- **`CrtBmrSplitOff` from the kernel (with its off-curve fact), the real reading and the coin split.** -/
theorem crtBmrSplitOff_of (K : TableKernel) (off : KernelOff K)
    (real : ∀ [FieldCertificate] [GroupCertificate], RealReading K)
    (split : ∀ [FieldCertificate] [GroupCertificate], CoinsSplit) : H8.CrtBmrSplitOff Tb := by
  intro _ _ parameter scalar u undefined w
  have hv := validate_false_of_function undefined
  have offCurve := not_onCurve_of_function undefined
  rw [idealReadingOff K off u hv, real parameter scalar u]
  simp only [PMF.bind_apply]
  let F : BMR.OutOff Tb u → ℝ≥0∞ := fun o => bmrLaw K u (offOut u o) w
  let g : Kriterion.ArgoMAC.Scheme.Coins → Layer → ℝ≥0∞ := fun coins layer =>
    ∑' τ, PMF.uniformOfFintype Targets τ *
      F (BMR.realOutOff (BmrEntry.bmrContextOf scalar coins) u (coinsOf τ layer))
  have rhs : ∀ coins, (∑' τ, PMF.uniformOfFintype Targets τ *
      (if H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u then PMF.pure none
        else (bmrLaw K u (BMR.realOut (BmrEntry.bmrContextOf scalar coins) u
          (coinsOf τ (layerOf coins)))).map some) (some w)) = g coins (layerOf coins) := by
    intro coins
    have noDouble := not_doubling_of_off scalar (coins, fun _ => (0, 0)) offCurve
    refine tsum_congr fun τ => ?_
    rw [if_neg noDouble, map_some_apply', bmrLaw_realOut_off K off u hv]
  have R : (∑' coins, coinLaw coins * ∑' τ, PMF.uniformOfFintype Targets τ *
      (if H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u then PMF.pure none
        else (bmrLaw K u (BMR.realOut (BmrEntry.bmrContextOf scalar coins) u
          (coinsOf τ (layerOf coins)))).map some) (some w)) =
      ∑' coins, coinLaw coins * g coins (layerOf coins) :=
    tsum_congr fun coins => by rw [rhs coins]
  have invariant : ∀ coins coins' layer, ctxPart coins = ctxPart coins' → g coins layer = g coins' layer := by
    intro coins coins' layer same
    simp only [g, BmrSplit.bmrContextOf_congr scalar same]
  have perCoins : ∀ coins, (∑' cells, PMF.uniformOfFintype (BMR.Source Tb × BMR.Cold Tb u) cells *
        idealCellLaw K u cells (some w)) ≤
      ∑' layer, PMF.uniformOfFintype Layer layer * g coins layer := by
    intro coins
    have equiv : (∑' layer, PMF.uniformOfFintype Layer layer * g coins layer) =
        ∑' c, PMF.uniformOfFintype (BMR.Coins Tb) c *
          (some (BMR.realOutOff (BmrEntry.bmrContextOf scalar coins) u c)).elim 0 F :=
      BmrSplit.uniform_sum_equiv BmrSplit.coinsEquiv
        (fun c => (some (BMR.realOutOff (BmrEntry.bmrContextOf scalar coins) u c)).elim 0 F)
    rw [equiv]
    simp only [idealCellLaw_some]
    exact BmrSplit.weighted_le _ _ _ _ (fun o => core_below_off Flags.Wrap.entryTableFacts
      (BmrEntry.bmrContextOf scalar coins) u (windowFlag u) (not_window u) o) F
  refine le_of_le_of_eq ?_ (R.trans (split g invariant)).symm
  have one : ∑' coins, coinLaw coins = 1 := PMF.tsum_coe _
  calc (∑' cells, PMF.uniformOfFintype (BMR.Source Tb × BMR.Cold Tb u) cells * idealCellLaw K u cells (some w))
      = ∑' coins, coinLaw coins *
          ∑' cells, PMF.uniformOfFintype (BMR.Source Tb × BMR.Cold Tb u) cells *
            idealCellLaw K u cells (some w) := by
        rw [ENNReal.tsum_mul_right, one, one_mul]
    _ ≤ ∑' coins, coinLaw coins * ∑' layer, PMF.uniformOfFintype Layer layer * g coins layer :=
        ENNReal.tsum_le_tsum fun coins => by gcongr; exact perCoins coins

end Composition

end

end Kriterion.CRT.Privacy.BmrOff
