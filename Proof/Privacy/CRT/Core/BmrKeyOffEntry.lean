/-
**The bridge key's label at the entry, off the curve**.

`BmrOff.keyLabel_weighted` bounds the key label at P45's level: summed against any weight of P45's off-curve output,
the coins whose curve encodings are outside the wrap window and whose bridge key has a given low part weigh at most
`keyError` of all coins. This file lifts it to the swapped tape of the entry, for any view `V` of the tape that is a
function of the coins' rest, P45's published output and the table off the positions P45 hides (`ViewFD`):

* **window** (`far_of_not_curveNearEdge`, `curveWindowFree_of_far`): off `StageTwo.curveNearEdge` every curve
  encoding's offset `O` satisfies `B ≤ O` and `O + 2B ≤ M`, and the evaluator's integer is `O + a·v` with `a·v < B`
  (`BMR.evalInt_eq`), so it lies outside the two-sided window, at every input (section 6 item 2 of the finish log);
* **kernel** (`given_restrictOff`): under the swapped table conditioned on its targets, the table off the hidden
  positions (`HidPos`: the hot body positions and every mask position) has a law that depends on the targets only
  through the cold pads (`TargetLaw.swapped_event_eq`, as `BmrKernel.given_map_eq`);
* **support** (`outer_eq_of_fd`): two laws with the same image under `f`, and two events that agree on supports
  wherever `f` agrees, have the same mass;
* **the bound** (`keyLabel_entry`): for a fixed rest the view's conditional mass given the targets and the layer is a
  function of P45's output (`phi_congr`), and `keyLabel_weighted` applies.
-/

import Proof.Privacy.CRT.Core.BmrKeyOff
import Proof.Privacy.CRT.Core.BmrReal
import Proof.Privacy.CRT.Core.BmrKernel
import Proof.Privacy.CRT.Core.BmrCoins
import Proof.Privacy.CRT.Flags.Wrap
import Proof.Privacy.CRT.Hidden.StageTwo

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.KeyOffEntry

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance Kriterion.CRT.Privacy.BmrSplit
open scoped ENNReal

noncomputable section

attribute [local instance 2000] H8.tableModulusNeZero

/-! ### 1. Far from the edges, the curve encodings are outside the window -/

section Window

/-- **An offset far from the edges gives an evaluator's integer outside the two-sided window**, at every input. -/
theorem not_inWindow_of_far {T : CrtTable} [∀ i, NeZero (T.modulus i)] (facts : BMR.TableFacts T)
    (ctx : BMR.Context) (u : AffineInput) (c : BMR.Coins T) (e : BMR.Enc)
    (low : T.wrapBound ≤ BMR.offset c e) (high : BMR.offset c e + 2 * T.wrapBound ≤ T.product) :
    ¬ BMR.InWindow T (BMR.evalInt u (BMR.join ctx c) (BMR.coldOf u c) e) := by
  set a := BMR.slope ctx c e
  set v := coordValue u (BMR.coordOf e)
  have hv : v < baseFieldModulus := by
    simp only [v, coordValue]
    split_ifs <;> exact ZMod.val_lt _
  have hu : a.val * v < T.wrapBound := by
    rw [facts.wrapBound_eq]
    unfold wrapBound
    have ha : a.val ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt a)
    have hv' : v ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt hv
    rw [sq]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul ha hv')
  rw [BMR.evalInt_eq facts ctx u c e]
  unfold BMR.InWindow
  have small : BMR.offset c e + a.val * v < T.product := by omega
  rw [Nat.mod_eq_of_lt small]
  omega

/-- The entry's form: an offset not near an edge. -/
theorem not_inWindow_of_not_nearEdge (ctx : BMR.Context) (u : AffineInput) (c : BMR.Coins Tb) (e : BMR.Enc)
    (far : ¬ StageTwo.nearEdge (BMR.offset c e)) :
    ¬ BMR.InWindow Tb (BMR.evalInt u (BMR.join ctx c) (BMR.coldOf u c) e) := by
  unfold StageTwo.nearEdge at far
  push Not at far
  exact not_inWindow_of_far Flags.Wrap.entryTableFacts ctx u c e far.1 (Nat.le_of_not_lt (by omega))

/-- **Window-free curve encodings** when every curve encoding's offset is far from the edges. -/
theorem curveWindowFree_of_far (ctx : BMR.Context) (u : AffineInput) (c : BMR.Coins Tb)
    (far : ∀ element, ¬ StageTwo.nearEdge (BMR.offset c (BMR.curveEnc element))) :
    BmrOff.CurveWindowFree u (BmrOff.cellsOfOut (BMR.realOutOff ctx u c)) :=
  fun element => not_inWindow_of_not_nearEdge ctx u c _ (far element)

/-- Below `p` the scheme's reading of the table oracle is `tagHash`: the `x` coordinate's garbling. -/
theorem gxOf_tableOracle (table : TagTable) (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    EntryCorrect.gxOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins =
      EntryCorrect.gxOf (H8.tagHash table) coins := by
  unfold EntryCorrect.gxOf
  refine BmrReal.eval_congr_asked _ _ _ fun n inside => ?_
  obtain ⟨k, -, range, label, rfl⟩ := Align.asked_of_tagged
    (Paths.coordGarbleM_tagged Entry.table Entry.xCount 0 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _
    inside
  exact BmrReal.schemeHash_eq_tagHash table _ (Paths.hashInput_lt range)

/-- The `y` coordinate's garbling. -/
theorem gyOf_tableOracle (table : TagTable) (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    EntryCorrect.gyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins =
      EntryCorrect.gyOf (H8.tagHash table) coins := by
  unfold EntryCorrect.gyOf
  refine BmrReal.eval_congr_asked _ _ _ fun n inside => ?_
  obtain ⟨k, -, range, label, rfl⟩ := Align.asked_of_tagged
    (Paths.coordGarbleM_tagged Entry.table Entry.yCount 1 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _
    inside
  exact BmrReal.schemeHash_eq_tagHash table _ (Paths.hashInput_lt range)

/-- **Off the bad event every curve encoding's offset is far from the edges** (the offsets `curveNearEdge` reads are
P45's offsets of the curve encodings). -/
theorem far_of_not_curveNearEdge (tape : TableTape crtEntry) (h : ¬ StageTwo.curveNearEdge tape)
    (element : CurveMembership.Element) :
    ¬ StageTwo.nearEdge (BMR.offset (BmrEntry.bmrCoinsOf tape.1 tape.2) (BMR.curveEnc element)) := by
  intro near
  apply h
  rcases element with x | y
  · left
    refine ⟨BMR.xFlat (.inr x), ?_, ?_⟩
    · show Kriterion.ArgoMAC.PlanB.pointElementCountX ≤ 455 + x.slot.val
      unfold Kriterion.ArgoMAC.PlanB.pointElementCountX
      omega
    · have e := BmrEntry.gxOf_offset tape.1 tape.2 (.inr x)
      rw [← gxOf_tableOracle tape.2 tape.1] at e
      rw [e]
      exact near
  · right
    refine ⟨BMR.yFlat (.inr y), ?_, ?_⟩
    · show Kriterion.ArgoMAC.PlanB.pointElementCountY ≤ 273 + y.slot.val
      unfold Kriterion.ArgoMAC.PlanB.pointElementCountY
      omega
    · have e := BmrEntry.gyOf_offset tape.1 tape.2 (.inr y)
      rw [← gyOf_tableOracle tape.2 tape.1] at e
      rw [e]
      exact near

end Window

/-! ### 2. The table off the hidden positions, given the targets -/

section Kernel

/-- **The positions P45 hides off the curve**: the hot body positions (family 6) and every mask position (family 7). -/
def HidPos (u : AffineInput) (q : Fin (2 ^ 40)) : Prop :=
  (tagFamily q.val = 6 ∧ hotTag Entry.table u q.val = true) ∨ tagFamily q.val = 7

/-- The positions off `HidPos`. -/
abbrev OffPos (u : AffineInput) := {q : Fin (2 ^ 40) // ¬ HidPos u q}

/-- The table off the hidden positions. -/
def restrictOff (u : AffineInput) (table : TagTable) : OffPos u → Block × Block := fun q => table q.1

/-- **A site holding a position off `HidPos`** is a pad site whose slot is not the hot residue of its coordinate. -/
theorem site_of_off (u : AffineInput) {s : SiteId} (member : s ∈ crtLayout.sites) (q : OffPos u)
    (inside : q.1 ∈ Laws.sitePos crtLayout s) :
    ∃ κ i ρ, s = .pad κ i ρ ∧ ∀ h : i < Tb.count, ρ < Tb.modulus ⟨i, h⟩ ∧ ρ ≠ coordValue u κ % Tb.modulus ⟨i, h⟩ := by
  obtain ⟨code, codeIn, at_pos⟩ := List.mem_map.mp inside
  rw [Laws.RefillLayout.siteTags_eq] at codeIn
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp codeIn
  obtain ⟨famLt, inRange⟩ := Laws.RefillLayout.fields_inRange member
  have range := inRange j (List.mem_range.mp hj)
  have val := Laws.RefillLayout.tagPos_tagCode famLt range
  rw [at_pos] at val
  have notHid : ¬ HidPos u q.1 := q.2
  unfold HidPos at notHid
  rw [val] at notHid
  cases s with
  | pad κ i ρ =>
    refine ⟨κ, i, ρ, rfl, fun h => ⟨?_, ?_⟩⟩
    · rcases List.mem_append.mp member with pad | mask
      · obtain ⟨κ', i', ρ', same, -, -, hρ⟩ := Layout.mem_padSites pad
        cases same
        rw [← PadLaw.padModulus_eq ⟨i, h⟩]
        exact hρ
      · rcases Layout.mem_maskSites mask with ⟨k, same, -⟩ | ⟨k, same, -⟩ <;> cases same
    · change TagInRange κ i 0 0 ρ j at range
      change ¬ ((tagFamily (tagCode Family.body κ i 0 0 ρ j) = 6 ∧
        hotTag Entry.table u (tagCode Family.body κ i 0 0 ρ j) = true) ∨
          tagFamily (tagCode Family.body κ i 0 0 ρ j) = 7) at notHid
      have hfam : tagFamily (tagCode Family.body κ i 0 0 ρ j) = 6 := tagFamily_tagCode range
      have hcoord : tagCoord (tagCode Family.body κ i 0 0 ρ j) = κ := tagCoord_tagCode range
      have hidx : tagIdx (tagCode Family.body κ i 0 0 ρ j) = i := tagIdx_tagCode range
      have hslot : tagSlot (tagCode Family.body κ i 0 0 ρ j) = ρ := tagSlot_tagCode range
      have cold : hotTag Entry.table u (tagCode Family.body κ i 0 0 ρ j) = false := by
        cases hh : hotTag Entry.table u (tagCode Family.body κ i 0 0 ρ j)
        · rfl
        · exact absurd (Or.inl ⟨hfam, hh⟩) notHid
      unfold hotTag at cold
      simp only [hfam, hcoord, hidx, hslot, dif_pos h] at cold
      have key : (ρ == coordValue u κ % Tb.modulus ⟨i, h⟩) = false := by simpa using cold
      intro same
      simp [same] at key
  | mask st k =>
    exfalso
    change TagInRange 0 0 st 0 k j at range
    change ¬ ((tagFamily (tagCode Family.mask 0 0 st 0 k j) = 6 ∧
        hotTag Entry.table u (tagCode Family.mask 0 0 st 0 k j) = true) ∨
          tagFamily (tagCode Family.mask 0 0 st 0 k j) = 7) at notHid
    have hfam : tagFamily (tagCode Family.mask 0 0 st 0 k j) = 7 := tagFamily_tagCode range
    exact notHid (Or.inr hfam)

/-- **The table off the hidden positions, given the targets, depends only on the cold pads.** -/
theorem given_restrictOff (u : AffineInput) (τ τ' : Targets) (cold : coldOfPads u τ.1 = coldOfPads u τ'.1) :
    (crtKernel.given τ).map (restrictOff u) = (crtKernel.given τ').map (restrictOff u) := by
  show (BmrKernel.given τ).map (restrictOff u) = (BmrKernel.given τ').map (restrictOff u)
  refine TargetLaw.map_condLaw _ _ BmrKernel.targets_uniform (restrictOff u) τ τ' fun z => ?_
  have e : ∀ σ : Targets, {x | restrictOff u x = z ∧ bmrTargetsOf x = σ} =
      {t | (∀ q : OffPos u, t q.1 = z q) ∧ bmrTargetsOf t = σ} := by
    intro σ
    ext t
    simp only [Set.mem_ofPred_eq, restrictOff, funext_iff]
  rw [e, e]
  refine swapped_event_eq (fun q : OffPos u => q.1) z τ τ' fun s member => ?_
  rintro ⟨q, inside⟩
  obtain ⟨κ, i, ρ, rfl, away⟩ := site_of_off u member q inside
  show PadLaw.matchSite τ.1 _ ∩ _ = PadLaw.matchSite τ'.1 _ ∩ _
  rw [BmrKernel.cold_match u τ τ' cold away]
  rfl

end Kernel

/-! ### 3. Masses of events that agree on supports -/

section Support

theorem outer_le_of_fd {X Z : Type} (p p' : PMF X) (f : X → Z) (same : p.map f = p'.map f) (E E' : Set X)
    (fd : ∀ x ∈ p.support, ∀ x' ∈ p'.support, f x = f x' → x ∈ E → x' ∈ E') :
    p.toOuterMeasure E ≤ p'.toOuterMeasure E' := by
  calc p.toOuterMeasure E = p.toOuterMeasure (E ∩ p.support) := (PMF.toOuterMeasure_apply_inter_support p E).symm
    _ ≤ p.toOuterMeasure (f ⁻¹' (f '' (E ∩ p.support))) := by
        refine PMF.toOuterMeasure_mono p fun x inside => ?_
        exact ⟨x, inside.1, rfl⟩
    _ = (p.map f).toOuterMeasure (f '' (E ∩ p.support)) := (PMF.toOuterMeasure_map_apply f p _).symm
    _ = (p'.map f).toOuterMeasure (f '' (E ∩ p.support)) := by rw [same]
    _ = p'.toOuterMeasure (f ⁻¹' (f '' (E ∩ p.support))) := PMF.toOuterMeasure_map_apply f p' _
    _ ≤ p'.toOuterMeasure E' := by
        refine PMF.toOuterMeasure_mono p' fun x' inside => ?_
        obtain ⟨hZ, inS'⟩ := inside
        obtain ⟨x, ⟨inE, inS⟩, hx⟩ := hZ
        exact fd x inS x' inS' hx inE

/-- **Two laws with the same image under `f`, and two events that agree on the supports wherever `f` agrees, have the
same mass.** -/
theorem outer_eq_of_fd {X Z : Type} (p p' : PMF X) (f : X → Z) (same : p.map f = p'.map f) (E E' : Set X)
    (fd : ∀ x ∈ p.support, ∀ x' ∈ p'.support, f x = f x' → (x ∈ E ↔ x' ∈ E')) :
    p.toOuterMeasure E = p'.toOuterMeasure E' :=
  le_antisymm (outer_le_of_fd p p' f same E E' fun x hx x' hx' hf => (fd x hx x' hx' hf).mp)
    (outer_le_of_fd p' p f same.symm E' E fun x' hx' x hx hf => (fd x hx x' hx' hf.symm).mpr)

end Support

/-! ### 4. The bound, for a view that reads P45 only through its output -/

section Bound

variable [FieldCertificate] [GroupCertificate]

/-- P45's context of a rest (every layer gives the same context, `bmrContextOf_congr`). -/
def ctxOf (scalar : NonZeroScalar) (r : Rest) : BMR.Context :=
  BmrEntry.bmrContextOf scalar (splitEquiv.symm (r, Classical.arbitrary Layer))

theorem ctxOf_eq (scalar : NonZeroScalar) (r : Rest) (l : Layer) :
    BmrEntry.bmrContextOf scalar (splitEquiv.symm (r, l)) = ctxOf scalar r :=
  bmrContextOf_congr scalar (by rw [ctxPart_symm, ctxPart_symm])

/-- **A view that reads P45 only through its output**: at a fixed rest of the coins, two tapes whose P45 outputs
publish the same cells and hints and whose tables agree off the hidden positions have the same view. -/
def ViewFD {α : Type} (scalar : NonZeroScalar) (u : AffineInput)
    (V : Kriterion.ArgoMAC.Scheme.Coins → TagTable → α) : Prop :=
  ∀ (r : Rest) (l l' : Layer) (T T' : TagTable),
    (BMR.realOutOff (ctxOf scalar r) u (BmrEntry.bmrCoinsOf (splitEquiv.symm (r, l)) T)).1 =
        (BMR.realOutOff (ctxOf scalar r) u (BmrEntry.bmrCoinsOf (splitEquiv.symm (r, l')) T')).1 →
      restrictOff u T = restrictOff u T' → V (splitEquiv.symm (r, l)) T = V (splitEquiv.symm (r, l')) T'

/-- The view's conditional mass given the coins and the targets. -/
def phi {α : Type} (V : Kriterion.ArgoMAC.Scheme.Coins → TagTable → α) (v : α)
    (coins : Kriterion.ArgoMAC.Scheme.Coins) (τ : Targets) : ℝ≥0∞ :=
  (crtKernel.given τ).toOuterMeasure {T | V coins T = v}

/-- On the kernel's support P45's coins are the targets and the coins' layer. -/
theorem coins_of_support (coins : Kriterion.ArgoMAC.Scheme.Coins) (τ : Targets) (T : TagTable)
    (member : T ∈ (crtKernel.given τ).support) :
    BmrEntry.bmrCoinsOf coins T = coinsOf τ (layerOf coins) := by
  obtain ⟨pads, masks⟩ := crtKernel.reads τ T member
  exact BmrReal.bmrCoinsOf_of_reads coins T τ pads masks

/-- **At a fixed rest, the view's conditional mass is a function of P45's output.** -/
theorem phi_congr {α : Type} (scalar : NonZeroScalar) (u : AffineInput)
    (V : Kriterion.ArgoMAC.Scheme.Coins → TagTable → α) (fd : ViewFD scalar u V) (v : α) (r : Rest)
    (l l' : Layer) (τ τ' : Targets)
    (same : BMR.realOutOff (ctxOf scalar r) u (coinsOf τ l) = BMR.realOutOff (ctxOf scalar r) u (coinsOf τ' l')) :
    phi V v (splitEquiv.symm (r, l)) τ = phi V v (splitEquiv.symm (r, l')) τ' := by
  unfold phi
  refine outer_eq_of_fd _ _ (restrictOff u) (given_restrictOff u τ τ' (congrArg Prod.snd same)) _ _
    fun T hT T' hT' agree => ?_
  have c1 : BmrEntry.bmrCoinsOf (splitEquiv.symm (r, l)) T = coinsOf τ l := by
    rw [coins_of_support _ τ T hT, layerOf_symm]
  have c2 : BmrEntry.bmrCoinsOf (splitEquiv.symm (r, l')) T' = coinsOf τ' l' := by
    rw [coins_of_support _ τ' T' hT', layerOf_symm]
  have eqv := fd r l l' T T' (by rw [c1, c2, same]) agree
  show V (splitEquiv.symm (r, l)) T = v ↔ V (splitEquiv.symm (r, l')) T' = v
  rw [eqv]

open Classical in
/-- The indicator of window-free curve encodings and the key label, at P45's coins. -/
def keyInd (ctx : BMR.Context) (u : AffineInput) (ℓ : ℕ) (c : BMR.Coins Tb) : ℝ≥0∞ :=
  if BmrOff.CurveWindowFree u (BmrOff.cellsOfOut (BMR.realOutOff ctx u c)) ∧ (c.bridge).val % 2 ^ 128 = ℓ then 1
  else 0

/-- P45's summed bound at a fixed rest, through the targets and the layer. -/
theorem rest_le {α : Type} (scalar : NonZeroScalar) (u : AffineInput) (off : ¬ OnCurve u)
    (V : Kriterion.ArgoMAC.Scheme.Coins → TagTable → α) (fd : ViewFD scalar u V) (v : α) (ℓ : ℕ) (r : Rest) :
    ∑' l : Layer, ∑' τ : Targets, phi V v (splitEquiv.symm (r, l)) τ * keyInd (ctxOf scalar r) u ℓ (coinsOf τ l) ≤
      BmrOff.keyError * ∑' l : Layer, ∑' τ : Targets, phi V v (splitEquiv.symm (r, l)) τ := by
  classical
  let F : BMR.OutOff Tb u → ℝ≥0∞ := fun o =>
    if h : ∃ p : Targets × Layer, BMR.realOutOff (ctxOf scalar r) u (coinsOf p.1 p.2) = o then
      phi V v (splitEquiv.symm (r, h.choose.2)) h.choose.1 else 0
  have F_spec : ∀ (l : Layer) (τ : Targets),
      phi V v (splitEquiv.symm (r, l)) τ = F (BMR.realOutOff (ctxOf scalar r) u (coinsOf τ l)) := by
    intro l τ
    have h : ∃ p : Targets × Layer,
        BMR.realOutOff (ctxOf scalar r) u (coinsOf p.1 p.2) = BMR.realOutOff (ctxOf scalar r) u (coinsOf τ l) :=
      ⟨(τ, l), rfl⟩
    simp only [F, dif_pos h]
    exact phi_congr scalar u V fd v r l h.choose.2 τ h.choose.1 h.choose_spec.symm
  have reidx : ∀ H : BMR.Coins Tb → ℝ≥0∞, ∑' l : Layer, ∑' τ : Targets, H (coinsOf τ l) = ∑' c, H c := by
    intro H
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    exact coinsEquiv.tsum_eq H
  simp only [F_spec]
  rw [reidx (fun c => F (BMR.realOutOff (ctxOf scalar r) u c) * keyInd (ctxOf scalar r) u ℓ c),
    reidx (fun c => F (BMR.realOutOff (ctxOf scalar r) u c))]
  have w := BmrOff.keyLabel_weighted Flags.Wrap.entryTableFacts (ctxOf scalar r) u off F ℓ
  rw [← tsum_fintype (L := SummationFilter.unconditional _),
    ← tsum_fintype (L := SummationFilter.unconditional _)] at w
  exact w

open Classical in
/-- **The key label at the entry, off the curve**: for a view that reads P45 only through its output, the swapped
tapes with the view, the bridge key's low part `ℓ` and curve encodings far from the edges weigh at most `keyError` of
the tapes with the view. -/
theorem keyLabel_entry {α : Type} (scalar : NonZeroScalar) (u : AffineInput) (off : ¬ OnCurve u)
    (V : Kriterion.ArgoMAC.Scheme.Coins → TagTable → α) (fd : ViewFD scalar u V) (v : α) (ℓ : ℕ) :
    (swappedTableTape crtEntry).toOuterMeasure
        {tape | V tape.1 tape.2 = v ∧ tape.1.bridgeKey.val % 2 ^ 128 = ℓ ∧ ¬ StageTwo.curveNearEdge tape} ≤
      BmrOff.keyError * (swappedTableTape crtEntry).toOuterMeasure {tape | V tape.1 tape.2 = v} := by
  rw [BmrReal.swappedTableTape_eq crtKernel]
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  -- the event given the coins and the targets
  have step : ∀ (coins : Kriterion.ArgoMAC.Scheme.Coins) (τ : Targets),
      (crtKernel.given τ).toOuterMeasure ((fun table => ((coins, table) : TableTape crtEntry)) ⁻¹'
        {tape | V tape.1 tape.2 = v ∧ tape.1.bridgeKey.val % 2 ^ 128 = ℓ ∧ ¬ StageTwo.curveNearEdge tape}) ≤
      phi V v coins τ * keyInd (BmrEntry.bmrContextOf scalar coins) u ℓ (coinsOf τ (layerOf coins)) := by
    intro coins τ
    unfold keyInd
    split_ifs with good
    · rw [mul_one]
      exact PMF.toOuterMeasure_mono _ fun T inside => inside.1.1
    · rw [mul_zero, nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff]
      refine Set.disjoint_left.mpr fun T member inside => good ⟨?_, inside.2.1⟩
      rw [← coins_of_support coins τ T member]
      exact curveWindowFree_of_far _ u _ (far_of_not_curveNearEdge (coins, T) inside.2.2)
  have hphi : ∀ (coins : Kriterion.ArgoMAC.Scheme.Coins) (τ : Targets),
      (crtKernel.given τ).toOuterMeasure ((fun table => ((coins, table) : TableTape crtEntry)) ⁻¹'
        {tape | V tape.1 tape.2 = v}) = phi V v coins τ := fun _ _ => rfl
  refine le_trans (ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun τ =>
    mul_le_mul' le_rfl (step coins τ))) ?_
  simp only [hphi]
  -- the uniform weights are constants
  obtain ⟨c0⟩ : Nonempty Kriterion.ArgoMAC.Scheme.Coins := ⟨crtEntry.coinWitness⟩
  obtain ⟨τ0⟩ : Nonempty Targets := inferInstance
  have hcoin : ∀ c : Kriterion.ArgoMAC.Scheme.Coins, coinLaw c = coinLaw c0 := by
    intro c
    unfold coinLaw
    rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  have htarget : ∀ τ : Targets, PMF.uniformOfFintype Targets τ = PMF.uniformOfFintype Targets τ0 := by
    intro τ
    rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  simp only [hcoin, htarget, ENNReal.tsum_mul_left]
  rw [mul_left_comm BmrOff.keyError, mul_left_comm BmrOff.keyError]
  refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
  -- the coins as a rest and a layer
  have split : ∀ f : Kriterion.ArgoMAC.Scheme.Coins → ℝ≥0∞,
      ∑' c, f c = ∑' r : Rest, ∑' l : Layer, f (splitEquiv.symm (r, l)) := by
    intro f
    rw [← splitEquiv.symm.tsum_eq f]
    exact ENNReal.tsum_prod' (f := fun x : Rest × Layer => f (splitEquiv.symm x))
  conv_lhs => rw [split]
  conv_rhs => rw [split]
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun r => ?_
  simp only [layerOf_symm, ctxOf_eq]
  exact rest_le scalar u off V fd v ℓ r

end Bound

end

end Kriterion.CRT.Privacy.KeyOffEntry
