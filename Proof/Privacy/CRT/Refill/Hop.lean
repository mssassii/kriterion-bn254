/-
**P10: the refill hop `H → I`** (row H10, `crt_refill_of_layout`).

`H` (`openedHybrid`) and `I` (`idealHybrid`) run the same route-M simulator except for the reader of the replay:
`refillReader E.layout` against `lazyReader`. After stage 1 and the adversary's input choice, stage 2 runs route
M's replay (`routeMReplay`), draws the rows and the collector limbs, programs the collector points, and the
adversary decides. Everything after the replay depends on the lazy state only through its view and is unchanged
in law by filling points outside route M's collector points (`restView_fill`); the refilled points are never
collector points (`pending_good`: tags of distinct in-range fields, labels below `2^128`, no reduction mod `p`).
The replay itself is coupled by `couple` (`Coupling.lean`), which spends each refilled site's bias once
(`ReplaySingleLabel`). The distance is therefore at most the sum of the biases, which `SwapLayoutFacts.total`
bounds by `padSwapError`.
-/

import Proof.Privacy.CRT.Refill.Coupling
import Proof.Privacy.CRT.Swap.Layout
import Proof.Privacy.Phase3.GameSwap

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Refill

open BN254 Cryptography GarbledCircuit Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le_const advantage_eq_etvDist)
open scoped ENNReal

noncomputable section

/-! ### The refilled points are never route M's collector points -/

theorem baseFieldModulus_gt : 2 ^ 168 < baseFieldModulus := by decide

theorem natCast_inj_of_lt {a b : ℕ} (ha : a < 2 ^ 168) (hb : b < 2 ^ 168)
    (same : (a : BaseField) = (b : BaseField)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at same
  rwa [Nat.mod_eq_of_lt (lt_trans ha baseFieldModulus_gt), Nat.mod_eq_of_lt (lt_trans hb baseFieldModulus_gt)]
    at same

theorem point_lt {label t : ℕ} (hl : label < 2 ^ 128) (ht : t < 2 ^ 40) : label + 2 ^ 128 * t < 2 ^ 168 := by
  calc label + 2 ^ 128 * t < 2 ^ 128 + 2 ^ 128 * t := Nat.add_lt_add_right hl _
    _ = 2 ^ 128 * (t + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ 2 ^ 128 * 2 ^ 40 := Nat.mul_le_mul_left _ ht
    _ = 2 ^ 168 := by rw [← pow_add]

theorem point_div {label t : ℕ} (hl : label < 2 ^ 128) : (label + 2 ^ 128 * t) / 2 ^ 128 = t := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.div_eq_of_lt hl, Nat.zero_add]

theorem tagCode_lt {fam coord idx stage level slot part : ℕ} (hfam : fam < 8)
    (h : TagInRange coord idx stage level slot part) : tagCode fam coord idx stage level slot part < 2 ^ 40 := by
  have := h.coord; have := h.idx; have := h.stage; have := h.level; have := h.slot; have := h.part
  unfold tagCode
  omega

theorem drawable_pad {κ i ρ : ℕ} (drawable : Drawable (.pad κ i ρ)) : κ < 2 ∧ i < 128 ∧ ρ < 65536 := by
  obtain ⟨tag, decode, _⟩ := drawable
  unfold siteOf at decode
  split at decode
  · simp only [Option.some.injEq, SiteId.pad.injEq] at decode
    obtain ⟨rfl, rfl, rfl⟩ := decode
    refine ⟨?_, ?_, ?_⟩ <;> [unfold tagCoord; unfold tagIdx; unfold tagSlot] <;> omega
  · simp at decode
  · simp at decode

theorem drawable_mask {st k : ℕ} (drawable : Drawable (.mask st k)) : 0 < st ∧ st < 4 ∧ k < 65536 := by
  obtain ⟨tag, decode, notCollector⟩ := drawable
  unfold siteOf at decode
  split at decode
  · simp at decode
  · rename_i family
    simp only [Option.some.injEq, SiteId.mask.injEq] at decode
    obtain ⟨rfl, rfl⟩ := decode
    have stage : tagStage tag ≠ 0 := by
      intro zero
      simp [isCollectorMaskTag, family, zero] at notCollector
    refine ⟨Nat.pos_of_ne_zero stage, ?_, ?_⟩ <;> [unfold tagStage; unfold tagSlot] <;> omega
  · simp at decode

/-- **A drawable site's point is no collector point**, for any key. -/
theorem sitePoint_ne_collector {layout : SiteLayout} {site : SiteId} (drawable : Drawable site)
    (few : layout.answers site ≤ 64) {label : ℕ} (small : label < 2 ^ 128) {x : BaseField}
    (member : x ∈ sitePoints layout site label) (key : Block) {k j : ℕ} (hk : k < 65536) (hj : j < 64) :
    x ≠ collectorPoint key k j := by
  unfold sitePoints at member
  obtain ⟨t, tMember, rfl⟩ := List.mem_map.mp member
  intro same
  unfold collectorPoint at same
  have hc : TagInRange 0 0 0 0 k j := ⟨by omega, by omega, by omega, by omega, hk, hj⟩
  have collectorSmall := tagCode_lt (fam := Family.mask) (by decide) hc
  have keySmall : hashInput key (tagCode Family.mask 0 0 0 0 k j) < 2 ^ 168 := by
    unfold hashInput
    exact point_lt key.isLt collectorSmall
  have tagOf : ∀ {t'}, t' < 2 ^ 40 → (label + 2 ^ 128 * t' : ℕ) = hashInput key (tagCode Family.mask 0 0 0 0 k j) →
      t' = tagCode Family.mask 0 0 0 0 k j := by
    intro t' _ equal
    rw [← point_div (t := t') small, equal, hashInput_tag]
  cases site with
  | pad κ i ρ =>
      obtain ⟨hκ, hi, hρ⟩ := drawable_pad drawable
      simp only [siteTags, List.mem_map, List.mem_range] at tMember
      obtain ⟨j', hj', rfl⟩ := tMember
      have ht : TagInRange κ i 0 0 ρ j' := ⟨hκ, hi, by omega, by omega, hρ, by omega⟩
      have tSmall := tagCode_lt (fam := Family.body) (by decide) ht
      have equal := tagOf tSmall (natCast_inj_of_lt (point_lt small tSmall) keySmall same)
      have := (tagCode_injective ht hc equal).1
      exact absurd this (by decide)
  | mask st k' =>
      obtain ⟨hst, hst', hk'⟩ := drawable_mask drawable
      simp only [siteTags, List.mem_map, List.mem_range] at tMember
      obtain ⟨j', hj', rfl⟩ := tMember
      have ht : TagInRange 0 0 st 0 k' j' := ⟨by omega, by omega, hst', by omega, hk', by omega⟩
      have tSmall := tagCode_lt (fam := Family.mask) (by decide) ht
      have equal := tagOf tSmall (natCast_inj_of_lt (point_lt small tSmall) keySmall same)
      have := (tagCode_injective ht hc equal).2.2.2.1
      omega

/-- Points outside route M's collector points, for every key. -/
def CollectorSafe (P : Finset BaseField) : Prop :=
  ∀ (key : Block) (k j : ℕ), k < 65536 → j < 64 → collectorPoint key k j ∉ P

/-- **The pending points are never collector points.** -/
theorem pending_good (layout : SiteLayout) (few : ∀ site ∈ layout.sites, layout.answers site ≤ 64)
    {seen : SiteId → Option ℕ} {S : List (SiteId × ℕ)} (inv : Inv layout seen S) :
    CollectorSafe (pending layout S) := by
  intro key k j hk hj member
  unfold pending at member
  rw [List.mem_toFinset, List.mem_flatMap] at member
  obtain ⟨e, eMember, xMember⟩ := member
  obtain ⟨siteMember, drawable, small⟩ := inv.site e eMember
  exact sitePoint_ne_collector drawable (few _ siteMember) small xMember key hk hj rfl

theorem collectorIndex_lt (c : BMR.Collector) : collectorIndex c < 273 := by
  have := c.1.1.isLt
  unfold collectorIndex
  split <;> omega

theorem requests_outside {P : Finset BaseField} (safe : CollectorSafe P) (key : Block)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    ∀ request ∈ programRequests key drawn, request.1 ∉ P := by
  intro request member
  unfold programRequests at member
  rw [List.mem_flatMap] at member
  obtain ⟨entry, _, member⟩ := member
  have small : collectorIndex entry.1 < 65536 := lt_trans (collectorIndex_lt _) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact safe key _ 0 small (by decide)
  · exact safe key _ 1 small (by decide)

/-! ### Stage 2 on views -/

section Stage

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI] [FieldCertificate] {Public : Type}
variable (rv : RouteMView Public)

/-- Route M's replay on views. -/
def routeMReplayView (readerView : ℕ → View FI EI → PMF ((Block × Block) × View FI EI)) (published : Public)
    (u : AffineInput) (labels : LamportSignature) (w : View FI EI) : PMF (ReplayOut × View FI EI) :=
  (runView readerView (rv.replayConv published u labels) w).bind fun conv =>
    (queryView.hashQueryView conv.2 (rv.keyInput published u conv.1)).bind fun keyed =>
      (runView readerView (rv.nonCollectorReplay keyed.1.1) keyed.2).map fun masked =>
        ({ delivered := rv.delivered conv.1, masks := masked.1, key := keyed.1.1 }, masked.2)

theorem routeMReplay_view (reader : Reader FI EI) (readerView : ℕ → View FI EI → PMF ((Block × Block) × View FI EI))
    (factors : ∀ input σ, (reader input σ).map (fun a => (a.1, view a.2)) = readerView input (view σ))
    (published : Public) (u : AffineInput) (labels : LamportSignature) (σ : LazyOracle.State FI EI) :
    (routeMReplay rv reader published u labels σ).map (fun r => (r.1, view r.2))
      = routeMReplayView rv readerView published u labels (view σ) := by
  unfold routeMReplay routeMReplayView
  rw [PMF.map_bind, ← runReader_view reader readerView factors, PMF.bind_map]
  refine congrArg _ (funext fun conv => ?_)
  rw [Function.comp_apply, PMF.map_bind]
  show ((hashQuery conv.2 (rv.keyInput published u conv.1)).bind fun keyed => _) = _
  rw [← hashQuery_view, PMF.bind_map]
  refine congrArg _ (funext fun keyed => ?_)
  rw [Function.comp_apply, PMF.map_comp, ← runReader_view reader readerView factors, PMF.map_comp]
  rfl

/-- What follows route M's replay, on views: the rows, the collector limbs, the programming of the collector
points and the adversary's decision. -/
def restView (rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
    (published : Public) (u : AffineInput) (target : Point) {budget : ℕ}
    (decide : OracleProgram (publicOracleSpec FI EI) Bool budget) (out : ReplayOut) (w : View FI EI) : PMF Bool :=
  (rows u target).bind fun drawnRows => match drawnRows with
    | none => PMF.pure false
    | some targets =>
      (drawAll (fun c => (rv.preimage (collectorMasks u out (rv.gammaOf published) targets c)).bind fun limbs =>
          match limbs with
          | none => PMF.pure none
          | some limbs => rv.fourth.map (Option.map fun fourth => (limbs, fourth)))
        collectorList).bind fun drawn => match drawn with
        | none => PMF.pure false
        | some drawn => match programHashAllView (programRequests out.key drawn) w with
          | none => PMF.pure false
          | some updated => (runSampled queryView decide updated).map Prod.fst

/-- The decision after stage 2 (the staged game's last step). -/
def decideAfter {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) :
    Option (LamportSignature × LazyOracle.State FI EI) → PMF Bool
  | none => PMF.pure false
  | some (labels, updated) => (LazyOracle.run (decide labels) updated).map Prod.fst

/-- **Stage 2 followed by the decision factors through route M's replay on views.** -/
theorem stage2_view (rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
    (reader : Reader FI EI) (readerView : ℕ → View FI EI → PMF ((Block × Block) × View FI EI))
    (factors : ∀ input σ, (reader input σ).map (fun a => (a.1, view a.2)) = readerView input (view σ))
    (source : rv.Source) (u : AffineInput) (target : Point) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (σ : LazyOracle.State FI EI) :
    ((routeMSimulator rv rows reader).stage2 source u (some target) σ).bind (decideAfter decide)
      = (routeMReplayView rv readerView (rv.publish source) u (rv.labels source u) (view σ)).bind fun r =>
          restView rv rows (rv.publish source) u target (decide (rv.labels source u)) r.1 r.2 := by
  rw [← routeMReplay_view rv reader readerView factors, PMF.bind_map]
  show ((routeMReplay rv reader (rv.publish source) u (rv.labels source u) σ).bind _).bind _ = _
  rw [PMF.bind_bind]
  refine congrArg _ (funext fun ran => ?_)
  rw [Function.comp_apply, PMF.bind_bind]
  unfold restView
  refine congrArg _ (funext fun drawnRows => ?_)
  cases drawnRows with
  | none => rw [PMF.pure_bind]; rfl
  | some targets =>
      simp only []
      rw [PMF.bind_map]
      refine congrArg _ (funext fun drawn => ?_)
      cases drawn with
      | none => rfl
      | some drawn =>
          have factor := programHashAll_view (programRequests ran.1.key drawn) ran.2
          simp only [Function.comp_apply]
          cases programmed : programHashAll (programRequests ran.1.key drawn) ran.2 with
          | none =>
              rw [programmed, Option.map_none] at factor
              rw [← factor]
              rfl
          | some updated =>
              rw [programmed, Option.map_some] at factor
              rw [← factor]
              show (LazyOracle.run (decide (rv.labels source u)) updated).map Prod.fst
                = (runSampled queryView (decide (rv.labels source u)) (view updated)).map Prod.fst
              rw [← run_view, PMF.map_comp]
              rfl

/-- **The rest is unchanged in law by filling points that are never collector points.** -/
theorem restView_fill (rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
    (published : Public) (u : AffineInput) (target : Point) {budget : ℕ}
    (decide : OracleProgram (publicOracleSpec FI EI) Bool budget) (out : ReplayOut) (w : View FI EI)
    {P : Finset BaseField} (safe : CollectorSafe P) :
    (fillK w P).bind (restView rv rows published u target decide out) = restView rv rows published u target decide out w := by
  unfold restView
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun drawnRows => ?_)
  cases drawnRows with
  | none => exact PMF.bind_const _ _
  | some targets =>
      simp only []
      rw [PMF.bind_comm]
      refine congrArg _ (funext fun drawn => ?_)
      cases drawn with
      | none => exact PMF.bind_const _ _
      | some drawn =>
          simp only []
          have outside := requests_outside safe out.key drawn
          unfold fillK
          rw [PMF.bind_map]
          simp only [Function.comp_def, programHashAllView_fill _ w P _ outside]
          cases programmed : programHashAllView (programRequests out.key drawn) w with
          | none => exact PMF.bind_const _ _
          | some updated =>
              simp only [Option.map_some]
              calc (PMF.uniformOfFintype (BaseField → Block × Block)).bind
                    (fun v => (runSampled queryView decide (fill updated P v)).map Prod.fst)
                  = ((fillK updated P).bind (runSampled queryView decide)).map Prod.fst := by
                    unfold fillK
                    rw [PMF.bind_map, PMF.map_bind]
                    rfl
                _ = (runSampled queryView decide updated).map Prod.fst := by
                    rw [run_fill, PMF.map_bind]
                    conv_rhs => rw [← PMF.bind_pure (runSampled queryView decide updated), PMF.map_bind]
                    refine congrArg _ (funext fun r => ?_)
                    rw [PMF.map_comp, PMF.pure_map]
                    exact PMF.map_const _ _

/-- **The replay coupled, then the rest**: route M's replay through the refill reader and through the lazy reader,
each followed by the rest of stage 2 and the decision, are within the sum of the layout's biases. -/
theorem replay_etvDist (layout : SiteLayout) (facts : SwapLayoutFacts layout)
    (few : ∀ site ∈ layout.sites, layout.answers site ≤ 64)
    (rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
    (published : Public) (u : AffineInput) (target : Point) (labels : LamportSignature) {budget : ℕ}
    (decide : OracleProgram (publicOracleSpec FI EI) Bool budget)
    (single : SingleLabelFrom layout
      (fun seen _ => ∀ key : Block, SingleLabelFrom layout (fun _ _ => True) seen (rv.nonCollectorReplay key))
      (fun _ => none) (rv.replayConv published u labels))
    (w : View FI EI) :
    ((routeMReplayView rv (refillView layout layout.law) published u labels w).bind fun r =>
        restView rv rows published u target decide r.1 r.2).etvDist
      ((routeMReplayView rv lazyView published u labels w).bind fun r =>
        restView rv rows published u target decide r.1 r.2) ≤ (layout.sites.map facts.bias).sum := by
  let rest : ReplayOut → View FI EI → PMF Bool := restView rv rows published u target decide
  let make : rv.ConvOut → Block → (BMR.NonCollector → BaseField) → ReplayOut := fun conv key masks =>
    { delivered := rv.delivered conv, masks, key }
  let after : (ℕ → View FI EI → PMF ((Block × Block) × View FI EI)) → rv.ConvOut → View FI EI → PMF Bool :=
    fun readerView conv w' =>
      (queryView.hashQueryView w' (rv.keyInput published u conv)).bind fun keyed =>
        (runView readerView (rv.nonCollectorReplay keyed.1.1) keyed.2).bind fun m => rest (make conv keyed.1.1 m.1) m.2
  have shape : ∀ readerView : ℕ → View FI EI → PMF ((Block × Block) × View FI EI),
      ((routeMReplayView rv readerView published u labels w).bind fun r => rest r.1 r.2)
        = (runView readerView (rv.replayConv published u labels) w).bind fun r => after readerView r.1 r.2 := by
    intro readerView
    simp only [routeMReplayView, PMF.bind_bind, PMF.bind_map]
    rfl
  show ((routeMReplayView rv (refillView layout layout.law) published u labels w).bind fun r => rest r.1 r.2).etvDist
      ((routeMReplayView rv lazyView published u labels w).bind fun r => rest r.1 r.2) ≤ _
  rw [shape, shape]
  have tail : ∀ seen S (m : BMR.NonCollector → BaseField) (conv : rv.ConvOut) (key : Block) (w' : View FI EI),
      Inv layout seen S → True →
      ((fillK w' (pending layout S)).bind (rest (make conv key m))).etvDist (rest (make conv key m) w')
        ≤ cost layout facts.bias S := by
    intro seen S m conv key w' inv _
    rw [restView_fill rv rows published u target decide _ w' (pending_good layout few inv), PMF.etvDist_self]
    simp
  have middle : ∀ seen S (conv : rv.ConvOut) (w' : View FI EI), Inv layout seen S →
      (∀ key : Block, SingleLabelFrom layout (fun _ _ => True) seen (rv.nonCollectorReplay key)) →
      ((fillK w' (pending layout S)).bind (after (refillView layout layout.law) conv)).etvDist
        (after lazyView conv w') ≤ cost layout facts.bias S := by
    intro seen S conv w' inv paths
    exact hash_step _ w' _ _ _ _ fun r =>
      couple layout facts.bias facts.close (fun _ _ => True) (fun m => rest (make conv r.1.1 m))
        (fun m => rest (make conv r.1.1 m)) (fun seen' S' m w'' inv' ok => tail seen' S' m conv r.1.1 w'' inv' ok)
        (rv.nonCollectorReplay r.1.1) seen S r.2 inv (paths r.1.1)
  have start : Inv layout (fun _ => none) [] :=
    ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
  have base := couple layout facts.bias facts.close _ (after (refillView layout layout.law)) (after lazyView)
    middle (rv.replayConv published u labels) (fun _ => none) [] w start single
  rw [pending_nil, fillK_empty, PMF.pure_bind] at base
  have costNil : cost layout facts.bias [] = (layout.sites.map facts.bias).sum := by
    unfold cost
    simp
  rwa [costNil] at base

end Stage

/-! ### The games -/

/-- The abstract ideal game in staged form (xinshu's `stagedGame`, for the CRT's abstract simulators). -/
def stagedGame [FieldCertificate] {FI EI Randomness Public Key Oracle Aux : Type} [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FI EI Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : ℕ) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  (simulator.stage1 parameter LazyOracle.empty).bind fun first => match first with
  | none => PMF.pure false
  | some (circuit, state, oracle) =>
    (LazyOracle.run (adversary.chooseInput parameter circuit auxiliary) oracle).bind fun selected =>
      (simulator.stage2 state selected.1.1 (scheme.function scalar selected.1.1) selected.2).bind
        fun second => match second with
        | none => PMF.pure false
        | some (labels, updated) =>
          (LazyOracle.run (adversary.decide parameter circuit labels auxiliary selected.1.2) updated).map Prod.fst

theorem abstractIdealGame_eq_staged [FieldCertificate] {FI EI Randomness Public Key Oracle Aux : Type}
    [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FI EI Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : ℕ) (scalar : NonZeroScalar) (auxiliary : Aux) :
    abstractIdealGame scheme simulator adversary parameter scalar auxiliary =
      stagedGame scheme simulator adversary parameter scalar auxiliary := by
  unfold abstractIdealGame stagedGame
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, liftM, monadLift,
    MonadLift.monadLift, OptionT.lift, Option.elimM, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map_bind, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext first
  rcases first with _ | ⟨circuit, state, oracle⟩
  · simp [PMF.pure_map]
  · simp only [Option.elim, PMF.map_bind]
    congr 1
    funext selected
    congr 1
    funext second
    rcases second with _ | ⟨labels, updated⟩
    · simp [PMF.pure_map]
    · simp only [PMF.map_bind, PMF.pure_map, Option.getD_some]
      exact PMF.bind_pure_comp Prod.fst _

/-- **`H` and `I` are within the layout's biases.** -/
theorem refill_games_etvDist {FI EI : Type} [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI]
    [DecidableEq FI] [DecidableEq EI] (E : CrtEntry FI EI) (facts : SwapLayoutFacts E.layout)
    (single : ReplaySingleLabel E) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    (openedHybrid E adversary parameter scalar).etvDist (idealHybrid E adversary parameter scalar)
      ≤ (E.layout.sites.map facts.bias).sum := by
  unfold openedHybrid idealHybrid
  rw [abstractIdealGame_eq_staged, abstractIdealGame_eq_staged]
  unfold stagedGame
  refine etvDist_bind_left_le_const _ _ _ _ fun first => ?_
  rcases first with _ | ⟨circuit, state, oracle⟩
  · rw [PMF.etvDist_self]
    simp
  · refine etvDist_bind_left_le_const _ _ _ _ fun selected => ?_
    have after : (fun second : Option (LamportSignature × LazyOracle.State FI EI) => match second with
        | none => PMF.pure false
        | some (labels, updated) =>
          (LazyOracle.run (adversary.decide parameter circuit labels () selected.1.2) updated).map Prod.fst)
        = decideAfter (fun labels => adversary.decide parameter circuit labels () selected.1.2) := by
      funext second
      rcases second with _ | ⟨labels, updated⟩ <;> rfl
    rw [after]
    cases output : (E.scheme inferInstance inferInstance).function scalar selected.1.1 with
    | none =>
        calc _ = (0 : ℝ≥0∞) := PMF.etvDist_eq_zero_iff.mpr rfl
          _ ≤ _ := by simp
    | some target =>
        rw [stage2_view (E.view inferInstance inferInstance) ((E.view inferInstance inferInstance).simRows scalar)
            (refillReader E.layout) (refillView E.layout E.layout.law) (refillReader_view E.layout) state selected.1.1
            target (fun labels => adversary.decide parameter circuit labels () selected.1.2) selected.2,
          stage2_view (E.view inferInstance inferInstance) ((E.view inferInstance inferInstance).simRows scalar)
            lazyReader lazyView lazyReader_view state selected.1.1
            target (fun labels => adversary.decide parameter circuit labels () selected.1.2) selected.2]
        exact replay_etvDist _ E.layout facts single.answers_le _ _ _ _ _ _ (single.replay _ _ _ _) _

end

end Kriterion.CRT.Privacy.Refill

namespace Kriterion.CRT.Privacy

open BN254 Cryptography Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3 (advantage_eq_etvDist)

/-- **Ledger row H10 (P10): the refill hop `H → I` costs at most `padSwapError`**, for any entry whose site layout
satisfies `SwapLayoutFacts` and whose replay reads each site at one label (`ReplaySingleLabel`). -/
theorem crt_refill_of_layout {FI EI : Type} [Finite FI] [Finite EI] (E : CrtEntry FI EI)
    (facts : SwapLayoutFacts E.layout) (single : ReplaySingleLabel E) :
    HopBound (crtChain E).opened (crtChain E).ideal fun _ _ => padSwapError := by
  intro field group adversary parameter scalar _
  simp only [atSolution, crtChain]
  rw [advantage_eq_etvDist]
  refine ENNReal.toReal_le_of_le_ofReal padSwapError_nonneg ?_
  let _field := field
  let _group := group
  let _fintypeFI := Fintype.ofFinite FI
  let _fintypeEI := Fintype.ofFinite EI
  let _decFI := Classical.decEq FI
  let _decEI := Classical.decEq EI
  exact le_trans (Refill.refill_games_etvDist E facts single adversary parameter scalar) facts.total

/-- The real layout's sites read at most 64 answers (the `answers_le` field of `ReplaySingleLabel` for an entry
whose layout is `crtLayout`). -/
theorem crtLayout_answers_le : ∀ site ∈ crtLayout.sites, crtLayout.answers site ≤ 64 := by
  intro site member
  rcases List.mem_append.mp member with pad | mask
  · obtain ⟨κ, i, ρ, rfl, hκ, hi, _⟩ := Layout.mem_padSites pad
    have := (Layout.tableFacts κ hκ i hi).2.2.1
    show Layout.padCount κ i ≤ 64
    omega
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, _⟩ | ⟨k, rfl, _⟩
    · show 2 ≤ 64
      omega
    · show 3 ≤ 64
      omega

end Kriterion.CRT.Privacy
