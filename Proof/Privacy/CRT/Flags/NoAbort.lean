/-
**P8, no abort for `crtEntry`** (`CrtNoAbort`): `M'`'s stage 2 at the empty stage-1 state, with no reveal, never
flags.

* The rows kernel, the preimage sampler and the fourth block of `crtEntry`'s view always return (the rows kernel is
  a map of `some`; `collectorSample_ne_none`, `drawAll_ne_none`).
* A collector program fails only at a point already stored. The private replay from the empty oracle stores no
  collector point (`replay_collectorFree`): every query of its two programs is a labelled input of a key that is no
  collector key (`replayConv_tagged`, `viewNonCollectorReplay_tagged`; `keyed_ne_collector`), the key
  query is a family-10 input, and a refill installs only the points of a drawable site (`sitePoint_ne_collector`). The 546 requests are pairwise distinct (`requestPoints_nodup`: the collector numbers of
  `collectorList` are `0, …, 272`), so every program succeeds (`programHashAll_isSome`).
-/

import Proof.Privacy.CRT.Flags.CrtFlags
import Proof.Privacy.CRT.Flags.ThirdSwap
import Proof.Privacy.CRT.Paths.SingleLabel

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open Kriterion.CRT.Paths (TagKey KeyRun Tagged SitesOK)
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### 1. States without collector points -/

section Free

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- **No stored point is a collector point**, at any key. -/
def CollectorFree (σ : LazyOracle.State FI EI) : Prop :=
  ∀ x ∈ storedPoints σ, ∀ (key : Block) (k j : ℕ), k < 65536 → j < 64 → x ≠ collectorPoint key k j

theorem collectorFree_empty : CollectorFree (LazyOracle.empty : LazyOracle.State FI EI) := by
  intro x member
  simp [storedPoints, LazyOracle.empty] at member

/-- The key of collector `k`'s answer `j`. -/
def collectorKey (k j : ℕ) : TagKey := ⟨7, 0, 0, 0, 0, k, j⟩

theorem collectorKey_range {k j : ℕ} (hk : k < 65536) (hj : j < 64) : (collectorKey k j).InRange :=
  ⟨show 7 < 16 by decide, show 0 < 2 by decide, show 0 < 128 by decide, show 0 < 4 by decide,
    show 0 < 16 by decide, hk, hj⟩

theorem hashInput_lt (label : Block) {tag : ℕ} (small : tag < 2 ^ 40) : hashInput label tag < 2 ^ 168 := by
  unfold hashInput
  exact Refill.point_lt label.isLt small

theorem hashInput_div (label : Block) (tag : ℕ) : hashInput label tag / 2 ^ 128 = tag := by
  unfold hashInput
  exact Refill.point_div label.isLt

/-- **A labelled input of a key that is no collector key is no collector point.** -/
theorem keyed_ne_collector {key' : TagKey} (range : key'.InRange) (away : key'.fam ≠ 7 ∨ key'.stage ≠ 0)
    (label K : Block) {k j : ℕ} (hk : k < 65536) (hj : j < 64) :
    ((hashInput label key'.code : ℕ) : BaseField) ≠ collectorPoint K k j := by
  intro same
  have rangeC : (collectorKey k j).InRange := collectorKey_range hk hj
  have eq := Refill.natCast_inj_of_lt (hashInput_lt label (TagKey.code_lt range))
    (hashInput_lt K (TagKey.code_lt rangeC)) same
  have codes : key'.code = (collectorKey k j).code := by
    have := congrArg (· / 2 ^ 128) eq
    simp only [hashInput_div] at this
    exact this
  have keys := TagKey.code_injective range rangeC codes
  subst keys
  simp [collectorKey] at away

/-- What a lazy hash query stores: the old points and its own. -/
theorem query_stored (σ : LazyOracle.State FI EI) (x : BaseField) (a : (Block × Block) × LazyOracle.State FI EI)
    (member : a ∈ (LazyOracle.query (.hash x) σ).support) (y : BaseField) (stored : y ∈ storedPoints a.2) :
    y ∈ storedPoints σ ∨ y = x := by
  unfold LazyOracle.query at member
  simp only at member
  obtain ⟨b, inQuery, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  subst same
  rcases hashQuery_support σ.hash x b inQuery with ⟨kept, _⟩ | added
  · left
    show y ∈ σ.hash.map Prod.fst
    have : y ∈ b.2.map Prod.fst := stored
    rwa [kept] at this
  · have : y ∈ b.2.map Prod.fst := stored
    rw [added, List.map_cons, List.mem_cons] at this
    rcases this with same | old
    · exact Or.inr same
    · exact Or.inl old

/-- What an installation stores: the old points and the installed ones. -/
theorem install_stored : ∀ (pairs : List (BaseField × (Block × Block))) (σ : LazyOracle.State FI EI) (y : BaseField),
    y ∈ storedPoints (installPoints pairs σ) → y ∈ storedPoints σ ∨ y ∈ pairs.map Prod.fst
  | [], σ, y, stored => Or.inl stored
  | pair :: rest, σ, y, stored => by
    unfold installPoints at stored
    rw [List.foldl_cons] at stored
    rcases install_stored rest _ y stored with old | inRest
    · unfold LazyOracle.program at old
      simp only at old
      split at old
      · have : y ∈ pair.1 :: σ.hash.map Prod.fst := old
        rcases List.mem_cons.mp this with same | older
        · exact Or.inr (by rw [same]; exact List.mem_cons_self)
        · exact Or.inl older
      · exact Or.inl old
    · exact Or.inr (List.mem_cons_of_mem _ inRest)

/-- What a refill query stores: the old points, its own, and the points of the site it refills. -/
theorem refill_stored (layout : SiteLayout) (input : ℕ) (σ : LazyOracle.State FI EI)
    (a : (Block × Block) × LazyOracle.State FI EI) (member : a ∈ (refillReader layout input σ).support)
    (y : BaseField) (stored : y ∈ storedPoints a.2) :
    y ∈ storedPoints σ ∨ y = (input : BaseField) ∨
      ∃ site, siteOf (input / 2 ^ 128) = some site ∧ y ∈ sitePoints layout site (input % 2 ^ 128) := by
  unfold refillReader at member
  cases hsite : siteOf (input / 2 ^ 128) with
  | none =>
    rw [hsite] at member
    rcases query_stored σ _ a member y stored with old | same
    · exact Or.inl old
    · exact Or.inr (Or.inl same)
  | some site =>
    rw [hsite] at member
    dsimp only at member
    split at member
    · obtain ⟨answers, -, inLazy⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      rcases query_stored _ _ a inLazy y stored with installed | same
      · rcases install_stored _ σ y installed with old | inPairs
        · exact Or.inl old
        · right; right
          refine ⟨site, rfl, ?_⟩
          obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp inPairs
          exact (List.of_mem_zip pairMember).1
      · exact Or.inr (Or.inl same)
    · rcases query_stored σ _ a member y stored with old | same
      · exact Or.inl old
      · exact Or.inr (Or.inl same)

/-- **A refill run of a tag run with no collector key stores no collector point.** -/
theorem keyRun_collectorFree (layout : SiteLayout) {S : Set TagKey} {α : Type}
    {Q : α → List (TagKey × Block) → Prop} (sites : SitesOK layout S)
    (few : ∀ site ∈ layout.sites, layout.answers site ≤ 64) (away : ∀ k ∈ S, k.fam ≠ 7 ∨ k.stage ≠ 0)
    {seen : List (TagKey × Block)} {R : CM α} (run : KeyRun S Q seen R) :
    ∀ σ : LazyOracle.State FI EI, CollectorFree σ →
      ∀ p ∈ (runReader (refillReader layout) R σ).support, CollectorFree p.2 := by
  induction run with
  | pure seen value post =>
    intro σ free p member
    simp only [runReader, PMF.mem_support_pure_iff] at member
    subst member
    exact free
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
    intro σ free p pMember
    simp only [runReader] at pMember
    obtain ⟨a, aMember, pRest⟩ := (PMF.mem_support_bind_iff _ _ _).mp pMember
    refine ih a.1 a.2 ?_ p pRest
    intro x stored K k j hk hj
    rcases refill_stored layout _ σ a aMember x stored with old | same | ⟨site, decode, inSite⟩
    · exact free x old K k j hk hj
    · rw [same, ← coded]
      exact keyed_ne_collector range (away key member) label K hk hj
    · rw [hashInput_div, ← coded, Paths.siteOf_code range] at decode
      obtain ⟨siteMember, notCollector⟩ := sites key member range site decode
      have drawable : Refill.Drawable site := ⟨key.code, by rw [Paths.siteOf_code range]; exact decode, notCollector⟩
      exact Refill.sitePoint_ne_collector drawable (few site siteMember) (Nat.mod_lt _ (by positivity)) inSite K hk hj

end Free

/-! ### 2. The private replay of `crtEntry` stores no collector point -/

section Replay

variable [FieldCertificate] [GroupCertificate]

theorem replayConvKeys_away : ∀ k ∈ Paths.replayConvKeys, k.fam ≠ 7 ∨ k.stage ≠ 0 := by
  intro k member
  have := Paths.replayConvKeys_sub member
  simp only [Paths.coordKeys, Set.mem_union, Set.mem_ofPred_eq] at this
  left
  omega

theorem nonCollectorKeys_away : ∀ k ∈ Paths.nonCollectorKeys digitCount, k.fam ≠ 7 ∨ k.stage ≠ 0 := by
  intro k member
  simp only [Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
    Set.mem_ofPred_eq] at member
  right
  omega

/-- The key's input is a family-10 input. -/
theorem keyField_ne_collector (t : BaseField) (K : Block) {k j : ℕ} (hk : k < 65536) (hj : j < 64) :
    EntryReading.keyField t ≠ collectorPoint K k j := by
  have range : (⟨10, 0, 0, 0, 0, 0, 0⟩ : TagKey).InRange :=
    ⟨show 10 < 16 by decide, show 0 < 2 by decide, show 0 < 128 by decide, show 0 < 4 by decide,
      show 0 < 16 by decide, show 0 < 65536 by decide, show 0 < 64 by decide⟩
  exact keyed_ne_collector range (Or.inl (by decide)) (BitVec.ofNat 128 t.val) K hk hj

/-- **The private replay of `crtEntry` from the empty oracle stores no collector point.** -/
theorem replay_collectorFree (published : crtEntry.Public) (u : AffineInput) (labels : LamportSignature)
    (ran : ReplayOut × LazyOracle.State Empty Empty)
    (member : ran ∈ (routeMReplay (viewHere crtEntry) (refillReader crtEntry.layout) published u labels
      LazyOracle.empty).support) :
    CollectorFree ran.2 := by
  unfold routeMReplay at member
  obtain ⟨conv, convMember, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  obtain ⟨keyed, keyedMember, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp rest
  obtain ⟨masked, maskedMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp rest
  subst same
  have convFree : CollectorFree conv.2 :=
    keyRun_collectorFree crtLayout Paths.replayConvKeys_sites crtLayout_answers_le replayConvKeys_away
      (Paths.replayConv_tagged published u labels) LazyOracle.empty collectorFree_empty conv convMember
  have keyedFree : CollectorFree keyed.2 := by
    intro x stored K k j hk hj
    rcases query_stored conv.2 _ keyed keyedMember x stored with old | same
    · exact convFree x old K k j hk hj
    · rw [same]
      exact keyField_ne_collector _ K hk hj
  exact keyRun_collectorFree crtLayout Paths.nonCollectorKeys_sites crtLayout_answers_le
    nonCollectorKeys_away (Paths.viewNonCollectorReplay_tagged keyed.1.1) keyed.2 keyedFree masked maskedMember

end Replay

/-! ### 3. The collector programs succeed -/

section Programs

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- **Distinct fresh points are all programmed.** -/
theorem programHashAll_isSome :
    ∀ (requests : List (BaseField × (Block × Block))) (σ : LazyOracle.State FI EI),
      (∀ r ∈ requests, r.1 ∉ storedPoints σ) → (requests.map Prod.fst).Nodup →
        (programHashAll requests σ).isSome
  | [], _, _, _ => rfl
  | (point, answer) :: rest, σ, fresh, nodup => by
    have notStored : point ∉ storedPoints σ := fresh _ List.mem_cons_self
    have lookupNone : σ.hash.lookup point = none := by
      cases found : σ.hash.lookup point with
      | none => rfl
      | some v => exact absurd (mem_keys_of_lookup σ.hash point v found) notStored
    have step : LazyOracle.program (.hash point) answer σ =
        some { σ with hash := (point, Refill.hashCode answer) :: σ.hash } := by
      unfold LazyOracle.program
      simp only
      rw [if_pos lookupNone]
      rfl
    show ((LazyOracle.program (.hash point) answer σ).bind (programHashAll rest)).isSome
    rw [step]
    rw [List.map_cons, List.nodup_cons] at nodup
    refine programHashAll_isSome rest _ (fun r member stored => ?_) nodup.2
    have : r.1 ∈ point :: storedPoints σ := stored
    rcases List.mem_cons.mp this with same | old
    · exact nodup.1 (List.mem_map.mpr ⟨r, member, same⟩)
    · exact fresh r (List.mem_cons_of_mem _ member) old

/-- The collector numbers of `collectorList`. -/
theorem collectorList_indices : collectorList.map collectorIndex = List.range 273 := by
  decide +kernel

/-- A draw over a list keeps its keys. -/
theorem drawAll_keys {α β : Type} (sample : α → PMF (Option β)) :
    ∀ (l : List α) (drawn : List (α × β)), some drawn ∈ (drawAll sample l).support → drawn.map Prod.fst = l
  | [], drawn, member => by
    simp only [drawAll, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    rfl
  | a :: rest, drawn, member => by
    simp only [drawAll] at member
    obtain ⟨b, -, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    rcases b with _ | b
    · simp at inner
    · obtain ⟨tail, tailMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
      rcases tail with _ | tail
      · simp at same
      · simp only [Option.map_some, Option.some.injEq] at same
        subst same
        rw [List.map_cons, drawAll_keys sample rest tail tailMember]

/-- The request points of a draw over `collectorList`. -/
theorem requestPoints_eq (key : Block) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (keys : drawn.map Prod.fst = collectorList) :
    (programRequests key drawn).map Prod.fst =
      (List.range 273).flatMap fun i => [collectorPoint key i 0, collectorPoint key i 1] := by
  rw [← collectorList_indices, ← keys]
  unfold programRequests
  simp only [List.map_flatMap, List.flatMap_map, List.map_cons, List.map_nil]

theorem collectorPoint_inj (key : Block) {i i' j j' : ℕ} (hi : i < 65536) (hi' : i' < 65536) (hj : j < 64)
    (hj' : j' < 64) (same : collectorPoint key i j = collectorPoint key i' j') : i = i' ∧ j = j' := by
  have range : (collectorKey i j).InRange := collectorKey_range hi hj
  have range' : (collectorKey i' j').InRange := collectorKey_range hi' hj'
  have eq := Refill.natCast_inj_of_lt (hashInput_lt key (TagKey.code_lt range))
    (hashInput_lt key (TagKey.code_lt range')) same
  have codes : (collectorKey i j).code = (collectorKey i' j').code := by
    have := congrArg (· / 2 ^ 128) eq
    simp only [hashInput_div] at this
    exact this
  have keys := TagKey.code_injective range range' codes
  simp only [collectorKey, TagKey.mk.injEq] at keys
  exact ⟨keys.2.2.2.2.2.1, keys.2.2.2.2.2.2⟩

/-- **The 546 request points are pairwise distinct.** -/
theorem requestPoints_nodup (key : Block) :
    ((List.range 273).flatMap fun i => [collectorPoint key i 0, collectorPoint key i 1]).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun i member => ?_, ?_⟩
  · have small : i < 65536 := lt_trans (List.mem_range.mp member) (by decide)
    rw [List.nodup_cons, List.nodup_cons]
    refine ⟨fun inTail => ?_, fun inNil => absurd inNil List.not_mem_nil, List.nodup_nil⟩
    rw [List.mem_singleton] at inTail
    exact absurd (collectorPoint_inj key small small (by decide) (by decide) inTail).2 (by decide)
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
    intro i i' member member' different
    show List.Disjoint _ _
    have small := lt_trans (List.mem_range.mp member) (show 273 < 65536 by decide)
    have small' := lt_trans (List.mem_range.mp member') (show 273 < 65536 by decide)
    rw [List.disjoint_left]
    intro x inFirst inSecond
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inFirst inSecond
    rcases inFirst with rfl | rfl <;> rcases inSecond with same | same <;>
      exact different (collectorPoint_inj key small small' (by decide) (by decide) same).1

/-- **Every collector program succeeds** on a private state with no collector point. -/
theorem programs_isSome (σ : LazyOracle.State FI EI) (free : CollectorFree σ) (key : Block)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (keys : drawn.map Prod.fst = collectorList) :
    (programHashAll (programRequests key drawn) σ).isSome := by
  have nodup : ((programRequests key drawn).map Prod.fst).Nodup := by
    rw [requestPoints_eq key drawn keys]
    exact requestPoints_nodup key
  refine programHashAll_isSome _ σ (fun r member stored => ?_) nodup
  have inPoints : r.1 ∈ (programRequests key drawn).map Prod.fst := List.mem_map_of_mem member
  rw [requestPoints_eq key drawn keys, List.mem_flatMap] at inPoints
  obtain ⟨i, iMember, inPair⟩ := inPoints
  have small : i < 65536 := lt_trans (List.mem_range.mp iMember) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inPair
  rcases inPair with same | same <;> rw [same] at stored <;>
    exact free _ stored key i _ small (by decide) rfl

end Programs

/-! ### 4. No abort -/

theorem tsum_mul_zero {α : Type} (μ : PMF α) (g : α → ℝ≥0∞) (zero : ∀ a ∈ μ.support, g a = 0) :
    ∑' a, μ a * g a = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  by_cases member : a ∈ μ.support
  · rw [zero a member, mul_zero]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul]

theorem finish_false_flagDown {FI EI : Type} [DecidableEq FI] [DecidableEq EI] (labels : LamportSignature)
    (state : LazyOracle.State FI EI) : flagDown (finishPrivate LazyOracle.empty labels False state) = 0 := by
  unfold finishPrivate
  rw [if_neg (fun either => either.elim (not_meets_empty state) id)]
  rfl

/-- A draw over a list whose every sample returns never aborts. -/
theorem drawAll_ne_none {α β : Type} (sample : α → PMF (Option β))
    (never : ∀ a, ∀ o ∈ (sample a).support, o ≠ none) :
    ∀ l : List α, none ∉ (drawAll sample l).support
  | [], member => by simp [drawAll] at member
  | a :: rest, member => by
    simp only [drawAll] at member
    obtain ⟨drawn, drawnMember, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    rcases drawn with _ | b
    · exact never a none drawnMember rfl
    · obtain ⟨tail, tailMember, tailSame⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
      rcases tail with _ | tail
      · exact drawAll_ne_none sample never rest tailMember
      · simp at tailSame

/-- `crtEntry`'s collector sample never aborts. -/
theorem collectorSample_ne_none [FieldCertificate] [GroupCertificate] (value : BaseField)
    (o : Option ((Block × Block × Block) × Block))
    (member : o ∈ (((viewHere crtEntry).preimage value).bind fun limbs => match limbs with
      | none => PMF.pure none
      | some limbs => (viewHere crtEntry).fourth.map (Option.map fun fourth => (limbs, fourth))).support) :
    o ≠ none := by
  obtain ⟨limbs, limbsMember, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  obtain ⟨pre, -, preSame⟩ := (PMF.mem_support_map_iff _ _ _).mp limbsMember
  subst preSame
  obtain ⟨fourth, fourthMember, fourthSame⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
  obtain ⟨f, -, fSame⟩ := (PMF.mem_support_map_iff _ _ _).mp fourthMember
  subst fSame
  subst fourthSame
  simp

/-- **`CrtNoAbort`.** -/
theorem crtNoAbort : CrtNoAbort := by
  intro field group scalar source u
  letI := field
  letI := group
  letI := @Fintype.ofFinite Empty inferInstance
  letI := Classical.decEq Empty
  unfold flagAt
  generalize (crtEntry.scheme inferInstance inferInstance).function scalar u = output
  cases output with
  | none =>
    simp only [middleStage2, withReveal]
    refine tsum_mul_zero _ _ fun o member => ?_
    obtain ⟨coin, -, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨ran, -, same⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
    rw [← same]
    exact finish_false_flagDown _ _
  | some target =>
    simp only [middleStage2, withReveal]
    rw [tsum_bind_mul]
    refine tsum_mul_zero _ _ fun ran ranMember => ?_
    have free := replay_collectorFree _ u _ ran ranMember
    rw [if_neg (not_meets_empty ran.2), tsum_bind_mul]
    refine tsum_mul_zero _ _ fun drawnRows rowsMember => ?_
    obtain ⟨coins, -, rowsSame⟩ := (PMF.mem_support_map_iff _ _ _).mp rowsMember
    rw [← rowsSame]
    dsimp only
    rw [tsum_bind_mul]
    refine tsum_mul_zero _ _ fun drawn drawnMember => ?_
    rcases drawn with _ | drawn
    · exfalso
      exact drawAll_ne_none _ (fun c o member => collectorSample_ne_none _ o member) collectorList drawnMember
    · have keys := drawAll_keys _ collectorList drawn drawnMember
      obtain ⟨installed, programmed⟩ := Option.isSome_iff_exists.mp
        (programs_isSome ran.2 free ran.1.key drawn keys)
      dsimp only
      rw [programmed]
      dsimp only
      rw [tsum_bind_mul]
      refine tsum_mul_zero _ _ fun coin _ => ?_
      rw [tsum_map_mul]
      exact tsum_mul_zero _ _ fun p _ => finish_false_flagDown _ _

end

end Kriterion.CRT.Privacy.Flags
