/-
**(B) on the curve: `M'`'s private stage 2 below the ideal view law**.

At one source on the curve, `middleStage2_on` writes `M'`'s stage 2 as a swapped table followed by the rest of the
stage on the replay's value and the deterministic private state; `idealCore`'s body at that source draws the same
table, the same rows and the same collector answers. The comparison is then pointwise in (table, rows, draws):

* a replay that meets `σ₁`, an abort and a failed collector program weigh nothing on `M'`'s side;
* if the ideal reveal holds on the programmed table, the shadow's reveal holds on every final private state (the
  named input `OnFlag`), so `M'` weighs nothing;
* otherwise `shadow_law_step` bounds the shadow's flagged run by the adversary's stage 2 on the merge of
  the private state into `σ₁`, and `merge_sameLookup` with the containment clause of the named input `OnDecomp` (the
  private state after the collector programs has the lookups of the view's entries other than `u`'s digest labels)
  makes that the weight of the view without the digest labels.
* the digest labels are visible but `M'` leaves them to lazy reads, so the comparison holds after averaging
  the ideal side over the table at their positions (`OnDecomp`'s `P`, outside every site): installing uniform answers
  there is invisible (`uniform_part_invisible'`).

* `idealOnAt`, `idealCore_eq`: `idealCore` is a uniform source, then `idealOnAt`;
* **`middleOn_le`**: the bound at one source;
* **`crtMiddle_on`**: the bound summed over the source, at an input on the curve.
-/

import Proof.Privacy.CRT.Laws.Invisible

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.H8
open Kriterion.CRT.Privacy.PublicFirst (Meets mergeState finishPrivate stageTwoWeight middleStage2 middleWeight
  collectorDraws OffRun viewHere contHW shadow_law_step shadow_law_meets weight_none tsum_bind_mul tsum_map_mul
  tsum_pure_mul_eq CrtShadow)
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

section On

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

open Classical in
/-- **The ideal view law on the curve at one source** (the body of `idealCore`). -/
def idealOnAt (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (source : (viewHere E).Source) :
    PMF (Option (CoreView E T u)) :=
  (swappedTableLaw E.layout).bind fun table =>
    let published := (viewHere E).publish source
    let labels := (viewHere E).labels source u
    let out := ((viewHere E).replayProgram published u labels).eval (tagHash table)
    ((viewHere E).realRows scalar u Q).bind fun drawnRows => match drawnRows with
      | none => PMF.pure none
      | some targets =>
        (collectorDrawsOf E (collectorMasks u out ((viewHere E).gammaOf published) targets)).map fun drawn =>
          match drawn with
          | none => none
          | some drawn =>
            if reveal source u targets (programmedTable table drawn) then none
            else some (published, labels, fun tag => programmedTable table drawn tag.1)

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem idealCore_eq (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) :
    idealCore E T reveal scalar u Q =
      (letI := (viewHere E).sourceFintype
       haveI := (viewHere E).sourceNonempty
       (PMF.uniformOfFintype (viewHere E).Source).bind (idealOnAt E T reveal scalar u Q)) := rfl

omit [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem collectorDraws_eq [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI]
    [DecidableEq EI] (masks : BMR.Collector → BaseField) : collectorDraws E masks = collectorDrawsOf E masks := rfl

/-- The weight of an optional view (a flag weighs nothing). -/
def optWeight (T : CrtTable) (u : AffineInput) (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool) : Option (CoreView E T u) → ℝ≥0∞
  | none => 0
  | some v => weight v.1 * viewWeight E T u v planted decide b

/-- The replay's value on a table. -/
abbrev outOf (table : TagTable) (source : (viewHere E).Source) (u : AffineInput) : ReplayOut :=
  (replayOf E source u).eval (tagHash table)

/-- The private state after the replay on a table. -/
abbrev finOf (table : TagTable) (source : (viewHere E).Source) (u : AffineInput) : LazyOracle.State FI EI :=
  tableFinal E.layout table (replayOf E source u) LazyOracle.empty

/-- The ideal view of a table and the collector draws. -/
abbrev viewOf (T : CrtTable) (source : (viewHere E).Source) (u : AffineInput) (table : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) : CoreView E T u :=
  ((viewHere E).publish source, (viewHere E).labels source u, fun tag => programmedTable table drawn tag.1)

/-- The view's entries at inputs outside a list (for the CRT entry: all but `u`'s digest labels). -/
def restEntries (T : CrtTable) (u : AffineInput) (ds : List BaseField) (v : CoreView E T u) : List (Entry FI EI) :=
  (viewEntries E T u v).filter fun e => decide (entryInput e ∉ ds)

/-- A table with the positions `P` taken from `w`. -/
def overlayP (P : Finset (Fin (2 ^ 40))) (w t : TagTable) : TagTable := fun p => if p ∈ P then w p else t p

/-- **The decomposition on the curve (named input)**, with a finite set `P` of positions and inputs `ds`
(for the CRT entry: the visible family-8 positions at `u` and `u`'s digest-label inputs): `P` lies outside every site
and is visible at `u`; the inputs `ds` have pairwise distinct tags, all in `P`; the collector programming leaves `P`
alone; the replay's value and the reveal on the programmed table ignore `P`; the view's entries are hash entries,
split as the entries off `ds` followed by the view table's answers at `ds`, and the former ignore `P`; and after the
collector programs of draws covering every collector, the private state has the lookups of the entries off `ds`. -/
def OnDecomp (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (source : (viewHere E).Source) (u : AffineInput) (P : Finset (Fin (2 ^ 40))) (ds : List BaseField) : Prop :=
  (∀ p ∈ P, ∀ site ∈ E.layout.sites, p ∉ (siteTags E.layout site).map tagPos) ∧
    (∀ p ∈ P, visTag T u p.val = true) ∧
    (ds.map tagOfInput).Nodup ∧ (∀ x ∈ ds, tagOfInput x ∈ P) ∧
    (∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))), ∀ p ∈ P,
      programmedTable table drawn p = table p) ∧
    Ignores ↑P (fun table => outOf E table source u) ∧
    (∀ (targets : Fin 91 → FieldMacToECMac.HomogeneousValue)
      (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (t t' : TagTable),
      (∀ p, p ∉ P → t p = t' p) →
        (reveal source u targets (programmedTable t drawn) ↔ reveal source u targets (programmedTable t' drawn))) ∧
    (∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))),
      HashEntries (viewEntries E T u (viewOf E T source u table drawn))) ∧
    (∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))),
      viewEntries E T u (viewOf E T source u table drawn) =
        restEntries E T u ds (viewOf E T source u table drawn) ++
          tableEntries (viewTable E T u (viewOf E T source u table drawn)) ds) ∧
    (∀ drawn : List (BMR.Collector × ((Block × Block × Block) × Block)),
      Ignores ↑P fun table => restEntries E T u ds (viewOf E T source u table drawn)) ∧
    ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
      (installed : LazyOracle.State FI EI), drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (outOf E table source u).key drawn) (finOf E table source u) = some installed →
        ∀ x, installed.hash.lookup x =
          (Privacy.installEntries (restEntries E T u ds (viewOf E T source u table drawn)) LazyOracle.empty).hash.lookup x

/-- **The flag on the curve (named input)**: the ideal reveal on the programmed table implies the shadow's reveal on
every final private state. -/
def OnFlag (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (source : (viewHere E).Source) (u : AffineInput) : Prop :=
  ∀ (table : TagTable) (targets : Fin 91 → FieldMacToECMac.HomogeneousValue)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State FI EI)
    (coin : shadow.Coin),
    programHashAll (programRequests (outOf E table source u).key drawn) (finOf E table source u) = some installed →
      ∀ shadowed ∈ (runReader lazyReader (shadow.onCurve source u coin) installed).support,
        reveal source u targets (programmedTable table drawn) → shadow.revealOn source u targets coin shadowed.2

/-! #### The ideal side at one table -/

omit [FieldCertificate] [GroupCertificate] in
theorem drawAll_keys {α β : Type} (sample : α → PMF (Option β)) :
    ∀ (l : List α) (drawn : List (α × β)), some drawn ∈ (drawAll sample l).support → drawn.map Prod.fst = l
  | [], drawn, member => by
      have same : some drawn = some [] := (PMF.mem_support_pure_iff _ _).mp member
      cases same
      rfl
  | a :: rest, drawn, member => by
      obtain ⟨first, -, hit⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      rcases first with _ | b
      · have same := (PMF.mem_support_pure_iff _ _).mp hit
        cases same
      · obtain ⟨tail, inTail, same⟩ := (PMF.mem_support_map_iff _ _ _).mp hit
        rcases tail with _ | tail
        · cases same
        · have eq : (a, b) :: tail = drawn := Option.some_injective _ same
          subst eq
          rw [List.map_cons, drawAll_keys sample rest tail inTail]

omit [FieldCertificate] [GroupCertificate] in
theorem tsum_swap_mul {W R : Type} (ν : W → ℝ≥0∞) (a : R → ℝ≥0∞) (X : W → R → ℝ≥0∞) :
    ∑' w, ν w * ∑' r, a r * X w r = ∑' r, a r * ∑' w, ν w * X w r := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun r => tsum_congr fun w => by ring

open Classical in
/-- The body of `idealOnAt` at one table. -/
def idealBody (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (source : (viewHere E).Source) (table : TagTable) :
    PMF (Option (CoreView E T u)) :=
  let published := (viewHere E).publish source
  let labels := (viewHere E).labels source u
  let out := ((viewHere E).replayProgram published u labels).eval (tagHash table)
  ((viewHere E).realRows scalar u Q).bind fun drawnRows => match drawnRows with
    | none => PMF.pure none
    | some targets =>
      (collectorDrawsOf E (collectorMasks u out ((viewHere E).gammaOf published) targets)).map fun drawn =>
        match drawn with
        | none => none
        | some drawn =>
          if reveal source u targets (programmedTable table drawn) then none
          else some (published, labels, fun tag => programmedTable table drawn tag.1)

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem idealOnAt_eq (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (source : (viewHere E).Source) :
    idealOnAt E T reveal scalar u Q source =
      (swappedTableLaw E.layout).bind (idealBody E T reveal scalar u Q source) := rfl

open Classical in
/-- **The ideal side at one table, expanded**, against a weight on the collector draws. -/
def expOn (_T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (source : (viewHere E).Source) (table : TagTable)
    (G : List (BMR.Collector × ((Block × Block × Block) × Block)) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' r, (viewHere E).realRows scalar u Q r * match r with
    | none => 0
    | some targets =>
      ∑' d, collectorDrawsOf E (collectorMasks u (outOf E table source u)
          ((viewHere E).gammaOf ((viewHere E).publish source)) targets) d * match d with
        | none => 0
        | some drawn => if reveal source u targets (programmedTable table drawn) then 0 else G drawn

/-- A weight on views, extended by `0` to a flag. -/
def optOf (T : CrtTable) (u : AffineInput) (F : CoreView E T u → ℝ≥0∞) : Option (CoreView E T u) → ℝ≥0∞
  | none => 0
  | some v => F v

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- **The ideal side at one table is `expOn`** of the weight at the view. -/
theorem idealBody_tsum (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (source : (viewHere E).Source) (table : TagTable)
    (F : CoreView E T u → ℝ≥0∞) :
    ∑' o, idealBody E T reveal scalar u Q source table o * optOf E T u F o =
      expOn E T reveal scalar u Q source table fun drawn => F (viewOf E T source u table drawn) := by
  unfold idealBody expOn
  dsimp only
  rw [tsum_bind_mul]
  refine tsum_congr fun r => congrArg _ ?_
  rcases r with _ | targets
  · dsimp only
    rw [tsum_pure_mul_eq]
    rfl
  · dsimp only
    rw [tsum_map_mul]
    refine tsum_congr fun d => congrArg _ ?_
    rcases d with _ | drawn
    · rfl
    · dsimp only
      split_ifs <;> rfl

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- `expOn` commutes with an average of weights. -/
theorem expOn_tsum {W : Type} (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (source : (viewHere E).Source) (table : TagTable)
    (ν : W → ℝ≥0∞) (G : W → List (BMR.Collector × ((Block × Block × Block) × Block)) → ℝ≥0∞) :
    ∑' w, ν w * expOn E T reveal scalar u Q source table (G w) =
      expOn E T reveal scalar u Q source table fun drawn => ∑' w, ν w * G w drawn := by
  unfold expOn
  rw [tsum_swap_mul]
  refine tsum_congr fun r => congrArg _ ?_
  rcases r with _ | targets
  · simp only [mul_zero, tsum_zero]
  · dsimp only
    rw [tsum_swap_mul]
    refine tsum_congr fun d => congrArg _ ?_
    rcases d with _ | drawn
    · simp only [mul_zero, tsum_zero]
    · dsimp only
      split_ifs
      · simp only [mul_zero, tsum_zero]
      · rfl

/-- **(B) at one table, after averaging the digest labels away**: `M'`'s weight is below the ideal side with the weight
of the view's entries off `ds`. -/
theorem middleTable_le (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (Q : Point)
    (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool) (ds : List BaseField)
    (hashes : ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))),
      HashEntries (viewEntries E T u (viewOf E T source u table drawn)))
    (contain : ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
      (installed : LazyOracle.State FI EI), drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (outOf E table source u).key drawn) (finOf E table source u) = some installed →
        ∀ x, installed.hash.lookup x =
          (Privacy.installEntries (restEntries E T u ds (viewOf E T source u table drawn)) LazyOracle.empty).hash.lookup x)
    (flag : OnFlag E shadow reveal source u) (table : TagTable) :
    ∑' o, middleContOn E shadow scalar source u Q planted (outOf E table source u, finOf E table source u) o *
        (weight ((viewHere E).publish source) * stageTwoWeight (decide ((viewHere E).publish source)) b o) ≤
      expOn E T reveal scalar u Q source table fun drawn =>
        weight ((viewHere E).publish source) *
          ((LazyOracle.run (decide ((viewHere E).publish source) ((viewHere E).labels source u))
            (Privacy.installEntries (restEntries E T u ds (viewOf E T source u table drawn)) planted)).map
              Prod.fst) b := by
  unfold middleContOn expOn
  dsimp only
  by_cases meets : Meets planted (finOf E table source u)
  · rw [if_pos meets, tsum_pure_mul_eq, weight_none, mul_zero]
    exact zero_le
  · rw [if_neg meets, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun drawnRows => mul_le_mul' le_rfl ?_
    rcases drawnRows with _ | targets
    · dsimp only
      rw [tsum_pure_mul_eq, weight_none, mul_zero]
    · dsimp only
      rw [collectorDraws_eq, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun d => ?_
      rcases d with _ | drawn
      · dsimp only
        rw [tsum_pure_mul_eq, weight_none, mul_zero]
      · dsimp only
        by_cases zero : collectorDrawsOf E (collectorMasks u (outOf E table source u)
            ((viewHere E).gammaOf ((viewHere E).publish source)) targets) (some drawn) = 0
        · rw [zero, zero_mul, zero_mul]
        refine mul_le_mul' le_rfl ?_
        have keys : drawn.map Prod.fst = collectorList :=
          drawAll_keys _ _ drawn ((PMF.mem_support_iff _ _).mpr zero)
        cases privately : programHashAll (programRequests (outOf E table source u).key drawn)
            (finOf E table source u) with
        | none =>
            dsimp only
            rw [tsum_pure_mul_eq, weight_none, mul_zero]
            exact zero_le
        | some installed =>
            dsimp only
            by_cases rv : reveal source u targets (programmedTable table drawn)
            · rw [if_pos rv]
              rw [tsum_bind_mul]
              refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun coin => ?_)
              rw [tsum_map_mul]
              refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun p => ?_)
              by_cases member : p ∈ (runReader lazyReader (shadow.onCurve source u coin) installed).support
              · unfold finishPrivate
                rw [if_pos (Or.inr (flag table targets drawn installed coin privately p member rv)), weight_none,
                  mul_zero, mul_zero]
              · rw [PMF.apply_eq_zero_iff _ _ |>.mpr member, zero_mul]
            · rw [if_neg rv]
              rw [show ∀ f : Option (Option (LamportSignature × LazyOracle.State FI EI)) → ℝ≥0∞,
                  ∀ μ : PMF (Option (Option (LamportSignature × LazyOracle.State FI EI))),
                  ∑' o, μ o * (weight ((viewHere E).publish source) * f o) =
                    weight ((viewHere E).publish source) * ∑' o, μ o * f o from fun f μ => by
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr fun o => by ring]
              refine mul_le_mul' le_rfl ?_
              by_cases met : Meets planted installed
              · rw [shadow_law_meets shadow.law planted installed met _ _ _ _ b]
                exact zero_le
              · refine le_trans (shadow_law_step shadow.law planted installed _ _ _ _ b) (le_of_eq ?_)
                have restHashes : HashEntries (restEntries E T u ds (viewOf E T source u table drawn)) :=
                  fun e he => hashes table drawn e (List.mem_of_mem_filter he)
                have sl := merge_sameLookup planted installed _ restHashes
                  (contain table drawn installed keys privately) met
                show ((LazyOracle.run (decide ((viewHere E).publish source) ((viewHere E).labels source u))
                    (mergeState planted installed)).map Prod.fst) b = _
                rw [run_lookup_congr _ _ _ sl]

/-- **(B) at one source on the curve.** -/
theorem middleOn_le (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (Q : Point)
    (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool) (facts : RefillLayoutFacts E.layout) (points : PointFacts E.layout)
    (keyNonSite : ∀ conv, siteOf (((viewHere E).keyInput ((viewHere E).publish source) u conv).val / 2 ^ 128) = none)
    (path : RefillPath E.layout ∅ (LazyOracle.empty : LazyOracle.State FI EI) (replayOf E source u))
    (canon : Canonical E.layout (replayOf E source u))
    (decomp : ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField), OnDecomp E T reveal source u P ds)
    (flag : OnFlag E shadow reveal source u) :
    ∑' o, middleStage2 E shadow offRun scalar source u (some Q) planted o *
        (weight ((viewHere E).publish source) * stageTwoWeight (decide ((viewHere E).publish source)) b o) ≤
      ∑' o, idealOnAt E T reveal scalar u Q source o * optWeight E T u planted decide weight b o := by
  obtain ⟨P, ds, away, visible, nodup, inP, keepP, outIgn, revIgn, hashes, split, restIgn, contain⟩ := decomp
  set pub := (viewHere E).publish source
  set labels := (viewHere E).labels source u
  let Φ : LazyOracle.State FI EI → ℝ≥0∞ := fun σ => ((LazyOracle.run (decide pub labels) σ).map Prod.fst) b
  let R : TagTable → ℝ≥0∞ := fun t => ∑' o, idealBody E T reveal scalar u Q source t o *
    optWeight E T u planted decide weight b o
  let ν : PMF TagTable := (swappedTableLaw E.layout).map (resP P)
  -- the ideal side at a table, as `expOn`
  have Rexp : ∀ t, R t = expOn E T reveal scalar u Q source t fun drawn =>
      weight pub * viewWeight E T u (viewOf E T source u t drawn) planted decide b := by
    intro t
    have same : optWeight E T u planted decide weight b =
        optOf E T u (fun v => weight v.1 * viewWeight E T u v planted decide b) := by
      funext o
      cases o <;> rfl
    show ∑' o, _ * optWeight E T u planted decide weight b o = _
    rw [same, idealBody_tsum]
  -- the ideal side ignores `P` except through the view's entries at `ds`
  have overlaySame : ∀ w t, ∀ p, p ∉ P → overlayP P w t p = t p := fun w t p hp => by
    simp only [overlayP, if_neg hp]
  have expOverlay : ∀ w t G, expOn E T reveal scalar u Q source (overlayP P w t) G =
      expOn E T reveal scalar u Q source t G := by
    intro w t G
    have hOut : outOf E (overlayP P w t) source u = outOf E t source u := outIgn _ _ (overlaySame w t)
    unfold expOn
    rw [hOut]
    refine tsum_congr fun r => congrArg _ ?_
    rcases r with _ | targets
    · rfl
    · dsimp only
      refine tsum_congr fun d => congrArg _ ?_
      rcases d with _ | drawn
      · rfl
      · dsimp only
        have hRev := revIgn targets drawn _ _ (overlaySame w t)
        by_cases rv : reveal source u targets (programmedTable t drawn)
        · rw [if_pos (hRev.mpr rv), if_pos rv]
        · rw [if_neg (fun h => rv (hRev.mp h)), if_neg rv]
  -- averaging the view's weight over the table at `P`
  have average : ∀ t drawn, ∑' w, ν w * (weight pub *
      viewWeight E T u (viewOf E T source u (overlayP P w t) drawn) planted decide b) =
        weight pub * Φ (Privacy.installEntries (restEntries E T u ds (viewOf E T source u t drawn)) planted) := by
    intro t drawn
    have viewEq : ∀ w, viewEntries E T u (viewOf E T source u (overlayP P w t) drawn) =
        restEntries E T u ds (viewOf E T source u t drawn) ++ tableEntries w ds := by
      intro w
      rw [split, show restEntries E T u ds (viewOf E T source u (overlayP P w t) drawn) =
        restEntries E T u ds (viewOf E T source u t drawn) from restIgn drawn _ _ (overlaySame w t)]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      have tagIn := inP x hx
      show (⟨.hash x, viewTable E T u (viewOf E T source u (overlayP P w t) drawn) (tagOfInput x)⟩ : Entry FI EI) =
        ⟨.hash x, w (tagOfInput x)⟩
      unfold viewTable
      rw [dif_pos (visible _ tagIn)]
      show (⟨.hash x, programmedTable (overlayP P w t) drawn (tagOfInput x)⟩ : Entry FI EI) = _
      rw [keepP _ drawn _ tagIn]
      simp only [overlayP, if_pos tagIn]
    have weightEq : ∀ w, viewWeight E T u (viewOf E T source u (overlayP P w t) drawn) planted decide b =
        Φ (Privacy.installEntries (tableEntries w ds)
          (Privacy.installEntries (restEntries E T u ds (viewOf E T source u t drawn)) planted)) := by
      intro w
      show ((LazyOracle.run (decide pub labels) (Privacy.installEntries
        (viewEntries E T u (viewOf E T source u (overlayP P w t) drawn)) planted)).map Prod.fst) b = _
      rw [viewEq, installEntries_append]
    simp only [weightEq]
    rw [show ∑' w, ν w * (weight pub * Φ (Privacy.installEntries (tableEntries w ds)
          (Privacy.installEntries (restEntries E T u ds (viewOf E T source u t drawn)) planted))) =
        weight pub * ∑' w, ν w * Φ (Privacy.installEntries (tableEntries w ds)
          (Privacy.installEntries (restEntries E T u ds (viewOf E T source u t drawn)) planted)) by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun w => by ring]
    exact congrArg _ (uniform_part_invisible' E.layout P away (decide pub labels) _ ds nodup inP b)
  -- the chain
  rw [middleStage2_on E shadow offRun scalar source u Q planted facts points keyNonSite path canon, tsum_bind_mul,
    idealOnAt_eq, tsum_bind_mul]
  have indep := indep_swapped_read E.layout P away (resP P) fun t t' agree => funext fun p => by
    by_cases hp : p ∈ P
    · simp only [resP, if_pos hp, agree p hp]
    · simp only [resP, if_neg hp]
  calc ∑' t, swappedTableLaw E.layout t *
        ∑' o, middleContOn E shadow scalar source u Q planted (outOf E t source u, finOf E t source u) o *
          (weight pub * stageTwoWeight (decide pub) b o)
      ≤ ∑' t, swappedTableLaw E.layout t * expOn E T reveal scalar u Q source t fun drawn =>
          weight pub * Φ (Privacy.installEntries (restEntries E T u ds (viewOf E T source u t drawn)) planted) :=
        ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl
          (middleTable_le E T shadow reveal scalar source u Q planted decide weight b ds hashes contain flag t)
    _ = ∑' t, swappedTableLaw E.layout t * ∑' w, ν w * R (overlayP P w t) := by
        refine tsum_congr fun t => congrArg _ ?_
        simp only [Rexp, expOverlay]
        rw [expOn_tsum]
        exact congrArg _ (funext fun drawn => (average t drawn).symm)
    _ = ∑' w, ν w * ∑' t, swappedTableLaw E.layout t * R (overlayP P w t) := (tsum_swap_mul _ _ _).symm
    _ = ∑' t, swappedTableLaw E.layout t * R (overlayP P (resP P t) t) :=
        (indep.tsum (fun w t => R (overlayP P w t)) fun w t t' agree => by
          show R (overlayP P w t) = R (overlayP P w t')
          congr 1
          funext p
          by_cases hp : p ∈ P
          · simp only [overlayP, if_pos hp]
          · simp only [overlayP, if_neg hp, agree p hp]).symm
    _ = ∑' t, swappedTableLaw E.layout t * R t := by
        refine tsum_congr fun t => ?_
        congr 2
        funext p
        by_cases hp : p ∈ P
        · simp only [overlayP, resP, if_pos hp]
        · simp only [overlayP, if_neg hp]

/-- **(B) on the curve**: at an input on the curve, `M'`'s weighted stage-2 mass is at most the ideal view law's. -/
theorem crtMiddle_on (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (revealOn : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (revealOff : (viewHere E).Source → AffineInput → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point)
    (onCurve : (E.scheme inferInstance inferInstance).function scalar u = some Q)
    (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool) (facts : RefillLayoutFacts E.layout) (points : PointFacts E.layout)
    (keyNonSite : ∀ source conv,
      siteOf (((viewHere E).keyInput ((viewHere E).publish source) u conv).val / 2 ^ 128) = none)
    (path : ∀ source, RefillPath E.layout ∅ (LazyOracle.empty : LazyOracle.State FI EI) (replayOf E source u))
    (canon : ∀ source, Canonical E.layout (replayOf E source u))
    (decomp : ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField), OnDecomp E T revealOn source u P ds)
    (flag : ∀ source, OnFlag E shadow revealOn source u) :
    (letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        (weight ((viewHere E).publish source) *
          middleWeight E shadow offRun scalar source u planted decide b))
      ≤ ∑' v, idealAt E T revealOn revealOff scalar u (some v) * (weight v.1 * viewWeight E T u v planted decide b) := by
  let _ : Fintype (viewHere E).Source := (viewHere E).sourceFintype
  have _ : Nonempty (viewHere E).Source := (viewHere E).sourceNonempty
  have rhs : ∑' v, idealAt E T revealOn revealOff scalar u (some v) * (weight v.1 * viewWeight E T u v planted decide b) =
      ∑' o, idealAt E T revealOn revealOff scalar u o * optWeight E T u planted decide weight b o := by
    rw [tsum_option _ ENNReal.summable]
    simp [optWeight]
  rw [rhs]
  unfold idealAt
  rw [onCurve]
  dsimp only
  rw [idealCore_eq, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
  unfold middleWeight
  rw [onCurve, ← ENNReal.tsum_mul_left]
  calc ∑' o, weight ((viewHere E).publish source) *
        (middleStage2 E shadow offRun scalar source u (some Q) planted o *
          stageTwoWeight (decide ((viewHere E).publish source)) b o)
      = ∑' o, middleStage2 E shadow offRun scalar source u (some Q) planted o *
          (weight ((viewHere E).publish source) * stageTwoWeight (decide ((viewHere E).publish source)) b o) :=
        tsum_congr fun o => by ring
    _ ≤ _ := middleOn_le E T shadow offRun revealOn scalar source u Q planted decide weight b facts points
        (keyNonSite source) (path source) (canon source) (decomp source) (flag source)

end On

end

end Kriterion.CRT.Privacy.Laws
