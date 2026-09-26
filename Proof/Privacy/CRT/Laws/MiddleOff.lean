/-
**(B) off the curve: `M'`'s private stage 2 below the ideal view law**.

Off the curve `M'` draws a swapped table and runs the shadow's program on it (`tableRun`): every read is
answered by the table at its tag and stored. The ideal view law `idealCoreOff` shows the table at the visible tags
only. The private state therefore holds, beyond the view's entries, the table's answers at some invisible inputs (for
the CRT entry, the digest finals). Those answers sit at positions outside every site, so under the swapped law they
are uniform and independent of everything else the comparison reads; planting them is invisible to the adversary
(`plant_table_invisible`).

Named inputs, per source:

* `OffFlag` (`crtRevealOff_final_iff`): the ideal reveal on the table implies the shadow's reveal on the
  final private state;
* `OffSplit`: for each shadow coin, a finite set `P` of invisible positions outside every
  site that the reveal ignores, and inputs `xs(table)` that ignore `P`, with distinct tags in `P`, outside the view's
  entries, such that the final private state has the lookups of the view's entries followed by the table's answers
  at `xs`.

* the tools (`installEntries_isSome`, `resP`, `swapped_map_resP`, `uniform_part_invisible`) are in `Invisible.lean`;
* **`middleOff_le`**: the bound at one source;
* **`crtMiddle_off`**: the bound summed over the source, at an input off the curve.
-/

import Proof.Privacy.CRT.Laws.MiddleOn
import Proof.Privacy.CRT.Laws.Invisible

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.H8
open Kriterion.CRT.Privacy.PublicFirst (Meets mergeState finishPrivate stageTwoWeight middleStage2 middleWeight OffRun
  viewHere contHW weight_none tsum_bind_mul tsum_map_mul tsum_pure_mul_eq CrtShadow tableRun storedPoints
  mem_keys_of_lookup lookup_isSome_of_mem)
open scoped ENNReal

noncomputable section

variable {FI EI : Type}

/-! ### 1. The bound off the curve -/

variable (E : CrtEntry FI EI)

section Off

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The ideal view of a table off the curve. -/
abbrev offView (T : CrtTable) (source : (viewHere E).Source) (u : AffineInput) (table : TagTable) : CoreView E T u :=
  ((viewHere E).publish source, (viewHere E).labels source u, fun tag => table tag.1)

open Classical in
/-- **The ideal view law off the curve at one source** (the body of `idealCoreOff`). -/
def idealOffAt (T : CrtTable) (reveal : (viewHere E).Source → AffineInput → TagTable → Prop) (u : AffineInput)
    (source : (viewHere E).Source) : PMF (Option (CoreView E T u)) :=
  (swappedTableLaw E.layout).map fun table =>
    if reveal source u table then none
    else some ((viewHere E).publish source, (viewHere E).labels source u, fun tag => table tag.1)

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem idealCoreOff_eq (T : CrtTable) (reveal : (viewHere E).Source → AffineInput → TagTable → Prop)
    (u : AffineInput) :
    idealCoreOff E T reveal u =
      (letI := (viewHere E).sourceFintype
       haveI := (viewHere E).sourceNonempty
       (PMF.uniformOfFintype (viewHere E).Source).bind (idealOffAt E T reveal u)) := rfl

/-- The final private state off the curve. -/
abbrev offFinOf (shadow : CrtShadow (viewHere E).Source FI EI) (source : (viewHere E).Source) (u : AffineInput)
    (coin : shadow.Coin) (table : TagTable) : LazyOracle.State FI EI :=
  offFinal table (shadow.offCurve source u coin) LazyOracle.empty

/-- **The flag off the curve (named input).** -/
def OffFlag (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → TagTable → Prop) (source : (viewHere E).Source)
    (u : AffineInput) : Prop :=
  ∀ coin table, reveal source u table → shadow.revealOff source u coin (offFinOf E shadow source u coin table)

/-- **The decomposition off the curve (named input)**, at one shadow coin, with a finite set `P` of
positions and the extra inputs `xs`: `P` lies outside every site and is invisible at `u`; the reveal and `xs` ignore
`P`; the extra inputs have pairwise distinct tags, all in `P`, and are not inputs of the view's entries; and the final
private state has the lookups of the view's entries followed by the table's answers at the extra inputs. -/
def OffDecomp (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → TagTable → Prop) (source : (viewHere E).Source)
    (u : AffineInput) (coin : shadow.Coin) (P : Finset (Fin (2 ^ 40))) (xs : TagTable → List BaseField) : Prop :=
  (∀ p ∈ P, ∀ site ∈ E.layout.sites, p ∉ (siteTags E.layout site).map tagPos) ∧
    (∀ p ∈ P, visTag T u p.val = false) ∧
    (∀ t t' : TagTable, (∀ p, p ∉ P → t p = t' p) → (reveal source u t ↔ reveal source u t')) ∧
    Ignores ↑P xs ∧
    (∀ t, ((xs t).map tagOfInput).Nodup) ∧ (∀ t, ∀ x ∈ xs t, tagOfInput x ∈ P) ∧
    (∀ t, HashEntries (viewEntries E T u (offView E T source u t))) ∧
    (∀ t, ∀ x ∈ xs t, x ∉ (viewEntries E T u (offView E T source u t)).map entryInput) ∧
    ∀ t x, (offFinOf E shadow source u coin t).hash.lookup x =
      (Privacy.installEntries (viewEntries E T u (offView E T source u t) ++ tableEntries t (xs t))
        LazyOracle.empty).hash.lookup x

/-- The decomposition at every shadow coin. -/
def OffSplit (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → TagTable → Prop) (source : (viewHere E).Source)
    (u : AffineInput) : Prop :=
  ∀ coin : shadow.Coin, ∃ (P : Finset (Fin (2 ^ 40))) (xs : TagTable → List BaseField),
    OffDecomp E T shadow reveal source u coin P xs

omit [Fintype FI] [Fintype EI] in
theorem middleStage2_none (shadow : CrtShadow (viewHere E).Source FI EI) (scalar : NonZeroScalar)
    (source : (viewHere E).Source) (u : AffineInput) (planted : LazyOracle.State FI EI) :
    middleStage2 E shadow (tableRun (swappedTableLaw E.layout)) scalar source u none planted =
      shadow.law.bind fun coin =>
        ((swappedTableLaw E.layout).bind fun table =>
          PMF.pure ((shadow.offCurve source u coin).eval (offAnswer table), offFinOf E shadow source u coin table)).map
          fun ran => finishPrivate planted ((viewHere E).labels source u)
            (shadow.revealOff source u coin ran.2) ran.2 := by
  show shadow.law.bind (fun coin => ((swappedTableLaw E.layout).bind fun table =>
      runReader (PublicFirst.tableReader table) (shadow.offCurve source u coin) LazyOracle.empty).map _) = _
  refine congrArg _ (funext fun coin => ?_)
  refine congrArg _ (congrArg _ (funext fun table => ?_))
  exact (tableRunOff_empty table _).1

open Classical in
/-- **(B) at one source off the curve.** -/
theorem middleOff_le (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → TagTable → Prop) (scalar : NonZeroScalar)
    (source : (viewHere E).Source) (u : AffineInput) (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool) (flag : OffFlag E shadow reveal source u)
    (split : OffSplit E T shadow reveal source u) :
    ∑' o, middleStage2 E shadow (tableRun (swappedTableLaw E.layout)) scalar source u none planted o *
        (weight ((viewHere E).publish source) * stageTwoWeight (decide ((viewHere E).publish source)) b o) ≤
      ∑' o, idealOffAt E T reveal u source o * optWeight E T u planted decide weight b o := by
  set pub := (viewHere E).publish source
  set labels := (viewHere E).labels source u
  set μT := swappedTableLaw E.layout
  let Φ : LazyOracle.State FI EI → ℝ≥0∞ := fun σ => ((LazyOracle.run (decide pub labels) σ).map Prod.fst) b
  let V : TagTable → List (Entry FI EI) := fun t => viewEntries E T u (offView E T source u t)
  -- the right side, per table
  have rhs : ∑' o, idealOffAt E T reveal u source o * optWeight E T u planted decide weight b o =
      ∑' t, μT t * (if reveal source u t then 0 else weight pub * Φ (Privacy.installEntries (V t) planted)) := by
    unfold idealOffAt
    rw [tsum_map_mul]
    refine tsum_congr fun t => congrArg _ ?_
    by_cases rv : reveal source u t
    · rw [if_pos rv, if_pos rv]
      rfl
    · rw [if_neg rv, if_neg rv]
      rfl
  rw [rhs, middleStage2_none, tsum_bind_mul]
  -- average over the coins
  suffices perCoin : ∀ coin, ∑' o, (((μT.bind fun table =>
        PMF.pure ((shadow.offCurve source u coin).eval (offAnswer table), offFinOf E shadow source u coin table)).map
        fun ran => finishPrivate planted labels (shadow.revealOff source u coin ran.2) ran.2) o *
          (weight pub * stageTwoWeight (decide pub) b o)) ≤
        ∑' t, μT t * (if reveal source u t then 0 else weight pub * Φ (Privacy.installEntries (V t) planted)) by
    calc _ ≤ ∑' coin, shadow.law coin *
          ∑' t, μT t * (if reveal source u t then 0 else weight pub * Φ (Privacy.installEntries (V t) planted)) :=
          ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl (perCoin coin)
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  intro coin
  obtain ⟨P, xs, away, invis, revIgn, xsIgn, nodup, inP, hashes, disj, lookups⟩ := split coin
  let fin : TagTable → LazyOracle.State FI EI := offFinOf E shadow source u coin
  let σ : TagTable → LazyOracle.State FI EI := fun t => Privacy.installEntries (V t) planted
  have hashesVJ : ∀ t (w : TagTable), HashEntries (V t ++ tableEntries w (xs t)) := fun t w e he =>
    (List.mem_append.mp he).elim (hashes t e) (tableEntries_hash w (xs t) e)
  -- the view's entries read the table only at visible tags, so off `P`
  have VIgn : ∀ t t' : TagTable, (∀ p, p ∉ P → t p = t' p) → V t = V t' := by
    intro t t' agree
    show viewEntries E T u (offView E T source u t) = viewEntries E T u (offView E T source u t')
    congr 1
    refine Prod.ext rfl (Prod.ext rfl (funext fun tag => agree tag.1 fun hp => ?_))
    have hidden := invis tag.1 hp
    rw [tag.2] at hidden
    cases hidden
  have storedIff : ∀ t x, ((fin t).hash.lookup x).isSome ↔ (x ∈ (V t).map entryInput ∨ x ∈ xs t) := by
    intro t x
    rw [lookups t x, installEntries_isSome _ (hashesVJ t t) LazyOracle.empty x, List.map_append,
      tableEntries_inputs, List.mem_append]
    simp [LazyOracle.empty]
  have meetsIff : ∀ t, Meets planted (fin t) ↔
      ∃ x, (x ∈ (V t).map entryInput ∨ x ∈ xs t) ∧ (planted.hash.lookup x).isSome := by
    intro t
    constructor
    · rintro ⟨x, inFin, inPlanted⟩
      exact ⟨x, (storedIff t x).mp ((mem_storedPoints_iff _ x).mp inFin), (mem_storedPoints_iff _ x).mp inPlanted⟩
    · rintro ⟨x, inFin, inPlanted⟩
      exact ⟨x, (mem_storedPoints_iff _ x).mpr ((storedIff t x).mpr inFin), (mem_storedPoints_iff _ x).mpr inPlanted⟩
  -- the weight read with the extra answers taken from `w`
  let f : TagTable → TagTable → ℝ≥0∞ := fun w t =>
    if reveal source u t ∨ Meets planted (fin t) then 0
    else weight pub * Φ (Privacy.installEntries (tableEntries w (xs t)) (σ t))
  have fIgn : ∀ w, Ignores ↑P (f w) := by
    intro w t t' agree
    have vSame := VIgn t t' agree
    have xsSame : xs t = xs t' := xsIgn t t' agree
    have revSame : reveal source u t ↔ reveal source u t' := revIgn t t' agree
    have meetSame : Meets planted (fin t) ↔ Meets planted (fin t') := by
      rw [meetsIff, meetsIff, vSame, xsSame]
    simp only [f, σ, vSame, xsSame, propext revSame, propext meetSame]
  -- pointwise: `M'`'s weight is below `f` at the table's own answers
  have pointwise : ∀ t, weight pub * stageTwoWeight (decide pub) b
      (finishPrivate planted labels (shadow.revealOff source u coin (fin t)) (fin t)) ≤ f (resP P t) t := by
    intro t
    have extraSame : tableEntries (FI := FI) (EI := EI) (resP P t) (xs t) = tableEntries t (xs t) :=
      List.map_congr_left fun x hx => by simp only [resP, if_pos (inP t x hx)]
    simp only [f, extraSame]
    by_cases bad : reveal source u t ∨ Meets planted (fin t)
    · rw [if_pos bad]
      unfold finishPrivate
      rcases bad with rv | met
      · rw [if_pos (Or.inr (flag coin t rv)), weight_none, mul_zero]
      · rw [if_pos (Or.inl met), weight_none, mul_zero]
    · rw [if_neg bad]
      have rv : ¬ reveal source u t := fun h => bad (Or.inl h)
      have met : ¬ Meets planted (fin t) := fun h => bad (Or.inr h)
      unfold finishPrivate
      by_cases revealed : shadow.revealOff source u coin (fin t)
      · rw [if_pos (Or.inr revealed), weight_none, mul_zero]
        exact zero_le
      · rw [if_neg fun either => either.elim met revealed]
        refine mul_le_mul' le_rfl (le_of_eq ?_)
        have sl := merge_sameLookup planted (fin t) (V t ++ tableEntries t (xs t)) (hashesVJ t t) (lookups t) met
        show ((LazyOracle.run (decide pub labels) (mergeState planted (fin t))).map fun result => some result.1)
            (some b) = _
        rw [show (fun result : Bool × LazyOracle.State FI EI => some result.1) = some ∘ Prod.fst from rfl,
          ← PMF.map_comp, map_apply_inj _ (Option.some_injective _) b, run_lookup_congr _ _ _ sl]
        rw [installEntries_append]
  -- the left side, per table
  have lhs : ∑' o, (((μT.bind fun table =>
        PMF.pure ((shadow.offCurve source u coin).eval (offAnswer table), offFinOf E shadow source u coin table)).map
        fun ran => finishPrivate planted labels (shadow.revealOff source u coin ran.2) ran.2) o *
          (weight pub * stageTwoWeight (decide pub) b o)) =
      ∑' t, μT t * (weight pub * stageTwoWeight (decide pub) b
        (finishPrivate planted labels (shadow.revealOff source u coin (fin t)) (fin t))) := by
    rw [tsum_map_mul, tsum_bind_mul]
    exact tsum_congr fun t => congrArg _ (tsum_pure_mul_eq _ _)
  rw [lhs]
  calc ∑' t, μT t * (weight pub * stageTwoWeight (decide pub) b
          (finishPrivate planted labels (shadow.revealOff source u coin (fin t)) (fin t)))
      ≤ ∑' t, μT t * f (resP P t) t := ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl (pointwise t)
    _ = ∑' w, (μT.map (resP P)) w * ∑' t, μT t * f w t :=
        (indep_swapped_read E.layout P away (resP P) fun t t' agree => funext fun p => by
          by_cases hp : p ∈ P
          · simp only [resP, if_pos hp, agree p hp]
          · simp only [resP, if_neg hp]).tsum f fIgn
    _ = ∑' t, μT t * ∑' w, (μT.map (resP P)) w * f w t := by
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun t => tsum_congr fun w => by ring
    _ = ∑' t, μT t * (if reveal source u t ∨ Meets planted (fin t) then 0 else weight pub * Φ (σ t)) := by
        refine tsum_congr fun t => congrArg _ ?_
        by_cases bad : reveal source u t ∨ Meets planted (fin t)
        · simp only [f, if_pos bad, mul_zero, tsum_zero]
        · simp only [f, if_neg bad]
          have met : ¬ Meets planted (fin t) := fun h => bad (Or.inr h)
          have absent : ∀ x ∈ xs t, (σ t).hash.lookup x = none := by
            intro x hx
            refine Option.not_isSome_iff_eq_none.mp fun stored => ?_
            rcases (installEntries_isSome (V t) (hashes t) planted x).mp stored with inPlanted | inV
            · exact met ((meetsIff t).mpr ⟨x, Or.inr hx, inPlanted⟩)
            · exact disj t x hx inV
          calc ∑' w, (μT.map (resP P)) w *
                (weight pub * Φ (Privacy.installEntries (tableEntries w (xs t)) (σ t)))
              = weight pub * ∑' w, (μT.map (resP P)) w *
                  Φ (Privacy.installEntries (tableEntries w (xs t)) (σ t)) := by
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr fun w => by ring
            _ = weight pub * Φ (σ t) := by
                congr 1
                exact uniform_part_invisible E.layout P away (decide pub labels) (σ t) (xs t) absent (nodup t)
                  (inP t) b
    _ ≤ ∑' t, μT t * (if reveal source u t then 0 else weight pub * Φ (Privacy.installEntries (V t) planted)) := by
        refine ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl ?_
        by_cases rv : reveal source u t
        · rw [if_pos (Or.inl rv), if_pos rv]
        · rw [if_neg rv]
          split
          · exact zero_le
          · exact le_rfl

/-- **(B) off the curve**: at an input off the curve, `M'`'s weighted stage-2 mass is at most the ideal view law's. -/
theorem crtMiddle_off (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI)
    (revealOn : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (revealOff : (viewHere E).Source → AffineInput → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput)
    (offCurve : (E.scheme inferInstance inferInstance).function scalar u = none)
    (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool) (flag : ∀ source, OffFlag E shadow revealOff source u)
    (split : ∀ source, OffSplit E T shadow revealOff source u) :
    (letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        (weight ((viewHere E).publish source) *
          middleWeight E shadow (tableRun (swappedTableLaw E.layout)) scalar source u planted decide b))
      ≤ ∑' v, idealAt E T revealOn revealOff scalar u (some v) * (weight v.1 * viewWeight E T u v planted decide b) := by
  let _ : Fintype (viewHere E).Source := (viewHere E).sourceFintype
  have _ : Nonempty (viewHere E).Source := (viewHere E).sourceNonempty
  have rhs : ∑' v, idealAt E T revealOn revealOff scalar u (some v) * (weight v.1 * viewWeight E T u v planted decide b) =
      ∑' o, idealAt E T revealOn revealOff scalar u o * optWeight E T u planted decide weight b o := by
    rw [tsum_option _ ENNReal.summable]
    simp [optWeight]
  rw [rhs]
  unfold idealAt
  rw [offCurve]
  dsimp only
  rw [idealCoreOff_eq, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
  unfold middleWeight
  rw [offCurve, ← ENNReal.tsum_mul_left]
  calc ∑' o, weight ((viewHere E).publish source) *
        (middleStage2 E shadow (tableRun (swappedTableLaw E.layout)) scalar source u none planted o *
          stageTwoWeight (decide ((viewHere E).publish source)) b o)
      = ∑' o, middleStage2 E shadow (tableRun (swappedTableLaw E.layout)) scalar source u none planted o *
          (weight ((viewHere E).publish source) * stageTwoWeight (decide ((viewHere E).publish source)) b o) :=
        tsum_congr fun o => by ring
    _ ≤ _ := middleOff_le E T shadow revealOff scalar source u planted decide weight b (flag source) (split source)

end Off

/-! ### 2. The middle factor -/

/-- **(B): `CrtMiddleFactor` from the named inputs** (the paths of the replay; on the curve the decomposition
`OnDecomp` and the flag; off the curve the flag and the decomposition `OffSplit`). -/
theorem crtMiddleFactor_of (T : CrtTable)
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI)
    (revealOn : RevealOn E) (revealOff : RevealOff E)
    (facts : RefillLayoutFacts E.layout) (points : PointFacts E.layout)
    (keyNonSite : ∀ [FieldCertificate] [GroupCertificate] (source : (viewHere E).Source) (u : AffineInput) conv,
      siteOf (((viewHere E).keyInput ((viewHere E).publish source) u conv).val / 2 ^ 128) = none)
    (path : ∀ [FieldCertificate] [GroupCertificate] [DecidableEq FI] [DecidableEq EI] (source : (viewHere E).Source)
      (u : AffineInput), RefillPath E.layout ∅ (LazyOracle.empty : LazyOracle.State FI EI) (replayOf E source u))
    (canon : ∀ [FieldCertificate] [GroupCertificate] (source : (viewHere E).Source) (u : AffineInput),
      Canonical E.layout (replayOf E source u))
    (decomp : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
      (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
      (E.scheme inferInstance inferInstance).function scalar u = some Q →
        ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField), OnDecomp E T revealOn source u P ds)
    (onFlag : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
      (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
      (E.scheme inferInstance inferInstance).function scalar u = some Q →
        ∀ source, OnFlag E shadow revealOn source u)
    (offFlag : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
      (scalar : NonZeroScalar) (u : AffineInput),
      (E.scheme inferInstance inferInstance).function scalar u = none →
        ∀ source, OffFlag E shadow revealOff source u)
    (offSplit : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
      (scalar : NonZeroScalar) (u : AffineInput),
      (E.scheme inferInstance inferInstance).function scalar u = none →
        ∀ source, OffSplit E T shadow revealOff source u) :
    CrtMiddleFactor E T shadow revealOn revealOff := by
  intro _ _ _ _ _ _ scalar u planted budget decide weight b
  cases output : (E.scheme inferInstance inferInstance).function scalar u with
  | some Q =>
      exact crtMiddle_on E T shadow (tableRun (swappedTableLaw E.layout)) revealOn revealOff scalar u Q output
        planted decide weight b facts points (fun source => keyNonSite source u) (fun source => path source u)
        (fun source => canon source u) (decomp scalar u Q output) (onFlag scalar u Q output)
  | none =>
      exact crtMiddle_off E T shadow revealOn revealOff scalar u output planted decide weight b
        (offFlag scalar u output) (offSplit scalar u output)

end

end Kriterion.CRT.Privacy.Laws
