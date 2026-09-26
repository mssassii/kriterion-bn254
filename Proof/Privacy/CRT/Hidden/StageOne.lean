/-
**H6 for the CRT entry: the stage-1 guess, split by the family of the touched tag**.

A stage-1 query touches a garbler entry only at the garbler's input at its tag (`touch_garbler`): the garbler asks
each tag at one input below `p`, so the query's value `N` is one of the garbler's inputs. The tag `N / 2^128` is fixed
by the query, so its family is fixed, and H6 splits into one bound per family (`OneCase`):

* families 0 to 6 (conversion and body labels): by coarsening from the stage-2 case `convHot` at an input where the
  tag is hot (`ConvTagsReachable`), except the 30 casts of chunk 31 at leaves 49 to 63, which are hot at no input
  (`NeverHotCast`);
* family 7 (the masks, label `K`), family 9 (the digest finals, label `key_o`), family 10 (the key, label
  `t mod 2^128`): direct;
* family 8 (the digest labels): by coarsening from the stage-2 case `digestOther` at an input whose bit differs.

The coarsening (`outer_coarse_le`): the stage-2 view at any input refines the stage-1 view (its first component is the
published value), so a stage-2 bound at one input is a stage-1 bound.
-/

import Proof.Privacy.CRT.Hidden.StageTwo
import Proof.Privacy.CRT.Hidden.GuessCore

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.StageOneProof

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Privacy.StageTwo (gAsked garblerEntries_eq GuessCase convHot digestOther noExtra)
open scoped ENNReal

noncomputable section

/-! ### The touch -/

/-- **A touched garbler entry is the garbler's input at the query.** -/
theorem touch_garbler [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape Instance.crtEntry) (x : BaseField)
    (touch : Touches (garblerEntries Instance.crtEntry parameter scalar tape) (.hash x)) :
    x.val ∈ gAsked scalar tape := by
  obtain ⟨coins, table⟩ := tape
  unfold Touches at touch
  obtain ⟨entry, inGarbler, same⟩ := List.mem_map.mp touch
  rw [garblerEntries_eq] at inGarbler
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp inGarbler
  simp only at same
  have hx : x = (n : BaseField) := (PublicQuery.hash.inj same).symm
  have small := garbler_input_lt (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins n hn
  rw [hx, val_natCast_of_lt small]
  exact hn

/-- A garbler input is a labelled input at a garbler key in range. -/
theorem key_of_gAsked (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) (N : ℕ)
    (inside : N ∈ gAsked scalar tape) :
    ∃ k ∈ Paths.garblerKeys, k.InRange ∧ ∃ label, N = hashInput label k.code := by
  unfold gAsked at inside
  exact asked_of_tagged (Paths.garbleCM_tagged scalar tape.1)
    (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) N inside

/-- The tag of a garbler input is its key's code. -/
theorem tag_of_gAsked {k : Paths.TagKey} {label : Block} {N : ℕ} (same : N = hashInput label k.code) :
    N / 2 ^ 128 = k.code := by
  rw [same, hashInput_div]

/-! ### Coarsening -/

/-- **An outer measure is the sum of its parts over the fibres of a map.** -/
theorem outer_eq_tsum_fibre {Ω W : Type} (μ : PMF Ω) (f : Ω → W) (S : Set Ω) :
    μ.toOuterMeasure S = ∑' w, μ.toOuterMeasure (S ∩ {ω | f ω = w}) := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (f ω)]
  · by_cases hS : ω ∈ S
    · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (show ω ∈ S ∩ {ω' | f ω' = f ω} from ⟨hS, rfl⟩)]
    · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem (fun h => hS h.1)]
  · intro w hw
    exact Set.indicator_of_notMem (fun h => hw h.2.symm) _

/-- **A bound given a finer view is a bound given the coarser view.** -/
theorem outer_coarse_le {Ω V W : Type} (μ : PMF Ω) (fine : Ω → W) (coarse : W → V) (view : Ω → V)
    (hview : ∀ ω, view ω = coarse (fine ω)) (E : Ω → Prop) (ε : ℝ≥0∞)
    (each : ∀ w, μ.toOuterMeasure {ω | fine ω = w ∧ E ω} ≤ ε * μ.toOuterMeasure {ω | fine ω = w}) (v : V) :
    μ.toOuterMeasure {ω | view ω = v ∧ E ω} ≤ ε * μ.toOuterMeasure {ω | view ω = v} := by
  rw [outer_eq_tsum_fibre μ fine, outer_eq_tsum_fibre μ fine {ω | view ω = v}, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun w => ?_
  by_cases hw : coarse w = v
  · have e1 : {ω | view ω = v ∧ E ω} ∩ {ω | fine ω = w} = {ω | fine ω = w ∧ E ω} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hview]
      constructor
      · rintro ⟨⟨_, he⟩, hf⟩
        exact ⟨hf, he⟩
      · rintro ⟨hf, he⟩
        exact ⟨⟨by rw [hf, hw], he⟩, hf⟩
    have e2 : {ω | view ω = v} ∩ {ω | fine ω = w} = {ω | fine ω = w} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hview]
      constructor
      · rintro ⟨_, hf⟩
        exact hf
      · intro hf
        exact ⟨by rw [hf, hw], hf⟩
    rw [e1, e2]
    exact each w
  · have e1 : {ω | view ω = v ∧ E ω} ∩ {ω | fine ω = w} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, hview]
      rintro ⟨⟨hv, _⟩, hf⟩
      exact hw (hf ▸ hv)
    rw [e1, MeasureTheory.measure_empty]
    exact zero_le

/-! ### The cases -/

/-- **One case of the stage-1 guess**: at every tag satisfying `cond`, the garbler's input at it has conditional mass
at most `ε` given the published value. -/
def OneCase (cond : ℕ → Prop) (ε : ℝ≥0∞) : Prop :=
  ∀ (field : FieldCertificate) (group : GroupCertificate) (parameter : ℕ) (scalar : NonZeroScalar) (view : Instance.crtEntry.Public)
    (N : ℕ), cond (N / 2 ^ 128) →
    (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} ≤
      ε * (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | stageOneView Instance.crtEntry parameter scalar tape = view}

theorem OneCase.mono {cond cond' : ℕ → Prop} {ε ε' : ℝ≥0∞} (case : OneCase cond ε) (sub : ∀ τ, cond' τ → cond τ)
    (le : ε ≤ ε') : OneCase cond' ε' := by
  intro field group parameter scalar view N hc
  exact le_trans (case field group parameter scalar view N (sub _ hc)) (mul_le_mul' le le_rfl)

/-- A case whose tags the garbler never asks. -/
theorem oneCase_of_never {cond : ℕ → Prop} (ε : ℝ≥0∞)
    (never : ∀ scalar tape N, N ∈ gAsked scalar tape → ¬ cond (N / 2 ^ 128)) : OneCase cond ε := by
  intro field group parameter scalar view N hc
  have empty : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} = ∅ := by
    ext tape
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ inside
    exact never scalar tape N inside hc
  rw [empty, MeasureTheory.measure_empty]
  exact zero_le

/-- Two cases cover their union. -/
theorem OneCase.union {cond cond' : ℕ → Prop} {ε : ℝ≥0∞} (first : OneCase cond ε) (second : OneCase cond' ε) :
    OneCase (fun τ => cond τ ∨ cond' τ) ε := by
  intro field group parameter scalar view N hc
  rcases hc with h | h
  · exact first field group parameter scalar view N h
  · exact second field group parameter scalar view N h

/-- The stage-2 view's first component is the stage-1 view (for a generic entry, so that `rfl` does not unfold the
concrete one). -/
theorem stageTwoView_fst {FI EI : Type} (E : CrtEntry FI EI) [FieldCertificate] [GroupCertificate] (T : CrtTable)
    (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape E) :
    (stageTwoView E T parameter scalar u tape).1 = stageOneView E parameter scalar tape := rfl

/-- **Coarsening a stage-2 case**: if every garbler tag satisfying `cond` satisfies the stage-2 condition at some
input, the stage-2 bound at that input is a stage-1 bound. -/
theorem oneCase_of_guessCase {cond2 : AffineInput → ℕ → Prop} {ε : ℝ≥0∞} (case : GuessCase cond2 noExtra ε)
    (cond : ℕ → Prop)
    (reach : ∀ scalar tape N, N ∈ gAsked scalar tape → cond (N / 2 ^ 128) → ∃ u, cond2 u (N / 2 ^ 128)) :
    OneCase cond ε := by
  intro field group parameter scalar view N hc
  by_cases asked : ∃ tape, N ∈ gAsked scalar tape
  · obtain ⟨tape0, h0⟩ := asked
    obtain ⟨u, hu⟩ := reach scalar tape0 N h0 hc
    refine outer_coarse_le _ (stageTwoView Instance.crtEntry Entry.table parameter scalar u) Prod.fst
      (stageOneView Instance.crtEntry parameter scalar)
      (fun tape => (stageTwoView_fst Instance.crtEntry Entry.table parameter scalar u tape).symm)
      (fun tape => N ∈ gAsked scalar tape) ε
      (fun w => ?_) view
    refine le_trans (MeasureTheory.measure_mono ?_) (case parameter scalar u w N hu)
    intro tape member
    exact ⟨member.1, member.2, trivial⟩
  · have empty : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} = ∅ := by
      ext tape
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ inside
      exact asked ⟨tape, inside⟩
    rw [empty, MeasureTheory.measure_empty]
    exact zero_le

/-! ### Families 0 to 6 -/

/-- **The 30 casts that are hot at no input**: chunk 31's casts at leaves 49 to 63 (both coordinates; a coordinate
value is below `p`, whose top chunk is 48). -/
def NeverHotCast (τ : ℕ) : Prop := tagFamily τ = 1 ∧ tagIdx τ = 31 ∧ 49 ≤ tagSlot τ

/-- **Reachability of the conversion and body tags**: every garbler tag of families 0 to 6, except the 30 never-hot
casts, is hot at some input. -/
def ConvTagsReachable : Prop :=
  ∀ (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) (N : ℕ), N ∈ gAsked scalar tape →
    tagFamily (N / 2 ^ 128) ≤ 6 → ¬ NeverHotCast (N / 2 ^ 128) →
      ∃ u : AffineInput, hotTag Entry.table u (N / 2 ^ 128) = true

/-- **Families 0 to 6**, from the stage-2 case `convHot`, the reachability, and the never-hot casts. -/
theorem convCase_of {εConv εNever : ℝ≥0∞} (conv : GuessCase convHot noExtra εConv) (reach : ConvTagsReachable)
    (never : OneCase NeverHotCast εNever) : OneCase (fun τ => tagFamily τ ≤ 6) (max εConv εNever) := by
  have hot : OneCase (fun τ => tagFamily τ ≤ 6 ∧ ¬ NeverHotCast τ) εConv :=
    oneCase_of_guessCase conv (fun τ => tagFamily τ ≤ 6 ∧ ¬ NeverHotCast τ) fun scalar tape N inside hc => by
      obtain ⟨u, hu⟩ := reach scalar tape N inside hc.1 hc.2
      exact ⟨u, hc.1, hu⟩
  refine (OneCase.union (hot.mono (fun _ h => h) (le_max_left _ _))
    (never.mono (fun _ h => h) (le_max_right _ _))).mono ?_ le_rfl
  intro τ hτ
  by_cases h : NeverHotCast τ
  · exact Or.inr h
  · exact Or.inl ⟨hτ, h⟩

/-! ### Family 8 -/

/-- `2^253 < p`. -/
theorem pow253_lt : 2 ^ 253 < baseFieldModulus := by
  unfold baseFieldModulus
  decide +kernel

/-- An input whose bit `i` of coordinate `κ` is `1` (`i < 254`). -/
def bitInput (κ i : ℕ) : AffineInput :=
  if κ = 0 then ⟨((2 ^ i : ℕ) : BaseField), 0⟩ else ⟨0, ((2 ^ i : ℕ) : BaseField)⟩

theorem inputBit_bitInput (κ i : ℕ) (hi : i < 254) : inputBit (bitInput κ i) κ i = 1 := by
  have small : 2 ^ i < baseFieldModulus :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) pow253_lt
  unfold inputBit coordValue bitInput
  by_cases hκ : κ = 0
  · simp only [hκ, if_true]
    rw [val_natCast_of_lt small, Nat.div_self (Nat.two_pow_pos i)]
  · simp only [hκ, if_false]
    rw [val_natCast_of_lt small, Nat.div_self (Nat.two_pow_pos i)]

theorem inputBit_zero (κ i : ℕ) : inputBit ⟨0, 0⟩ κ i = 0 := by
  unfold inputBit coordValue
  by_cases hκ : κ = 0 <;> simp [hκ]

/-- **The digest labels are hidden at some input**: every garbler tag of family 8 has part `0` or `1` and position
below 254, so an input whose bit there differs exists. -/
theorem digest_reach (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) (N : ℕ)
    (inside : N ∈ gAsked scalar tape) (fam : tagFamily (N / 2 ^ 128) = 8) :
    ∃ u, digestOther u (N / 2 ^ 128) := by
  obtain ⟨k, member, range, label, same⟩ := key_of_gAsked scalar tape N inside
  rw [tag_of_gAsked same] at fam ⊢
  have famK := fam
  rw [tagFamily_key range] at famK
  have digest : k ∈ Paths.digestLabelKeys coordinateBitCount := by
    rcases member with inC | inC | inKey | inMask | inLabel | inFinal
    · simp only [Paths.coordKeys, Set.mem_ofPred_eq] at inC
      omega
    · simp only [Paths.coordKeys, Set.mem_ofPred_eq] at inC
      omega
    · rw [Set.mem_singleton_iff.mp inKey] at famK
      exact absurd famK (by decide)
    · simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
        Set.mem_ofPred_eq] at inMask
      omega
    · exact inLabel
    · simp only [Paths.digestFinalKeys, Set.mem_ofPred_eq] at inFinal
      omega
  simp only [Paths.digestLabelKeys, Set.mem_ofPred_eq] at digest
  obtain ⟨_, _, _, _, _, hslot, hpart⟩ := digest
  have tr := tagInRange_of_key range
  unfold Paths.TagKey.code at *
  refine ⟨if k.part = 1 then ⟨0, 0⟩ else bitInput k.coord k.slot, fam, ?_⟩
  rw [tagPart_tagCode tr, tagCoord_tagCode tr, tagSlot_tagCode tr]
  by_cases hp : k.part = 1
  · rw [if_pos hp, inputBit_zero, hp]
    decide
  · rw [if_neg hp, inputBit_bitInput _ _ (by simpa [coordinateBitCount] using hslot)]
    omega

/-- **Family 8**, from the stage-2 case `digestOther`. -/
theorem digestCase_of {ε : ℝ≥0∞} (digest : GuessCase digestOther noExtra ε) :
    OneCase (fun τ => tagFamily τ = 8) ε :=
  oneCase_of_guessCase digest (fun τ => tagFamily τ = 8) fun scalar tape N inside fam =>
    digest_reach scalar tape N inside fam

/-! ### The reduction -/

/-- **H6 from the five family cases.** -/
theorem crtEntry_stageOneGuess_of_cases {εConv εMask εDigest εFinal εKey : ℝ≥0∞}
    (conv : OneCase (fun τ => tagFamily τ ≤ 6) εConv) (mask : OneCase (fun τ => tagFamily τ = 7) εMask)
    (digest : OneCase (fun τ => tagFamily τ = 8) εDigest) (fin : OneCase (fun τ => tagFamily τ = 9) εFinal)
    (key : OneCase (fun τ => tagFamily τ = 10) εKey)
    (le : εConv ≤ ENNReal.ofReal crtHiddenCharge ∧ εMask ≤ ENNReal.ofReal crtHiddenCharge ∧
      εDigest ≤ ENNReal.ofReal crtHiddenCharge ∧ εFinal ≤ ENNReal.ofReal crtHiddenCharge ∧
      εKey ≤ ENNReal.ofReal crtHiddenCharge) :
    CrtStageOneGuess Instance.crtEntry (ENNReal.ofReal crtHiddenCharge) := by
  have all : OneCase (fun τ => tagFamily τ ≤ 10) (ENNReal.ofReal crtHiddenCharge) := by
    have c7 := mask.mono (fun _ h => h) le.2.1
    have c8 := digest.mono (fun _ h => h) le.2.2.1
    have c9 := fin.mono (fun _ h => h) le.2.2.2.1
    have c10 := key.mono (fun _ h => h) le.2.2.2.2
    refine (OneCase.union (conv.mono (fun _ h => h) le.1)
      (OneCase.union c7 (OneCase.union c8 (OneCase.union c9 c10)))).mono ?_ le_rfl
    intro τ hτ
    omega
  have beyond : OneCase (fun τ => ¬ tagFamily τ ≤ 10) (ENNReal.ofReal crtHiddenCharge) :=
    oneCase_of_never (cond := fun τ => ¬ tagFamily τ ≤ 10) _ fun scalar tape N inside big => by
      obtain ⟨k, member, range, label, same⟩ := key_of_gAsked scalar tape N inside
      rw [tag_of_gAsked same, tagFamily_key range] at big
      exact big (Paths.garblerKeys_fam k member)
  intro field group parameter scalar view query
  cases query with
  | fixedForward index _ => exact index.elim
  | fixedInverse index _ => exact index.elim
  | encForward index _ => exact index.elim
  | encInverse index _ => exact index.elim
  | hash x =>
    have sub : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧
        Touches (garblerEntries Instance.crtEntry parameter scalar tape) (.hash x)} ⊆
        {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ x.val ∈ gAsked scalar tape} :=
      fun tape member => ⟨member.1, touch_garbler parameter scalar tape x member.2⟩
    refine le_trans (MeasureTheory.measure_mono sub) ?_
    by_cases small : tagFamily (x.val / 2 ^ 128) ≤ 10
    · exact all field group parameter scalar view x.val small
    · exact beyond field group parameter scalar view x.val small

/-- **H6 from the stage-2 cases `convHot` and `digestOther`, the reachability, and the direct cases.** -/
theorem crtEntry_stageOneGuess_of {εConv εNever εMask εDigest εFinal εKey : ℝ≥0∞}
    (conv : GuessCase convHot noExtra εConv) (reach : ConvTagsReachable) (never : OneCase NeverHotCast εNever)
    (mask : OneCase (fun τ => tagFamily τ = 7) εMask) (digest : GuessCase digestOther noExtra εDigest)
    (fin : OneCase (fun τ => tagFamily τ = 9) εFinal) (key : OneCase (fun τ => tagFamily τ = 10) εKey)
    (le : εConv ≤ ENNReal.ofReal crtHiddenCharge ∧ εNever ≤ ENNReal.ofReal crtHiddenCharge ∧
      εMask ≤ ENNReal.ofReal crtHiddenCharge ∧ εDigest ≤ ENNReal.ofReal crtHiddenCharge ∧
      εFinal ≤ ENNReal.ofReal crtHiddenCharge ∧ εKey ≤ ENNReal.ofReal crtHiddenCharge) :
    CrtStageOneGuess Instance.crtEntry (ENNReal.ofReal crtHiddenCharge) :=
  crtEntry_stageOneGuess_of_cases (convCase_of conv reach never) mask (digestCase_of digest) fin key
    ⟨max_le le.1 le.2.1, le.2.2.1, le.2.2.2.1, le.2.2.2.2.1, le.2.2.2.2.2⟩

end

end Kriterion.CRT.Privacy.StageOneProof
