/-
**H6 for the CRT entry: the cases whose label is a table answer**.

On the table tape the published value reads the table only at the tags of families other than 8 and 10
(`pubOf_congr`): the conversion layer asks families 0 to 6, the masks are read by their tags (the key `K` is only a
label), and each digest entry reads only its final's answer (the digest key is only a label). So a garbler label that
is a table answer at a family-8 or family-10 position is uniform and independent of the published value:

* family 7 (the masks): the label is the key answer `(A keyPos).1` (`maskCase`);
* family 9 (the digest finals): the label is the XOR of digest answers at the exceptional input's bits, one of which is
  the answer at `(0, 0)` (`finalCase`).

Both bounds are `2^128 / #(Block × Block) = 2^-128`.
-/

import Proof.Privacy.CRT.Hidden.StageOne
import Proof.Privacy.CRT.Core.DigestSplit
import Proof.Privacy.CRT.Core.BmrEntry

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.StageOneProof

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Privacy.StageTwo (gAsked)
open Kriterion.CRT.Privacy.Laws (Indep Ignores)
open scoped ENNReal

noncomputable section

/-! ### Tagged programs read the hash only at their keys -/

/-- **A tagged program reads the hash only at its keys**: its value and its asked inputs agree on two hashes that agree
at every labelled input of its keys. -/
theorem keyRun_congr {α : Type} {S : Set Paths.TagKey} {Q : α → List (Paths.TagKey × Block) → Prop}
    {seen : List (Paths.TagKey × Block)} {P : CM α} (run : Paths.KeyRun S Q seen P) (H H' : HashN)
    (agree : ∀ k ∈ S, k.InRange → ∀ label, H (hashInput label k.code) = H' (hashInput label k.code)) :
    P.eval H = P.eval H' ∧ asked H P = asked H' P := by
  induction run with
  | pure seen value post => exact ⟨rfl, rfl⟩
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
    have h := agree key member range label
    rw [coded] at h
    show (next (H (hashInput label tag))).eval H = (next (H' (hashInput label tag))).eval H' ∧
      hashInput label tag :: asked H (next (H (hashInput label tag))) =
        hashInput label tag :: asked H' (next (H' (hashInput label tag)))
    rw [h]
    exact ⟨(ih _).1, by rw [(ih _).2]⟩

/-- On a keyed input the scheme's reading of the table oracle is the tag reading. -/
theorem schemeHash_key (A : TagTable) {k : Paths.TagKey} (range : k.InRange) (label : Block) :
    schemeHash (tableOracle (FI := Empty) (EI := Empty) A) (hashInput label k.code) =
      H8.tagHash A (hashInput label k.code) := by
  rw [Asks.schemeHash_small A _ (Asks.hashInput_small label _ (Paths.TagKey.code_lt range))]
  rfl

/-- **The garbler on the table oracle is the garbler on the tag reading.** -/
theorem garbleCM_tagHash (scalar : NonZeroScalar) (coins : Entry.Coins) (A : TagTable) :
    (garbleCM scalar coins).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) A)) =
        (garbleCM scalar coins).eval (H8.tagHash A) ∧
      asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) A)) (garbleCM scalar coins) =
        asked (H8.tagHash A) (garbleCM scalar coins) :=
  keyRun_congr (Paths.garbleCM_tagged scalar coins) _ _ fun _ _ range label => schemeHash_key A range label

theorem gAsked_eq (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) :
    gAsked scalar tape = asked (H8.tagHash tape.2) (garbleCM scalar tape.1) :=
  (garbleCM_tagHash scalar tape.1 tape.2).2

/-- The stage-1 view is the first component of the real garbling (generic entry). -/
theorem stageOneView_realGarbled {FI EI : Type} (E : CrtEntry FI EI) [FieldCertificate] [GroupCertificate]
    (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) :
    stageOneView E parameter scalar tape = (H8.realGarbled E parameter scalar tape).1 := rfl

/-- **The stage-1 view is the published value on the tag reading.** -/
theorem stageOneView_eq [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape Instance.crtEntry) :
    stageOneView Instance.crtEntry parameter scalar tape = EntryCorrect.pubOf (H8.tagHash tape.2) scalar tape.1 := by
  rw [stageOneView_realGarbled, ConvSplit.realGarbled_eq, (garbleCM_tagHash scalar tape.1 tape.2).1]
  exact congrArg Prod.fst (EntryCorrect.garbleCM_eval (H8.tagHash tape.2) scalar tape.1)

/-! ### What the published value reads -/

/-- A position given by a tag below `2^40`. -/
theorem tagHash_key (A : TagTable) {k : Paths.TagKey} (range : k.InRange) (label : Block) :
    H8.tagHash A (hashInput label k.code) = A (Conv.tag40 k.code) :=
  BmrEntry.tagHash_hashInput A label k.code

theorem family_tag40 {k : Paths.TagKey} (range : k.InRange) : tagFamily (Conv.tag40 k.code).val = k.fam := by
  show tagFamily (k.code % 2 ^ 40) = k.fam
  rw [Nat.mod_eq_of_lt (Paths.TagKey.code_lt range)]
  exact tagFamily_key range

/-- **The digest entries on a tag table**: each reads only its two finals' answers. -/
theorem entriesOf_tagHash (A : TagTable) (scalar : NonZeroScalar) (coins : Entry.Coins) (o : Fin digitCount) :
    EntryCorrect.entriesOf (H8.tagHash A) scalar coins o =
      DigestSplit.entryOf ((outputKeysOf scalar coins).get o).digit
        ((outputKeysOf scalar coins).get o).offset.coordinates (coins.exceptionPad.get o,
          (A (DigestSplit.finalPos (2 * o.val)), A (DigestSplit.finalPos (2 * o.val + 1)))) := by
  unfold EntryCorrect.entriesOf digestEntries garbleEntry DigestSplit.entryOf
  cases digitEndomorphismBase ((outputKeysOf scalar coins).get o).digit with
  | none => rfl
  | some phi =>
      simp only
      unfold finalMask h128
      rw [BmrEntry.tagHash_hashInput, BmrEntry.tagHash_hashInput]
      rfl

/-- **The published value reads the table only at families other than 8 and 10.** -/
theorem pubOf_congr (scalar : NonZeroScalar) (coins : Entry.Coins) (A A' : TagTable)
    (agree : ∀ p : Fin (2 ^ 40), tagFamily p.val ≠ 8 → tagFamily p.val ≠ 10 → A p = A' p) :
    EntryCorrect.pubOf (H8.tagHash A) scalar coins = EntryCorrect.pubOf (H8.tagHash A') scalar coins := by
  have keyed : ∀ (S : Set Paths.TagKey), (∀ k ∈ S, k.fam ≠ 8 ∧ k.fam ≠ 10) → ∀ k ∈ S, k.InRange → ∀ label,
      H8.tagHash A (hashInput label k.code) = H8.tagHash A' (hashInput label k.code) := by
    intro S fams k member range label
    rw [tagHash_key A range, tagHash_key A' range]
    exact agree _ (by rw [family_tag40 range]; exact (fams k member).1)
      (by rw [family_tag40 range]; exact (fams k member).2)
  have coordFams : ∀ κ, ∀ k ∈ Paths.coordKeys κ, k.fam ≠ 8 ∧ k.fam ≠ 10 := by
    intro κ k member
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  have gx : EntryCorrect.gxOf (H8.tagHash A) coins = EntryCorrect.gxOf (H8.tagHash A') coins :=
    (keyRun_congr (Paths.coordGarbleM_tagged Entry.table Entry.xCount 0 (Paths.bn254_ranges _ (by decide))
      (by norm_num) _ _) _ _ (keyed _ (coordFams 0))).1
  have gy : EntryCorrect.gyOf (H8.tagHash A) coins = EntryCorrect.gyOf (H8.tagHash A') coins :=
    (keyRun_congr (Paths.coordGarbleM_tagged Entry.table Entry.yCount 1 (Paths.bn254_ranges _ (by decide))
      (by norm_num) _ _) _ _ (keyed _ (coordFams 1))).1
  have masks : EntryCorrect.masksOf (H8.tagHash A) coins = EntryCorrect.masksOf (H8.tagHash A') coins := by
    have maskFams : ∀ k ∈ Paths.maskKeys digitCount, k.fam ≠ 8 ∧ k.fam ≠ 10 := by
      intro k member
      simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
        Set.mem_setOf_eq] at member
      omega
    have tagged := Paths.maskAnswersM_tagged (0 : Block) digitCount (by decide) (by decide)
    have same := (keyRun_congr tagged (H8.tagHash A) (H8.tagHash A') (keyed _ maskFams)).1
    calc EntryCorrect.masksOf (H8.tagHash A) coins
        = maskValues (H8.tagHash A) 0 digitCount := BmrEntry.maskValues_tagHash A _
      _ = (maskAnswersM (0 : Block) digitCount).eval (H8.tagHash A) := (eval_maskAnswersM _ _ _).symm
      _ = (maskAnswersM (0 : Block) digitCount).eval (H8.tagHash A') := same
      _ = maskValues (H8.tagHash A') 0 digitCount := eval_maskAnswersM _ _ _
      _ = EntryCorrect.masksOf (H8.tagHash A') coins := (BmrEntry.maskValues_tagHash A' _).symm
  have entries : EntryCorrect.entriesOf (H8.tagHash A) scalar coins = EntryCorrect.entriesOf (H8.tagHash A') scalar coins := by
    funext o
    rw [entriesOf_tagHash, entriesOf_tagHash]
    have h0 : 2 * o.val < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
    have h1 : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
    rw [agree _ (by rw [DigestSplit.family_final _ h0]; decide) (by rw [DigestSplit.family_final _ h0]; decide),
      agree _ (by rw [DigestSplit.family_final _ h1]; decide) (by rw [DigestSplit.family_final _ h1]; decide)]
  unfold EntryCorrect.pubOf
  rw [gx, gy, masks, entries]

/-! ### Positions away from the sites -/

/-- **A position of a family other than 6 and 7 lies away from every pad and mask site.** -/
theorem away_of_family (p : Fin (2 ^ 40)) (h6 : tagFamily p.val ≠ 6) (h7 : tagFamily p.val ≠ 7) :
    ∀ site ∈ crtLayout.sites, p ∉ (siteTags crtLayout site).map tagPos := by
  intro site mem hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  have fam67 : ∀ {fam' coord idx stage level slot part : ℕ}, (fam' = 6 ∨ fam' = 7) →
      TagInRange coord idx stage level slot part →
      tagFamily (tagPos (tagCode fam' coord idx stage level slot part)).val = 6 ∨
        tagFamily (tagPos (tagCode fam' coord idx stage level slot part)).val = 7 := by
    intro fam' coord idx stage level slot part hf hin
    simp only [tagPos]
    rw [Nat.mod_eq_of_lt (Asks.tagCode_lt (by omega) hin), tagFamily_tagCode hin]
    exact hf
  have fam : tagFamily (tagPos t).val = 6 ∨ tagFamily (tagPos t).val = 7 := by
    rcases List.mem_append.mp mem with pad | mask
    · obtain ⟨κ', i, ρ, rfl, hκ', hi, hρ⟩ := Layout.mem_padSites pad
      obtain ⟨-, -, -, -, hm, hq⟩ := Layout.tableFacts κ' hκ' i hi
      simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < Layout.padCount κ' i := hj
      exact fam67 (Or.inl rfl) ⟨hκ', by omega, by omega, by omega, by omega, by omega⟩
    · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
      · simp only [siteTags, List.mem_map, List.mem_range] at ht
        obtain ⟨j, hj, rfl⟩ := ht
        have hj' : j < 2 := hj
        exact fam67 (Or.inr rfl) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · simp only [siteTags, List.mem_map, List.mem_range] at ht
        obtain ⟨j, hj, rfl⟩ := ht
        have hj' : j < 3 := hj
        exact fam67 (Or.inr rfl) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [heq] at fam
  rcases fam with f | f
  · exact h6 f
  · exact h7 f

/-! ### One table position, chosen by the coins -/

open Classical in
/-- **One table position chosen by the coins, uniform and independent of the rest**: an event that forces its
answer into a set of at most `k` values (fixed by the rest of the table and the coins) has conditional mass at most
`k / #(Block × Block)` given a view that does not read the position. -/
theorem outer_table_gen_le {C V : Type} (coinsLaw : PMF C) (μT : PMF TagTable) (pos : C → Fin (2 ^ 40))
    (indep : ∀ c, Indep μT {pos c} (PMF.uniformOfFintype (Block × Block)) (fun T => T (pos c)) (fun _ => True))
    (view : C → TagTable → V) (ignores : ∀ c, Ignores {pos c} (view c))
    (R : C → TagTable → Block × Block → Prop) (ignoresR : ∀ c a, Ignores {pos c} fun T => R c T a)
    (k : ℕ) (few : ∀ c T (inst : DecidablePred (R c T)), (@Finset.filter _ (R c T) inst Finset.univ).card ≤ k)
    (v : V) :
    (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure
        {ω | view ω.1 ω.2 = v ∧ R ω.1 ω.2 (ω.2 (pos ω.1))} ≤
      ((k : ℝ≥0∞) / Fintype.card (Block × Block)) *
        (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure {ω | view ω.1 ω.2 = v} := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  let G : Block × Block → TagTable → PMF Bool := fun a T => PMF.pure (decide (view c T = v ∧ R c T a))
  have ignoresG : ∀ a, True → Ignores {pos c} (G a) := fun a _ T T' agree => by
    simp only [G, ignores c T T' agree, ignoresR c a T T' agree]
  have law := indep c Bool G ignoresG
  have atTrue := congrArg (fun p : PMF Bool => p true) law
  simp only [G] at atTrue
  have lhsEq : μT.toOuterMeasure ((fun T => (c, T)) ⁻¹'
      {ω : C × TagTable | view ω.1 ω.2 = v ∧ R ω.1 ω.2 (ω.2 (pos ω.1))}) =
      (μT.bind fun T => PMF.pure (decide (view c T = v ∧ R c T (T (pos c))))) true := by
    rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v ∧ R c T (T (pos c))
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have viewEq : μT.toOuterMeasure ((fun T => (c, T)) ⁻¹' {ω : C × TagTable | view ω.1 ω.2 = v}) =
      ∑' T, μT T * (if view c T = v then 1 else 0) := by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have each : ∀ a, (μT.bind fun T => PMF.pure (decide (view c T = v ∧ R c T a))) true =
      ∑' T, μT T * (if view c T = v ∧ R c T a then 1 else 0) := by
    intro a
    rw [PMF.bind_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v ∧ R c T a
    · simp [h]
    · simp [h]
  rw [lhsEq, atTrue, viewEq, PMF.bind_apply]
  simp_rw [each, PMF.uniformOfFintype_apply]
  set N := (Fintype.card (Block × Block) : ℝ≥0∞)
  have inner : ∀ T, (∑ a : Block × Block, (if view c T = v ∧ R c T a then (1 : ℝ≥0∞) else 0)) =
      (if view c T = v then 1 else 0) * ((Finset.univ.filter (R c T)).card : ℝ≥0∞) := by
    intro T
    by_cases hv : view c T = v
    · simp only [hv, true_and, if_true, one_mul]
      rw [Finset.sum_boole]
    · simp only [hv, false_and, if_false, zero_mul, Finset.sum_const_zero]
  have swap : ∑' a : Block × Block, N⁻¹ * ∑' T, μT T * (if view c T = v ∧ R c T a then 1 else 0) =
      N⁻¹ * ∑' T, μT T * ((if view c T = v then 1 else 0) * (Finset.univ.filter (R c T)).card) := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
    refine congrArg (N⁻¹ * ·) (tsum_congr fun T => ?_)
    rw [ENNReal.tsum_mul_left, tsum_fintype, inner T]
  rw [swap]
  calc N⁻¹ * ∑' T, μT T * ((if view c T = v then 1 else 0) * (Finset.univ.filter (R c T)).card)
      ≤ N⁻¹ * ∑' T, μT T * ((if view c T = v then 1 else 0) * (k : ℝ≥0∞)) := by
        refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun T => mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
        exact_mod_cast few c T _
    _ = ((k : ℝ≥0∞) / N) * ∑' T, μT T * (if view c T = v then 1 else 0) := by
        rw [ENNReal.div_eq_inv_mul, mul_assoc, ← ENNReal.tsum_mul_left (a := (k : ℝ≥0∞))]
        refine congrArg (N⁻¹ * ·) (tsum_congr fun T => ?_)
        ring

/-! ### Family 7: the masks -/

/-- The key's position. -/
def keyPos : Fin (2 ^ 40) := Conv.tag40 maskKeyTag

theorem maskKeyTag_lt : maskKeyTag < 2 ^ 40 :=
  Asks.tagCode_lt (by decide) ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem keyPos_family : tagFamily keyPos.val = 10 := by
  show tagFamily (maskKeyTag % 2 ^ 40) = 10
  rw [Nat.mod_eq_of_lt maskKeyTag_lt]
  exact maskKeyTag_family

/-- Every mask query is at the key. -/
theorem mask_asked (H : HashN) (K : Block) (digits : ℕ) :
    ∀ x ∈ asked H (maskAnswersM K digits), ∃ tag, x = hashInput K tag := by
  intro x inside
  simp only [maskAnswersM, collectorMasksM, nonCollectorMasksM, pairMasksM, singleMaskM, siteAnswersM,
    asked_bind, asked_tableM, asked_askN, asked_pure, List.append_nil, List.mem_append, List.mem_flatMap,
    List.mem_finRange, true_and, List.mem_singleton, asked_ite] at inside
  rcases inside with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · split at h
    · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at h
      obtain ⟨i, hi⟩ := h
      exact ⟨_, hi⟩
    · exact absurd h List.not_mem_nil

/-- **A garbler input of family 7 is labelled by the key answer.** -/
theorem mask_input (scalar : NonZeroScalar) (coins : Entry.Coins) (A : TagTable) (N : ℕ)
    (inside : N ∈ asked (H8.tagHash A) (garbleCM scalar coins)) (fam : tagFamily (N / 2 ^ 128) = 7) :
    N = hashInput (A keyPos).1 (N / 2 ^ 128) := by
  unfold garbleCM at inside
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table xCount 0 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _ inX
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table yCount 1 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _ inY
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inKey
    subst inKey
    unfold maskKeyInput at fam
    rw [hashInput_div, maskKeyTag_family] at fam
    exact absurd fam (by decide)
  · obtain ⟨tag, rfl⟩ := mask_asked _ _ _ _ inMask
    rw [hashInput_div]
    congr 1
    rw [eval_keyM]
    unfold maskKey maskKeyInput
    rw [BmrEntry.tagHash_hashInput]
    rfl
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.digestGarbleM_tagged coordinateBitCount digitCount (by decide) (by decide) _ _ _ _ _) _ _ inDigest
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.digestKeys, Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union,
      Set.mem_setOf_eq] at member
    omega

/-- The label of a labelled input. -/
theorem label_of_hashInput (label : Block) (tag : ℕ) : BitVec.ofNat 128 (hashInput label tag) = label := by
  unfold hashInput
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt label.isLt]

set_option linter.constructorNameAsVariable false in
theorem card_fst_eq (g : Block) (F : Block → Block) (inj : Function.Injective F)
    [DecidablePred (fun a : Block × Block => F a.1 = g)] :
    (Finset.univ.filter (fun a : Block × Block => F a.1 = g)).card ≤ Fintype.card Block := by
  classical
  have sub : Finset.univ.filter (fun a : Block × Block => F a.1 = g) ⊆
      (Finset.univ.filter (fun b : Block => F b = g)) ×ˢ Finset.univ := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at ha ⊢
    exact ⟨ha, trivial⟩
  refine le_trans (Finset.card_le_card sub) ?_
  rw [Finset.card_product, Finset.card_univ]
  have one : (Finset.univ.filter (fun b : Block => F b = g)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact inj (ha.trans hb.symm)
  generalize Fintype.card Block = n
  calc (Finset.univ.filter (fun b : Block => F b = g)).card * n ≤ 1 * n := Nat.mul_le_mul_right n one
    _ = n := Nat.one_mul n

/-- `2^128 / #(Block × Block) = 2^-128`. -/
theorem half_card : ((Fintype.card Block : ℕ) : ℝ≥0∞) / (Fintype.card (Block × Block) : ℝ≥0∞) =
    ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  have cast : ((Fintype.card Block : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
    rw [Kriterion.ArgoMAC.Security.PGS.card_block, Nat.cast_pow, Nat.cast_ofNat]
  rw [Fintype.card_prod, Nat.cast_mul, cast]
  generalize hx : (2 : ℝ≥0∞) ^ 128 = x
  have x0 : x ≠ 0 := by rw [← hx]; exact pow_ne_zero _ two_ne_zero
  have xt : x ≠ ⊤ := by rw [← hx]; exact ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl x0) (Or.inl xt), mul_assoc, ENNReal.inv_mul_cancel x0 xt,
    mul_one]

/-- The published value of a table tape, typed at the entry. -/
def pubT (scalar : NonZeroScalar) (c : Instance.crtEntry.Coins) (T : TagTable) : Instance.crtEntry.Public :=
  EntryCorrect.pubOf (H8.tagHash T) scalar c

theorem pubT_congr (scalar : NonZeroScalar) (c : Instance.crtEntry.Coins) (T T' : TagTable)
    (agree : ∀ p : Fin (2 ^ 40), tagFamily p.val ≠ 8 → tagFamily p.val ≠ 10 → T p = T' p) :
    pubT scalar c T = pubT scalar c T' :=
  pubOf_congr scalar c T T' agree

theorem stageOneView_pubT [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape Instance.crtEntry) :
    stageOneView Instance.crtEntry parameter scalar tape = pubT scalar tape.1 tape.2 :=
  stageOneView_eq parameter scalar tape

/-- The published value's view set on the tag reading. -/
theorem viewSet_eq [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Instance.crtEntry.Public) :
    {tape : TableTape Instance.crtEntry | stageOneView Instance.crtEntry parameter scalar tape = view} =
      {ω : TableTape Instance.crtEntry | pubT scalar ω.1 ω.2 = view} := by
  ext tape
  show stageOneView Instance.crtEntry parameter scalar tape = view ↔ pubT scalar tape.1 tape.2 = view
  rw [stageOneView_pubT]

/-- The swapped tape as coins and a table. -/
theorem swappedTableTape_eq :
    swappedTableTape Instance.crtEntry =
      (@PMF.uniformOfFintype _ (@Fintype.ofFinite _ Instance.crtEntry.coinsFinite) ⟨Instance.crtEntry.coinWitness⟩).bind
        fun c => (swappedTableLaw crtLayout).map fun T => (c, T) := rfl

/-- **Family 7 (the masks)**: the label is the key answer, a position the published value does not read. -/
theorem maskCase : OneCase (fun τ => tagFamily τ = 7) ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  intro field group parameter scalar view N fam
  set g : Block := BitVec.ofNat 128 N
  let R : Instance.crtEntry.Coins → TagTable → Block × Block → Prop := fun _ _ a => id a.1 = g
  have sub : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} ⊆
      {ω : TableTape Instance.crtEntry | pubT scalar ω.1 ω.2 = view ∧ R ω.1 ω.2 (ω.2 keyPos)} := by
    intro tape member
    obtain ⟨hv, hN⟩ := member
    rw [stageOneView_pubT] at hv
    rw [gAsked_eq] at hN
    refine ⟨hv, ?_⟩
    have same := mask_input scalar tape.1 tape.2 N hN fam
    show id (tape.2 keyPos).1 = g
    rw [show g = BitVec.ofNat 128 N from rfl, same, label_of_hashInput]
    rfl
  have few : ∀ (c : Instance.crtEntry.Coins) (T : TagTable) (inst : DecidablePred (R c T)),
      (@Finset.filter _ (R c T) inst Finset.univ).card ≤ Fintype.card Block :=
    fun _ _ inst => @card_fst_eq g id Function.injective_id inst
  refine le_trans (MeasureTheory.measure_mono sub) ?_
  rw [viewSet_eq, swappedTableTape_eq, ← half_card]
  exact outer_table_gen_le _ (swappedTableLaw crtLayout) (fun _ => keyPos)
    (fun _ => Laws.indep_swapped_pos crtLayout keyPos (away_of_family keyPos (by rw [keyPos_family]; decide)
      (by rw [keyPos_family]; decide)))
    (pubT scalar)
    (fun c T T' agree => pubT_congr scalar c T T' fun p _ h10 => agree p fun hp => h10 (by
      rw [Set.mem_singleton_iff] at hp; rw [hp]; exact keyPos_family))
    R (fun _ _ _ _ _ => rfl) (Fintype.card Block) few view

/-! ### Family 9: the digest finals -/

/-- **A garbler input of family 9 is a final at the garbler's key of an exceptional input of its site.** -/
theorem final_input (scalar : NonZeroScalar) (coins : Entry.Coins) (A : TagTable) (N : ℕ)
    (inside : N ∈ asked (H8.tagHash A) (garbleCM scalar coins)) (fam : tagFamily (N / 2 ^ 128) = 9) :
    ∃ (o : DigestSplit.FinalSite) (w : AffineInput), exceptional scalar coins o.val = some w ∧
      N = hashInput (garblerKey (digestTable (H8.tagHash A) coordinateBitCount (zeroOf coins) (deltaOf coins)) w)
        (digestFinalTag o.val) := by
  unfold garbleCM at inside
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table xCount 0 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _ inX
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.coordGarbleM_tagged table yCount 1 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _) _ _ inY
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inKey
    subst inKey
    unfold maskKeyInput at fam
    rw [hashInput_div, maskKeyTag_family] at fam
    exact absurd fam (by decide)
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.maskAnswersM_tagged _ digitCount (by decide) (by decide)) _ _ inMask
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
      Set.mem_setOf_eq] at member
    omega
  · unfold digestGarbleM at inDigest
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inDigest
    rcases inDigest with inTable | inFinals
    · rw [asked_digestTableM] at inTable
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at inTable
      obtain ⟨c, p, same | same⟩ := inTable
      · subst same
        obtain ⟨hf, -, -, -⟩ := digestLabelTag_fields (b := 0) c.isLt (lt_of_lt_of_le p.isLt (by decide))
          (by norm_num)
        rw [hashInput_div, hf] at fam
        exact absurd fam (by decide)
      · subst same
        obtain ⟨hf, -, -, -⟩ := digestLabelTag_fields (b := 1) c.isLt (lt_of_lt_of_le p.isLt (by decide))
          (by norm_num)
        rw [hashInput_div, hf] at fam
        exact absurd fam (by decide)
    · rw [asked_tableM] at inFinals
      simp only [List.mem_flatMap, List.mem_finRange, true_and] at inFinals
      obtain ⟨o, inEntry⟩ := inFinals
      rw [asked_garbleEntryM] at inEntry
      split at inEntry
      · exact absurd inEntry List.not_mem_nil
      · rename_i phi selected
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inEntry
        rcases inEntry with inEntry | inEntry
        · refine ⟨DigestSplit.siteOf o 0, _, exceptional_some scalar coins o phi selected, ?_⟩
          rw [inEntry, eval_digestTableM]
          rfl
        · refine ⟨DigestSplit.siteOf o 1, _, triple_some scalar coins o phi selected, ?_⟩
          rw [inEntry, eval_digestTableM]
          rfl

/-- The digest table on a tag table. -/
theorem digestTable_tagHash (A : TagTable) (bits : ℕ) (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (c : Fin 2) (p : Fin bits) :
    digestTable (H8.tagHash A) bits zero delta c p =
      ((A (Conv.tag40 (digestLabelTag c.val p.val 0))).1, (A (Conv.tag40 (digestLabelTag c.val p.val 1))).1) := by
  unfold digestTable h128
  rw [BmrEntry.tagHash_hashInput, BmrEntry.tagHash_hashInput]
  rfl

/-- The digest answer the garbler's key reads at a position. -/
def keyAnswer (A : TagTable) (u : AffineInput) (c : Fin 2) (p : Fin coordinateBitCount) : Block :=
  (A (Conv.tag40 (digestLabelTag c.val p.val (coordBit u c p.val)))).1

theorem coordBit_cases (u : AffineInput) (c : Fin 2) (p : ℕ) : coordBit u c p = 0 ∨ coordBit u c p = 1 := by
  unfold coordBit
  split <;> simp

theorem garblerKey_tagHash (A : TagTable) (zero : Fin 2 → Fin coordinateBitCount → Block) (delta : Fin 2 → Block)
    (u : AffineInput) :
    garblerKey (digestTable (H8.tagHash A) coordinateBitCount zero delta) u =
      xorFold fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => keyAnswer A u c p := by
  unfold garblerKey keyAnswer
  refine congrArg xorFold (funext fun c => congrArg xorFold (funext fun p => ?_))
  rw [digestTable_tagHash]
  rcases coordBit_cases u c p.val with h | h
  · rw [h, if_neg (by decide)]
  · rw [h, if_pos rfl]

/-- The first position of the key. -/
def zeroPos : Fin coordinateBitCount := ⟨0, by decide⟩

/-- **The key splits off its answer at `(x, 0)`.** -/
theorem key_split (A : TagTable) (u : AffineInput) :
    (xorFold fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => keyAnswer A u c p) =
      (xorFoldExcept 0 (fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => keyAnswer A u c p) ^^^
        xorFoldExcept zeroPos (fun p => keyAnswer A u 0 p)) ^^^ keyAnswer A u 0 zeroPos := by
  rw [← SliceC.xorFoldExcept_xor 0, ← SliceC.xorFoldExcept_xor zeroPos (fun p => keyAnswer A u 0 p)]
  rw [BitVec.xor_assoc]

/-- The position of the key's answer at `(x, 0)`. -/
def keyPos0 (u : AffineInput) : Fin (2 ^ 40) := Conv.tag40 (digestLabelTag 0 0 (coordBit u 0 0))

theorem digestLabelTag_lt {c p b : ℕ} (hc : c < 2) (hp : p < 65536) (hb : b < 64) : digestLabelTag c p b < 2 ^ 40 :=
  Asks.tagCode_lt (by decide) ⟨hc, by decide, by decide, by decide, hp, hb⟩

theorem coordBit_lt (u : AffineInput) (c : Fin 2) (p : ℕ) : coordBit u c p < 64 := by
  rcases coordBit_cases u c p with h | h <;> rw [h] <;> decide

theorem keyPos0_family (u : AffineInput) : tagFamily (keyPos0 u).val = 8 := by
  show tagFamily (digestLabelTag 0 0 (coordBit u 0 0) % 2 ^ 40) = 8
  rw [Nat.mod_eq_of_lt (digestLabelTag_lt (by decide) (by decide) (coordBit_lt u 0 0))]
  exact (digestLabelTag_fields (by decide) (by decide) (coordBit_lt u 0 0)).1

/-- Two digest positions are equal only at the same coordinate and position. -/
theorem tag40_digest_inj {c p b c' p' b' : ℕ} (hc : c < 2) (hp : p < 65536) (hb : b < 64) (hc' : c' < 2)
    (hp' : p' < 65536) (hb' : b' < 64)
    (same : Conv.tag40 (digestLabelTag c p b) = Conv.tag40 (digestLabelTag c' p' b')) : c = c' ∧ p = p' := by
  have e := congrArg Fin.val same
  simp only [Conv.tag40] at e
  rw [Nat.mod_eq_of_lt (digestLabelTag_lt hc hp hb), Nat.mod_eq_of_lt (digestLabelTag_lt hc' hp' hb')] at e
  have f1 := digestLabelTag_fields hc hp hb
  have f2 := digestLabelTag_fields hc' hp' hb'
  exact ⟨by rw [← f1.2.1, ← f2.2.1, e], by rw [← f1.2.2.1, ← f2.2.2.1, e]⟩

/-- **The rest of the key does not read the position at `(x, 0)`.** -/
theorem keyRest_ignores (u : AffineInput) :
    Ignores {keyPos0 u} fun A =>
      xorFoldExcept 0 (fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => keyAnswer A u c p) ^^^
        xorFoldExcept zeroPos (fun p => keyAnswer A u 0 p) := by
  intro A A' agree
  show (xorFoldExcept 0 (fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => keyAnswer A u c p) ^^^
      xorFoldExcept zeroPos (fun p => keyAnswer A u 0 p)) =
    (xorFoldExcept 0 (fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => keyAnswer A' u c p) ^^^
      xorFoldExcept zeroPos (fun p => keyAnswer A' u 0 p))
  have away : ∀ (c : Fin 2) (p : Fin coordinateBitCount), (c ≠ 0 ∨ p ≠ zeroPos) → keyAnswer A u c p = keyAnswer A' u c p := by
    intro c p ne
    unfold keyAnswer
    rw [agree _ fun hmem => ?_]
    rw [Set.mem_singleton_iff] at hmem
    have hp : p.val < 65536 := lt_of_lt_of_le p.isLt (by decide)
    obtain ⟨e1, e2⟩ := tag40_digest_inj c.isLt hp (coordBit_lt u c p.val) (by decide) (by decide)
      (coordBit_lt u 0 0) hmem
    rcases ne with h | h
    · exact h (Fin.ext e1)
    · exact h (Fin.ext e2)
  have outer : ∀ c : Fin 2, c ≠ 0 → (xorFold fun p : Fin coordinateBitCount => keyAnswer A u c p) =
      xorFold fun p : Fin coordinateBitCount => keyAnswer A' u c p := by
    intro c hc
    exact congrArg xorFold (funext fun p => away c p (Or.inl hc))
  rw [SliceC.xorFoldExcept_congr 0 _ _ outer,
    SliceC.xorFoldExcept_congr zeroPos _ _ fun p hp => away 0 p (Or.inr hp)]

/-- The exceptional input of final site `o` for the given coins (the origin for a zero digit). -/
def excOf (scalar : NonZeroScalar) (c : Entry.Coins) (o : DigestSplit.FinalSite) : AffineInput :=
  (exceptional scalar c o.val).getD ⟨0, 0⟩

theorem slot_digestFinalTag (o : ℕ) (ho : o < 65536) : tagSlot (digestFinalTag o) = o :=
  (digestFinalTag_fields ho).2

/-- **Family 9 (the digest finals)**: the label is the key, whose answer at `(x, 0)` is a position the published
value does not read. -/
theorem finalCase : OneCase (fun τ => tagFamily τ = 9) ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  intro field group parameter scalar view N fam
  by_cases small : tagSlot (N / 2 ^ 128) < 2 * digitCount
  · obtain ⟨o, ho⟩ : ∃ o : DigestSplit.FinalSite, o.val = tagSlot (N / 2 ^ 128) := ⟨⟨_, small⟩, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : Block, g = BitVec.ofNat 128 N := ⟨_, rfl⟩
    let pos : Instance.crtEntry.Coins → Fin (2 ^ 40) := fun c => keyPos0 (excOf scalar c o)
    let F : Instance.crtEntry.Coins → TagTable → Block := fun c A =>
      xorFoldExcept 0 (fun c' : Fin 2 => xorFold fun p : Fin coordinateBitCount => keyAnswer A (excOf scalar c o) c' p) ^^^
        xorFoldExcept zeroPos (fun p => keyAnswer A (excOf scalar c o) 0 p)
    let R : Instance.crtEntry.Coins → TagTable → Block × Block → Prop := fun c A a => a.1 ^^^ F c A = g
    have sub : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} ⊆
        {ω : TableTape Instance.crtEntry | pubT scalar ω.1 ω.2 = view ∧ R ω.1 ω.2 (ω.2 (pos ω.1))} := by
      intro tape member
      obtain ⟨hv, hN⟩ := member
      rw [stageOneView_pubT] at hv
      rw [gAsked_eq] at hN
      refine ⟨hv, ?_⟩
      obtain ⟨o', w, selected, same⟩ := final_input scalar tape.1 tape.2 N hN fam
      have ho' : o' = o := by
        apply Fin.ext
        rw [ho, same, hashInput_div, slot_digestFinalTag _ (DigestSplit.finalSite_lt o')]
      rw [ho'] at selected same
      have exc : excOf scalar tape.1 o = w := by
        unfold excOf
        rw [selected]
        rfl
      show (tape.2 (keyPos0 (excOf scalar tape.1 o))).1 ^^^ F tape.1 tape.2 = g
      have label : g = garblerKey (digestTable (H8.tagHash tape.2) coordinateBitCount (zeroOf tape.1) (deltaOf tape.1))
          (excOf scalar tape.1 o) := by
        rw [hg, same, label_of_hashInput, exc]
      rw [label, garblerKey_tagHash, key_split, BitVec.xor_comm]
      rfl
    have few : ∀ (c : Instance.crtEntry.Coins) (T : TagTable) (inst : DecidablePred (R c T)),
        (@Finset.filter _ (R c T) inst Finset.univ).card ≤ Fintype.card Block :=
      fun c T inst => @card_fst_eq g (fun b => b ^^^ F c T)
        (fun x y h => by simpa using congrArg (· ^^^ F c T) h) inst
    refine le_trans (MeasureTheory.measure_mono sub) ?_
    rw [viewSet_eq, swappedTableTape_eq, ← half_card]
    exact outer_table_gen_le _ (swappedTableLaw crtLayout) pos
      (fun c => Laws.indep_swapped_pos crtLayout (pos c) (away_of_family (pos c)
        (by rw [keyPos0_family]; decide) (by rw [keyPos0_family]; decide)))
      (pubT scalar)
      (fun c T T' agree => pubT_congr scalar c T T' fun p h8 _ => agree p fun hp => h8 (by
        rw [Set.mem_singleton_iff] at hp; rw [hp]; exact keyPos0_family _))
      R (fun c a T T' agree => by
        have same : F c T = F c T' := keyRest_ignores (excOf scalar c o) T T' agree
        show (a.1 ^^^ F c T = g) = (a.1 ^^^ F c T' = g)
        rw [same])
      (Fintype.card Block) few view
  · refine le_trans (MeasureTheory.measure_mono (t := ∅) ?_) (by simp)
    intro tape member
    obtain ⟨_, hN⟩ := member
    rw [gAsked_eq] at hN
    obtain ⟨o', w, _, same⟩ := final_input scalar tape.1 tape.2 N hN fam
    refine small ?_
    rw [same, hashInput_div, slot_digestFinalTag _ (DigestSplit.finalSite_lt o')]
    exact o'.isLt

end

end Kriterion.CRT.Privacy.StageOneProof
