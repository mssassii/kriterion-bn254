/-
**H7, the two cases with a table residual** (P2b; `Hidden/StageTwo.lean`).

* `maskOff`: off the curve a mask input is `hashInput K τ` with `K = (table keyTag).1`; the stage-2 view does not read
  the key's position (the key's answer is only a label, and the table oracle ignores labels); the key's position is not
  a site, so it is uniform and independent of the rest of the table.
* `final`: a final's label is the digit's key, an XOR of digest answers, one of them at a position where the digit's
  exceptional input and `u` differ (`diffIdx`); the key is affine in that answer (`keyOn_update`), the stage-2 view does
  not read that position (`stageTwoView_otherFree`), and it is not a site.

Both cases are at most `2^-128` (`maskOff_case`, `final_case`); `crtEntry_stageTwoGuess_of` is H7 from the other three
cases.

Generic tools: `outer_table_pos_le` (one non-site position per coins, the event read off that position),
`asked_eval_congr` (a program asks and computes the same on two hashes that agree on what it asks), and the table
hash on labelled inputs (`tableHash_hashInput`).
-/

import Proof.Privacy.CRT.Hidden.StageTwo
import Proof.Privacy.CRT.Hidden.GuessCore
import Proof.Privacy.CRT.Laws.Rest
import Proof.Privacy.CRT.Laws.RefillFacts
import Proof.Privacy.CRT.Core.ConvAsks

namespace Kriterion.CRT.Privacy.StageTwo

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Privacy.Laws (Indep Ignores)
open scoped ENNReal

noncomputable section

/-! ### One non-site position per coins -/

open Classical in
/-- **A non-site position per coins**, uniform and independent of the rest of the table, hits a set of at most `k`
answers fixed by the coins and the rest of the table with conditional mass at most `k / #(Block × Block)`, when the
view does not read the position. -/
theorem outer_table_pos_le {C V : Type} (coinsLaw : PMF C) (μT : PMF TagTable) (pos : C → Fin (2 ^ 40))
    (indep : ∀ c, Indep μT {pos c} (PMF.uniformOfFintype (Block × Block)) (fun T => T (pos c)) (fun _ => True))
    (view : C → TagTable → V) (ignores : ∀ c, Ignores {pos c} (view c))
    (P : C → TagTable → Block × Block → Prop) (Pignores : ∀ c a, Ignores {pos c} fun T => P c T a)
    (k : ℕ) (few : ∀ c T, (Finset.univ.filter (P c T)).card ≤ k) (v : V) :
    (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure
        {ω | view ω.1 ω.2 = v ∧ P ω.1 ω.2 (ω.2 (pos ω.1))} ≤
      ((k : ℝ≥0∞) / Fintype.card (Block × Block)) *
        (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure {ω | view ω.1 ω.2 = v} := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  let G : Block × Block → TagTable → PMF Bool := fun a T => PMF.pure (decide (view c T = v ∧ P c T a))
  have ignoresG : ∀ a, True → Ignores {pos c} (G a) := fun a _ T T' agree => by
    simp only [G, ignores c T T' agree, Pignores c a T T' agree]
  have law := indep c Bool G ignoresG
  have atTrue := congrArg (fun p : PMF Bool => p true) law
  simp only [G] at atTrue
  have lhsEq : μT.toOuterMeasure ((fun T => (c, T)) ⁻¹'
      {ω : C × TagTable | view ω.1 ω.2 = v ∧ P ω.1 ω.2 (ω.2 (pos ω.1))}) =
      (μT.bind fun T => PMF.pure (decide (view c T = v ∧ P c T (T (pos c))))) true := by
    rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v ∧ P c T (T (pos c))
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have viewEq : μT.toOuterMeasure ((fun T => (c, T)) ⁻¹' {ω : C × TagTable | view ω.1 ω.2 = v}) =
      ∑' T, μT T * (if view c T = v then 1 else 0) := by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [lhsEq, atTrue, viewEq, PMF.bind_apply, tsum_fintype]
  have each : ∀ a : Block × Block, (μT.bind fun T => PMF.pure (decide (view c T = v ∧ P c T a))) true =
      ∑' T, μT T * (if view c T = v ∧ P c T a then 1 else 0) := by
    intro a
    rw [PMF.bind_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v ∧ P c T a
    · simp [h]
    · simp [h]
  simp only [each, PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ENNReal.div_eq_inv_mul, mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [← tsum_fintype (L := SummationFilter.unconditional _), ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun T => ?_
  rw [ENNReal.tsum_mul_left, mul_comm (k : ℝ≥0∞), mul_assoc]
  refine mul_le_mul' le_rfl ?_
  by_cases hv : view c T = v
  · simp only [hv, true_and, if_true, one_mul]
    rw [tsum_fintype]
    calc ∑ a : Block × Block, (if P c T a then (1 : ℝ≥0∞) else 0)
        = ((Finset.univ.filter (P c T)).card : ℝ≥0∞) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ k := by exact_mod_cast few c T
  · simp [hv]

/-! ### The table hash on labelled inputs -/

theorem hashInput_lt_p (label : Block) {τ : ℕ} (hτ : τ < 2 ^ 40) : hashInput label τ < baseFieldModulus := by
  have labelLt := label.isLt
  unfold hashInput
  calc label.toNat + 2 ^ 128 * τ < 2 ^ 128 + 2 ^ 128 * τ := by omega
    _ = 2 ^ 128 * (τ + 1) := by ring
    _ ≤ 2 ^ 128 * 2 ^ 40 := Nat.mul_le_mul_left _ (by omega)
    _ < baseFieldModulus := by unfold baseFieldModulus; norm_num

/-- **The table oracle answers a labelled input by its tag.** -/
theorem tableHash_hashInput (T : TagTable) (label : Block) {τ : ℕ} (hτ : τ < 2 ^ 40) :
    schemeHash (tableOracle (FI := Empty) (EI := Empty) T) (hashInput label τ) = T ⟨τ, hτ⟩ := by
  unfold schemeHash tableOracle tagOfInput
  simp only
  congr 1
  apply Fin.ext
  simp only
  rw [val_natCast_of_lt (hashInput_lt_p label hτ), hashInput_div, Nat.mod_eq_of_lt hτ]

/-! ### Congruence of a program on two hashes -/

/-- **A program asks and computes the same on two hashes that agree on what it asks.** -/
theorem asked_eval_congr {α : Type} (H H' : HashN) :
    ∀ program : CM α, (∀ n ∈ asked H program, H n = H' n) →
      asked H program = asked H' program ∧ program.eval H = program.eval H' := by
  intro program
  induction program with
  | pure value => intro _; exact ⟨rfl, rfl⟩
  | query n next ih =>
      intro agree
      have here : H n = H' n := agree n (List.mem_cons_self)
      have rest := ih (H n) fun m inside => agree m (List.mem_cons_of_mem _ inside)
      refine ⟨?_, ?_⟩
      · show n :: asked H (next (H n)) = n :: asked H' (next (H' n))
        rw [← here, rest.1]
      · show (next (H n)).eval H = (next (H' n)).eval H'
        rw [← here, rest.2]

/-! ### The key's position -/

theorem maskKeyTag_lt : maskKeyTag < 2 ^ 40 := by
  unfold maskKeyTag tagCode Family.key
  norm_num

/-- The table position of the key. -/
def keyPos : Fin (2 ^ 40) := ⟨maskKeyTag, maskKeyTag_lt⟩

theorem card_block : Fintype.card Block = 2 ^ 128 := by
  rw [Fintype.card_congr (Equiv.mk BitVec.toFin BitVec.ofFin (fun _ => rfl) (fun _ => rfl)), Fintype.card_fin]

/-- A labelled input in range is answered by the table at its key's position. -/
theorem tableHash_key (T : TagTable) (label : Block) {k : Paths.TagKey} (range : k.InRange) :
    schemeHash (tableOracle (FI := Empty) (EI := Empty) T) (hashInput label k.code) =
      T ⟨k.code, Paths.TagKey.code_lt range⟩ :=
  tableHash_hashInput T label (Paths.TagKey.code_lt range)

/-- A key whose family is not 10 has a position other than the key's. -/
theorem pos_ne_keyPos {k : Paths.TagKey} (range : k.InRange) (fam : k.fam ≠ 10) :
    (⟨k.code, Paths.TagKey.code_lt range⟩ : Fin (2 ^ 40)) ≠ keyPos := by
  intro same
  have codes : k.code = maskKeyTag := congrArg Fin.val same
  have f1 := tagFamily_key range
  rw [codes, maskKeyTag_family] at f1
  exact fam f1.symm

/-- **A tag run whose keys avoid family 10 asks and computes the same on two tables that agree off the key.** -/
theorem keyFree_congr {α : Type} {S : Set Paths.TagKey} {program : CM α} (tagged : Paths.Tagged S program)
    (fams : ∀ k ∈ S, k.fam ≠ 10) (T T' : TagTable) (agree : ∀ q, q ≠ keyPos → T q = T' q) :
    asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) program =
        asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) program ∧
      program.eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) =
        program.eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) := by
  refine asked_eval_congr _ _ program fun n inside => ?_
  obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged tagged _ n inside
  rw [tableHash_key T label range, tableHash_key T' label range]
  exact agree _ (pos_ne_keyPos range (fams k member))

/-! ### The masks read the table, not the key -/

theorem siteAnswers_table (T : TagTable) (K K' : Block) (stage site count : ℕ) (stageLt : stage < 4)
    (siteLt : site < 65536) (countLe : count ≤ 64) :
    siteAnswers (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) K stage site count =
      siteAnswers (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) K' stage site count := by
  funext part
  have range : TagInRange 0 0 stage 0 site part.val :=
    ⟨by norm_num, by norm_num, stageLt, by norm_num, siteLt, by have := part.isLt; omega⟩
  have lt : maskTag stage site part.val < 2 ^ 40 := Asks.tagCode_lt (by decide) range
  unfold siteAnswers
  rw [tableHash_hashInput T K lt, tableHash_hashInput T K' lt]

theorem siteAnswers_agree (T T' : TagTable) (agree : ∀ q, q ≠ keyPos → T q = T' q) (K : Block)
    (stage site count : ℕ) (stageLt : stage < 4) (siteLt : site < 65536) (countLe : count ≤ 64) :
    siteAnswers (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) K stage site count =
      siteAnswers (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) K stage site count := by
  funext part
  have range : TagInRange 0 0 stage 0 site part.val :=
    ⟨by norm_num, by norm_num, stageLt, by norm_num, siteLt, by have := part.isLt; omega⟩
  have lt : maskTag stage site part.val < 2 ^ 40 := Asks.tagCode_lt (by decide) range
  unfold siteAnswers
  rw [tableHash_hashInput T K lt, tableHash_hashInput T' K lt]
  refine agree _ fun same => ?_
  have codes : maskTag stage site part.val = maskKeyTag := congrArg Fin.val same
  have f := tagFamily_tagCode (fam := Family.mask) range
  unfold maskTag at codes
  rw [codes, maskKeyTag_family] at f
  exact absurd f (by decide)

/-- **The entry's masks on two tables that agree off the key, at any two keys.** -/
theorem maskValues_keyFree (T T' : TagTable) (agree : ∀ q, q ≠ keyPos → T q = T' q) (K K' : Block) :
    maskValues (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) K digitCount =
      maskValues (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) K' digitCount := by
  unfold maskValues
  have hc : ∀ c : Fin (collectorSites digitCount), c.val < 65536 := fun c => by
    have := c.isLt; unfold collectorSites digitCount at this; omega
  have hp : ∀ k : Fin (pairSites digitCount), k.val < 65536 := fun k => by
    have := k.isLt; unfold pairSites nonCollectorCount digitCount at this; omega
  have single : ¬ singleSites digitCount = 1 := by decide
  rw [if_neg single, if_neg single]
  congr 1
  · funext c
    rw [siteAnswers_table T K K' 0 c.val 2 (by norm_num) (hc c) (by norm_num),
      siteAnswers_agree T T' agree K' 0 c.val 2 (by norm_num) (hc c) (by norm_num)]
  · funext k
    rw [siteAnswers_table T K K' 1 k.val 3 (by norm_num) (hp k) (by norm_num),
      siteAnswers_agree T T' agree K' 1 k.val 3 (by norm_num) (hp k) (by norm_num)]

/-! ### The garbling and the stage-2 view do not read the key's position off the curve -/

theorem coordKeys_fam {κ : ℕ} : ∀ k ∈ Paths.coordKeys κ, k.fam ≠ 10 := by
  intro k member
  simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
  omega

theorem digestKeys_fam : ∀ k ∈ Paths.digestLabelKeys coordinateBitCount ∪ Paths.digestFinalKeys digitCount,
    k.fam ≠ 10 := by
  intro k member
  simp only [Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at member
  omega

theorem coordX_tagged (coins : Entry.Coins) :
    Paths.Tagged (Paths.coordKeys 0)
      (coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))) :=
  Paths.coordGarbleM_tagged Entry.table Entry.xCount 0 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _

theorem coordY_tagged (coins : Entry.Coins) :
    Paths.Tagged (Paths.coordKeys 1)
      (coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))) :=
  Paths.coordGarbleM_tagged Entry.table Entry.yCount 1 (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _

/-- The garbler's actual zero labels on a table (no chunk joins: the coins' zero labels XOR the absorbed chunk joins
of the coordinate garblings on that table). -/
def zeroOn (coins : Entry.Coins) (T : TagTable) : Fin 2 → Fin coordinateBitCount → Block :=
  Entry.keyZeroOf coins (Entry.absorbedOf
    ((coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)))
    ((coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))))

/-- The actual zero labels on a table are the garbler's `keyZero` at the table's hash. -/
theorem zeroOn_eq (coins : Entry.Coins) (T : TagTable) :
    zeroOn coins T = EntryCorrect.keyZero (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) coins := rfl

theorem digest_tagged (scalar : NonZeroScalar) (coins : Entry.Coins) (zero : Fin 2 → Fin coordinateBitCount → Block) :
    Paths.Tagged (Paths.digestLabelKeys coordinateBitCount ∪ Paths.digestFinalKeys digitCount)
      (digestGarbleM coordinateBitCount digitCount zero (Entry.deltaOf coins)
        (fun o => ((Entry.outputKeysOf scalar coins).get o).digit)
        (fun o => ((Entry.outputKeysOf scalar coins).get o).offset.coordinates)
        (fun o => coins.exceptionPad.get o)) :=
  Paths.digestGarbleM_tagged coordinateBitCount digitCount (by decide) (by decide) _ _ _ _ _

/-- **The garbling does not read the key's position** (the key answer is only the masks' label). -/
theorem garbleCM_eval_keyFree (scalar : NonZeroScalar) (coins : Entry.Coins) (T T' : TagTable)
    (agree : ∀ q, q ≠ keyPos → T q = T' q) :
    (Entry.garbleCM scalar coins).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) =
      (Entry.garbleCM scalar coins).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) := by
  unfold Entry.garbleCM
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, eval_maskAnswersM]
  rw [(keyFree_congr (coordX_tagged coins) coordKeys_fam T T' agree).2,
    (keyFree_congr (coordY_tagged coins) coordKeys_fam T T' agree).2,
    maskValues_keyFree T T' agree _ _,
    (keyFree_congr (digest_tagged scalar coins _) digestKeys_fam T T' agree).2]

/-- The scheme's garbling is the garbler program's value. -/
theorem scheme_garble [field : FieldCertificate] [group : GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (coins : Entry.Coins) (oracle : PublicOracle Empty Empty) :
    (@Entry.scheme field group).garble parameter scalar (coins, oracle) =
      (Entry.garbleCM scalar coins).eval (schemeHash oracle) := by
  refine (Paths.entry_garble_eval field group parameter scalar coins oracle).trans ?_
  unfold Entry.garbleProgram
  rw [FreeQuery.eval_toProgram]
  unfold Entry.garbleM
  rw [eval_liftHash]

/-- **The designed entries** are the garbler's designed inputs with the table's answers. -/
theorem designedEntries_eq [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape Instance.crtEntry) (u : AffineInput) :
    designedEntries Instance.crtEntry Entry.table parameter scalar tape u =
      ((gAsked scalar tape).filter fun n =>
          designTag Entry.table (Entry.exceptional scalar tape.1) u (n / 2 ^ 128)).map fun n : ℕ =>
        (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) tape.2).2.2 (n : BaseField)⟩ :
          Entry Empty Empty) := by
  unfold designedEntries
  rw [garblerEntries_eq, List.filter_map]
  refine congrArg (fun l => List.map _ l) (List.filter_congr fun n member => ?_)
  obtain ⟨coins, table⟩ := tape
  have small := garbler_input_lt (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins n member
  simp only [Function.comp]
  unfold tapeOracle
  dsimp only [Instance.crtEntry]
  rw [crtDesigned_hash, val_natCast_of_lt small]

/-! ### The garbler's inputs, block by block -/

theorem gAsked_eq (scalar : NonZeroScalar) (coins : Entry.Coins) (T : TagTable) :
    gAsked scalar (coins, T) =
      asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
          (coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))) ++
        (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
            (coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))) ++
          (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) (keyM coins.bridgeKey) ++
            (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
                (maskAnswersM ((keyM coins.bridgeKey).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)))
                  digitCount) ++
              asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
                (digestGarbleM coordinateBitCount digitCount (zeroOn coins T) (Entry.deltaOf coins)
                  (fun o => ((Entry.outputKeysOf scalar coins).get o).digit)
                  (fun o => ((Entry.outputKeysOf scalar coins).get o).offset.coordinates)
                  (fun o => coins.exceptionPad.get o))))) := by
  unfold gAsked Entry.garbleCM zeroOn
  rw [asked_bind]
  refine congrArg _ ?_
  rw [asked_bind]
  refine congrArg _ ?_
  rw [asked_bind]
  refine congrArg _ ?_
  rw [asked_bind]
  refine congrArg _ ?_
  rw [asked_bind]
  simp only [asked_pure, List.append_nil]

theorem asked_keyM (H : HashN) (t : BaseField) : asked H (keyM t) = [maskKeyInput t] := by
  unfold keyM
  rw [asked_bind]
  rfl

theorem mask_fam (H : HashN) (K : Block) : ∀ n ∈ asked H (maskAnswersM K digitCount), tagFamily (n / 2 ^ 128) = 7 := by
  intro n inside
  obtain ⟨k, member, range, label, rfl⟩ :=
    asked_of_tagged (Paths.maskAnswersM_tagged K digitCount (by decide) (by decide)) H n inside
  rw [hashInput_div, tagFamily_key range]
  simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
    Set.mem_setOf_eq] at member
  omega

theorem hashInput_mod (label : Block) (τ : ℕ) : hashInput label τ % 2 ^ 128 = label.toNat := by
  unfold hashInput
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt label.isLt]

theorem mask_label (H : HashN) (K : Block) (digits : ℕ) :
    ∀ n ∈ asked H (maskAnswersM K digits), n % 2 ^ 128 = K.toNat := by
  intro n inside
  simp only [maskAnswersM, collectorMasksM, nonCollectorMasksM, pairMasksM, singleMaskM, siteAnswersM,
    asked_bind, asked_tableM, asked_askN, asked_pure, asked_ite, List.append_nil, List.mem_append,
    List.mem_flatMap, List.mem_singleton, List.mem_finRange, true_and] at inside
  rcases inside with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | inside
  · exact hashInput_mod _ _
  · exact hashInput_mod _ _
  · split at inside
    · simp only [List.mem_flatMap, List.mem_singleton, List.mem_finRange, true_and] at inside
      obtain ⟨_, rfl⟩ := inside
      exact hashInput_mod _ _
    · exact absurd inside List.not_mem_nil

theorem keyInput_fam (t : BaseField) : tagFamily (maskKeyInput t / 2 ^ 128) = 10 := by
  unfold maskKeyInput
  rw [hashInput_div]
  exact maskKeyTag_family

/-- The actual zero labels do not read the key's position. -/
theorem zeroOn_keyFree (coins : Entry.Coins) (T T' : TagTable) (agree : ∀ q, q ≠ keyPos → T q = T' q) :
    zeroOn coins T = zeroOn coins T' := by
  unfold zeroOn
  rw [(keyFree_congr (coordX_tagged coins) coordKeys_fam T T' agree).2,
    (keyFree_congr (coordY_tagged coins) coordKeys_fam T T' agree).2]

/-- **The stage-2 view off the curve does not read the key's position.** -/
theorem stageTwoView_keyFree [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (off : validate u = false) (coins : Entry.Coins) (T T' : TagTable)
    (agree : ∀ q, q ≠ keyPos → T q = T' q) :
    stageTwoView Instance.crtEntry Entry.table parameter scalar u (coins, T) =
      stageTwoView Instance.crtEntry Entry.table parameter scalar u (coins, T') := by
  have hg : (Instance.crtEntry.scheme inferInstance inferInstance).garble parameter scalar
        (coins, tapeOracle Instance.crtEntry (coins, T)) =
      (Instance.crtEntry.scheme inferInstance inferInstance).garble parameter scalar
        (coins, tapeOracle Instance.crtEntry (coins, T')) := by
    unfold tapeOracle
    dsimp only [Instance.crtEntry]
    rw [scheme_garble, scheme_garble, garbleCM_eval_keyFree scalar coins T T' agree]
  unfold stageTwoView
  dsimp only
  rw [hg, designedEntries_eq, designedEntries_eq]
  have hl : List.map (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) T).2.2
        (n : BaseField)⟩ : Entry Empty Empty))
        (List.filter (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128))
          (gAsked scalar (coins, T))) =
      List.map (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) T').2.2
        (n : BaseField)⟩ : Entry Empty Empty))
        (List.filter (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128))
          (gAsked scalar (coins, T'))) := by
    rw [gAsked_eq, gAsked_eq, (keyFree_congr (coordX_tagged coins) coordKeys_fam T T' agree).1,
      (keyFree_congr (coordY_tagged coins) coordKeys_fam T T' agree).1, zeroOn_keyFree coins T T' agree,
      (keyFree_congr (digest_tagged scalar coins _) digestKeys_fam T T' agree).1]
    have maskGone : ∀ H K, (asked H (maskAnswersM K digitCount)).filter
        (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128)) = [] := by
      intro H K
      refine List.filter_eq_nil_iff.mpr fun n inside => ?_
      rw [designTag_of_family _ _ _ (Or.inl (mask_fam H K n inside)), off]
      simp
    have keyGone : ∀ H, (asked H (keyM coins.bridgeKey)).filter
        (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128)) = [] := by
      intro H
      refine List.filter_eq_nil_iff.mpr fun n inside => ?_
      rw [asked_keyM] at inside
      rw [List.mem_singleton.mp inside, designTag_of_family _ _ _ (Or.inr (keyInput_fam _)), off]
      simp
    rw [List.filter_append, List.filter_append, List.filter_append, List.filter_append,
      List.filter_append, List.filter_append, List.filter_append, List.filter_append, maskGone, maskGone,
      keyGone, keyGone, List.nil_append, List.nil_append]
    refine List.map_congr_left fun n inside => ?_
    have member : n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T'))
          (coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))) ∨
        n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T'))
          (coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))) ∨
        n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T'))
          (digestGarbleM coordinateBitCount digitCount (zeroOn coins T') (Entry.deltaOf coins)
            (fun o => ((Entry.outputKeysOf scalar coins).get o).digit)
            (fun o => ((Entry.outputKeysOf scalar coins).get o).offset.coordinates)
            (fun o => coins.exceptionPad.get o)) := by
      simp only [List.mem_append, List.mem_filter] at inside
      rcases inside with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr a)
    have answer : ∀ {S : Set Paths.TagKey} {α : Type} {program : CM α}, Paths.Tagged S program →
        (∀ k ∈ S, k.fam ≠ 10) → n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) program →
        (tableOracle (FI := Empty) (EI := Empty) T).2.2 (n : BaseField) =
          (tableOracle (FI := Empty) (EI := Empty) T').2.2 (n : BaseField) := by
      intro S α program tagged fams inside
      obtain ⟨k, kmem, range, label, rfl⟩ := asked_of_tagged tagged _ n inside
      show schemeHash (tableOracle (FI := Empty) (EI := Empty) T) (hashInput label k.code) =
        schemeHash (tableOracle (FI := Empty) (EI := Empty) T') (hashInput label k.code)
      rw [tableHash_key T label range, tableHash_key T' label range]
      exact agree _ (pos_ne_keyPos range (fams k kmem))
    have same : (tableOracle (FI := Empty) (EI := Empty) T).2.2 (n : BaseField) =
        (tableOracle (FI := Empty) (EI := Empty) T').2.2 (n : BaseField) := by
      rcases member with a | a | a
      · exact answer (coordX_tagged coins) coordKeys_fam a
      · exact answer (coordY_tagged coins) coordKeys_fam a
      · exact answer (digest_tagged scalar coins _) digestKeys_fam a
    rw [same]
  dsimp only
  rw [hl]

/-! ### The mask case -/

/-- **A position whose family is neither 6 nor 7 lies away from every pad and mask site** of the real layout. -/
theorem away_of_family (pos : Fin (2 ^ 40)) (six : tagFamily pos.val ≠ 6) (seven : tagFamily pos.val ≠ 7) :
    ∀ site ∈ crtLayout.sites, pos ∉ (siteTags crtLayout site).map tagPos := by
  intro site mem hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  rw [← heq] at six seven
  have ne : ∀ {fam' coord idx stage level slot part : ℕ}, 5 < fam' → fam' < 8 →
      TagInRange coord idx stage level slot part →
      tagFamily (tagPos (tagCode fam' coord idx stage level slot part)).val ≠ 6 →
      tagFamily (tagPos (tagCode fam' coord idx stage level slot part)).val ≠ 7 → False := by
    intro fam' coord idx stage level slot part h1 h2 hin n6 n7
    simp only [tagPos] at n6 n7
    rw [Nat.mod_eq_of_lt (Asks.tagCode_lt (by omega) hin), tagFamily_tagCode hin] at n6 n7
    omega
  rcases List.mem_append.mp mem with pad | mask
  · obtain ⟨κ', i, ρ, rfl, hκ', hi, hρ⟩ := Layout.mem_padSites pad
    obtain ⟨-, -, -, -, hm, hq⟩ := Layout.tableFacts κ' hκ' i hi
    simp only [siteTags, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have hj' : j < Layout.padCount κ' i := hj
    exact ne (by decide) (by decide) ⟨hκ', by omega, by omega, by omega, by omega, by omega⟩ six seven
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 2 := hj
      exact ne (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ six seven
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 3 := hj
      exact ne (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ six seven

theorem keyPos_away : ∀ site ∈ crtLayout.sites, keyPos ∉ (siteTags crtLayout site).map tagPos :=
  away_of_family keyPos (by rw [show keyPos.val = maskKeyTag from rfl, maskKeyTag_family]; decide)
    (by rw [show keyPos.val = maskKeyTag from rfl, maskKeyTag_family]; decide)

set_option linter.constructorNameAsVariable false in
theorem card_first_eq (b : Block) {d : DecidablePred fun a : Block × Block => a.1 = b} :
    (@Finset.filter _ (fun a : Block × Block => a.1 = b) d Finset.univ).card ≤ 2 ^ 128 := by
  have sub : @Finset.filter _ (fun a : Block × Block => a.1 = b) d Finset.univ ⊆ Finset.univ.image fun x : Block => (b, x) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨a.2, by rw [← ha]⟩
  calc _ ≤ _ := Finset.card_le_card sub
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = 2 ^ 128 := by rw [Finset.card_univ, card_block]

/-- A garbler input of family 7 is a mask input, at the key's answer. -/
theorem mask_of_fam7 (scalar : NonZeroScalar) (coins : Entry.Coins) (T : TagTable) (N : ℕ)
    (inside : N ∈ gAsked scalar (coins, T)) (fam : tagFamily (N / 2 ^ 128) = 7) :
    N ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
      (maskAnswersM ((keyM coins.bridgeKey).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)))
        digitCount) := by
  rw [gAsked_eq] at inside
  simp only [List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (coordX_tagged coins) _ _ inX
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (coordY_tagged coins) _ _ inY
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · rw [asked_keyM, List.mem_singleton] at inKey
    rw [inKey, keyInput_fam] at fam
    exact absurd fam (by decide)
  · exact inMask
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (digest_tagged scalar coins _) _ _ inDigest
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at member
    omega

/-- The key's answer on a table is the table at the key's position. -/
theorem keyM_eval_table (T : TagTable) (t : BaseField) :
    (keyM t).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) = (T keyPos).1 := by
  rw [eval_keyM]
  unfold maskKey maskKeyInput
  rw [tableHash_hashInput T _ maskKeyTag_lt]
  rfl

/-- **The mask case** (`maskOff`): at most `2^128 / #(Block × Block) = 2^-128`. -/
theorem case_maskOff :
    GuessCase maskOff noExtra ((2 ^ 128 : ℕ) / (Fintype.card (Block × Block) : ℝ≥0∞)) := by
  intro field group parameter scalar u view N hc
  obtain ⟨h7, off⟩ := hc
  rw [Laws.swappedTableTape_eq]
  let view' : Instance.crtEntry.Coins → TagTable → Instance.crtEntry.Public × LamportSignature ×
      List (Entry Empty Empty) := fun c T => stageTwoView Instance.crtEntry Entry.table parameter scalar u (c, T)
  let P : Instance.crtEntry.Coins → TagTable → Block × Block → Prop := fun _ _ a => a.1 = BitVec.ofNat 128 N
  have sub : {tape : TableTape Instance.crtEntry | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape =
        view ∧ N ∈ gAsked scalar tape ∧ noExtra scalar u N tape} ⊆
      {ω : Instance.crtEntry.Coins × TagTable | view' ω.1 ω.2 = view ∧ P ω.1 ω.2 (ω.2 keyPos)} := by
    rintro ⟨c, T⟩ ⟨hv, inside, -⟩
    refine ⟨hv, ?_⟩
    have masks := mask_of_fam7 scalar c T N inside h7
    have label := mask_label _ _ _ N masks
    rw [keyM_eval_table] at label
    show (T keyPos).1 = BitVec.ofNat 128 N
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, label]
  refine le_trans (MeasureTheory.measure_mono sub) ?_
  have bound := outer_table_pos_le Laws.coinLaw (swappedTableLaw crtLayout) (fun _ => keyPos)
    (fun _ => Laws.indep_swapped_pos crtLayout keyPos keyPos_away) view'
    (fun c T T' agree => stageTwoView_keyFree parameter scalar u off c T T' fun q hq => agree q (by simpa using hq))
    P (fun _ _ _ _ _ => rfl) (2 ^ 128) (fun _ _ => card_first_eq _) view
  exact le_trans bound (le_of_eq rfl)

/-- The case's error is `2^-128`. -/
theorem blockShare_eq :
    ((2 ^ 128 : ℕ) : ℝ≥0∞) / (Fintype.card (Block × Block) : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  have ne0 : (2 : ℝ≥0∞) ^ 128 ≠ 0 := pow_ne_zero _ two_ne_zero
  have neTop : (2 : ℝ≥0∞) ^ 128 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [Fintype.card_prod, card_block, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl ne0) (Or.inl neTop), mul_assoc, ENNReal.inv_mul_cancel ne0 neTop, mul_one]

/-- `2^-128` is within the hidden charge. -/
theorem invPow128_le_charge : ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ ENNReal.ofReal crtHiddenCharge := by
  have real : (1 : ℝ) / 2 ^ 128 ≤ crtHiddenCharge := by
    rw [crtHiddenCharge_eq]
    have pos : 0 ≤ 1 / ((BN254.baseFieldModulus : ℝ) - 1) := by
      unfold BN254.baseFieldModulus
      norm_num
    have four : (1 : ℝ) / 2 ^ 128 ≤ 4 / 2 ^ 104 := by norm_num
    linarith
  calc ((2 : ℝ≥0∞) ^ 128)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal crtHiddenCharge := ENNReal.ofReal_le_ofReal real

/-- **H7's case `maskOff`**, at `2^-128`. -/
theorem maskOff_case : GuessCase maskOff noExtra ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
  blockShare_eq ▸ case_maskOff

/-! ### The final case: the digest labels at the other bit -/

/-- The table position of a digest label. -/
def labelPos (κ : Fin 2) (i : Fin coordinateBitCount) (b : ℕ) : Fin (2 ^ 40) := tagPos (digestLabelTag κ.val i.val b)

theorem labelTag_lt (κ : Fin 2) (i : Fin coordinateBitCount) {b : ℕ} (hb : b < 64) :
    digestLabelTag κ.val i.val b < 2 ^ 40 := by
  unfold digestLabelTag
  exact Asks.tagCode_lt (by decide) ⟨κ.isLt, by norm_num, by norm_num, by norm_num, lt_trans i.isLt (by norm_num), hb⟩

theorem labelPos_eq (κ : Fin 2) (i : Fin coordinateBitCount) {b : ℕ} (hb : b < 64) :
    labelPos κ i b = ⟨digestLabelTag κ.val i.val b, labelTag_lt κ i hb⟩ :=
  Fin.ext (Nat.mod_eq_of_lt (labelTag_lt κ i hb))

theorem labelPos_inj {κ κ' : Fin 2} {i i' : Fin coordinateBitCount} {b b' : ℕ} (hb : b < 64) (hb' : b' < 64)
    (same : labelPos κ i b = labelPos κ' i' b') : κ = κ' ∧ i = i' := by
  rw [labelPos_eq κ i hb, labelPos_eq κ' i' hb'] at same
  have codes : digestLabelTag κ.val i.val b = digestLabelTag κ'.val i'.val b' := congrArg Fin.val same
  obtain ⟨-, c1, s1, -⟩ := digestLabelTag_fields κ.isLt (lt_trans i.isLt (by norm_num)) hb
  obtain ⟨-, c2, s2, -⟩ := digestLabelTag_fields κ'.isLt (lt_trans i'.isLt (by norm_num)) hb'
  rw [codes] at c1 s1
  exact ⟨Fin.ext (c1.symm.trans c2), Fin.ext (s1.symm.trans s2)⟩

theorem coordBit_lt (u : AffineInput) (κ : Fin 2) (i : ℕ) : coordBit u κ i < 2 := by
  unfold coordBit
  split <;> norm_num

/-- The position of the digest label at the bit `u` does not hold. -/
def otherPos (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount) : Fin (2 ^ 40) :=
  labelPos κ i (1 - coordBit u κ i.val)

theorem otherPos_family (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount) :
    tagFamily (otherPos u κ i).val = 8 := by
  have hb : 1 - coordBit u κ i.val < 64 := by omega
  unfold otherPos
  rw [labelPos_eq κ i hb]
  exact (digestLabelTag_fields κ.isLt (lt_trans i.isLt (by norm_num)) hb).1

/-- **A position of a family other than 8, or a designed one, is not the other bit's label.** -/
theorem ne_otherPos (exc : ℕ → Option AffineInput) (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount)
    {τ : ℕ} (hτ : τ < 2 ^ 40) (h : tagFamily τ ≠ 8 ∨ designTag Entry.table exc u τ = true) :
    (⟨τ, hτ⟩ : Fin (2 ^ 40)) ≠ otherPos u κ i := by
  intro same
  have hb : 1 - coordBit u κ i.val < 64 := by omega
  have codes : τ = digestLabelTag κ.val i.val (1 - coordBit u κ i.val) := by
    have := congrArg Fin.val same
    unfold otherPos at this
    rw [labelPos_eq κ i hb] at this
    exact this
  obtain ⟨hf, hc, hs, hp⟩ := digestLabelTag_fields κ.isLt (lt_trans i.isLt (by norm_num)) hb
  rw [← codes] at hf hc hs hp
  rcases h with h | h
  · exact h hf
  · rw [designTag_label _ _ _ hf, hc, hs, hp, inputBit_eq_coordBit, beq_iff_eq] at h
    have := coordBit_lt u κ i.val
    omega

/-- A label at `u`'s own bit is not the other bit's label. -/
theorem labelPos_ne_other (u : AffineInput) (κ κ' : Fin 2) (i i' : Fin coordinateBitCount) :
    labelPos κ' i' (coordBit u κ' i'.val) ≠ otherPos u κ i := by
  have hb : coordBit u κ' i'.val < 64 := lt_trans (coordBit_lt _ _ _) (by norm_num)
  rw [labelPos_eq κ' i' hb]
  refine ne_otherPos (fun _ => none) u κ i _ (Or.inr ?_)
  obtain ⟨hf, hc, hs, hp⟩ := digestLabelTag_fields κ'.isLt (lt_trans i'.isLt (by norm_num)) hb
  rw [designTag_label _ _ _ hf, hc, hs, hp, inputBit_eq_coordBit]
  exact beq_self_eq_true _

theorem keyPos_ne_other (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount) : keyPos ≠ otherPos u κ i :=
  ne_otherPos (fun _ => none) u κ i maskKeyTag_lt (Or.inl (by rw [maskKeyTag_family]; decide))

theorem finalTag_lt (o : ℕ) (ho : o < 65536) : digestFinalTag o < 2 ^ 40 := by
  unfold digestFinalTag
  exact Asks.tagCode_lt (by decide) ⟨by decide, by decide, by decide, by decide, ho, by decide⟩

theorem finalPos_ne_other (o : ℕ) (ho : o < 65536) (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount) :
    (⟨digestFinalTag o, finalTag_lt o ho⟩ : Fin (2 ^ 40)) ≠ otherPos u κ i :=
  ne_otherPos (fun _ => none) u κ i _ (Or.inl (by rw [(digestFinalTag_fields ho).1]; decide))

/-- **A tagged run whose keys avoid a position asks and computes the same on two tables that agree off it.** -/
theorem posFree_congr {α : Type} {S : Set Paths.TagKey} {program : CM α} (tagged : Paths.Tagged S program)
    (p : Fin (2 ^ 40))
    (avoid : ∀ k ∈ S, ∀ range : k.InRange, (⟨k.code, Paths.TagKey.code_lt range⟩ : Fin (2 ^ 40)) ≠ p)
    (T T' : TagTable) (agree : ∀ q, q ≠ p → T q = T' q) :
    asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) program =
        asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) program ∧
      program.eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) =
        program.eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) := by
  refine asked_eval_congr _ _ program fun n inside => ?_
  obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged tagged _ n inside
  rw [tableHash_key T label range, tableHash_key T' label range]
  exact agree _ (avoid k member range)

theorem avoid_of_fam {S : Set Paths.TagKey} (fams : ∀ k ∈ S, k.fam ≠ 8) (u : AffineInput) (κ : Fin 2)
    (i : Fin coordinateBitCount) :
    ∀ k ∈ S, ∀ range : k.InRange, (⟨k.code, Paths.TagKey.code_lt range⟩ : Fin (2 ^ 40)) ≠ otherPos u κ i :=
  fun k member range =>
    ne_otherPos (fun _ => none) u κ i _ (Or.inl (by rw [tagFamily_key range]; exact fams k member))

theorem coordKeys_fam8 {κ : ℕ} : ∀ k ∈ Paths.coordKeys κ, k.fam ≠ 8 := by
  intro k member
  simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
  omega

theorem maskKeys_fam8 : ∀ k ∈ Paths.maskKeys digitCount, k.fam ≠ 8 := by
  intro k member
  simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
    Set.mem_setOf_eq] at member
  omega

theorem mask_tagged (K : Block) : Paths.Tagged (Paths.maskKeys digitCount) (maskAnswersM K digitCount) :=
  Paths.maskAnswersM_tagged K digitCount (by decide) (by decide)

/-- The digest table on the table oracle, read at the labels' positions. -/
def tableOn (T : TagTable) : Fin 2 → Fin coordinateBitCount → Block × Block :=
  fun κ i => ((T (labelPos κ i 0)).1, (T (labelPos κ i 1)).1)

theorem digestTable_table (T : TagTable) (zero : Fin 2 → Fin coordinateBitCount → Block) (delta : Fin 2 → Block) :
    digestTable (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) coordinateBitCount zero delta = tableOn T := by
  funext κ i
  unfold digestTable tableOn h128
  rw [tableHash_hashInput T _ (labelTag_lt κ i (b := 0) (by norm_num)),
    tableHash_hashInput T _ (labelTag_lt κ i (b := 1) (by norm_num)), labelPos_eq κ i (b := 0) (by norm_num),
    labelPos_eq κ i (b := 1) (by norm_num)]

/-- On the table oracle a final's mask reads only the final's position. -/
theorem finalMask_table (T : TagTable) (key : Block) (o : ℕ) (ho : o < 65536) :
    finalMask (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) key o =
      Exception.lowNibble (T ⟨digestFinalTag o, finalTag_lt o ho⟩).1 := by
  unfold finalMask h128
  rw [tableHash_hashInput T key (finalTag_lt o ho)]

/-- **The digest gadget's value does not read the other bit's label.** -/
theorem digest_eval_otherFree (zero : Fin 2 → Fin coordinateBitCount → Block) (delta : Fin 2 → Block)
    (digitOf : Fin digitCount → Digit) (offsetOf : Fin digitCount → AffineInput)
    (padOf : Fin digitCount → Exception.Entry) (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount)
    (T T' : TagTable) (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) :
    (digestGarbleM coordinateBitCount digitCount zero delta digitOf offsetOf padOf).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) =
      (digestGarbleM coordinateBitCount digitCount zero delta digitOf offsetOf padOf).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) := by
  rw [eval_digestGarbleM, eval_digestGarbleM]
  funext o
  have h0 : 2 * o.val < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  have h1 : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  unfold digestEntries garbleEntry
  cases digitEndomorphismBase (digitOf o) with
  | none => rfl
  | some phi =>
      simp only
      rw [finalMask_table T _ _ h0, finalMask_table T' _ _ h0, agree _ (finalPos_ne_other _ h0 u κ i),
        finalMask_table T _ _ h1, finalMask_table T' _ _ h1, agree _ (finalPos_ne_other _ h1 u κ i)]

/-- **The garbling does not read the other bit's label.** -/
theorem garbleCM_eval_otherFree (scalar : NonZeroScalar) (coins : Entry.Coins) (u : AffineInput) (κ : Fin 2)
    (i : Fin coordinateBitCount) (T T' : TagTable) (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) :
    (Entry.garbleCM scalar coins).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) =
      (Entry.garbleCM scalar coins).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) := by
  unfold Entry.garbleCM
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [(posFree_congr (coordX_tagged coins) _ (avoid_of_fam coordKeys_fam8 u κ i) T T' agree).2,
    (posFree_congr (coordY_tagged coins) _ (avoid_of_fam coordKeys_fam8 u κ i) T T' agree).2,
    keyM_eval_table T, keyM_eval_table T', agree keyPos (keyPos_ne_other u κ i),
    (posFree_congr (mask_tagged _) _ (avoid_of_fam maskKeys_fam8 u κ i) T T' agree).2,
    digest_eval_otherFree _ _ _ _ _ u κ i T T' agree]

/-- Every garbler input is a labelled input with a tag below `2^40`. -/
theorem gAsked_labelled (scalar : NonZeroScalar) (coins : Entry.Coins) (T : TagTable) :
    ∀ n ∈ gAsked scalar (coins, T), ∃ label τ, ∃ _ : τ < 2 ^ 40, n = hashInput label τ := by
  intro n inside
  rw [gAsked_eq] at inside
  simp only [List.mem_append] at inside
  have tagged : ∀ {S : Set Paths.TagKey} {α : Type} {program : CM α}, Paths.Tagged S program →
      n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) program →
      ∃ label τ, ∃ _ : τ < 2 ^ 40, n = hashInput label τ := by
    intro S α program t inn
    obtain ⟨k, _, range, label, rfl⟩ := asked_of_tagged t _ n inn
    exact ⟨label, k.code, Paths.TagKey.code_lt range, rfl⟩
  rcases inside with a | a | a | a | a
  · exact tagged (coordX_tagged coins) a
  · exact tagged (coordY_tagged coins) a
  · rw [asked_keyM, List.mem_singleton] at a
    exact ⟨_, _, maskKeyTag_lt, a⟩
  · exact tagged (mask_tagged _) a
  · exact tagged (digest_tagged scalar coins _) a

/-- The garbler's key at `u` does not read the other bit's label at `u`. -/
theorem key_otherFree (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount) (T T' : TagTable)
    (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) :
    garblerKey (tableOn T) u = garblerKey (tableOn T') u := by
  unfold garblerKey tableOn
  refine congrArg (fun f => xorFold f) (funext fun κ' => congrArg (fun f => xorFold f) (funext fun i' => ?_))
  have ne := labelPos_ne_other u κ κ' i i'
  split
  · rename_i one
    rw [one] at ne
    dsimp only
    rw [agree _ ne]
  · rename_i zero
    have z : coordBit u κ' i'.val = 0 := by have := coordBit_lt u κ' i'.val; omega
    rw [z] at ne
    dsimp only
    rw [agree _ ne]

/-- A designed final of site `s` is at the key of `u`: its exceptional input is `u`. -/
theorem final_filter_otherFree (scalar : NonZeroScalar) (coins : Entry.Coins) (u : AffineInput) (κ : Fin 2)
    (i : Fin coordinateBitCount) (T T' : TagTable) (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) (s : ℕ)
    (hs : s < 65536) (w : AffineInput) (ex : Entry.exceptional scalar coins s = some w)
    (designed : designTag Entry.table (Entry.exceptional scalar coins) u (digestFinalTag s) = true) :
    hashInput (garblerKey (tableOn T) w) (digestFinalTag s) = hashInput (garblerKey (tableOn T') w) (digestFinalTag s) := by
  obtain ⟨hf, hslot⟩ := digestFinalTag_fields hs
  rw [designTag_final _ _ _ hf, hslot, beq_iff_eq, ex, Option.some.injEq] at designed
  rw [designed, key_otherFree u κ i T T' agree]

/-- **The designed digest inputs do not read the other bit's label.** -/
theorem digestFilter_otherFree (scalar : NonZeroScalar) (coins : Entry.Coins)
    (zero : Fin 2 → Fin coordinateBitCount → Block) (u : AffineInput) (κ : Fin 2)
    (i : Fin coordinateBitCount) (T T' : TagTable) (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) :
    (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
        (digestGarbleM coordinateBitCount digitCount zero (Entry.deltaOf coins)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).digit)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).offset.coordinates)
          (fun o => coins.exceptionPad.get o))).filter
        (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128)) =
      (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T'))
        (digestGarbleM coordinateBitCount digitCount zero (Entry.deltaOf coins)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).digit)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).offset.coordinates)
          (fun o => coins.exceptionPad.get o))).filter
        (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128)) := by
  unfold digestGarbleM
  rw [asked_bind, asked_bind, eval_digestTableM, eval_digestTableM, digestTable_table, digestTable_table,
    asked_digestTableM, asked_digestTableM, List.filter_append, List.filter_append]
  refine congrArg _ ?_
  rw [asked_tableM, asked_tableM, List.filter_flatMap, List.filter_flatMap]
  refine congrArg (fun g => List.flatMap g (List.finRange digitCount)) (funext fun o => ?_)
  rw [asked_garbleEntryM, asked_garbleEntryM]
  have h0 : 2 * o.val < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  have h1 : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
  cases selected : digitEndomorphismBase ((Entry.outputKeysOf scalar coins).get o).digit with
  | none => rfl
  | some phi =>
      simp only
      rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons, List.filter_nil,
        hashInput_div, hashInput_div, hashInput_div, hashInput_div]
      have e0 := final_filter_otherFree scalar coins u κ i T T' agree _ h0 _
        (exceptional_some scalar coins o phi selected)
      have e1 := final_filter_otherFree scalar coins u κ i T T' agree _ h1 _
        (triple_some scalar coins o phi selected)
      by_cases d0 : designTag Entry.table (Entry.exceptional scalar coins) u (digestFinalTag (2 * o.val)) = true
      · rw [if_pos d0, if_pos d0, e0 d0]
        by_cases d1 : designTag Entry.table (Entry.exceptional scalar coins) u (digestFinalTag (2 * o.val + 1)) = true
        · rw [if_pos d1, if_pos d1, e1 d1]
        · rw [if_neg d1, if_neg d1]
      · rw [if_neg d0, if_neg d0]
        by_cases d1 : designTag Entry.table (Entry.exceptional scalar coins) u (digestFinalTag (2 * o.val + 1)) = true
        · rw [if_pos d1, if_pos d1, e1 d1]
        · rw [if_neg d1, if_neg d1]

/-- The actual zero labels do not read the other bit's label (the coordinate garblings ask families 0 to 6). -/
theorem zeroOn_otherFree (coins : Entry.Coins) (u : AffineInput) (κ : Fin 2) (i : Fin coordinateBitCount)
    (T T' : TagTable) (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) : zeroOn coins T = zeroOn coins T' := by
  unfold zeroOn
  rw [(posFree_congr (coordX_tagged coins) _ (avoid_of_fam coordKeys_fam8 u κ i) T T' agree).2,
    (posFree_congr (coordY_tagged coins) _ (avoid_of_fam coordKeys_fam8 u κ i) T T' agree).2]

/-- **The designed garbler inputs do not read the other bit's label.** -/
theorem designedInputs_otherFree (scalar : NonZeroScalar) (coins : Entry.Coins) (u : AffineInput) (κ : Fin 2)
    (i : Fin coordinateBitCount) (T T' : TagTable) (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) :
    (gAsked scalar (coins, T)).filter (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128)) =
      (gAsked scalar (coins, T')).filter
        (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128)) := by
  rw [gAsked_eq, gAsked_eq,
    (posFree_congr (coordX_tagged coins) _ (avoid_of_fam coordKeys_fam8 u κ i) T T' agree).1,
    (posFree_congr (coordY_tagged coins) _ (avoid_of_fam coordKeys_fam8 u κ i) T T' agree).1,
    keyM_eval_table T, keyM_eval_table T', agree keyPos (keyPos_ne_other u κ i),
    (posFree_congr (mask_tagged _) _ (avoid_of_fam maskKeys_fam8 u κ i) T T' agree).1,
    asked_keyM, asked_keyM,
    List.filter_append, List.filter_append, List.filter_append, List.filter_append,
    List.filter_append, List.filter_append, List.filter_append, List.filter_append,
    zeroOn_otherFree coins u κ i T T' agree, digestFilter_otherFree scalar coins _ u κ i T T' agree]

/-- **The stage-2 view does not read the other bit's label.** -/
theorem stageTwoView_otherFree [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (coins : Entry.Coins) (κ : Fin 2) (i : Fin coordinateBitCount) (T T' : TagTable)
    (agree : ∀ q, q ≠ otherPos u κ i → T q = T' q) :
    stageTwoView Instance.crtEntry Entry.table parameter scalar u (coins, T) =
      stageTwoView Instance.crtEntry Entry.table parameter scalar u (coins, T') := by
  have hg : (Instance.crtEntry.scheme inferInstance inferInstance).garble parameter scalar
        (coins, tapeOracle Instance.crtEntry (coins, T)) =
      (Instance.crtEntry.scheme inferInstance inferInstance).garble parameter scalar
        (coins, tapeOracle Instance.crtEntry (coins, T')) := by
    unfold tapeOracle
    dsimp only [Instance.crtEntry]
    rw [scheme_garble, scheme_garble, garbleCM_eval_otherFree scalar coins u κ i T T' agree]
  unfold stageTwoView
  dsimp only
  rw [hg, designedEntries_eq, designedEntries_eq]
  have hl : List.map (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) T).2.2
        (n : BaseField)⟩ : Entry Empty Empty))
        (List.filter (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128))
          (gAsked scalar (coins, T))) =
      List.map (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) T').2.2
        (n : BaseField)⟩ : Entry Empty Empty))
        (List.filter (fun n => designTag Entry.table (Entry.exceptional scalar coins) u (n / 2 ^ 128))
          (gAsked scalar (coins, T'))) := by
    rw [designedInputs_otherFree scalar coins u κ i T T' agree]
    refine List.map_congr_left fun n inside => ?_
    rw [List.mem_filter] at inside
    obtain ⟨member, designed⟩ := inside
    obtain ⟨label, τ, hτ, rfl⟩ := gAsked_labelled scalar coins T' _ member
    rw [hashInput_div] at designed
    have same : (tableOracle (FI := Empty) (EI := Empty) T).2.2 ((hashInput label τ : ℕ) : BaseField) =
        (tableOracle (FI := Empty) (EI := Empty) T').2.2 ((hashInput label τ : ℕ) : BaseField) := by
      show schemeHash (tableOracle (FI := Empty) (EI := Empty) T) (hashInput label τ) =
        schemeHash (tableOracle (FI := Empty) (EI := Empty) T') (hashInput label τ)
      rw [tableHash_hashInput T label hτ, tableHash_hashInput T' label hτ]
      exact agree _ (ne_otherPos _ u κ i hτ (Or.inr designed))
    rw [same]
  dsimp only
  rw [hl]

/-- **A garbler input of family 9 is a final**, labelled with the digit's key at the exceptional input of its site. -/
theorem final_of_fam9 (scalar : NonZeroScalar) (coins : Entry.Coins) (T : TagTable) (N : ℕ)
    (inside : N ∈ gAsked scalar (coins, T)) (fam : tagFamily (N / 2 ^ 128) = 9) :
    ∃ o : Fin (2 * digitCount), ∃ e, Entry.exceptional scalar coins o.val = some e ∧
      N = hashInput (garblerKey (tableOn T) e) (digestFinalTag o.val) := by
  rw [gAsked_eq] at inside
  simp only [List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (coordX_tagged coins) _ _ inX
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (coordY_tagged coins) _ _ inY
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_setOf_eq] at member
    omega
  · rw [asked_keyM, List.mem_singleton] at inKey
    rw [inKey, keyInput_fam] at fam
    exact absurd fam (by decide)
  · rw [mask_fam _ _ N inMask] at fam
    exact absurd fam (by decide)
  · unfold digestGarbleM at inDigest
    rw [asked_bind, List.mem_append, eval_digestTableM, digestTable_table, asked_digestTableM] at inDigest
    rcases inDigest with inTable | inFinals
    · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at inTable
      obtain ⟨c, p, same | same⟩ := inTable
      · subst same
        rw [hashInput_div, (digestLabelTag_fields (b := 0) c.isLt (lt_trans p.isLt (by norm_num))
          (by norm_num)).1] at fam
        exact absurd fam (by decide)
      · subst same
        rw [hashInput_div, (digestLabelTag_fields (b := 1) c.isLt (lt_trans p.isLt (by norm_num))
          (by norm_num)).1] at fam
        exact absurd fam (by decide)
    · rw [asked_tableM, List.mem_flatMap] at inFinals
      obtain ⟨o, -, inEntry⟩ := inFinals
      rw [asked_garbleEntryM] at inEntry
      split at inEntry
      · exact absurd inEntry List.not_mem_nil
      · rename_i phi selected
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inEntry
        rcases inEntry with inEntry | inEntry
        · exact ⟨⟨2 * o.val, by have := o.isLt; omega⟩, _, exceptional_some scalar coins o phi selected, inEntry⟩
        · exact ⟨⟨2 * o.val + 1, by have := o.isLt; omega⟩, _, triple_some scalar coins o phi selected, inEntry⟩

/-! ### The key of a digit, one label at a time -/

/-- The digit key at `e` on a table. -/
def keyOn (T : TagTable) (e : AffineInput) : Block := garblerKey (tableOn T) e

theorem keyOn_eq (T : TagTable) (e : AffineInput) :
    keyOn T e = xorFold fun κ : Fin 2 => xorFold fun i : Fin coordinateBitCount =>
      (T (labelPos κ i (coordBit e κ i.val))).1 := by
  unfold keyOn garblerKey
  refine congrArg (fun f => xorFold f) (funext fun κ => congrArg (fun f => xorFold f) (funext fun i => ?_))
  unfold tableOn
  split
  · rename_i one
    rw [one]
  · rename_i zero
    have z : coordBit e κ i.val = 0 := by have := coordBit_lt e κ i.val; omega
    rw [z]

/-- **The key is affine in one of its labels.** -/
theorem keyOn_update (T : TagTable) (e : AffineInput) (κ0 : Fin 2) (i0 : Fin coordinateBitCount) :
    ∃ X : Block, ∀ a : Block × Block,
      keyOn (Function.update T (labelPos κ0 i0 (coordBit e κ0 i0.val)) a) e = X ^^^ a.1 := by
  set S := labelPos κ0 i0 (coordBit e κ0 i0.val) with hS
  have bitLt : ∀ (κ : Fin 2) (i : ℕ), coordBit e κ i < 64 := fun κ i => lt_trans (coordBit_lt e κ i) (by norm_num)
  have offRow : ∀ κ : Fin 2, κ ≠ κ0 → ∀ i : Fin coordinateBitCount, labelPos κ i (coordBit e κ i.val) ≠ S :=
    fun κ hκ i same => hκ (labelPos_inj (bitLt _ _) (bitLt _ _) same).1
  have offSlot : ∀ i : Fin coordinateBitCount, i ≠ i0 → labelPos κ0 i (coordBit e κ0 i.val) ≠ S :=
    fun i hi same => hi (labelPos_inj (bitLt _ _) (bitLt _ _) same).2
  let zero : Block × Block := ((0 : Block), (0 : Block))
  let F : Block × Block → Fin 2 → Block := fun a κ =>
    xorFold fun i : Fin coordinateBitCount => (Function.update T S a (labelPos κ i (coordBit e κ i.val))).1
  let G : Block × Block → Fin coordinateBitCount → Block := fun a i =>
    (Function.update T S a (labelPos κ0 i (coordBit e κ0 i.val))).1
  have split : ∀ a, keyOn (Function.update T S a) e =
      xorFoldExcept κ0 (F zero) ^^^ (xorFoldExcept i0 (G zero) ^^^ a.1) := by
    intro a
    have rows : xorFoldExcept κ0 (F a) = xorFoldExcept κ0 (F zero) :=
      SliceC.xorFoldExcept_congr κ0 _ _ fun κ hκ => by
        show xorFold _ = xorFold _
        refine congrArg (fun f => xorFold f) (funext fun i => ?_)
        rw [Function.update_of_ne (offRow κ hκ i), Function.update_of_ne (offRow κ hκ i)]
    have slots : xorFoldExcept i0 (G a) = xorFoldExcept i0 (G zero) :=
      SliceC.xorFoldExcept_congr i0 _ _ fun i hi => by
        show (Function.update T S a _).1 = (Function.update T S zero _).1
        rw [Function.update_of_ne (offSlot i hi), Function.update_of_ne (offSlot i hi)]
    have last : G a i0 = a.1 := by
      show (Function.update T S a S).1 = a.1
      rw [Function.update_self]
    rw [keyOn_eq]
    show xorFold (F a) = _
    rw [← SliceC.xorFoldExcept_xor κ0 (F a), rows]
    show _ ^^^ xorFold (G a) = _
    rw [← SliceC.xorFoldExcept_xor i0 (G a), slots, last]
  exact ⟨_, fun a => (split a).trans (BitVec.xor_assoc _ _ _).symm⟩

/-! ### The differing bit -/

open Classical in
/-- A coordinate bit at which `e` and `u` differ (`(0, 0)` when there is none). -/
def diffIdx (u e : AffineInput) : Fin 2 × Fin coordinateBitCount :=
  if h : ∃ d : Fin 2 × Fin coordinateBitCount, coordBit e d.1 d.2.val ≠ coordBit u d.1 d.2.val then
    Classical.choose h
  else (0, 0)

theorem coordNat_lt (u : AffineInput) (κ : Fin 2) : coordNat u κ < 2 ^ 254 := by
  unfold coordNat
  split
  · exact EntryCorrect.val_lt_two_pow _
  · exact EntryCorrect.val_lt_two_pow _

theorem exists_diff {u e : AffineInput} (ne : e ≠ u) :
    ∃ d : Fin 2 × Fin coordinateBitCount, coordBit e d.1 d.2.val ≠ coordBit u d.1 d.2.val := by
  by_contra none'
  push_neg at none'
  have coords : ∀ κ : Fin 2, coordNat e κ = coordNat u κ := by
    intro κ
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 254
    · have this := none' (κ, ⟨j, hj⟩)
      clear none'
      unfold coordBit at this
      dsimp only at this
      by_cases h1 : (coordNat e κ).testBit j <;> by_cases h2 : (coordNat u κ).testBit j <;> simp_all
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (coordNat_lt e κ) (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (coordNat_lt u κ) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  have hx := coords 0
  have hy := coords 1
  unfold coordNat at hx hy
  rw [if_pos rfl, if_pos rfl] at hx
  rw [if_neg (by decide), if_neg (by decide)] at hy
  apply ne
  cases e
  cases u
  simp only at hx hy
  rw [ZMod.val_injective _ hx, ZMod.val_injective _ hy]

theorem otherPos_diff {u e : AffineInput} (ne : e ≠ u) :
    otherPos u (diffIdx u e).1 (diffIdx u e).2 =
      labelPos (diffIdx u e).1 (diffIdx u e).2 (coordBit e (diffIdx u e).1 (diffIdx u e).2.val) := by
  have spec : coordBit e (diffIdx u e).1 (diffIdx u e).2.val ≠ coordBit u (diffIdx u e).1 (diffIdx u e).2.val := by
    unfold diffIdx
    rw [dif_pos (exists_diff ne)]
    exact Classical.choose_spec (exists_diff ne)
  have h1 := coordBit_lt e (diffIdx u e).1 (diffIdx u e).2.val
  have h2 := coordBit_lt u (diffIdx u e).1 (diffIdx u e).2.val
  unfold otherPos
  congr 1
  omega

/-! ### The final case -/

/-- The differing bit of the final's digit at the coins (`(0, 0)` without an exceptional input). -/
def finalIdx (scalar : NonZeroScalar) (u : AffineInput) (N : ℕ) (c : Entry.Coins) : Fin 2 × Fin coordinateBitCount :=
  diffIdx u ((Entry.exceptional scalar c (tagSlot (N / 2 ^ 128))).getD u)

/-- The hidden position of the final case: the digit's key label at the differing bit. -/
def finalHide (scalar : NonZeroScalar) (u : AffineInput) (N : ℕ) (c : Entry.Coins) : Fin (2 ^ 40) :=
  otherPos u (finalIdx scalar u N c).1 (finalIdx scalar u N c).2

/-- The final case's event on the hidden position's answer `a`. -/
def finalEvent (scalar : NonZeroScalar) (u : AffineInput) (N : ℕ) (c : Entry.Coins) (T : TagTable)
    (a : Block × Block) : Prop :=
  ∃ e, Entry.exceptional scalar c (tagSlot (N / 2 ^ 128)) = some e ∧ e ≠ u ∧
    keyOn (Function.update T (finalHide scalar u N c) a) e = BitVec.ofNat 128 N

theorem finalHide_away (scalar : NonZeroScalar) (u : AffineInput) (N : ℕ) (c : Entry.Coins) :
    ∀ site ∈ crtLayout.sites, finalHide scalar u N c ∉ (siteTags crtLayout site).map tagPos := by
  have fam := otherPos_family u (finalIdx scalar u N c).1 (finalIdx scalar u N c).2
  exact away_of_family _ (by unfold finalHide; rw [fam]; decide) (by unfold finalHide; rw [fam]; decide)

theorem finalEvent_ignores (scalar : NonZeroScalar) (u : AffineInput) (N : ℕ) (c : Entry.Coins) (a : Block × Block) :
    Ignores {finalHide scalar u N c} fun T => finalEvent scalar u N c T a := by
  intro T T' agree
  have same : Function.update T (finalHide scalar u N c) a = Function.update T' (finalHide scalar u N c) a := by
    funext q
    by_cases hq : q = finalHide scalar u N c
    · rw [hq, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]
      exact agree q hq
  show finalEvent scalar u N c T a = finalEvent scalar u N c T' a
  unfold finalEvent
  rw [same]

set_option linter.constructorNameAsVariable false in
theorem finalEvent_few (scalar : NonZeroScalar) (u : AffineInput) (N : ℕ) (c : Entry.Coins) (T : TagTable)
    {d : DecidablePred (finalEvent scalar u N c T)} :
    (@Finset.filter _ (finalEvent scalar u N c T) d Finset.univ).card ≤ 2 ^ 128 := by
  rcases Classical.em (∃ e, Entry.exceptional scalar c (tagSlot (N / 2 ^ 128)) = some e ∧ e ≠ u) with h | h
  · obtain ⟨e, he, ne⟩ := h
    obtain ⟨X, hX⟩ := keyOn_update T e (diffIdx u e).1 (diffIdx u e).2
    have hide : finalHide scalar u N c =
        labelPos (diffIdx u e).1 (diffIdx u e).2 (coordBit e (diffIdx u e).1 (diffIdx u e).2.val) := by
      unfold finalHide finalIdx
      rw [he, Option.getD_some]
      exact otherPos_diff ne
    refine le_trans (Finset.card_le_card
      (t := Finset.univ.filter fun a : Block × Block => a.1 = X ^^^ BitVec.ofNat 128 N) ?_) (card_first_eq _)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, finalEvent] at ha ⊢
    obtain ⟨e', he', -, key⟩ := ha
    rw [he] at he'
    obtain rfl := Option.some.inj he'
    rw [hide, hX] at key
    rw [← key, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · have empty : @Finset.filter _ (finalEvent scalar u N c T) d Finset.univ = ∅ := by
      refine Finset.filter_false_of_mem fun a _ ev => h ?_
      obtain ⟨e, he, ne, -⟩ := ev
      exact ⟨e, he, ne⟩
    rw [empty, Finset.card_empty]
    exact Nat.zero_le _

/-- **The final case** (`final` with `notExceptional`): at most `2^128 / #(Block × Block) = 2^-128`. -/
theorem case_final :
    GuessCase final notExceptional ((2 ^ 128 : ℕ) / (Fintype.card (Block × Block) : ℝ≥0∞)) := by
  intro field group parameter scalar u view N h9
  rw [Laws.swappedTableTape_eq]
  let view' : Instance.crtEntry.Coins → TagTable → Instance.crtEntry.Public × LamportSignature ×
      List (Entry Empty Empty) := fun c T => stageTwoView Instance.crtEntry Entry.table parameter scalar u (c, T)
  have sub : {tape : TableTape Instance.crtEntry | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape =
        view ∧ N ∈ gAsked scalar tape ∧ notExceptional scalar u N tape} ⊆
      {ω : Instance.crtEntry.Coins × TagTable | view' ω.1 ω.2 = view ∧
        finalEvent scalar u N ω.1 ω.2 (ω.2 (finalHide scalar u N ω.1))} := by
    rintro ⟨c, T⟩ ⟨hv, inside, notExc⟩
    refine ⟨hv, ?_⟩
    change Entry.exceptional scalar c (tagSlot (N / 2 ^ 128)) ≠ some u at notExc
    obtain ⟨o, e, he, hN⟩ := final_of_fam9 scalar c T N inside h9
    have slot : tagSlot (N / 2 ^ 128) = o.val := by
      rw [hN, hashInput_div]
      exact (digestFinalTag_fields (lt_trans o.isLt (by decide))).2
    refine ⟨e, by rw [slot]; exact he, fun eq => notExc (by rw [slot, he, eq]), ?_⟩
    rw [Function.update_eq_self]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hN, hashInput_mod]
    rfl
  refine le_trans (MeasureTheory.measure_mono sub) ?_
  exact outer_table_pos_le Laws.coinLaw (swappedTableLaw crtLayout) (finalHide scalar u N)
    (fun c => Laws.indep_swapped_pos crtLayout _ (finalHide_away scalar u N c)) view'
    (fun c T T' agree => stageTwoView_otherFree parameter scalar u c _ _ T T' fun q hq =>
      agree q (by rw [Set.mem_singleton_iff]; exact hq))
    (finalEvent scalar u N) (fun c a => finalEvent_ignores scalar u N c a)
    (2 ^ 128) (fun c T => finalEvent_few scalar u N c T) view

/-- **H7's case `final`**, at `2^-128`. -/
theorem final_case : GuessCase final notExceptional ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
  blockShare_eq ▸ case_final

/-! ### H7 with the two table cases in place -/

/-- **H7 from the three remaining cases** (`convHot`, `digestOther`, `keyOff`): `maskOff` and `final` are proved here,
each at `2^-128`. -/
theorem crtEntry_stageTwoGuess_of {εConv εDigest εKey : ℝ≥0∞}
    (conv : GuessCase convHot noExtra εConv) (digest : GuessCase digestOther noExtra εDigest)
    (key : GuessCase keyOff notNearEdge εKey)
    (le : εConv ≤ ENNReal.ofReal crtHiddenCharge ∧ εDigest ≤ ENNReal.ofReal crtHiddenCharge ∧
      εKey ≤ ENNReal.ofReal crtHiddenCharge)
    (window : CurveWindowMass) :
    CrtStageTwoGuess Instance.crtEntry Entry.table (ENNReal.ofReal crtHiddenCharge)
      (ENNReal.ofReal hiddenWindowError) :=
  crtEntry_stageTwoGuess conv digest maskOff_case key final_case
    ⟨le.1, le.2.1, invPow128_le_charge, le.2.2, invPow128_le_charge⟩ window

end

end Kriterion.CRT.Privacy.StageTwo
