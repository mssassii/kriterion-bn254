/-
H6 for the 30 never-hot chunk casts. Their query labels are clipped table
materials at final-level slots 17..31 of chunk 31.

The conversion split at input zero hides a disjoint hot set. Its public vector
is uniform independently of these cold materials and of the remaining public
fields. Those fields ignore conversion positions altogether (for this
coordinate), since tag-table records read only the body pads. A one-position
uniform refill therefore gives the same 2^-104 conditional guessing bound.
This proof does not assume that casts are independent of their label bits.
-/

import Proof.Privacy.CRT.Hidden.StageOneTable
import Proof.Privacy.CRT.Laws.CoreReads
import Proof.Correctness.CRT.ChunkStep

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxRecDepth 4096

namespace Kriterion.CRT.Privacy.CastNever

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Privacy.StageTwo (gAsked)
open Kriterion.CRT.Privacy.StageOneProof (OneCase NeverHotCast keyRun_congr tagHash_key label_of_hashInput pubT
  viewSet_eq swappedTableTape_eq stageOneView_pubT gAsked_eq entriesOf_tagHash away_of_family)
open Kriterion.CRT.Privacy.Laws (Indep Ignores)
open scoped ENNReal

noncomputable section

attribute [local instance 2000] H8.tableModulusNeZero

/-! ### The query label -/

/-- The position of the level-5 material at slot `s` of chunk 31's tree of coordinate `κ`. -/
def treePos (κ s : ℕ) : Fin (2 ^ 40) := Conv.tag40 (chunkTreeTag κ 31 5 s)

theorem treeRange {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : TagInRange κ 31 0 5 s 0 :=
  ⟨hκ, by norm_num, by norm_num, by norm_num, hs, by norm_num⟩

theorem treeTag_lt {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : chunkTreeTag κ 31 5 s < 2 ^ 40 :=
  Asks.tagCode_lt (by decide) (treeRange hκ hs)

theorem treePos_val {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : (treePos κ s).val = chunkTreeTag κ 31 5 s :=
  Nat.mod_eq_of_lt (treeTag_lt hκ hs)

theorem treePos_family {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : tagFamily (treePos κ s).val = 0 := by
  rw [treePos_val hκ hs]
  exact tagFamily_tagCode (treeRange hκ hs)

theorem treePos_slot {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : tagSlot (treePos κ s).val = s := by
  rw [treePos_val hκ hs]
  exact tagSlot_tagCode (treeRange hκ hs)

theorem treePos_inj {κ s t : ℕ} (hκ : κ < 2) (hs : s < 65536) (ht : t < 65536) (same : treePos κ s = treePos κ t) :
    s = t := by
  rw [← treePos_slot hκ hs, ← treePos_slot hκ ht, same]

/-- A one-block hash on the tag reading. -/
theorem hLabel_tagHash (A : TagTable) (label : Label) (tag : ℕ) :
    hLabel (H8.tagHash A) label tag = clip (A (Conv.tag40 tag)).1 := by
  unfold hLabel h128
  rw [BmrEntry.tagHash_hashInput]
  rfl

/-- The right half of the last level of a tree is its last level's materials. -/
theorem tree_right (H : HashN) (tagOf : ℕ → ℕ → ℕ) (Δ b0 : Label) (L n : ℕ) (hL : L = n + 1) (hn : n ≠ 0)
    (leaf : Fin (2 ^ L)) (big : 2 ^ n ≤ leaf.val) :
    ∃ label, ((treeGarbleM tagOf Δ b0 L).eval H).1 leaf = hLabel H label (tagOf n (leaf.val - 2 ^ n)) := by
  subst hL
  rw [SliceC.eval_treeGarbleM_succ H tagOf Δ b0 n hn]
  simp only [extendLevel, dif_neg (not_lt.mpr big)]
  exact ⟨_, rfl⟩

theorem table_chunkCount' : table.chunkCount = 32 := Paths.bn254_chunkCount

/-- What a never-hot garbler input is: a cast of chunk 31 of a coordinate at a leaf `49 ≤ α < 64`, labelled by the
first block of the table at the level-5 material `α − 32`. -/
def NeverFacts (A : TagTable) (N : ℕ) : Prop :=
  tagCoord (N / 2 ^ 128) < 2 ∧ 49 ≤ tagSlot (N / 2 ^ 128) ∧ tagSlot (N / 2 ^ 128) < 64 ∧
    BitVec.ofNat 128 N = embed (clip (A (treePos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32))).1)

/-- **One coordinate's never-hot inputs.** -/
theorem coord_never (A : TagTable) (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label)
    (N : ℕ) (inside : N ∈ asked (H8.tagHash A) (coordGarbleM table S coord Δ Z))
    (never : NeverHotCast (N / 2 ^ 128)) : NeverFacts A N := by
  have ranges := Paths.bn254_ranges S hS
  obtain ⟨fam1, idx31, slot49⟩ := never
  simp only [coordGarbleM, asked_bind, asked_tableM, asked_pure, List.append_nil, List.mem_append,
    List.mem_flatMap, List.mem_finRange, true_and] at inside
  rcases inside with ⟨c, inC⟩ | ⟨i, inM⟩
  · have cLt : c.val < 32 := lt_of_lt_of_le c.isLt table_chunkCount'.le
    rw [asked_chunkGarbleM] at inC
    rcases List.mem_append.mp inC with inTree | inCast
    · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (Paths.treeGarbleM_tagged 0 coord c.val 0
        ⟨by norm_num, hc, by omega, by norm_num, by norm_num, by norm_num⟩ Δ _ (table.chunkWidth c.val)
        (ranges.chunkWidth c.val c.isLt)) _ _ inTree
      rw [hashInput_tag, tagFamily_key range] at fam1
      simp only [Paths.treeKeys, Set.mem_ofPred_eq] at member
      omega
    · obtain ⟨leaf, -, inCast⟩ := List.mem_flatMap.mp inCast
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp inCast
      rw [hashInput_tag] at fam1 idx31 slot49
      have leafLt : leaf.val < 256 := lt_of_lt_of_le leaf.isLt
        (le_trans (Nat.pow_le_pow_right (by norm_num) (Paths.bn254_chunkWidth c.val)) (by norm_num))
      have jLt : j.val < 64 := lt_of_lt_of_le j.isLt ranges.castAnswers
      have range : TagInRange coord c.val 0 0 leaf.val j.val := ⟨hc, by omega, by norm_num, by norm_num, by omega, jLt⟩
      have hidx : tagIdx (chunkCastTag coord c.val leaf.val j.val) = c.val := tagIdx_tagCode range
      have hslot : tagSlot (chunkCastTag coord c.val leaf.val j.val) = leaf.val := tagSlot_tagCode range
      have hcoord : tagCoord (chunkCastTag coord c.val leaf.val j.val) = coord := tagCoord_tagCode range
      rw [hidx] at idx31
      rw [hslot] at slot49
      have hw : table.chunkWidth c.val = 5 + 1 := by rw [idx31]; rfl
      have e64 : (2 : ℕ) ^ table.chunkWidth c.val = 64 := by rw [hw]; norm_num
      have leaf64 : leaf.val < 64 := lt_of_lt_of_eq leaf.isLt e64
      obtain ⟨label, hlabel⟩ := tree_right (H8.tagHash A) (chunkTreeTag coord c.val) Δ
        (Z (table.chunkOffset c.val + 0)) (table.chunkWidth c.val) 5 hw (by norm_num) leaf (by norm_num; omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hashInput_tag, hcoord]; exact hc
      · rw [hashInput_tag, hslot]; exact slot49
      · rw [hashInput_tag, hslot]; exact leaf64
      · rw [label_of_hashInput, hlabel, hLabel_tagHash, hashInput_tag, hcoord, hslot]
        have same : ∀ x, chunkTreeTag coord c.val 5 x = chunkTreeTag coord 31 5 x := fun x => by rw [idx31]
        show embed (clip (A (Conv.tag40 (chunkTreeTag coord c.val 5 (leaf.val - 2 ^ 5)))).1) =
          embed (clip (A (Conv.tag40 (chunkTreeTag coord 31 5 (leaf.val - 32)))).1)
        rw [same, show (2 : ℕ) ^ 5 = 32 by norm_num]
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.modGarbleM_tagged table S coord ranges hc Δ _ i) _ _ inM
    rw [hashInput_tag, tagFamily_key range] at fam1
    simp only [Paths.modKeys, Set.mem_ofPred_eq] at member
    omega

/-- **A garbler input at a never-hot cast tag is labelled by the level-5 material at slot `α − 32`.** -/
theorem never_input (scalar : NonZeroScalar) (coins : Entry.Coins) (A : TagTable) (N : ℕ)
    (inside : N ∈ asked (H8.tagHash A) (garbleCM scalar coins)) (never : NeverHotCast (N / 2 ^ 128)) :
    NeverFacts A N := by
  unfold garbleCM at inside
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · exact coord_never A xCount 0 (by decide) (by norm_num) _ _ N inX never
  · exact coord_never A yCount 1 (by decide) (by norm_num) _ _ N inY never
  · simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inKey
    subst inKey
    have fam := never.1
    unfold maskKeyInput at fam
    rw [hashInput_div, maskKeyTag_family] at fam
    exact absurd fam (by decide)
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.maskAnswersM_tagged _ digitCount (by decide) (by decide)) _ _ inMask
    have fam := never.1
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
      Set.mem_ofPred_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.digestGarbleM_tagged coordinateBitCount digitCount (by decide) (by decide) _ _ _ _ _) _ _ inDigest
    have fam := never.1
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union, Set.mem_ofPred_eq] at member
    omega

/-! ### The public fields outside one conversion vector -/

/-- Conversion positions belonging to one coordinate (body pads are excluded). -/
def ConvPos (κ : Fin 2) (p : Fin (2 ^ 40)) : Prop :=
  tagFamily p.val ≤ 5 ∧ tagCoord p.val = κ.val

/-- Read one coordinate's public vector. -/
def crtOf (κ : Fin 2) (p : Entry.Public) : Vector Label convCount :=
  if κ = 0 then p.crtX else p.crtY

/-- Replace one public conversion vector. -/
def setCrt (κ : Fin 2) (b : Vector Label convCount) (p : Entry.Public) : Entry.Public :=
  if κ = 0 then { p with crtX := b } else { p with crtY := b }

/-- The remaining public fields. -/
def restPub (κ : Fin 2) (p : Entry.Public) : Entry.Public :=
  setCrt κ (Vector.replicate convCount 0) p

theorem setCrt_rest (κ : Fin 2) (p : Entry.Public) :
    setCrt κ (crtOf κ p) (restPub κ p) = p := by
  fin_cases κ <;> cases p <;> rfl

theorem pub_eq_iff (κ : Fin 2) (p q : Entry.Public) :
    p = q ↔ crtOf κ p = crtOf κ q ∧ restPub κ p = restPub κ q := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨hc, hr⟩
    calc p = setCrt κ (crtOf κ p) (restPub κ p) := (setCrt_rest κ p).symm
      _ = setCrt κ (crtOf κ q) (restPub κ q) := by rw [hc, hr]
      _ = q := setCrt_rest κ q

section Public

variable [FieldCertificate] [GroupCertificate]

/-- On the tag reading, all fields other than this conversion vector ignore
its conversion positions. In particular, changing its truth words does not
change records: pad answers depend on their tags alone. -/
theorem restPub_congr (κ : Fin 2) (scalar : NonZeroScalar) (c : Entry.Coins)
    (A A' : TagTable) (agree : ∀ p, ¬ ConvPos κ p → A p = A' p) :
    restPub κ (pubT scalar c A) = restPub κ (pubT scalar c A') := by
  have fams : Laws.P4Reads.FamAgree A A' := by
    intro p hp
    apply agree
    rintro ⟨low, _⟩
    rcases hp with h | h | h <;> omega
  have bc : BmrEntry.bmrCoinsOf c A = BmrEntry.bmrCoinsOf c A' := by
    unfold BmrEntry.bmrCoinsOf
    rw [Laws.P4Reads.bmrPadsOf_congr fams, Laws.P4Reads.bmrMasksOf_congr fams]
  have curve : (pubT scalar c A).curve = (pubT scalar c A').curve := by
    unfold pubT
    rw [BmrEntry.curve_eq, BmrEntry.curve_eq, bc]
  have rows : (pubT scalar c A).rows = (pubT scalar c A').rows := by
    ext i hi
    change (pubT scalar c A).rows.get ⟨i, hi⟩ = (pubT scalar c A').rows.get ⟨i, hi⟩
    unfold pubT
    have h := BmrEntry.rows_eq scalar c A ⟨i, hi⟩
    rw [bc] at h
    exact h.trans (BmrEntry.rows_eq scalar c A' ⟨i, hi⟩).symm
  have rx : (pubT scalar c A).recX = (pubT scalar c A').recX := by
    unfold pubT
    rw [BmrReal.recX_vec, BmrReal.recX_vec, bc]
  have ry : (pubT scalar c A).recY = (pubT scalar c A').recY := by
    unfold pubT
    rw [BmrReal.recY_vec, BmrReal.recY_vec, bc]
  have ex : (pubT scalar c A).exception = (pubT scalar c A').exception := by
    have h := Laws.P4Reads.exception_congr 0 scalar c (t := A) (t' := A')
      (fun p hp => agree p (fun h => by have := h.1; omega))
    rw [BmrReal.realGarbled_pair, BmrReal.realGarbled_pair] at h
    exact h
  have coord : ∀ (S k : ℕ), S ≤ 1000 → k < 2 → k ≠ κ.val → ∀ (Δ : Label) (Z : ℕ → Label),
      (coordGarbleM table S k Δ Z).eval (H8.tagHash A) =
        (coordGarbleM table S k Δ Z).eval (H8.tagHash A') := by
    intro S k hS hk hne Δ Z
    refine (keyRun_congr (Paths.coordGarbleM_tagged table S k (Paths.bn254_ranges S hS) hk Δ Z)
      _ _ fun key member range label => ?_).1
    rw [tagHash_key A range, tagHash_key A' range]
    apply agree
    rintro ⟨_, same⟩
    have val : (Conv.tag40 key.code).val = key.code := Nat.mod_eq_of_lt (Paths.TagKey.code_lt range)
    rw [val] at same
    have decoded : tagCoord key.code = key.coord := tagCoord_tagCode (tagInRange_of_key range)
    rw [decoded, member.2] at same
    exact hne same
  have other : (if κ = 0 then (pubT scalar c A).crtY else (pubT scalar c A).crtX) =
      (if κ = 0 then (pubT scalar c A').crtY else (pubT scalar c A').crtX) := by
    fin_cases κ
    · change convVector (EntryCorrect.gyOf (H8.tagHash A) c).pub =
        convVector (EntryCorrect.gyOf (H8.tagHash A') c).pub
      unfold EntryCorrect.gyOf
      rw [coord yCount 1 (by decide) (by decide) (by decide)]
    · change convVector (EntryCorrect.gxOf (H8.tagHash A) c).pub =
        convVector (EntryCorrect.gxOf (H8.tagHash A') c).pub
      unfold EntryCorrect.gxOf
      rw [coord xCount 0 (by decide) (by decide) (by decide)]
  fin_cases κ
  · change Entry.Public.mk _ _ _ _ _ _ _ = Entry.Public.mk _ _ _ _ _ _ _
    change (pubT scalar c A).crtY = (pubT scalar c A').crtY at other
    rw [curve, rows, ex, other, rx, ry]
  · change Entry.Public.mk _ _ _ _ _ _ _ = Entry.Public.mk _ _ _ _ _ _ _
    change (pubT scalar c A).crtX = (pubT scalar c A').crtX at other
    rw [curve, rows, ex, other, rx, ry]

/-- The zero input leaves the never-hot label's tree position cold. -/
def zeroInput : AffineInput := ⟨0, 0⟩

theorem treePos_cold (κ : Fin 2) {s : ℕ} (hs : s < 32) (hne : s ≠ 0) :
    ¬ H8.hotConvTag table zeroInput κ.val (treePos κ.val s) := by
  intro hot
  have h := hot.2.2
  rw [treePos_val κ.isLt (by omega), hotTag_chunkTree table zeroInput (treeRange κ.isLt (by omega))] at h
  have value : coordValue zeroInput κ.val = 0 := by simp [coordValue, zeroInput]
  have chunk : table.chunkValue 0 31 = 0 := by simp [CrtTable.chunkValue]
  rw [value, chunk, Nat.zero_mod, beq_iff_eq] at h
  exact hne h

theorem treePos_conv (κ : Fin 2) {s : ℕ} (hs : s < 32) : ConvPos κ (treePos κ.val s) := by
  refine ⟨by rw [treePos_family κ.isLt (by omega)]; omega, ?_⟩
  rw [treePos_val κ.isLt (by omega)]
  exact tagCoord_tagCode (treeRange κ.isLt (by omega))

/-- `restPub` ignores the full conversion family, hence also its hot subset. -/
theorem restPub_reads (κ : Fin 2) (scalar : NonZeroScalar) :
    H8.ReadsOff Eq (H8.hotConvTag table zeroInput κ.val)
      (fun tape => restPub κ (pubT scalar tape.1 tape.2)) := by
  rintro ⟨c, A⟩ ⟨c', A'⟩ same agree
  dsimp only at same ⊢
  subst c'
  apply restPub_congr κ scalar c A A'
  intro p hp
  exact agree p (fun hot => hp ⟨hot.1, hot.2.1⟩)

/-- Reading the target cold material does not disturb the conversion split. -/
theorem restPub_label_reads (κ : Fin 2) (scalar : NonZeroScalar) {s : ℕ}
    (hs : s < 32) (hne : s ≠ 0) :
    H8.ReadsOff Eq (H8.hotConvTag table zeroInput κ.val)
      (fun tape => (restPub κ (pubT scalar tape.1 tape.2), clip (tape.2 (treePos κ.val s)).1)) := by
  intro tape tape' same agree
  exact Prod.ext (restPub_reads κ scalar tape tape' same agree)
    (congrArg (fun answer : Block × Block => clip answer.1) (agree _ (treePos_cold κ hs hne)))

/-- The conversion part used by `conv_split` is the selected public vector. -/
theorem crtPart_pubT (κ : Fin 2) (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) :
    DeltaView.crtPart 0 scalar κ tape = crtOf κ (pubT scalar tape.1 tape.2) := by
  rcases tape with ⟨c, T⟩
  unfold DeltaView.crtPart crtOf pubT
  split_ifs
  · exact congrArg (fun p => p.1.crtX) (BmrReal.realGarbled_pair 0 scalar c T)
  · exact congrArg (fun p => p.1.crtY) (BmrReal.realGarbled_pair 0 scalar c T)

/-! ### Probability factorization -/

/-- A mass at a mapped value is the mass of its fibre. -/
theorem map_mass {Ω V : Type} (μ : PMF Ω) (f : Ω → V) (v : V) :
    (μ.map f) v = μ.toOuterMeasure {ω | f ω = v} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

set_option linter.constructorNameAsVariable false in
/-- The raw first-block fibre includes 24 unused high bits; the second block is arbitrary. -/
theorem clip_answer_card (g : Label) [DecidablePred fun a : Block × Block => clip a.1 = g] :
    (Finset.univ.filter fun a : Block × Block => clip a.1 = g).card ≤ 2 ^ (256 - labelBits) := by
  classical
  have sub : (Finset.univ.filter fun a : Block × Block => clip a.1 = g) ⊆
      (Finset.univ.filter fun b : Block => clip b = g) ×ˢ Finset.univ := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at ha ⊢
    exact ⟨ha, trivial⟩
  refine le_trans (Finset.card_le_card sub) ?_
  rw [Finset.card_product, Finset.card_univ]
  have fibre : (Finset.univ.filter fun b : Block => clip b = g).card = 2 ^ (128 - labelBits) := by
    rw [← Fintype.card_subtype]
    exact Narrow.card_clip_fibre g
  rw [fibre, Kriterion.ArgoMAC.Security.PGS.card_block]
  decide

theorem clip_answer_ratio :
    ((2 ^ (256 - labelBits) : ℕ) : ℝ≥0∞) / Fintype.card (Block × Block) =
      ((2 : ℝ≥0∞) ^ labelBits)⁻¹ := by
  have den : Fintype.card (Block × Block) = 2 ^ (256 - labelBits) * 2 ^ labelBits := by
    rw [Fintype.card_prod, Kriterion.ArgoMAC.Security.PGS.card_block]
    decide
  have nz : (2 : ℝ≥0∞) ^ (256 - labelBits) ≠ 0 := pow_ne_zero _ two_ne_zero
  have nt : (2 : ℝ≥0∞) ^ (256 - labelBits) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [den]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl nz) (Or.inl nt)]
  calc _ = (((2 : ℝ≥0∞) ^ (256 - labelBits))⁻¹ * 2 ^ (256 - labelBits)) *
      ((2 : ℝ≥0∞) ^ labelBits)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel nz nt, one_mul]

/-- The target material is uniform conditional on the remaining public fields. -/
theorem rest_guess (κ : Fin 2) (scalar : NonZeroScalar) {s : ℕ} (hs : s < 32)
    (g : Label) (v : Entry.Public) :
    (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | restPub κ (pubT scalar tape.1 tape.2) = v ∧ clip (tape.2 (treePos κ.val s)).1 = g} ≤
      ((2 : ℝ≥0∞) ^ labelBits)⁻¹ * (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | restPub κ (pubT scalar tape.1 tape.2) = v} := by
  rw [swappedTableTape_eq]
  rw [← clip_answer_ratio]
  refine HiddenGuess.outer_table_le _ (swappedTableLaw crtLayout) (treePos κ.val s)
    (Laws.indep_swapped_pos crtLayout _ (away_of_family _
      (by rw [treePos_family κ.isLt (by omega)]; decide)
      (by rw [treePos_family κ.isLt (by omega)]; decide)))
    (fun c T => restPub κ (pubT scalar c T)) ?_
    (fun _ _ a => clip a.1 = g) (2 ^ (256 - labelBits)) (fun _ _ => @clip_answer_card g (fun _ => Classical.propDecidable _)) v
  intro c A A' agree
  apply restPub_congr κ scalar c A A'
  intro p hp
  apply agree
  intro eq
  have eq' : p = treePos κ.val s := eq
  apply hp
  rw [eq']
  exact treePos_conv κ hs

/-- Factoring out the uniform conversion vector restores the same bound for
the complete public value, including every half-pin. -/
theorem public_guess (κ : Fin 2) (scalar : NonZeroScalar) {s : ℕ} (hs : s < 32) (hne : s ≠ 0)
    (g : Label) (v : Entry.Public) :
    (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | pubT scalar tape.1 tape.2 = v ∧ clip (tape.2 (treePos κ.val s)).1 = g} ≤
      ((2 : ℝ≥0∞) ^ labelBits)⁻¹ * (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | pubT scalar tape.1 tape.2 = v} := by
  have joint := DeltaView.conv_split 0 scalar zeroInput κ
    (fun tape => (restPub κ (pubT scalar tape.1 tape.2), clip (tape.2 (treePos κ.val s)).1))
    (restPub_label_reads κ scalar hs hne) (crtOf κ v) (restPub κ v, g)
  have marginal := DeltaView.conv_split 0 scalar zeroInput κ
    (fun tape => restPub κ (pubT scalar tape.1 tape.2)) (restPub_reads κ scalar)
    (crtOf κ v) (restPub κ v)
  simp only [crtPart_pubT, map_mass] at joint marginal
  have jointSet : {tape : TableTape Instance.crtEntry |
      (crtOf κ (pubT scalar tape.1 tape.2),
        (restPub κ (pubT scalar tape.1 tape.2), clip (tape.2 (treePos κ.val s)).1)) =
        (crtOf κ v, (restPub κ v, g))} =
      {tape | pubT scalar tape.1 tape.2 = v ∧ clip (tape.2 (treePos κ.val s)).1 = g} := by
    ext tape
    change ((crtOf κ (pubT scalar tape.1 tape.2),
      (restPub κ (pubT scalar tape.1 tape.2), clip (tape.2 (treePos κ.val s)).1)) =
      (crtOf κ v, (restPub κ v, g))) ↔ _
    rw [Prod.mk.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hc, hr, hy⟩
      exact ⟨(pub_eq_iff κ _ v).mpr ⟨hc, hr⟩, hy⟩
    · rintro ⟨hp, hy⟩
      obtain ⟨hc, hr⟩ := (pub_eq_iff κ _ v).mp hp
      exact ⟨hc, hr, hy⟩
  have marginalSet : {tape : TableTape Instance.crtEntry |
      (crtOf κ (pubT scalar tape.1 tape.2), restPub κ (pubT scalar tape.1 tape.2)) =
        (crtOf κ v, restPub κ v)} = {tape | pubT scalar tape.1 tape.2 = v} := by
    ext tape
    change ((crtOf κ (pubT scalar tape.1 tape.2), restPub κ (pubT scalar tape.1 tape.2)) =
      (crtOf κ v, restPub κ v)) ↔ _
    rw [Prod.mk.injEq]
    exact (pub_eq_iff κ _ v).symm
  rw [jointSet] at joint
  rw [marginalSet] at marginal
  have restSet : {tape : TableTape Instance.crtEntry |
      (restPub κ (pubT scalar tape.1 tape.2), clip (tape.2 (treePos κ.val s)).1) = (restPub κ v, g)} =
      {tape | restPub κ (pubT scalar tape.1 tape.2) = restPub κ v ∧
        clip (tape.2 (treePos κ.val s)).1 = g} := by
    ext tape
    simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  rw [restSet] at joint
  rw [joint, marginal]
  calc _ ≤ _ := mul_le_mul' le_rfl (rest_guess κ scalar hs g (restPub κ v))
    _ = _ := by ring

end Public

end

open Kriterion.CRT.Privacy.CastNever in
/-- **The 30 never-hot casts**, using conditional conversion uniformity and a cold material. -/
theorem _root_.Kriterion.CRT.Privacy.StageOneProof.neverCase :
    StageOneProof.OneCase StageOneProof.NeverHotCast ((2 : ℝ≥0∞) ^ labelBits)⁻¹ := by
  intro field group parameter scalar view N never
  by_cases asked : ∃ tape, N ∈ gAsked scalar tape
  · obtain ⟨tape0, h0⟩ := asked
    rw [gAsked_eq] at h0
    obtain ⟨hκ, lo, hi, -⟩ := never_input scalar tape0.1 tape0.2 N h0 never
    let κ : Fin 2 := ⟨tagCoord (N / 2 ^ 128), hκ⟩
    have hs : tagSlot (N / 2 ^ 128) - 32 < 32 := by omega
    have ne : tagSlot (N / 2 ^ 128) - 32 ≠ 0 := by omega
    have sub : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} ⊆
        {tape : TableTape Instance.crtEntry | pubT scalar tape.1 tape.2 = view ∧
          clip (tape.2 (treePos κ.val (tagSlot (N / 2 ^ 128) - 32))).1 = clip (BitVec.ofNat 128 N)} := by
      rintro tape ⟨hv, hN⟩
      rw [stageOneView_pubT] at hv
      rw [gAsked_eq] at hN
      refine ⟨hv, ?_⟩
      have label := congrArg clip (never_input scalar tape.1 tape.2 N hN never).2.2.2.symm
      simpa only [Narrow.clip_embed] using label
    refine le_trans (MeasureTheory.measure_mono sub) ?_
    rw [viewSet_eq]
    exact public_guess κ scalar hs ne (clip (BitVec.ofNat 128 N)) view
  · have empty : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} = ∅ := by
      ext tape
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ inside
      exact asked ⟨tape, inside⟩
    rw [empty, MeasureTheory.measure_empty]
    exact zero_le

end Kriterion.CRT.Privacy.CastNever
