/-
**CRT privacy core: the conversion row of H8** (`H8.CrtConvSplit table κ`).

Under the swapped table tape the real `crtX` (`κ = 0`) or `crtY` (`κ = 1`) is distributed as the uniform source's and
is independent of every `g` that reads the tape (coins included) off the hot conversion tags of `κ` at `u`.

* The hot reads' tags (`ConvRead.readTag` at the coordinate value `coordValue u κ`) are hidden (`hot_hidden`: family at
  most 5, coordinate `κ`, hot at `u`) and lie away from every pad and mask site (`hot_away`: families 6 and 7).
* So the swapped table is its cold part refilled uniformly at the hot tags (`swappedTableLaw_fill`),
  refilling does not change `g`, and the real material reads the refilled table (`Asks.real_readPub`,
  `Flat.convVector_eq_flatOf`). `Conv.conversion_law_fill` makes the in-range reading uniform and independent of the
  tape, so the pair has the product law (`split_apply`).
* The ideal side is `flatOf` of uniform conversion values (`Flat.source_crt_law`).
-/

import Proof.Privacy.CRT.Core.ConvFlat
import Proof.Privacy.CRT.Core.ConvAsks
import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Hidden.GuessCore

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.ConvSplit

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Conv (ConvVals rowOf readPub emptyRow HotRead StageRead readTag tag40 tagRead hotField
  readTag_eq_field hotField_range readTag_lt tag40_readTag_injective bn254Table_wf bn254Table_range fillHot
  conversion_law_fill)
open Kriterion.CRT.Privacy.Instance (crtEntry)
open scoped ENNReal

noncomputable section

/-! ### The hot tags -/

theorem hotField_fam (v : ℕ) (r : HotRead table) : (hotField table v r).1 ≤ 5 := by
  rcases r with (⟨c, k⟩ | ⟨c, j⟩) | ⟨i, ((k | j) | ((k | j) | (k | k)))⟩ <;> simp [hotField]

theorem tag40_val (κ v : ℕ) (hκ : κ < 2) (r : HotRead table) :
    (tag40 (readTag table κ v r)).val = readTag table κ v r :=
  Nat.mod_eq_of_lt (readTag_lt table bn254Table_range κ v hκ r)

theorem family_readTag (κ v : ℕ) (hκ : κ < 2) (r : HotRead table) :
    tagFamily (readTag table κ v r) = (hotField table v r).1 := by
  rw [readTag_eq_field]
  exact tagFamily_tagCode (hotField_range table bn254Table_range κ v hκ r).1

theorem coord_readTag (κ v : ℕ) (hκ : κ < 2) (r : HotRead table) : tagCoord (readTag table κ v r) = κ := by
  rw [readTag_eq_field]
  exact tagCoord_tagCode (hotField_range table bn254Table_range κ v hκ r).1

/-- A modulus with a hot read is odd. -/
theorem odd_of_read (i : Fin table.count) (s : StageRead (rowOf (table.kind i) (table.modulus i))) :
    ∃ row, table.kind i = .odd row := by
  cases hk : table.kind i with
  | odd row => exact ⟨row, rfl⟩
  | chunkZero =>
      exfalso
      have e : rowOf (table.kind i) (table.modulus i) = emptyRow := by
        rw [hk]
        rfl
      have empty : ∀ x : StageRead (rowOf (table.kind i) (table.modulus i)), False := by
        rw [e]
        intro x
        rcases x with ((k | j) | ((k | j) | (k | k)))
        all_goals exact Fin.elim0 ‹_›
      exact empty s

/-- **Every hot read's tag is hot at `u`.** -/
theorem hotTag_readTag (u : AffineInput) (κ : ℕ) (hκ : κ < 2) (r : HotRead table) :
    hotTag table u (readTag table κ (coordValue u κ) r) = true := by
  obtain ⟨hin, _⟩ := hotField_range table bn254Table_range κ (coordValue u κ) hκ r
  rw [readTag_eq_field]
  unfold hotTag
  simp only [tagFamily_tagCode hin, tagCoord_tagCode hin, tagIdx_tagCode hin, tagLevel_tagCode hin,
    tagSlot_tagCode hin, tagStage_tagCode hin]
  rcases r with (⟨c, k⟩ | ⟨c, j⟩) | ⟨i, s⟩
  · simp [hotField]
  · simp [hotField]
  · obtain ⟨row, hk⟩ := odd_of_read i s
    obtain ⟨wf, hm⟩ := bn254Table_wf.rows i row hk
    have hrow : rowOf (Kind.odd row) (table.modulus i) = row := Conv.rowOf_odd row _ wf hm
    rcases s with ((k | j) | ((k | j) | (k | k))) <;>
      simp [hotField, i.isLt, hk, hrow, stageValue]

/-- **The hot reads' tags are hidden** (`H8.hotConvTag`). -/
theorem hot_hidden (u : AffineInput) (κ : ℕ) (hκ : κ < 2) (r : HotRead table) :
    H8.hotConvTag table u κ (tag40 (readTag table κ (coordValue u κ) r)) := by
  unfold H8.hotConvTag
  rw [tag40_val κ _ hκ]
  exact ⟨by rw [family_readTag κ _ hκ]; exact hotField_fam _ r, coord_readTag κ _ hκ r, hotTag_readTag u κ hκ r⟩

/-- A site tag of family above 5 is not a hot read's position. -/
theorem site_ne (κ v : ℕ) (hκ : κ < 2) (r : HotRead table) {fam coord idx stage level slot part : ℕ}
    (hf : 5 < fam) (hf16 : fam < 16) (hin : TagInRange coord idx stage level slot part) :
    tagPos (tagCode fam coord idx stage level slot part) ≠ tag40 (readTag table κ v r) := by
  intro heq
  have h1 := Asks.tagCode_lt hf16 hin
  have e := congrArg Fin.val heq
  simp only [tagPos] at e
  rw [Nat.mod_eq_of_lt h1, tag40_val κ v hκ] at e
  have f1 := tagFamily_tagCode (fam := fam) hin
  rw [e, family_readTag κ v hκ] at f1
  have := hotField_fam v r
  omega

/-- **The hot reads' tags lie away from every pad and mask site.** -/
theorem hot_away (κ v : ℕ) (hκ : κ < 2) :
    ∀ site ∈ crtLayout.sites, ∀ r : HotRead table,
      tag40 (readTag table κ v r) ∉ (siteTags crtLayout site).map tagPos := by
  intro site mem r hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  rcases List.mem_append.mp mem with pad | mask
  · obtain ⟨κ', i, ρ, rfl, hκ', hi, hρ⟩ := Layout.mem_padSites pad
    obtain ⟨-, -, -, -, hm, hq⟩ := Layout.tableFacts κ' hκ' i hi
    simp only [siteTags, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have hj' : j < Layout.padCount κ' i := hj
    exact site_ne κ v hκ r (by decide) (by decide) ⟨hκ', by omega, by omega, by omega, by omega, by omega⟩ heq
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 2 := hj
      exact site_ne κ v hκ r (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        heq
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 3 := hj
      exact site_ne κ v hκ r (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        heq

/-! ### A product law -/

/-- **A uniform part paired with a function of the rest has the product law.** -/
theorem split_apply {Ω α β : Type} (μ : PMF Ω) (ν : PMF β) (g : Ω → α) (b : β) (a : α) :
    (μ.bind fun ω => ν.map fun b' => some (b', g ω)) (some (b, a)) = ν b * (μ.map fun ω => some (g ω)) (some a) := by
  classical
  have inner : ∀ ω, (ν.map fun b' => some (b', g ω)) (some (b, a)) = if a = g ω then ν b else 0 := by
    intro ω
    rw [PMF.map_apply]
    by_cases h : a = g ω
    · rw [if_pos h, tsum_eq_single b]
      · simp [h]
      · intro b' hb'
        simp [Ne.symm hb']
    · rw [if_neg h]
      apply ENNReal.tsum_eq_zero.mpr
      intro b'
      simp [h]
  rw [PMF.bind_apply, PMF.map_apply]
  simp_rw [inner]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext ω
  by_cases h : a = g ω
  · simp [h, mul_comm]
  · simp [h]

/-! ### The real material on the swapped tape -/

/-- The fill of the table at the hot tags is `ConvRead`'s. -/
theorem fillAt_eq (κ v : ℕ) (A : TagTable) (f : HotRead table → Block × Block) :
    HiddenGuess.fillAt (fun r => tag40 (readTag table κ v r)) f A = fillHot table κ v A f := rfl

/-- **The core of the split**, for one coordinate `κ` read at value `v`, with the coordinate's `Δ` and zero labels
taken from the coins. -/
theorem split_core {α : Type} (S κ : ℕ) (hκ : κ < 2) (v : ℕ) (Δof : crtEntry.Coins → Label)
    (Zof : crtEntry.Coins → ℕ → Label) (hidden : Fin (2 ^ 40) → Prop)
    (hhot : ∀ r : HotRead table, hidden (tag40 (readTag table κ v r)))
    (g : TableTape crtEntry → α) (hg : H8.ReadsOff Eq hidden g) (b : Vector Label convCount) (a : α) :
    ((swappedTableTape crtEntry).map fun tape => some (convVector ((coordGarbleM table S κ (Δof tape.1)
        (Zof tape.1)).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub, g tape))
        (some (b, a)) =
      ((PMF.uniformOfFintype (ConvVals table)).map Flat.flatOf) b *
        ((swappedTableTape crtEntry).map fun tape => some (g tape)) (some a) := by
  let pos : HotRead table → Fin (2 ^ 40) := fun r => tag40 (readTag table κ v r)
  have inj : Function.Injective pos := tag40_readTag_injective table bn254Table_range κ v hκ
  have away := hot_away κ v hκ
  let μ := swappedTableTape crtEntry
  letI : Fintype crtEntry.Coins := @Fintype.ofFinite _ crtEntry.coinsFinite
  haveI : Nonempty crtEntry.Coins := ⟨crtEntry.coinWitness⟩
  -- the swapped tape is its cold part refilled at the hot tags
  have hfill : μ = μ.bind fun ρ => (PMF.uniformOfFintype (HotRead table → Block × Block)).map fun f =>
      ((ρ.1, HiddenGuess.fillAt pos f ρ.2) : TableTape crtEntry) := by
    have law := HiddenGuess.swappedTableLaw_fill crtLayout pos inj away
    show (PMF.uniformOfFintype crtEntry.Coins).bind (fun coins => (swappedTableLaw crtLayout).map
        fun table => (coins, table)) = ((PMF.uniformOfFintype crtEntry.Coins).bind fun coins =>
          (swappedTableLaw crtLayout).map fun table => (coins, table)).bind _
    rw [PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun coins => ?_)
    rw [PMF.bind_map]
    conv_lhs => rw [← law]
    rw [PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun A => ?_)
    rw [PMF.map_comp]
    rfl
  -- refilling does not change `g`
  have gfill : ∀ ρ : TableTape crtEntry, ∀ f, g (ρ.1, HiddenGuess.fillAt pos f ρ.2) = g ρ := by
    intro ρ f
    refine hg (ρ.1, HiddenGuess.fillAt pos f ρ.2) ρ rfl fun tag htag => ?_
    dsimp only
    rw [HiddenGuess.fillAt_apply_of_not_mem pos f ρ.2 tag ?_]
    rintro ⟨r, hr⟩
    exact htag (by rw [← hr]; exact hhot r)
  -- the real material reads the refilled table
  have readFill : ∀ ρ : TableTape crtEntry, ∀ f,
      convVector ((coordGarbleM table S κ (Δof ρ.1) (Zof ρ.1)).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) (HiddenGuess.fillAt pos f ρ.2)))).pub =
      Flat.flatOf (readPub table ((coordGarbleM table S κ (Δof ρ.1) (Zof ρ.1)).eval
        (tableHash (tagRead (fillHot table κ v ρ.2 f)))).pub) := by
    intro ρ f
    rw [Flat.convVector_eq_flatOf, Asks.real_readPub _ S κ hκ, fillAt_eq]
  have lawEq := conversion_law_fill table bn254Table_wf bn254Table_range κ v hκ S μ (fun ρ => ρ.2)
    (fun ρ => Zof ρ.1) (fun ρ => Δof ρ.1)
  beta_reduce at lawEq
  have joint : (μ.map fun tape => some (convVector ((coordGarbleM table S κ (Δof tape.1)
        (Zof tape.1)).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub, g tape)) =
      μ.bind fun ρ => (PMF.uniformOfFintype (ConvVals table)).map fun x => some (Flat.flatOf x, g ρ) := by
    conv_lhs => rw [hfill]
    have step : (μ.bind fun ρ => ((PMF.uniformOfFintype (HotRead table → Block × Block)).map fun f =>
          ((ρ.1, HiddenGuess.fillAt pos f ρ.2) : TableTape crtEntry))).map (fun tape =>
            some (convVector ((coordGarbleM table S κ (Δof tape.1) (Zof tape.1)).eval
              (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub, g tape)) =
        (μ.bind fun ρ => (PMF.uniformOfFintype (HotRead table → Block × Block)).map fun f =>
          (ρ, readPub table ((coordGarbleM table S κ (Δof ρ.1) (Zof ρ.1)).eval
            (tableHash (tagRead (fillHot table κ v ρ.2 f)))).pub)).map
          (fun p => some (Flat.flatOf p.2, g p.1)) := by
      rw [PMF.map_bind, PMF.map_bind]
      refine congrArg (PMF.bind μ) (funext fun ρ => ?_)
      rw [PMF.map_comp, PMF.map_comp]
      refine congrArg (fun h => PMF.map h _) (funext fun f => ?_)
      simp only [Function.comp]
      rw [readFill ρ f, gfill ρ f]
    rw [step, lawEq, PMF.map_bind]
    refine congrArg (PMF.bind μ) (funext fun ρ => ?_)
    rw [PMF.map_comp]
    rfl
  rw [joint]
  have inner : ∀ ρ : TableTape crtEntry, ((PMF.uniformOfFintype (ConvVals table)).map fun x =>
      some (Flat.flatOf x, g ρ)) = ((PMF.uniformOfFintype (ConvVals table)).map Flat.flatOf).map
        fun b' => some (b', g ρ) := by
    intro ρ
    rw [PMF.map_comp]
    rfl
  simp_rw [inner]
  exact split_apply μ _ g b a

/-- **A part of the garbling that is one coordinate's flat vector splits off** (`H8.PartSplit` for the hot
conversion tags of `κ` at `u`). -/
theorem partSplit_of (u : AffineInput) (κ : ℕ) (hκ : κ < 2) (S : ℕ) (Δof : crtEntry.Coins → Label)
    (Zof : crtEntry.Coins → ℕ → Label) (part : TableTape crtEntry → Vector Label convCount)
    (hpart : ∀ tape : TableTape crtEntry, part tape = convVector ((coordGarbleM table S κ (Δof tape.1)
      (Zof tape.1)).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub)
    (ideal : PMF (Vector Label convCount))
    (hideal : ideal = (PMF.uniformOfFintype (ConvVals table)).map Flat.flatOf) :
    H8.PartSplit Eq (H8.hotConvTag table u κ) (fun _ => False) part ideal := by
  intro α g hg b a
  simp only [↓reduceIte]
  have hL : (fun tape : TableTape crtEntry => some (part tape, g tape)) = fun tape =>
      some (convVector ((coordGarbleM table S κ (Δof tape.1) (Zof tape.1)).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub, g tape) := by
    funext tape
    rw [hpart tape]
  rw [hL, hideal]
  exact split_core S κ hκ (coordValue u κ) Δof Zof _ (hot_hidden u κ hκ) g hg b a

/-! ### The garbler's flat vectors -/

theorem garbleCM_crtX (scalar : NonZeroScalar) (coins : Coins) (H : HashN) :
    ((garbleCM scalar coins).eval H).1.crtX =
      convVector ((coordGarbleM table xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))).eval H).pub := by
  simp only [garbleCM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rfl

theorem garbleCM_crtY (scalar : NonZeroScalar) (coins : Coins) (H : HashN) :
    ((garbleCM scalar coins).eval H).1.crtY =
      convVector ((coordGarbleM table yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))).eval H).pub := by
  simp only [garbleCM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rfl

section Row

variable [FieldCertificate] [GroupCertificate]

theorem realGarbled_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape crtEntry) :
    H8.realGarbled crtEntry parameter scalar tape =
      (garbleCM scalar tape.1).eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) := by
  unfold H8.realGarbled
  rw [show crtEntry.scheme = fun field group => @Entry.scheme field group from rfl]
  simp only [Entry.scheme]
  rfl

theorem realGarbled_crtX (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape crtEntry) :
    (H8.realGarbled crtEntry parameter scalar tape).1.crtX =
      convVector ((coordGarbleM table xCount 0 (clip (tape.1.inputDelta .x)) (fun j => clip (atNat (tape.1.inputZero .x) 0 j))).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub := by
  rw [realGarbled_eq]
  simp only [garbleCM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rfl

theorem realGarbled_crtY (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape crtEntry) :
    (H8.realGarbled crtEntry parameter scalar tape).1.crtY =
      convVector ((coordGarbleM table yCount 1 (clip (tape.1.inputDelta .y)) (fun j => clip (atNat (tape.1.inputZero .y) 0 j))).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub := by
  rw [realGarbled_eq]
  simp only [garbleCM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rfl

theorem ideal_eq (κ : Fin 2) :
    ((@PMF.uniformOfFintype _ (Instance.view).sourceFintype (Instance.view).sourceNonempty).map fun source =>
      if κ = 0 then ((Instance.view).publish source).crtX else ((Instance.view).publish source).crtY) =
      (PMF.uniformOfFintype (ConvVals table)).map Flat.flatOf := by
  rw [← @Flat.source_crt_law (Instance.view).sourceFintype κ]
  refine congrArg (fun h => PMF.map h _) (funext fun source => ?_)
  fin_cases κ
  · rfl
  · rfl

/-- **P3, the conversion row of H8 for `x`.** -/
theorem crtConvSplit_x : H8.CrtConvSplit table 0 := by
  intro _ _ parameter scalar u α g hg b a
  have hpart : ∀ tape : TableTape crtEntry, (if (0 : Fin 2) = 0 then (H8.realGarbled crtEntry parameter scalar tape).1.crtX
      else (H8.realGarbled crtEntry parameter scalar tape).1.crtY) =
      convVector ((coordGarbleM table xCount 0 (clip (tape.1.inputDelta .x)) (fun j => clip (atNat (tape.1.inputZero .x) 0 j))).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub :=
    fun tape => (if_pos rfl).trans (realGarbled_crtX parameter scalar tape)
  exact partSplit_of u 0 (by decide) xCount (fun c => clip (c.inputDelta .x)) (fun c j => clip (atNat (c.inputZero .x) 0 j)) _
    hpart _ (ideal_eq 0) g hg b a

/-- **P3, the conversion row of H8 for `y`.** -/
theorem crtConvSplit_y : H8.CrtConvSplit table 1 := by
  intro _ _ parameter scalar u α g hg b a
  have hpart : ∀ tape : TableTape crtEntry, (if (1 : Fin 2) = 0 then (H8.realGarbled crtEntry parameter scalar tape).1.crtX
      else (H8.realGarbled crtEntry parameter scalar tape).1.crtY) =
      convVector ((coordGarbleM table yCount 1 (clip (tape.1.inputDelta .y)) (fun j => clip (atNat (tape.1.inputZero .y) 0 j))).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2))).pub :=
    fun tape => (if_neg (by decide)).trans (realGarbled_crtY parameter scalar tape)
  exact partSplit_of u 1 (by decide) yCount (fun c => clip (c.inputDelta .y)) (fun c j => clip (atNat (c.inputZero .y) 0 j)) _
    hpart _ (ideal_eq 1) g hg b a

/-- **P3: the conversion row of H8, for both coordinates.** -/
theorem crtConvSplit (κ : Fin 2) : H8.CrtConvSplit table κ := by
  fin_cases κ
  · exact crtConvSplit_x
  · exact crtConvSplit_y

end Row

end

end Kriterion.CRT.Privacy.ConvSplit
