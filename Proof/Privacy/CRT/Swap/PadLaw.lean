/-
**The pads of the swapped table are uniform and independent of the rest**.

Under `swappedTableLaw crtLayout` the P45 pads a tag table holds (`padsOf`, the same as `BmrEntry.bmrPadsOf`) are uniform on
`BMR.Pads Entry.table`, jointly with anything that ignores the pad positions (`swapped_bmrPadsOf_split`). The proof
reads the product form (`Swap/Product.lean`): the pad sites are drawn independently of the mask sites and of the base
table; a pad site's law is a fibre law, so its reading is its uniform target; and with the flat index a bijection
(`xEncEquiv`, `yEncEquiv`), each pad value is exactly one site's digit, so every value of the pads has the same
probability.
-/

import Proof.Privacy.CRT.Swap.Product
import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Laws.RefillFacts

namespace Kriterion.CRT.Privacy

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3 (fibreLaw fibreLaw_map)
open scoped ENNReal

noncomputable section

/-- The body-pad positions of the real layout. -/
def padPositions : Set (Fin (2 ^ 40)) := {p | ∃ s ∈ Layout.padSites, p ∈ Laws.sitePos crtLayout s}

/-- The P45 pads a tag table holds (the body of `BmrEntry.bmrPadsOf`): at modulus `i`, slot `ρ` and
encoding `e`, the digit `flat e` of the pad vector of the body site `(κ(e), i, ρ)`. -/
def padsOf (table : TagTable) : BMR.Pads Entry.table := fun i ρ e =>
  match e with
  | .inl x => H8.padValues table 0 i ρ.val ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩
  | .inr y => H8.padValues table 1 i ρ.val ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩

namespace PadLaw

/-! ### Reading pad sites from drawn answers -/

/-- A pad site's reading from a list of answers: the pad vector of its first `padCount` entries. -/
def readList (κ : ℕ) (i : Fin Entry.table.count) (answers : List (Block × Block)) :
    Fin (Layout.padS κ) → ZMod (Entry.table.modulus i) :=
  padVector (Entry.table.modulus i) (Layout.padS κ) (Layout.padCount κ i) fun j => answers.getD j.val (0, 0)

/-- The pads drawn at the pad sites, in P45's index. -/
def padsOfDraws (A : SiteId → List (Block × Block)) : BMR.Pads Entry.table := fun i ρ e =>
  match e with
  | .inl x => readList 0 i (A (.pad 0 i ρ.val)) ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩
  | .inr y => readList 1 i (A (.pad 1 i ρ.val)) ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩

theorem count_eq : Entry.table.count = 85 := by decide +kernel

theorem padModulus_eq (i : Fin Entry.table.count) : Layout.padModulus i.val = Entry.table.modulus i := by
  unfold Layout.padModulus
  rw [dif_pos i.isLt]

theorem pad_mem_padSites {κ : ℕ} (hκ : κ < 2) (i : Fin Entry.table.count) {ρ : ℕ}
    (hρ : ρ < Entry.table.modulus i) : SiteId.pad κ i.val ρ ∈ Layout.padSites := by
  have hi : i.val < 85 := count_eq ▸ i.isLt
  simp only [Layout.padSites, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨κ, hκ, i.val, hi, ρ, by rw [padModulus_eq]; exact hρ, rfl⟩

theorem pad_mem_sites {κ : ℕ} (hκ : κ < 2) (i : Fin Entry.table.count) {ρ : ℕ}
    (hρ : ρ < Entry.table.modulus i) : SiteId.pad κ i.val ρ ∈ crtLayout.sites :=
  List.mem_append_left _ (pad_mem_padSites hκ i hρ)

/-- **A pad site of the written table reads its drawn answers.** -/
theorem padValues_overwriteSites (A : SiteId → List (Block × Block))
    (lengths : ∀ s ∈ crtLayout.sites, (A s).length = crtLayout.answers s) (T0 : TagTable) {κ : ℕ} (hκ : κ < 2)
    (i : Fin Entry.table.count) {ρ : ℕ} (hρ : ρ < Entry.table.modulus i) :
    H8.padValues (overwriteSites crtLayout crtLayout.sites A T0) κ i ρ = readList κ i (A (.pad κ i.val ρ)) := by
  have member := pad_mem_sites hκ i hρ
  have back := siteAnswersOf_overwriteSites crtLayout Laws.crtLayout_refill A lengths T0 _ member
  generalize overwriteSites crtLayout crtLayout.sites A T0 = T at back ⊢
  unfold H8.padValues readList
  refine congrArg _ (funext fun j => ?_)
  rw [← back]
  show _ = (((List.range (Layout.padCount κ i.val)).map fun j => tagCode Family.body κ i.val 0 0 ρ j).map
      fun tag => T (tagPos tag)).getD j.val (0, 0)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range j.isLt,
    Option.map_some, Option.map_some, Option.getD_some]
  rfl

/-- **The pads of the written table are the drawn pads.** -/
theorem padsOf_overwriteSites (A : SiteId → List (Block × Block))
    (lengths : ∀ s ∈ crtLayout.sites, (A s).length = crtLayout.answers s) (T0 : TagTable) :
    padsOf (overwriteSites crtLayout crtLayout.sites A T0) = padsOfDraws A := by
  funext i ρ e
  cases e with
  | inl x =>
      show H8.padValues _ 0 i ρ.val _ = readList 0 i (A (.pad 0 i ρ.val)) _
      rw [padValues_overwriteSites A lengths T0 (by norm_num) i (ZMod.val_lt ρ)]
  | inr y =>
      show H8.padValues _ 1 i ρ.val _ = readList 1 i (A (.pad 1 i ρ.val)) _
      rw [padValues_overwriteSites A lengths T0 (by norm_num) i (ZMod.val_lt ρ)]

/-! ### What ignores the pads -/

theorem overwriteSites_congr_at (layout : SiteLayout) :
    ∀ (sites : List SiteId) (A : SiteId → List (Block × Block)) (T T' : TagTable) (p : Fin (2 ^ 40)),
      T p = T' p → overwriteSites layout sites A T p = overwriteSites layout sites A T' p
  | [], _, _, _, _, same => same
  | site :: rest, A, T, T', p, same => by
      rw [Product.overwriteSites_cons, Product.overwriteSites_cons]
      exact overwriteSites_congr_at layout rest A _ _ p (Laws.overwrite_congr_at _ _ T T' p same)

theorem overwriteSites_append (layout : SiteLayout) (L1 L2 : List SiteId) (A : SiteId → List (Block × Block))
    (T : TagTable) :
    overwriteSites layout (L1 ++ L2) A T = overwriteSites layout L2 A (overwriteSites layout L1 A T) := by
  unfold overwriteSites
  rw [List.foldl_append]

/-- Off the pad positions, the written table is the base table with the mask sites written in. -/
theorem overwriteSites_offPads (A : SiteId → List (Block × Block)) (T0 : TagTable) (p : Fin (2 ^ 40))
    (off : p ∉ padPositions) :
    overwriteSites crtLayout crtLayout.sites A T0 p = overwriteSites crtLayout Layout.maskSites A T0 p := by
  show overwriteSites crtLayout (Layout.padSites ++ Layout.maskSites) A T0 p = _
  rw [overwriteSites_append]
  refine overwriteSites_congr_at crtLayout _ A _ _ p ?_
  exact Product.overwriteSites_apply_of_away crtLayout _ A T0 p fun s member inSite => off ⟨s, member, inSite⟩

/-! ### Splitting the draws -/

/-- Draws of a concatenation: the first list's draws, then the second's, merged. -/
theorem siteDraws_append (layout : SiteLayout) :
    ∀ (L1 L2 : List SiteId), siteDraws layout (L1 ++ L2) = (siteDraws layout L1).bind fun A1 =>
      (siteDraws layout L2).map fun A2 => fun s => if s ∈ L1 then A1 s else A2 s
  | [], L2 => by
      simp only [List.nil_append, siteDraws, PMF.pure_bind, List.not_mem_nil, if_false]
      exact (PMF.map_id _).symm
  | site :: L1, L2 => by
      rw [List.cons_append, siteDraws, siteDraws_append layout L1 L2, siteDraws, PMF.bind_bind]
      refine congrArg _ (funext fun answers => ?_)
      rw [PMF.map_bind, PMF.bind_map]
      refine congrArg _ (funext fun A1 => ?_)
      rw [PMF.map_comp, Function.comp_def]
      simp only [Function.comp_def]
      refine congrArg (fun f => PMF.map f _) (funext fun A2 => funext fun s => ?_)
      by_cases same : s = site
      · subst same
        simp
      · simp only [Function.update_of_ne same, List.mem_cons, same, false_or]

/-! ### The pads of the drawn pad sites are uniform -/

/-- A PMF whose atoms are all equal is uniform. -/
theorem eq_uniform_of_const {X : Type} [Fintype X] [Nonempty X] (μ : PMF X) (same : ∀ x y, μ x = μ y) :
    μ = PMF.uniformOfFintype X := by
  classical
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  have total : (Fintype.card X : ℝ≥0∞) * μ x0 = 1 := by
    have := μ.tsum_coe
    rw [tsum_fintype] at this
    rw [← this, Finset.sum_congr rfl fun x _ => same x x0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine PMF.ext fun x => ?_
  rw [same x x0, PMF.uniformOfFintype_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact total)

/-- The event on one pad site that its reading matches `P`. -/
def matchSite (P : BMR.Pads Entry.table) : SiteId → Set (List (Block × Block))
  | .pad κ i ρ =>
    if h : i < Entry.table.count then
      if κ = 0 then {a | ∀ x : BMR.XEnc, readList 0 ⟨i, h⟩ a ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩ =
          P ⟨i, h⟩ (ρ : ZMod (Entry.table.modulus ⟨i, h⟩)) (.inl x)}
      else if κ = 1 then {a | ∀ y : BMR.YEnc, readList 1 ⟨i, h⟩ a ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩ =
          P ⟨i, h⟩ (ρ : ZMod (Entry.table.modulus ⟨i, h⟩)) (.inr y)}
      else Set.univ
    else Set.univ
  | .mask _ _ => Set.univ

theorem preimage_padsOfDraws (P : BMR.Pads Entry.table) :
    padsOfDraws ⁻¹' {P} = {A | ∀ s ∈ Layout.padSites, A s ∈ matchSite P s} := by
  ext A
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro rfl s member
    obtain ⟨κ, i, ρ, rfl, hκ, hi, hρ⟩ := Layout.mem_padSites member
    have h : i < Entry.table.count := count_eq ▸ hi
    have hρ' : ρ < Entry.table.modulus ⟨i, h⟩ := by rw [← padModulus_eq ⟨i, h⟩]; exact hρ
    have val : ((ρ : ZMod (Entry.table.modulus ⟨i, h⟩))).val = ρ := ZMod.val_natCast_of_lt hρ'
    simp only [matchSite]
    rw [dif_pos h]
    interval_cases κ
    · simp only [if_true, Set.mem_ofPred_eq]
      intro x
      simp only [padsOfDraws, val]
    · simp only [one_ne_zero, if_false, if_true, Set.mem_ofPred_eq]
      intro y
      simp only [padsOfDraws, val]
  · intro hitAll
    funext i ρ e
    have hρ : ρ.val < Entry.table.modulus i := ZMod.val_lt ρ
    have cast : ((ρ.val : ℕ) : ZMod (Entry.table.modulus i)) = ρ := ZMod.natCast_zmod_val ρ
    cases e with
    | inl x =>
        have hit := hitAll _ (pad_mem_padSites (κ := 0) (by norm_num) i hρ)
        simp only [matchSite, dif_pos i.isLt, if_true] at hit
        have := hit x
        rw [cast] at this
        exact this
    | inr y =>
        have hit := hitAll _ (pad_mem_padSites (κ := 1) (by norm_num) i hρ)
        simp only [matchSite, dif_pos i.isLt, one_ne_zero, if_false, if_true] at hit
        have := hit y
        rw [cast] at this
        exact this

/-- The reading of a list of answers built from a function is the function's pad vector. -/
theorem readList_ofFn (κ : ℕ) (i : Fin Entry.table.count) (f : Fin (Layout.padCount κ i) → Block × Block) :
    readList κ i (List.ofFn f) = padVector (Entry.table.modulus i) (Layout.padS κ) (Layout.padCount κ i) f := by
  unfold readList
  refine congrArg _ (funext fun j => ?_)
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.isLt, Option.getD_some]

/-- A pad site's law read through `readList`: its uniform target. -/
theorem padSiteLaw_read {κ : ℕ} (hκ : κ < 2) (i : Fin Entry.table.count)
    (E : Set (Fin (Layout.padS κ) → ZMod (Entry.table.modulus i))) :
    (Layout.padSiteLaw (Layout.padS κ) (Layout.padModulus i.val) (Layout.padCount κ i.val)).toOuterMeasure
        {a | readList κ i a ∈ E} = (PMF.uniformOfFintype _).toOuterMeasure E := by
  have hi : i.val < 85 := count_eq ▸ i.isLt
  obtain ⟨pos, fits, -⟩ := Layout.tableFacts κ hκ i.val hi
  rw [padModulus_eq] at pos fits ⊢
  unfold Layout.padSiteLaw
  rw [dif_pos ⟨pos, fits⟩]
  unfold Layout.fibreSiteLaw
  rw [PMF.toOuterMeasure_map_apply]
  have pre : List.ofFn ⁻¹' {a | readList κ i a ∈ E} =
      padVector (Entry.table.modulus i) (Layout.padS κ) (Layout.padCount κ i) ⁻¹' E := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, readList_ofFn]
  rw [pre, ← PMF.toOuterMeasure_map_apply, PMF.map_bind]
  simp only [fibreLaw_map]
  rw [PMF.bind_pure]

/-- The uniform mass of a set with exactly one point. -/
theorem uniform_single {X : Type} [Fintype X] [Nonempty X] (M : Set X) (v : X) (only : ∀ w, w ∈ M ↔ w = v) :
    (PMF.uniformOfFintype X).toOuterMeasure M = (Fintype.card X : ℝ≥0∞)⁻¹ := by
  have : M = {v} := Set.ext fun w => by rw [only, Set.mem_singleton_iff]
  rw [this, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]

/-- **Each pad site's factor does not depend on the pads it must match.** -/
theorem matchSite_mass (P : BMR.Pads Entry.table) {s : SiteId} (member : s ∈ Layout.padSites) :
    (crtLayout.law s).toOuterMeasure (matchSite P s) =
      (crtLayout.law s).toOuterMeasure (matchSite 0 s) := by
  obtain ⟨κ, i, ρ, rfl, hκ, hi, hρ⟩ := Layout.mem_padSites member
  have h : i < Entry.table.count := count_eq ▸ hi
  -- both sides are the inverse cardinality of the site's readings
  suffices each : ∀ Q : BMR.Pads Entry.table, (crtLayout.law (.pad κ i ρ)).toOuterMeasure (matchSite Q (.pad κ i ρ))
      = (Fintype.card (Fin (Layout.padS κ) → ZMod (Entry.table.modulus ⟨i, h⟩)) : ℝ≥0∞)⁻¹ by
    rw [each P, each 0]
  intro Q
  show (Layout.padSiteLaw (Layout.padS κ) (Layout.padModulus (⟨i, h⟩ : Fin Entry.table.count).val)
    (Layout.padCount κ (⟨i, h⟩ : Fin Entry.table.count).val)).toOuterMeasure _ = _
  simp only [matchSite, dif_pos h]
  interval_cases κ
  · simp only [if_true]
    have := padSiteLaw_read (κ := 0) (by norm_num) ⟨i, h⟩
      {v | ∀ x : BMR.XEnc, v ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩ = Q ⟨i, h⟩ (ρ : ZMod _) (.inl x)}
    rw [show {a : List (Block × Block) | ∀ x : BMR.XEnc, readList 0 ⟨i, h⟩ a ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩ =
        Q ⟨i, h⟩ (ρ : ZMod _) (.inl x)} = {a | readList 0 ⟨i, h⟩ a ∈
        {v | ∀ x : BMR.XEnc, v ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩ = Q ⟨i, h⟩ (ρ : ZMod _) (.inl x)}} from rfl,
      this]
    refine uniform_single _ (fun f => Q ⟨i, h⟩ (ρ : ZMod _) (.inl (BMR.xEncEquiv.symm ⟨f.val, by
      have := f.isLt; simpa [Layout.padS] using this⟩))) fun w => ?_
    constructor
    · intro hw
      funext f
      have key := hw (BMR.xEncEquiv.symm ⟨f.val, by have := f.isLt; simpa [Layout.padS] using this⟩)
      have flat : (BMR.xFlat (BMR.xEncEquiv.symm ⟨f.val, by have := f.isLt; simpa [Layout.padS] using this⟩)).val
          = f.val := by
        have := BMR.xEncEquiv.apply_symm_apply ⟨f.val, by have := f.isLt; simpa [Layout.padS] using this⟩
        exact congrArg Fin.val this
      rw [← key]
      exact congrArg w (Fin.ext flat.symm)
    · rintro rfl x
      show Q ⟨i, h⟩ (ρ : ZMod _) (.inl (BMR.xEncEquiv.symm ⟨(BMR.xFlat x).val, _⟩)) = _
      congr 3
      exact BMR.xEncEquiv.symm_apply_apply x
  · simp only [one_ne_zero, if_false, if_true]
    have := padSiteLaw_read (κ := 1) (by norm_num) ⟨i, h⟩
      {v | ∀ y : BMR.YEnc, v ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩ = Q ⟨i, h⟩ (ρ : ZMod _) (.inr y)}
    rw [show {a : List (Block × Block) | ∀ y : BMR.YEnc, readList 1 ⟨i, h⟩ a ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩ =
        Q ⟨i, h⟩ (ρ : ZMod _) (.inr y)} = {a | readList 1 ⟨i, h⟩ a ∈
        {v | ∀ y : BMR.YEnc, v ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩ = Q ⟨i, h⟩ (ρ : ZMod _) (.inr y)}} from rfl,
      this]
    refine uniform_single _ (fun f => Q ⟨i, h⟩ (ρ : ZMod _) (.inr (BMR.yEncEquiv.symm ⟨f.val, by
      have := f.isLt; simpa [Layout.padS] using this⟩))) fun w => ?_
    constructor
    · intro hw
      funext f
      have key := hw (BMR.yEncEquiv.symm ⟨f.val, by have := f.isLt; simpa [Layout.padS] using this⟩)
      have flat : (BMR.yFlat (BMR.yEncEquiv.symm ⟨f.val, by have := f.isLt; simpa [Layout.padS] using this⟩)).val
          = f.val := by
        have := BMR.yEncEquiv.apply_symm_apply ⟨f.val, by have := f.isLt; simpa [Layout.padS] using this⟩
        exact congrArg Fin.val this
      rw [← key]
      exact congrArg w (Fin.ext flat.symm)
    · rintro rfl y
      show Q ⟨i, h⟩ (ρ : ZMod _) (.inr (BMR.yEncEquiv.symm ⟨(BMR.yFlat y).val, _⟩)) = _
      congr 3
      exact BMR.yEncEquiv.symm_apply_apply y

theorem padSites_nodup : Layout.padSites.Nodup :=
  (List.nodup_append.mp Laws.crtLayout_refill.sitesNodup).1

/-- **The pads of the drawn pad sites are uniform.** -/
theorem padDraws_uniform :
    (siteDraws crtLayout Layout.padSites).map padsOfDraws = PMF.uniformOfFintype (BMR.Pads Entry.table) := by
  refine eq_uniform_of_const _ fun P P' => ?_
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply, preimage_padsOfDraws, preimage_padsOfDraws,
    siteDraws_pi crtLayout _ padSites_nodup, siteDraws_pi crtLayout _ padSites_nodup]
  have same : (Layout.padSites.map fun s => (crtLayout.law s).toOuterMeasure (matchSite P s)) =
      Layout.padSites.map fun s => (crtLayout.law s).toOuterMeasure (matchSite P' s) :=
    List.map_congr_left fun s member => (matchSite_mass P member).trans (matchSite_mass P' member).symm
  rw [same]

theorem padsOfDraws_congr {A A' : SiteId → List (Block × Block)} (same : ∀ s ∈ Layout.padSites, A s = A' s) :
    padsOfDraws A = padsOfDraws A' := by
  funext i ρ e
  cases e with
  | inl x =>
      show readList 0 i (A (.pad 0 i ρ.val)) _ = readList 0 i (A' (.pad 0 i ρ.val)) _
      rw [same _ (pad_mem_padSites (κ := 0) (by norm_num) i (ZMod.val_lt ρ))]
  | inr y =>
      show readList 1 i (A (.pad 1 i ρ.val)) _ = readList 1 i (A' (.pad 1 i ρ.val)) _
      rw [same _ (pad_mem_padSites (κ := 1) (by norm_num) i (ZMod.val_lt ρ))]

theorem mask_not_pad {s : SiteId} (member : s ∈ Layout.maskSites) : s ∉ Layout.padSites := by
  intro pad
  obtain ⟨κ, i, ρ, rfl, -⟩ := Layout.mem_padSites pad
  rcases Layout.mem_maskSites member with ⟨k, eq, -⟩ | ⟨k, eq, -⟩ <;> cases eq

theorem map_congr_support {α β : Type} (p : PMF α) (f g : α → β) (h : ∀ x, p x ≠ 0 → f x = g x) :
    p.map f = p.map g :=
  PMF.bind_congr p _ _ fun x hx => by rw [Function.comp_apply, Function.comp_apply, h x hx]

theorem merged_lengths (A1 A2 : SiteId → List (Block × Block))
    (h1 : (siteDraws crtLayout Layout.padSites) A1 ≠ 0) (h2 : (siteDraws crtLayout Layout.maskSites) A2 ≠ 0) :
    ∀ s ∈ crtLayout.sites, ((fun s => if s ∈ Layout.padSites then A1 s else A2 s) s).length = crtLayout.answers s := by
  intro s member
  by_cases pad : s ∈ Layout.padSites
  · show (if s ∈ Layout.padSites then A1 s else A2 s).length = _
    rw [if_pos pad]
    exact Laws.crtLayout_refill.lengths s member _
      (siteDraws_support crtLayout _ A1 ((PMF.mem_support_iff _ _).mpr h1) s pad)
  · show (if s ∈ Layout.padSites then A1 s else A2 s).length = _
    rw [if_neg pad]
    have mask : s ∈ Layout.maskSites := by
      rcases List.mem_append.mp member with h | h
      · exact absurd h pad
      · exact h
    exact Laws.crtLayout_refill.lengths s member _
      (siteDraws_support crtLayout _ A2 ((PMF.mem_support_iff _ _).mpr h2) s mask)

end PadLaw

open PadLaw in
/-- **The pads of the swapped table are uniform, jointly with anything that ignores the pad positions**
(the (6')). -/
theorem swapped_pads_split {α : Type} (rest : TagTable → α)
    (away : ∀ T T' : TagTable, (∀ p, p ∉ padPositions → T p = T' p) → rest T = rest T') :
    (swappedTableLaw crtLayout).map (fun T => (padsOf T, rest T)) =
      (PMF.uniformOfFintype (BMR.Pads Entry.table)).bind fun P =>
        ((swappedTableLaw crtLayout).map rest).map fun r => (P, r) := by
  have nodup := Laws.crtLayout_refill.sitesNodup
  let R : TagTable → (SiteId → List (Block × Block)) → α := fun T0 A2 =>
    rest (overwriteSites crtLayout Layout.maskSites A2 T0)
  have restEq : ∀ A T0, rest (overwriteSites crtLayout crtLayout.sites A T0) = R T0 A := by
    intro A T0
    exact away _ _ fun p off => overwriteSites_offPads A T0 p off
  have merged : ∀ (A1 A2 : SiteId → List (Block × Block)) (T0 : TagTable),
      R T0 (fun s => if s ∈ Layout.padSites then A1 s else A2 s) = R T0 A2 := by
    intro A1 A2 T0
    show rest _ = rest _
    rw [Product.overwriteSites_congr crtLayout _ _ A2 (fun s member => by rw [if_neg (mask_not_pad member)]) T0]
  have draws : siteDraws crtLayout crtLayout.sites = (siteDraws crtLayout Layout.padSites).bind fun A1 =>
      (siteDraws crtLayout Layout.maskSites).map fun A2 => fun s => if s ∈ Layout.padSites then A1 s else A2 s :=
    siteDraws_append crtLayout Layout.padSites Layout.maskSites
  have restLaw : (swappedTableLaw crtLayout).map rest =
      (PMF.uniformOfFintype TagTable).bind fun T0 => (siteDraws crtLayout Layout.maskSites).map (R T0) := by
    rw [swappedTableLaw_product crtLayout nodup, PMF.map_bind]
    refine congrArg _ (funext fun T0 => ?_)
    rw [PMF.map_comp, draws, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, restEq, merged]
    exact PMF.bind_const _ _
  have perBase : ∀ T0, ((siteDraws crtLayout crtLayout.sites).map fun A =>
        overwriteSites crtLayout crtLayout.sites A T0).map (fun T => (padsOf T, rest T)) =
      (PMF.uniformOfFintype (BMR.Pads Entry.table)).bind fun P =>
        (siteDraws crtLayout Layout.maskSites).map fun A2 => (P, R T0 A2) := by
    intro T0
    rw [PMF.map_comp, ← padDraws_uniform, PMF.bind_map, draws, PMF.map_bind]
    refine PMF.bind_congr _ _ _ fun A1 h1 => ?_
    rw [PMF.map_comp, Function.comp_apply]
    refine map_congr_support _ _ _ fun A2 h2 => ?_
    simp only [Function.comp_apply]
    rw [padsOf_overwriteSites _ (merged_lengths A1 A2 h1 h2) T0, restEq, merged,
      padsOfDraws_congr (A' := A1) fun s member => by rw [if_pos member]]
  rw [restLaw, swappedTableLaw_product crtLayout nodup, PMF.map_bind]
  simp only [perBase]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun P => ?_)
  rw [PMF.map_bind]
  refine congrArg _ (funext fun T0 => ?_)
  rw [PMF.map_comp]
  rfl


end

end Kriterion.CRT.Privacy
