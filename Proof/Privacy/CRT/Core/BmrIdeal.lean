/-
**The P45 ideal reading on the curve**.

`BmrSplit.IdealReading BmrSplit.crtKernel`: at an input `u` on the curve, route M's P45 part (`H8.idealCore` under
`H8.bmrPart`) is the scheme's uniform coins, then uniform P45 cells, then `none` on `revealP45`, else the published
part of `BMR.idealOut` with the kernel's answers (`bmrLaw crtKernel`).

The argument, per source and coins:

* the swapped table is uniform targets followed by the kernel `crtKernel.given` (`crtKernel.law`); on the kernel's
  support the table's pads and masks are the targets (`crtKernel.reads`);
* the replay's delivered values are P45's ideal delivered values (`H8.crtReplayDelivered`) and its masks are the
  table's non-collector masks (`replayMasks_eq`), so route M's collector masks are P45's ideal collector masks
  (`collectorMasks_eq`); the reveal is `revealP45` (`reveal_iff`: programming changes no conversion tag);
* **the heart** (`programmed_given`): programming the collector sites of the kernel's table with preimages of the
  collector masks `π` (and a uniform fourth block) gives the kernel at the targets whose collector masks are `π`, at
  the visible P45 tags. Both sides are products over the sites (`TargetLaw.inner_mass`); they differ only at the
  collector sites, where the site law given its reading is the `sampleFp` fibre law, which is the preimage law with
  a uniform fourth block (`fibre_twoAnswers`, `OnE.idealPreimage_eq`);
* the targets' cold pads and non-collector masks are uniform (`uniform_visOf`), and the source's P45 cells are
  uniform (`BmrOff.uniform_srcOf`).
-/

import Proof.Privacy.CRT.Core.BmrKernel
import Proof.Privacy.CRT.Core.BmrSplitOff
import Proof.Privacy.CRT.Flags.WrapBridge
import Proof.Privacy.CRT.Glue.ContainParts

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.BmrIdealP4

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance
open Kriterion.ArgoMAC.Phase3.Glue (idealPreimage)
open Kriterion.ArgoMAC.Security.Phase3 (fibreLaw fibreLaw_apply)
open scoped ENNReal

noncomputable section

/-- The entry's table. -/
abbrev Tb : CrtTable := Kriterion.CRT.Entry.table

/-! ### 1. Generic facts -/

/-- **Two laws on `Option` that agree at every `some` agree.** -/
theorem option_ext {β : Type} (p q : PMF (Option β)) (h : ∀ b, p (some b) = q (some b)) : p = q := by
  have rest : (∑' o, @ite _ (o = none) (Classical.propDecidable _) (0 : ℝ≥0∞) (p o)) =
      ∑' o, @ite _ (o = none) (Classical.propDecidable _) (0 : ℝ≥0∞) (q o) := by
    refine tsum_congr fun o => ?_
    rcases o with _ | b
    · rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (Option.some_ne_none b), if_neg (Option.some_ne_none b)]
      exact h b
  have sp := p.tsum_coe
  have sq := q.tsum_coe
  rw [ENNReal.tsum_eq_add_tsum_ite none] at sp sq
  have finite : (∑' o, @ite _ (o = none) (Classical.propDecidable _) (0 : ℝ≥0∞) (q o)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← sq]
    exact le_add_left (le_refl _)
  refine PMF.ext fun o => ?_
  rcases o with _ | b
  · rw [rest] at sp
    exact (ENNReal.add_left_inj finite).mp (sp.trans sq.symm)
  · exact h b

/-- **Independent draws with no abort: the mass of drawing, for every key, a value in its event.** -/
theorem drawAll_mass {α β : Type} (P : α → PMF β) (E : α → Set β) :
    ∀ l : List α, (drawAll (fun a => (P a).map some) l).toOuterMeasure
        {o | ∃ drawn, o = some drawn ∧ ∀ e ∈ drawn, e.2 ∈ E e.1} = (l.map fun a => (P a).toOuterMeasure (E a)).prod
  | [] => by
      rw [drawAll, PMF.toOuterMeasure_pure_apply, if_pos ⟨[], rfl, fun e inside => absurd inside List.not_mem_nil⟩]
      rfl
  | a :: rest => by
      have ih := drawAll_mass P E rest
      rw [drawAll, PMF.bind_map, PMF.toOuterMeasure_bind_apply, List.map_cons, List.prod_cons, ← ih,
        PMF.toOuterMeasure_apply (P a), ← ENNReal.tsum_mul_right]
      refine tsum_congr fun b => ?_
      simp only [Function.comp_apply]
      rw [PMF.toOuterMeasure_map_apply]
      by_cases inside : b ∈ E a
      · rw [Set.indicator_of_mem inside]
        congr 2
        ext o
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨drawn, same, all⟩
          rcases o with _ | tail
          · cases same
          · exact ⟨tail, rfl, fun e member => all e (by
              rw [Option.map_some, Option.some.injEq] at same
              rw [← same]
              exact List.mem_cons_of_mem _ member)⟩
        · rintro ⟨tail, rfl, all⟩
          refine ⟨(a, b) :: tail, rfl, fun e member => ?_⟩
          rcases List.mem_cons.mp member with first | later
          · rw [first]
            exact inside
          · exact all e later
      · rw [Set.indicator_of_notMem inside, zero_mul]
        have empty : (Option.map fun tail => (a, b) :: tail) ⁻¹'
            {o | ∃ drawn, o = some drawn ∧ ∀ e ∈ drawn, e.2 ∈ E e.1} = ∅ := by
          ext o
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
          intro drawn same all
          rcases o with _ | tail
          · cases same
          · rw [Option.map_some, Option.some.injEq] at same
            exact inside (all (a, b) (by rw [← same]; exact List.mem_cons_self))
        rw [empty, PMF.toOuterMeasure_apply]
        simp

/-! ### 2. A collector site: its law given its reading is the preimage law with a uniform fourth block -/

/-- `sampleFp` of a triple. -/
def sampleTriple (tr : Block × Block × Block) : BaseField := sampleFp tr.1 tr.2.1 tr.2.2

theorem natToBlocks_blocksToNat (blocks : Block × Block × Block) :
    Security.Phase3.natToBlocks (blocksToNat blocks.1 blocks.2.1 blocks.2.2) = blocks := by
  obtain ⟨a, b, c⟩ := blocks
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [Security.Phase3.natToBlocks, blocksToNat]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat] <;> omega

theorem blocksToNat_lt (blocks : Block × Block × Block) :
    blocksToNat blocks.1 blocks.2.1 blocks.2.2 < 2 ^ 384 := by
  obtain ⟨a, b, c⟩ := blocks
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [blocksToNat]
  omega

theorem preimage_bound (y : BaseField) (m : ℕ) (small : m < Phase3.Glue.preimageCount y + 1) :
    y.val + baseFieldModulus * m < 2 ^ 384 := by
  have ySmall : y.val < baseFieldModulus := ZMod.val_lt y
  have pSmall : baseFieldModulus < 2 ^ 254 := baseFieldModulus_lt
  have mLe : m ≤ (2 ^ 384 - 1 - y.val) / baseFieldModulus := by
    unfold Phase3.Glue.preimageCount at small
    omega
  have step : baseFieldModulus * m ≤ 2 ^ 384 - 1 - y.val :=
    le_trans (Nat.mul_le_mul_left _ mLe) (Nat.mul_div_le _ _)
  have big : (2 : ℕ) ^ 254 < 2 ^ 384 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  omega

theorem cast_preimage (y : BaseField) (m : ℕ) : ((y.val + baseFieldModulus * m : ℕ) : BaseField) = y := by
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]

/-- The preimages of a residue: `y.val + p·m`, `m ≤ preimageCount y` (`OnE.preimageEquiv`, restated here to keep the
import closure small). -/
def preimageEquiv (y : BaseField) :
    Fin (Phase3.Glue.preimageCount y + 1) ≃ {tr : Block × Block × Block // sampleTriple tr = y} where
  toFun m := ⟨Security.Phase3.natToBlocks (y.val + baseFieldModulus * m.val), by
    unfold sampleTriple
    rw [Security.Phase3.sampleFp_natToBlocks _ (preimage_bound y m.val m.isLt), cast_preimage]⟩
  invFun tr := ⟨blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 / baseFieldModulus, by
    have pPos : 0 < baseFieldModulus := Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
    have lt := blocksToNat_lt tr.1
    have residue : blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 % baseFieldModulus = y.val := by
      have hit : ((blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 : ℕ) : BaseField) = y := tr.2
      have values := congrArg ZMod.val hit
      rwa [ZMod.val_natCast] at values
    have split := Nat.mod_add_div (blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2) baseFieldModulus
    have bound : blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 / baseFieldModulus * baseFieldModulus ≤
        2 ^ 384 - 1 - y.val := by
      rw [Nat.mul_comm]
      omega
    have le := (Nat.le_div_iff_mul_le pPos).mpr bound
    unfold Phase3.Glue.preimageCount
    omega⟩
  left_inv m := by
    have pPos : 0 < baseFieldModulus := Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
    apply Fin.ext
    show blocksToNat (Security.Phase3.natToBlocks _).1 (Security.Phase3.natToBlocks _).2.1
      (Security.Phase3.natToBlocks _).2.2 / baseFieldModulus = m.val
    rw [Security.Phase3.blocksToNat_natToBlocks _ (preimage_bound y m.val m.isLt), Nat.add_mul_div_left _ _ pPos,
      Nat.div_eq_of_lt (ZMod.val_lt y), zero_add]
  right_inv tr := by
    apply Subtype.ext
    have residue : blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 % baseFieldModulus = y.val := by
      have hit : ((blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 : ℕ) : BaseField) = y := tr.2
      have values := congrArg ZMod.val hit
      rwa [ZMod.val_natCast] at values
    show Security.Phase3.natToBlocks
      (y.val + baseFieldModulus * (blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 / baseFieldModulus)) = tr.1
    rw [← residue, Nat.mod_add_div]
    exact natToBlocks_blocksToNat tr.1

instance sampleTripleNonempty (y : BaseField) :
    Nonempty {tr : Block × Block × Block // sampleTriple tr = y} :=
  ⟨preimageEquiv y 0⟩

/-- **The ideal preimage is the fibre law of `sampleFp`** (`OnE.idealPreimage_eq`, restated). -/
theorem idealPreimage_eq (y : BaseField) :
    idealPreimage y = (PMF.uniformOfFintype {tr : Block × Block × Block // sampleTriple tr = y}).map
      Subtype.val := by
  have factor : (fun m : Fin (Phase3.Glue.preimageCount y + 1) =>
      Phase3.Glue.limbs (y.val + baseFieldModulus * m.val)) = Subtype.val ∘ preimageEquiv y := rfl
  unfold idealPreimage
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]

/-- A uniform preimage of `y` and a uniform fourth block. -/
def sampleOf (y : BaseField) : PMF ((Block × Block × Block) × Block) :=
  (idealPreimage y).bind fun limbs => (PMF.uniformOfFintype Block).map fun fourth => (limbs, fourth)

/-- The two answers of a collector site with reading `y`, as a used triple with reading `y` and the fourth block. -/
def fibreEquiv (y : BaseField) :
    {f : Fin 2 → Block × Block // readSingle f = y} ≃
      {tr : Block × Block × Block // sampleTriple tr = y} × Block where
  toFun f := (⟨(Layout.twoAnswers f.1).1, f.2⟩, (Layout.twoAnswers f.1).2)
  invFun p := ⟨Layout.twoAnswers.symm (p.1.1, p.2), p.1.2⟩
  left_inv f := Subtype.ext (Layout.twoAnswers.symm_apply_apply f.1)
  right_inv _ := rfl

instance readSingleNonempty (y : BaseField) : Nonempty {f : Fin 2 → Block × Block // readSingle f = y} :=
  ⟨⟨Classical.choose (Layout.readSingle_surjective y), Classical.choose_spec (Layout.readSingle_surjective y)⟩⟩

/-- **The collector fibre law, read as a triple and a fourth block, is the preimage law.** -/
theorem fibre_twoAnswers (y : BaseField) :
    (fibreLaw readSingle Layout.readSingle_surjective y).map Layout.twoAnswers = sampleOf y := by
  unfold fibreLaw sampleOf
  rw [idealPreimage_eq, PMF.bind_map, PMF.map_comp]
  have prod := EntrySplit.uniform_prod_eq_bind (A := {tr : Block × Block × Block //
    sampleTriple tr = y}) (B := Block)
  have rhs : ((PMF.uniformOfFintype {tr : Block × Block × Block //
      sampleTriple tr = y}).bind
        ((fun limbs => (PMF.uniformOfFintype Block).map fun fourth => (limbs, fourth)) ∘ Subtype.val)) =
      (PMF.uniformOfFintype ({tr : Block × Block × Block //
        sampleTriple tr = y} × Block)).map fun p => (p.1.val, p.2) := by
    rw [prod, PMF.map_bind]
    refine congrArg _ (funext fun tr => ?_)
    rw [Function.comp_apply, PMF.map_comp]
    rfl
  rw [rhs]
  have factor : (Layout.twoAnswers ∘ Subtype.val : {f : Fin 2 → Block × Block // readSingle f = y} → _) =
      (fun p => (p.1.val, p.2)) ∘ fibreEquiv y := rfl
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]

/-- The answers of a list, as a function of two answers. -/
theorem getD_ofFn_two (f : Fin 2 → Block × Block) :
    (fun j : Fin 2 => (List.ofFn f).getD j.val (0, 0)) = f := by
  funext j
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.isLt, Option.getD_some]

/-- **A collector site: the mass of reading `y` with the answers in `E`.** -/
theorem singleSite_hit (y : BaseField) (E : Set ((Block × Block × Block) × Block)) :
    Layout.singleSiteLaw.toOuterMeasure
        {a | TargetLaw.readSingleL a = y ∧ Layout.twoAnswers (fun j => a.getD j.val (0, 0)) ∈ E} =
      (Fintype.card BaseField : ℝ≥0∞)⁻¹ * (sampleOf y).toOuterMeasure E := by
  unfold Layout.singleSiteLaw Layout.fibreSiteLaw
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_bind_apply]
  have pre : List.ofFn ⁻¹' {a : List (Block × Block) |
      TargetLaw.readSingleL a = y ∧ Layout.twoAnswers (fun j => a.getD j.val (0, 0)) ∈ E} =
      {f | readSingle f = y ∧ Layout.twoAnswers f ∈ E} := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, TargetLaw.readSingleL, getD_ofFn_two]
  rw [pre, tsum_eq_single y]
  · rw [PMF.uniformOfFintype_apply, ← fibre_twoAnswers, PMF.toOuterMeasure_map_apply]
    congr 1
    refine TargetLaw.toOuterMeasure_congr_support _ fun f inside => ?_
    have reads : readSingle f = y := by
      by_contra other
      rw [PMF.mem_support_iff, fibreLaw_apply, if_neg other] at inside
      exact inside rfl
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, reads, true_and]
  · intro x other
    rw [(PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_, mul_zero]
    refine Set.disjoint_left.mpr fun f inside hit => ?_
    rw [PMF.mem_support_iff, fibreLaw_apply] at inside
    split_ifs at inside with reads
    · exact other (reads.symm.trans hit.1)
    · exact inside rfl

/-! ### 3. The kernel's mass of an event on shown answers -/

open Classical in
/-- **Comparing two kernel masses of events on shown answers**: it suffices to compare the products over the sites,
base table by base table. -/
theorem given_mass_mul {ι ι' : Type} (pos : ι → Fin (2 ^ 40)) (w : ι → Block × Block) (pos' : ι' → Fin (2 ^ 40))
    (w' : ι' → Block × Block) (σ σ' : TargetLaw.Targets) (Q : ℝ≥0∞)
    (base : ∀ T0, TargetLaw.BaseMatch pos w T0 ↔ TargetLaw.BaseMatch pos' w' T0)
    (sites : (crtLayout.sites.map fun s =>
        (crtLayout.law s).toOuterMeasure (TargetLaw.visMatch pos w s ∩ TargetLaw.matchT σ s)).prod * Q =
      (crtLayout.sites.map fun s =>
        (crtLayout.law s).toOuterMeasure (TargetLaw.visMatch pos' w' s ∩ TargetLaw.matchT σ' s)).prod) :
    (BmrSplit.BmrKernel.given σ).toOuterMeasure {t | ∀ i, t (pos i) = w i} * Q =
      (BmrSplit.BmrKernel.given σ').toOuterMeasure {t | ∀ i, t (pos' i) = w' i} := by
  unfold BmrSplit.BmrKernel.given
  rw [TargetLaw.toOuterMeasure_condLaw, TargetLaw.toOuterMeasure_condLaw, mul_right_comm]
  congr 1
  have e : ∀ {κ : Type} (p : κ → Fin (2 ^ 40)) (v : κ → Block × Block) (ρ : TargetLaw.Targets),
      {t : TagTable | ∀ i, t (p i) = v i} ∩ bmrTargetsOf ⁻¹' {ρ} =
        {t | (∀ i, t (p i) = v i) ∧ bmrTargetsOf t = ρ} := fun _ _ _ => rfl
  rw [e, e, swappedTableLaw_product crtLayout TargetLaw.sites_nodup, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun T0 => ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply, TargetLaw.inner_mass, TargetLaw.inner_mass,
    mul_assoc]
  refine congrArg _ ?_
  by_cases hit : TargetLaw.BaseMatch pos w T0
  · rw [if_pos hit, if_pos ((base T0).mp hit)]
    exact sites
  · rw [if_neg hit, if_neg (fun hit' => hit ((base T0).mpr hit')), zero_mul]

/-! ### 4. The collector sites and positions -/

/-- The tags of collector site `k`. -/
theorem siteTags_mask0 (k : ℕ) :
    siteTags crtLayout (.mask 0 k) = [tagCode Family.mask 0 0 0 0 k 0, tagCode Family.mask 0 0 0 0 k 1] := rfl

/-- A collector position: answer `j < 2` of collector site `k < 273`. -/
def IsCollTag (p : Fin (2 ^ 40)) : Prop := ∃ k < 273, ∃ j < 2, p = H8.collectorTag k j

theorem mask0_mem_sites {k : ℕ} (hk : k < 273) : SiteId.mask 0 k ∈ crtLayout.sites :=
  List.mem_append_right _ (TargetLaw.mask0_mem hk)

theorem collectorTag_mem {k j : ℕ} (hj : j < 2) : H8.collectorTag k j ∈ Laws.sitePos crtLayout (.mask 0 k) := by
  show H8.collectorTag k j ∈ (siteTags crtLayout (.mask 0 k)).map tagPos
  rw [siteTags_mask0]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_mask0_pos {k : ℕ} {p : Fin (2 ^ 40)} (inside : p ∈ Laws.sitePos crtLayout (.mask 0 k)) :
    ∃ j < 2, p = H8.collectorTag k j := by
  change p ∈ (siteTags crtLayout (.mask 0 k)).map tagPos at inside
  rw [siteTags_mask0] at inside
  rcases List.mem_cons.mp inside with first | later
  · exact ⟨0, by norm_num, first⟩
  · rcases List.mem_cons.mp later with second | none
    · exact ⟨1, by norm_num, second⟩
    · exact absurd none List.not_mem_nil

/-- A collector position lies in its collector site only. -/
theorem not_collTag_of_site {s : SiteId} (member : s ∈ crtLayout.sites) (other : ∀ k < 273, s ≠ .mask 0 k)
    {p : Fin (2 ^ 40)} (inside : p ∈ Laws.sitePos crtLayout s) : ¬ IsCollTag p := by
  rintro ⟨k, hk, j, hj, rfl⟩
  exact Laws.crtLayout_refill.disjoint s member (.mask 0 k) (mask0_mem_sites hk) (other k hk) _ inside
    (collectorTag_mem hj)

theorem collTag_of_site {k : ℕ} (hk : k < 273) {p : Fin (2 ^ 40)}
    (inside : p ∈ Laws.sitePos crtLayout (.mask 0 k)) : IsCollTag p := by
  obtain ⟨j, hj, rfl⟩ := mem_mask0_pos inside
  exact ⟨k, hk, j, hj, rfl⟩

/-- The collector of number `k`. -/
def cOf (k : ℕ) : BMR.Collector :=
  ⟨TargetLaw.collRow k, by
    unfold TargetLaw.collRow collectorSlot
    dsimp only
    split_ifs <;> simp [TargetLaw.xElemOfSlot, BMR.IsCollector]⟩

theorem cOf_collectorIndex (c : BMR.Collector) : cOf (collectorIndex c) = c := by
  obtain ⟨⟨d, e⟩, he⟩ := c
  apply Subtype.ext
  have hd := d.isLt
  have three : ∀ j < 3, TargetLaw.collRow (3 * d.val + j) =
      (d, .inl (TargetLaw.xElemOfSlot (collectorSlot j))) := by
    intro j hj
    unfold TargetLaw.collRow
    rw [show (3 * d.val + j) / 3 = d.val by omega, show (3 * d.val + j) % 3 = j by omega, TargetLaw.digitOf_val]
  rcases e with x | y
  · cases x <;> first
      | exact three 0 (by norm_num)
      | exact three 1 (by norm_num)
      | exact three 2 (by norm_num)
      | (exfalso; simp [BMR.IsCollector] at he)
  · exfalso
    simp [BMR.IsCollector] at he

/-- A non-collector row. -/
theorem ncRow_not (n : ℕ) : ¬ BMR.IsCollector (TargetLaw.ncRow n).2 := by
  unfold TargetLaw.ncRow
  split_ifs
  · rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h, TargetLaw.xElemOfSlot, BMR.IsCollector]
  · simp [BMR.IsCollector]

/-- The targets with the collector masks replaced. -/
def merge (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) : TargetLaw.Targets :=
  (τ.1, fun r => if h : BMR.IsCollector r.2 then π ⟨r, h⟩ else τ.2 r)

theorem maskInv_merge_pair (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) :
    (TargetLaw.maskInv (merge τ π).2).pair = (TargetLaw.maskInv τ.2).pair := by
  funext k
  show ((merge τ π).2 (TargetLaw.ncRow (2 * k.val)), (merge τ π).2 (TargetLaw.ncRow (2 * k.val + 1))) =
    (τ.2 (TargetLaw.ncRow (2 * k.val)), τ.2 (TargetLaw.ncRow (2 * k.val + 1)))
  unfold merge
  dsimp only
  rw [dif_neg (ncRow_not _), dif_neg (ncRow_not _)]

theorem maskInv_merge_single (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) :
    (TargetLaw.maskInv (merge τ π).2).single = (TargetLaw.maskInv τ.2).single := by
  show (merge τ π).2 (TargetLaw.ncRow 454) = τ.2 (TargetLaw.ncRow 454)
  unfold merge
  dsimp only
  rw [dif_neg (ncRow_not _)]

theorem maskInv_merge_collector (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) {k : ℕ} (hk : k < 273) :
    atNat (TargetLaw.maskInv (merge τ π).2).collector 0 k = π (cOf k) := by
  rw [TargetLaw.atNat_collector _ hk]
  show (merge τ π).2 (TargetLaw.collRow k) = _
  unfold merge
  dsimp only
  rw [dif_pos (show BMR.IsCollector (TargetLaw.collRow k).2 from (cOf k).2)]
  rfl

/-- Off the collector sites the merged targets match as the targets. -/
theorem matchT_merge (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) {s : SiteId}
    (member : s ∈ crtLayout.sites) (other : ∀ k < 273, s ≠ .mask 0 k) :
    TargetLaw.matchT (merge τ π) s = TargetLaw.matchT τ s := by
  rcases List.mem_append.mp member with pad | mask
  · obtain ⟨κ, i, ρ, rfl, -⟩ := Layout.mem_padSites pad
    rfl
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, -⟩
    · exact absurd rfl (other k hk)
    · show PadLaw.matchSite τ.1 _ ∩ TargetLaw.maskMatch _ _ = PadLaw.matchSite τ.1 _ ∩ TargetLaw.maskMatch _ _
      unfold TargetLaw.maskMatch
      rw [maskInv_merge_pair, maskInv_merge_single]
      rfl

/-! ### 5. The heart: programming the collector sites of the kernel's table -/

section Heart

variable (u : AffineInput)

/-- The visible P45 tags at `u`. -/
abbrev V := H8.BmrTags Tb u

/-- The visible P45 tags off the collector positions. -/
abbrev VO := {i : V u // ¬ IsCollTag i.1.1}

/-- The visible tag of answer `j` of collector site `k`, on the curve. -/
def vTag (valid : validate u = true) (k j : ℕ) (hk : k < 273) (hj : j < 2) : V u :=
  ⟨⟨H8.collectorTag k j, by
      have fam := (Contain.collectorTag_fields (k := k) (j := j) (by omega) (by omega)).1
      unfold H8.visTag
      simp only [fam]
      exact valid⟩,
    Or.inr (Or.inl (Contain.collectorTag_fields (k := k) (j := j) (by omega) (by omega)).1)⟩

theorem vTag_eq (valid : validate u = true) {k j : ℕ} (hk : k < 273) (hj : j < 2) (i : V u)
    (same : i.1.1 = H8.collectorTag k j) : i = vTag u valid k j hk hj :=
  Subtype.ext (Subtype.ext same)

/-- The event on a drawn collector that it writes the view `z` at its site. -/
def hitAt (valid : validate u = true) (z : V u → Block × Block) (k : ℕ) : Set ((Block × Block × Block) × Block) :=
  if hk : k < 273 then
    {x | (x.1.1, x.1.2.1) = z (vTag u valid k 0 hk (by norm_num)) ∧
      (x.1.2.2, x.2) = z (vTag u valid k 1 hk (by norm_num))}
  else Set.univ

/-- **The programmed table shows `z` exactly when the table does off the collector positions and every drawn
collector writes `z` at its site.** -/
theorem programmed_iff (valid : validate u = true) (z : V u → Block × Block) (t : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (keys : drawn.map Prod.fst = collectorList) :
    BmrSplit.restrictBmr u (H8.programmedTable t drawn) = z ↔
      (∀ i : VO u, t i.1.1.1 = z i.1) ∧ ∀ e ∈ drawn, e.2 ∈ hitAt u valid z (collectorIndex e.1) := by
  have indices : drawn.map (fun e => collectorIndex e.1) = List.range 273 := by
    rw [← Contain.collectorList_indices, ← keys, List.map_map]
    rfl
  have nodup : (drawn.map fun e => collectorIndex e.1).Nodup := by
    rw [indices]
    exact List.nodup_range
  have off : ∀ p : Fin (2 ^ 40), ¬ IsCollTag p → H8.programmedTable t drawn p = t p := fun p away =>
    Contain.programmedTable_off p drawn t fun e _ j hj same =>
      away ⟨collectorIndex e.1, Contain.collectorIndex_lt _, j, hj, same⟩
  constructor
  · intro shows
    refine ⟨fun i => ?_, fun e member => ?_⟩
    · rw [← off _ i.2]
      exact congrFun shows i.1
    · have hit := Contain.programmedTable_hit drawn t nodup e member
      have hk := Contain.collectorIndex_lt e.1
      unfold hitAt
      rw [dif_pos hk]
      refine ⟨?_, ?_⟩
      · rw [← hit.1]
        exact congrFun shows (vTag u valid _ 0 hk (by norm_num))
      · rw [← hit.2]
        exact congrFun shows (vTag u valid _ 1 hk (by norm_num))
  · rintro ⟨outside, written⟩
    funext i
    by_cases coll : IsCollTag i.1.1
    · obtain ⟨k, hk, j, hj, same⟩ := coll
      have inRange : k ∈ drawn.map (fun e => collectorIndex e.1) := by
        rw [indices]
        exact List.mem_range.mpr hk
      obtain ⟨e, member, idx⟩ := List.mem_map.mp inRange
      subst idx
      have hit := Contain.programmedTable_hit drawn t nodup e member
      have w := written e member
      unfold hitAt at w
      rw [dif_pos hk] at w
      show H8.programmedTable t drawn i.1.1 = z i
      rw [same, vTag_eq u valid hk hj i same]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [hit.1]
        exact w.1
      · rw [hit.2]
        exact w.2
    · show H8.programmedTable t drawn i.1.1 = z i
      rw [off _ coll]
      exact outside ⟨i, coll⟩

end Heart

/-! ### 6. The site factors -/

section Factors

variable (u : AffineInput) (valid : validate u = true)

/-- The tag of answer `j` of collector site `k`. -/
theorem tagPos_mask0 (k j : ℕ) (hj : j < (siteTags crtLayout (.mask 0 k)).length) :
    tagPos ((siteTags crtLayout (.mask 0 k))[j]) = H8.collectorTag k j := by
  have tag : (siteTags crtLayout (.mask 0 k))[j] = tagCode Family.mask 0 0 0 0 k j := by
    simp only [siteTags, List.getElem_map, List.getElem_range]
  rw [tag]
  rfl

theorem length_mask0 (k : ℕ) : (siteTags crtLayout (.mask 0 k)).length = 2 := by
  rw [siteTags_mask0]
  rfl

/-- Off the collector sites the view off the collector positions is the view. -/
theorem visMatch_other (z : V u → Block × Block) {s : SiteId} (member : s ∈ crtLayout.sites)
    (other : ∀ k < 273, s ≠ .mask 0 k) :
    TargetLaw.visMatch (fun i : VO u => i.1.1.1) (fun i => z i.1) s =
      TargetLaw.visMatch (fun i : V u => i.1.1) z s := by
  ext a
  simp only [TargetLaw.visMatch, Set.mem_ofPred_eq]
  constructor
  · intro h i j hj at_pos
    have inside : i.1.1 ∈ Laws.sitePos crtLayout s := List.mem_map.mpr ⟨_, List.getElem_mem hj, at_pos⟩
    exact h ⟨i, not_collTag_of_site member other inside⟩ j hj at_pos
  · intro h i j hj at_pos
    exact h i.1 j hj at_pos

/-- At a collector site the view off the collector positions shows nothing. -/
theorem visMatch_collO (z : V u → Block × Block) {k : ℕ} (hk : k < 273) :
    TargetLaw.visMatch (fun i : VO u => i.1.1.1) (fun i => z i.1) (.mask 0 k) = Set.univ := by
  ext a
  simp only [TargetLaw.visMatch, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro i j hj at_pos
  exact absurd (collTag_of_site hk (List.mem_map.mpr ⟨_, List.getElem_mem hj, at_pos⟩)) i.2

theorem visMatch_collV (z : V u → Block × Block) {k : ℕ} (hk : k < 273) (a : List (Block × Block)) :
    a ∈ TargetLaw.visMatch (fun i : V u => i.1.1) z (.mask 0 k) ↔
      a.getD 0 (0, 0) = z (vTag u valid k 0 hk (by norm_num)) ∧
        a.getD 1 (0, 0) = z (vTag u valid k 1 hk (by norm_num)) := by
  simp only [TargetLaw.visMatch, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨h _ 0 (by rw [length_mask0]; norm_num) (tagPos_mask0 k 0 _),
      h _ 1 (by rw [length_mask0]; norm_num) (tagPos_mask0 k 1 _)⟩
  · rintro ⟨h0, h1⟩ i j hj at_pos
    have hj2 : j < 2 := by rw [length_mask0] at hj; exact hj
    rw [tagPos_mask0] at at_pos
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [vTag_eq u valid hk (by norm_num) i at_pos.symm]
      exact h0
    · rw [vTag_eq u valid hk (by norm_num) i at_pos.symm]
      exact h1

theorem matchT_mask0 (σ : TargetLaw.Targets) (k : ℕ) :
    TargetLaw.matchT σ (.mask 0 k) =
      {a | TargetLaw.readSingleL a = atNat (TargetLaw.maskInv σ.2).collector 0 k} :=
  Set.univ_inter _

/-- The factor of the collector site `k` on the side of the programmed tables. -/
theorem factorO_coll (z : V u → Block × Block) (τ : TargetLaw.Targets) {k : ℕ} (hk : k < 273) :
    (crtLayout.law (.mask 0 k)).toOuterMeasure
        (TargetLaw.visMatch (fun i : VO u => i.1.1.1) (fun i => z i.1) (.mask 0 k) ∩ TargetLaw.matchT τ (.mask 0 k)) =
      (Fintype.card BaseField : ℝ≥0∞)⁻¹ := by
  rw [visMatch_collO u z hk, Set.univ_inter, matchT_mask0]
  exact TargetLaw.singleSite_mass _

/-- The factor of collector `k`: its preimage and fourth block write the view. -/
def qk (π : BMR.Collector → BaseField) (z : V u → Block × Block) (k : ℕ) : ℝ≥0∞ :=
  (sampleOf (π (cOf k))).toOuterMeasure (hitAt u valid z k)

/-- The factor of the collector site `k` on the side of the merged kernel. -/
theorem factorV_coll (z : V u → Block × Block) (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) {k : ℕ}
    (hk : k < 273) :
    (crtLayout.law (.mask 0 k)).toOuterMeasure
        (TargetLaw.visMatch (fun i : V u => i.1.1) z (.mask 0 k) ∩ TargetLaw.matchT (merge τ π) (.mask 0 k)) =
      (Fintype.card BaseField : ℝ≥0∞)⁻¹ * qk u valid π z k := by
  have sets : TargetLaw.visMatch (fun i : V u => i.1.1) z (.mask 0 k) ∩ TargetLaw.matchT (merge τ π) (.mask 0 k) =
      {a | TargetLaw.readSingleL a = π (cOf k) ∧
        Layout.twoAnswers (fun j => a.getD j.val (0, 0)) ∈ hitAt u valid z k} := by
    ext a
    rw [Set.mem_inter_iff, visMatch_collV u valid z hk, matchT_mask0, Set.mem_ofPred_eq,
      maskInv_merge_collector τ π hk, Set.mem_ofPred_eq]
    unfold hitAt
    rw [dif_pos hk]
    constructor
    · rintro ⟨⟨h0, h1⟩, reads⟩
      exact ⟨reads, h0, h1⟩
    · rintro ⟨reads, h0, h1⟩
      exact ⟨⟨h0, h1⟩, reads⟩
  rw [sets]
  exact singleSite_hit _ _

/-- The factor of a site on the side of the merged kernel over the other side's. -/
def hfac (π : BMR.Collector → BaseField) (z : V u → Block × Block) : SiteId → ℝ≥0∞
  | .mask 0 k => qk u valid π z k
  | _ => 1

/-- **The products over the sites.** -/
theorem sites_prod (z : V u → Block × Block) (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) :
    (crtLayout.sites.map fun s => (crtLayout.law s).toOuterMeasure
        (TargetLaw.visMatch (fun i : VO u => i.1.1.1) (fun i => z i.1) s ∩ TargetLaw.matchT τ s)).prod *
      ((List.range 273).map (qk u valid π z)).prod =
    (crtLayout.sites.map fun s => (crtLayout.law s).toOuterMeasure
        (TargetLaw.visMatch (fun i : V u => i.1.1) z s ∩ TargetLaw.matchT (merge τ π) s)).prod := by
  have each : ∀ s ∈ crtLayout.sites,
      (crtLayout.law s).toOuterMeasure
          (TargetLaw.visMatch (fun i : V u => i.1.1) z s ∩ TargetLaw.matchT (merge τ π) s) =
        (crtLayout.law s).toOuterMeasure
          (TargetLaw.visMatch (fun i : VO u => i.1.1.1) (fun i => z i.1) s ∩ TargetLaw.matchT τ s) *
          hfac u valid π z s := by
    intro s member
    by_cases coll : ∃ k < 273, s = .mask 0 k
    · obtain ⟨k, hk, rfl⟩ := coll
      rw [factorV_coll u valid z τ π hk, factorO_coll u z τ hk]
      rfl
    · have other : ∀ k < 273, s ≠ .mask 0 k := fun k hk same => coll ⟨k, hk, same⟩
      have one : hfac u valid π z s = 1 := by
        rcases List.mem_append.mp member with pad | mask
        · obtain ⟨κ, i, ρ, rfl, -⟩ := Layout.mem_padSites pad
          rfl
        · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, -⟩
          · exact absurd rfl (other k hk)
          · rfl
      rw [one, mul_one, visMatch_other u z member other, matchT_merge τ π member other]
  have hprod : (crtLayout.sites.map (hfac u valid π z)).prod = ((List.range 273).map (qk u valid π z)).prod := by
    show ((Layout.padSites ++ ((List.range 273).map (SiteId.mask 0) ++ (List.range 228).map (SiteId.mask 1))).map
      (hfac u valid π z)).prod = _
    rw [List.map_append, List.map_append, List.prod_append, List.prod_append, List.map_map, List.map_map]
    have pads : (Layout.padSites.map (hfac u valid π z)).prod = 1 := by
      refine List.prod_eq_one fun x inside => ?_
      obtain ⟨s, member, rfl⟩ := List.mem_map.mp inside
      obtain ⟨κ, i, ρ, rfl, -⟩ := Layout.mem_padSites member
      rfl
    have ones : ((List.range 228).map (hfac u valid π z ∘ SiteId.mask 1)).prod = 1 := by
      refine List.prod_eq_one fun x inside => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp inside
      rfl
    have colls : (List.range 273).map (hfac u valid π z ∘ SiteId.mask 0) = (List.range 273).map (qk u valid π z) :=
      List.map_congr_left fun k _ => rfl
    rw [pads, ones, one_mul, mul_one, colls]
  rw [List.map_congr_left each, List.prod_map_mul, hprod]

end Factors

/-! ### 7. The heart -/

section Programmed

variable (u : AffineInput) (valid : validate u = true)

/-- The collector draws of route M, as independent preimages with a uniform fourth block. -/
theorem collectorDraws_eq [FieldCertificate] [GroupCertificate] (π : BMR.Collector → BaseField) :
    H8.collectorDrawsOf crtEntry π = drawAll (fun c => (sampleOf (π c)).map some) collectorList := by
  unfold H8.collectorDrawsOf
  congr 1
  funext c
  show ((Phase3.Glue.idealPreimage (π c)).map some).bind (fun limbs => match limbs with
    | none => PMF.pure none
    | some limbs => ((PMF.uniformOfFintype Block).map some).map (Option.map fun fourth => (limbs, fourth))) = _
  rw [PMF.bind_map]
  unfold sampleOf
  rw [PMF.map_bind]
  refine congrArg _ (funext fun limbs => ?_)
  simp only [Function.comp_apply, PMF.map_comp]
  rfl

/-- The draws' product, by collector number. -/
theorem draws_prod (π : BMR.Collector → BaseField) (z : V u → Block × Block) :
    (collectorList.map fun c => (sampleOf (π c)).toOuterMeasure (hitAt u valid z (collectorIndex c))).prod =
      ((List.range 273).map (qk u valid π z)).prod := by
  rw [← Contain.collectorList_indices, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun c _ => ?_)
  show _ = (sampleOf (π (cOf (collectorIndex c)))).toOuterMeasure (hitAt u valid z (collectorIndex c))
  rw [cOf_collectorIndex]

include valid in
/-- **The heart: programming the collector sites of the kernel's table with preimages of `π`** gives the kernel at
the targets whose collector masks are `π`, at the visible P45 tags. -/
theorem programmed_given (τ : TargetLaw.Targets) (π : BMR.Collector → BaseField) :
    (BmrSplit.BmrKernel.given τ).bind (fun t => (drawAll (fun c => (sampleOf (π c)).map some) collectorList).map
        (Option.map fun drawn => BmrSplit.restrictBmr u (H8.programmedTable t drawn))) =
      (BmrSplit.BmrKernel.given (merge τ π)).map (fun t => some (BmrSplit.restrictBmr u t)) := by
  classical
  apply option_ext
  intro z
  have perTable : ∀ t : TagTable,
      ((drawAll (fun c => (sampleOf (π c)).map some) collectorList).map
        (Option.map fun drawn => BmrSplit.restrictBmr u (H8.programmedTable t drawn))) (some z) =
      (if ∀ i : VO u, t i.1.1.1 = z i.1 then ((List.range 273).map (qk u valid π z)).prod else 0) := by
    intro t
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    have supp : ∀ o ∈ (drawAll (fun c => (sampleOf (π c)).map some) collectorList).support,
        o ∈ (Option.map fun drawn => BmrSplit.restrictBmr u (H8.programmedTable t drawn)) ⁻¹' {some z} ↔
          o ∈ {o | (∀ i : VO u, t i.1.1.1 = z i.1) ∧
            ∃ drawn, o = some drawn ∧ ∀ e ∈ drawn, e.2 ∈ hitAt u valid z (collectorIndex e.1)} := by
      intro o member
      rcases o with _ | drawn
      · simp
      · have keys := Laws.drawAll_keys _ collectorList drawn member
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.map_some, Option.some.injEq,
          Set.mem_ofPred_eq, exists_eq_left']
        exact programmed_iff u valid z t drawn keys
    rw [TargetLaw.toOuterMeasure_congr_support _ supp]
    by_cases cond : ∀ i : VO u, t i.1.1.1 = z i.1
    · rw [if_pos cond]
      simp only [cond, implies_true, true_and]
      rw [drawAll_mass (fun c => sampleOf (π c)) (fun c => hitAt u valid z (collectorIndex c)), draws_prod]
    · rw [if_neg cond]
      simp only [cond, false_and, Set.ofPred_false]
      exact (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr (Set.disjoint_empty _)
  rw [PMF.bind_apply, tsum_congr fun t => congrArg _ (perTable t)]
  have lhs : (∑' t, BmrSplit.BmrKernel.given τ t *
      (if ∀ i : VO u, t i.1.1.1 = z i.1 then ((List.range 273).map (qk u valid π z)).prod else 0)) =
      (BmrSplit.BmrKernel.given τ).toOuterMeasure {t | ∀ i : VO u, t i.1.1.1 = z i.1} *
        ((List.range 273).map (qk u valid π z)).prod := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun t => ?_
    by_cases cond : ∀ i : VO u, t i.1.1.1 = z i.1
    · rw [if_pos cond, Set.indicator_of_mem (show t ∈ {t : TagTable | ∀ i : VO u, t i.1.1.1 = z i.1} from cond)]
    · rw [if_neg cond, Set.indicator_of_notMem (show t ∉ {t : TagTable | ∀ i : VO u, t i.1.1.1 = z i.1} from cond),
        mul_zero, zero_mul]
  have rhs : ((BmrSplit.BmrKernel.given (merge τ π)).map fun t => some (BmrSplit.restrictBmr u t)) (some z) =
      (BmrSplit.BmrKernel.given (merge τ π)).toOuterMeasure {t | ∀ i : V u, t i.1.1 = z i} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.some.injEq, Set.mem_ofPred_eq, funext_iff]
    rfl
  rw [lhs, rhs]
  refine given_mass_mul (fun i : VO u => i.1.1.1) (fun i => z i.1) (fun i : V u => i.1.1) z τ (merge τ π) _
    (fun T0 => ?_) (sites_prod u valid z τ π)
  constructor
  · intro h i away
    have notColl : ¬ IsCollTag i.1.1 := by
      rintro ⟨k, hk, j, hj, same⟩
      exact away (.mask 0 k) (mask0_mem_sites hk) (by
        show i.1.1 ∈ _
        rw [same]
        exact collectorTag_mem hj)
    exact h ⟨i, notColl⟩ away
  · intro h i away
    exact h i.1 away

end Programmed

/-! ### 8. Route M's replay on the kernel's tables -/

section Replay

variable [FieldCertificate] [GroupCertificate]

/-- The cold pads and non-collector masks of targets: P45's visible cells. -/
def visOf (u : AffineInput) (τ : TargetLaw.Targets) : BMR.Visible Tb u :=
  (BmrSplit.coldOfPads u τ.1, fun r => τ.2 r.1)

/-- The cold pads of a kernel table are its targets'. -/
theorem bmrColdOf_of_reads (u : AffineInput) {τ : TargetLaw.Targets} {t : TagTable} (reads : bmrTargetsOf t = τ) :
    H8.bmrColdOf t u = BmrSplit.coldOfPads u τ.1 := by
  rw [Flags.Wrap.bmrColdOf_eq, ← congrArg Prod.fst reads]
  rfl

theorem view_publish (s : Kriterion.CRT.Entry.Source) :
    (Instance.view).publish s = Kriterion.CRT.Entry.publish s := rfl

theorem view_gammaOf (pub : Kriterion.CRT.Entry.Public) :
    (Instance.view).gammaOf pub = Kriterion.CRT.Entry.gammaOf pub := rfl

theorem publish_rows (s : Kriterion.CRT.Entry.Source) :
    (Kriterion.CRT.Entry.publish s).rows = Vector.ofFn s.rows := rfl

/-- The non-collector masks of route M's replay on a tag table are the table's masks. -/
theorem replayMasks_eq (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature)
    (t : TagTable) (r : BMR.NonCollector) :
    (((Instance.view).replayProgram pub u labels).eval (H8.tagHash t)).masks r = BmrEntry.bmrMasksOf t r.1 := by
  rw [Instance.view_replayProgram_eval]
  generalize hR : (Kriterion.CRT.Entry.replayRouteM pub u labels).eval (H8.tagHash t) = R
  have pairs : R.pairs = (maskValues (H8.tagHash t) 0 digitCount).pair := by
    rw [← hR]
    unfold Kriterion.CRT.Entry.replayRouteM
    simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, eval_nonCollectorMasksM]
    rw [BmrEntry.maskValues_tagHash]
  have single : R.single = (maskValues (H8.tagHash t) 0 digitCount).single := by
    rw [← hR]
    unfold Kriterion.CRT.Entry.replayRouteM
    simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, eval_nonCollectorMasksM]
    rw [BmrEntry.maskValues_tagHash]
  have first : (EntryReading.nonCollectorValues (R.pairs, R.single)).pair =
      (maskValues (H8.tagHash t) 0 digitCount).pair := pairs
  have second : (EntryReading.nonCollectorValues (R.pairs, R.single)).single =
      (maskValues (H8.tagHash t) 0 digitCount).single := single
  obtain ⟨⟨d, x | y⟩, h⟩ := r
  · show maskOf (EntryReading.nonCollectorValues (R.pairs, R.single)) 0 (xElementIndex d x).val =
      maskOf (maskValues (H8.tagHash t) 0 digitCount) 0 (xElementIndex d x).val
    refine EntryReading.maskOf_eq_of_noncollector first second 0 _ ?_
    rintro ⟨-, -, slot⟩
    have hd := d.isLt
    cases x <;> simp_all [BMR.IsCollector, xElementIndex, xSlotsPerDigit, XElement.slot]
  · show maskOf (EntryReading.nonCollectorValues (R.pairs, R.single)) 1 (yElementIndex d y).val =
      maskOf (maskValues (H8.tagHash t) 0 digitCount) 1 (yElementIndex d y).val
    refine EntryReading.maskOf_eq_of_noncollector first second 1 _ ?_
    rintro ⟨one, -⟩
    exact absurd one (by norm_num)

/-- On sparse rows P45's row target is the evaluated row. -/
theorem rowTarget_eq_evaluateRow (rows : Coordinates.Rows) (u : AffineInput)
    (sparse : FieldMacToECMac.SparseRow rows) : BMR.rowTarget rows u = FieldMacToECMac.evaluateRow rows u := by
  obtain ⟨xXY, xY2, yX, zY, zXY, zX2, zY2⟩ := sparse
  simp only [BMR.rowTarget, FieldMacToECMac.evaluateRow, Coordinates.evaluate, xXY, xY2, yX, zY, zXY, zX2, zY2]
  congr 1 <;> ring

/-- **The true rows are P45's row targets at the coins' context.** -/
theorem trueRows_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (d : Fin 91) :
    Security.Phase3.trueRows scalar coins u d = BMR.rowTarget ((BmrEntry.bmrContextOf scalar coins).rows d) u := by
  have rows : (BmrEntry.bmrContextOf scalar coins).rows d =
      (FieldMacToECMac.rowsForOutputKeys (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
        coins.pointRandomness).get d := rfl
  rw [rows, rowTarget_eq_evaluateRow _ _ (FieldMacToECMac.rowsForOutputKeysSparse _ _ d)]
  rfl

/-- The ideal output of P45 at a source's cells and targets. -/
def oI (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (s : Kriterion.CRT.Entry.Source) (τ : TargetLaw.Targets) : BMR.Out Tb u :=
  BMR.idealOut (BmrEntry.bmrContextOf scalar coins) u (BmrOff.srcOf s, visOf u τ)

/-- **Route M's collector masks on a kernel table are P45's ideal collector masks.** -/
theorem collectorMasks_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (valid : validate u = true) (s : Kriterion.CRT.Entry.Source) {τ : TargetLaw.Targets} {t : TagTable}
    (reads : bmrTargetsOf t = τ) :
    collectorMasks u (((Instance.view).replayProgram ((Instance.view).publish s) u ((Instance.view).labels s u)).eval
        (H8.tagHash t)) ((Instance.view).gammaOf ((Instance.view).publish s))
        (fun digit => Security.Phase3.trueRows scalar coins u digit) = (oI scalar coins u s τ).2.2.1 := by
  have delivered := H8.crtReplayDelivered s u t valid
  have masks : ∀ r, (((Instance.view).replayProgram ((Instance.view).publish s) u ((Instance.view).labels s u)).eval
      (H8.tagHash t)).masks r = τ.2 r.1 := fun r => by
    rw [replayMasks_eq, ← congrArg Prod.snd reads]
    rfl
  funext c
  unfold collectorMasks replayRowValues oI BMR.idealOut
  dsimp only
  rw [delivered, bmrColdOf_of_reads u reads]
  have rowsEq : Security.Phase3.trueRows scalar coins u c.1.1 =
      BMR.rowTarget ((BmrEntry.bmrContextOf scalar coins).rows c.1.1) u := trueRows_eq scalar coins u c.1.1
  have gammaEq : (Instance.view).gammaOf ((Instance.view).publish s) c.1.1 = s.rows c.1.1 := by
    rw [view_gammaOf, view_publish]
    unfold Kriterion.CRT.Entry.gammaOf
    rw [publish_rows]
    exact Vector.get_ofFn _ _
  rw [rowsEq, gammaEq]
  simp only [masks]
  unfold BmrOff.srcOf visOf
  rw [view_publish]

/-- **The reveal of route M on a programmed kernel table is P45's reveal.** -/
theorem reveal_iff (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (s : Kriterion.CRT.Entry.Source) {τ : TargetLaw.Targets} {t : TagTable} (reads : bmrTargetsOf t = τ)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    H8.crtRevealOn s u (fun digit => Security.Phase3.trueRows scalar coins u digit) (H8.programmedTable t drawn) ↔
      BmrSplit.revealP45 scalar coins u (BmrOff.srcOf s, visOf u τ) := by
  unfold H8.crtRevealOn BmrSplit.revealP45
  refine or_congr Iff.rfl ?_
  rw [← Flags.replayWraps_programmed_iff s u t drawn, BmrOff.replayWraps_iff, bmrColdOf_of_reads u reads]
  rfl

/-- Two outputs with the same published cells and hints publish the same part. -/
theorem bmrOf_congr (u : AffineInput) {o o' : BMR.Out Tb u} (same : o.1 = o'.1)
    (answers : H8.BmrTags Tb u → Block × Block) : BmrSplit.bmrOf u o answers = BmrSplit.bmrOf u o' answers := by
  unfold BmrSplit.bmrOf
  rw [same]

/-- **The P45 part of route M's view is the published part of P45's ideal output.** -/
theorem bmrPart_view (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (s : Kriterion.CRT.Entry.Source) (τ : TargetLaw.Targets) (labels : LamportSignature) (table : TagTable) :
    H8.bmrPart Tb u ((Kriterion.CRT.Entry.publish s, labels, fun tag => table tag.1) : H8.CoreView crtEntry Tb u) =
      BmrSplit.bmrOf u (oI scalar coins u s τ) (BmrSplit.restrictBmr u table) := by
  rw [BmrOff.bmrPart_middle u s labels table (visOf u τ).1]
  exact bmrOf_congr u rfl _

/-- **The merged kernel at the visible tags is `bmrKernel` at the ideal output's visible targets.** -/
theorem merged_kernel (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (s : Kriterion.CRT.Entry.Source) (τ : TargetLaw.Targets) :
    (BmrSplit.BmrKernel.given (merge τ (oI scalar coins u s τ).2.2.1)).map (BmrSplit.restrictBmr u) =
      BmrSplit.bmrKernel BmrSplit.crtKernel u (BmrSplit.visTargets u (oI scalar coins u s τ)).1
        (BmrSplit.visTargets u (oI scalar coins u s τ)).2 := by
  unfold BmrSplit.bmrKernel
  refine BmrSplit.crtKernel.visible u _ _ ?_ ?_
  · show BmrSplit.coldOfPads u τ.1 = BmrSplit.coldOfPads u (BmrSplit.padsOfCold u (BmrSplit.coldOfPads u τ.1))
    rw [BmrOff.coldOfPads_padsOfCold]
  · funext r
    rfl

end Replay

/-! ### 9. Uniform cells -/

theorem bind_congr_supp {α β : Type} (p : PMF α) (f g : α → PMF β) (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ((PMF.mem_support_iff _ _).mpr ha)]

/-- The non-collector masks of all row masks. -/
def restrictMasks : (BMR.RowEnc → BaseField) →+ (BMR.NonCollector → BaseField) where
  toFun m r := m r.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `visOf` as an additive map. -/
def visHom (u : AffineInput) : TargetLaw.Targets →+ BMR.Visible Tb u :=
  AddMonoidHom.prod ((Flags.Wrap.restrictCold u).comp (AddMonoidHom.fst _ _))
    (restrictMasks.comp (AddMonoidHom.snd _ _))

theorem visHom_surjective (u : AffineInput) : Function.Surjective (visHom u) := by
  classical
  rintro ⟨cold, masks⟩
  obtain ⟨pads, hpads⟩ := Flags.Wrap.restrictCold_surjective u cold
  refine ⟨(pads, fun r => if h : BMR.IsCollector r.2 then 0 else masks ⟨r, h⟩), ?_⟩
  refine Prod.ext hpads (funext fun r => ?_)
  show (if h : BMR.IsCollector r.1.2 then 0 else masks ⟨r.1, h⟩) = masks r
  rw [dif_neg r.2]

/-- **The targets' visible cells are uniform.** -/
theorem uniform_visOf (u : AffineInput) :
    (PMF.uniformOfFintype TargetLaw.Targets).map (visOf u) = PMF.uniformOfFintype (BMR.Visible Tb u) := by
  letI : DecidableEq (BMR.Visible Tb u) := Classical.decEq _
  have same : (visOf u : TargetLaw.Targets → BMR.Visible Tb u) = visHom u := rfl
  rw [same]
  exact BMR.WrapMass.uniform_map_addHom (visHom u) (visHom_surjective u)

/-- **A uniform source's P45 cells and uniform visible cells are uniform cells.** -/
theorem uniform_cells (u : AffineInput) {β : Type} (F : BMR.Source Tb × BMR.Visible Tb u → PMF β) :
    (letI := Fintype.ofFinite Kriterion.CRT.Entry.Source
     haveI : Nonempty Kriterion.CRT.Entry.Source := inferInstance
     (PMF.uniformOfFintype Kriterion.CRT.Entry.Source).bind fun s =>
      (PMF.uniformOfFintype (BMR.Visible Tb u)).bind fun vis => F (BmrOff.srcOf s, vis)) =
      (PMF.uniformOfFintype (BMR.Source Tb × BMR.Visible Tb u)).bind F := by
  rw [EntrySplit.uniform_prod_eq_bind (A := BMR.Source Tb) (B := BMR.Visible Tb u), PMF.bind_bind,
    ← BmrOff.uniform_srcOf, PMF.bind_map]
  refine congrArg _ (funext fun s => ?_)
  rw [Function.comp_apply, PMF.bind_map]
  rfl

/-! ### 10. The assembly -/

section Assembly

variable [FieldCertificate] [GroupCertificate]

open Classical in
/-- Route M's body at a source and a table (the body of `H8.idealCore` at the entry). -/
def bodyOf (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (source : Kriterion.CRT.Entry.Source)
    (table : TagTable) : PMF (Option (H8.CoreView crtEntry Tb u)) :=
  let published := (Instance.view).publish source
  let labels := (Instance.view).labels source u
  let out := ((Instance.view).replayProgram published u labels).eval (H8.tagHash table)
  ((Instance.view).realRows scalar u Q).bind fun drawnRows => match drawnRows with
    | none => PMF.pure none
    | some targets =>
      (H8.collectorDrawsOf crtEntry (collectorMasks u out ((Instance.view).gammaOf published) targets)).map
        fun drawn => match drawn with
        | none => none
        | some drawn =>
          if H8.crtRevealOn source u targets (H8.programmedTable table drawn) then none
          else some (published, labels, fun tag => H8.programmedTable table drawn tag.1)

theorem idealCore_eq (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) :
    H8.idealCore crtEntry Tb H8.crtRevealOn scalar u Q =
      (letI := Fintype.ofFinite Kriterion.CRT.Entry.Source
       haveI : Nonempty Kriterion.CRT.Entry.Source := inferInstance
       (PMF.uniformOfFintype Kriterion.CRT.Entry.Source).bind fun s =>
        (swappedTableLaw crtLayout).bind (bodyOf scalar u Q s)) := rfl

open Classical in
/-- P45's ideal flagged part at coins and cells (the body of `IdealReading`'s right side). -/
def G (scalar : NonZeroScalar) (u : AffineInput) (coins : Kriterion.ArgoMAC.Scheme.Coins)
    (cells : BMR.Source Tb × BMR.Visible Tb u) : PMF (Option (BmrSplit.BmrPart u)) :=
  if BmrSplit.revealP45 scalar coins u cells then PMF.pure none
  else (BmrSplit.bmrLaw BmrSplit.crtKernel u (BMR.idealOut (BmrEntry.bmrContextOf scalar coins) u cells)).map some

theorem realRows_eq (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) :
    (Instance.view).realRows scalar u Q =
      BmrSplit.coinLaw.map fun coins => some fun digit => Security.Phase3.trueRows scalar coins u digit := rfl

/-- A law pushed through a map that is `none` everywhere. -/
theorem map_none_of {α β : Type} (p : PMF α) (f : α → Option β) (h : ∀ a, f a = none) :
    p.map f = PMF.pure none := by
  have : f = Function.const α none := funext h
  rw [this, PMF.map_const]

open Classical in
/-- **Route M's P45 part at a kernel table.** -/
theorem bodyOf_map (scalar : NonZeroScalar) (u : AffineInput) (valid : validate u = true) (Q : Point)
    (s : Kriterion.CRT.Entry.Source) {τ : TargetLaw.Targets} {t : TagTable} (reads : bmrTargetsOf t = τ) :
    (bodyOf scalar u Q s t).map (Option.map (H8.bmrPart Tb u)) =
      BmrSplit.coinLaw.bind fun coins =>
        if BmrSplit.revealP45 scalar coins u (BmrOff.srcOf s, visOf u τ) then PMF.pure none
        else (drawAll (fun c => (sampleOf ((oI scalar coins u s τ).2.2.1 c)).map some) collectorList).map
          (Option.map fun drawn => BmrSplit.bmrOf u (oI scalar coins u s τ)
            (BmrSplit.restrictBmr u (H8.programmedTable t drawn))) := by
  unfold bodyOf
  dsimp only
  rw [realRows_eq, PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind BmrSplit.coinLaw) (funext fun coins => ?_)
  rw [Function.comp_apply]
  dsimp only
  rw [collectorMasks_eq scalar coins u valid s reads, collectorDraws_eq, PMF.map_comp]
  by_cases R : BmrSplit.revealP45 scalar coins u (BmrOff.srcOf s, visOf u τ)
  · rw [if_pos R]
    refine map_none_of _ _ fun drawn => ?_
    rcases drawn with _ | drawn
    · rfl
    · show Option.map _ (if _ then none else some _) = none
      rw [if_pos ((reveal_iff scalar coins u s reads drawn).mpr R)]
      rfl
  · rw [if_neg R]
    refine congrArg (fun f => PMF.map f _) (funext fun drawn => ?_)
    rcases drawn with _ | drawn
    · rfl
    · show Option.map _ (if _ then none else some _) = some _
      rw [if_neg fun hit => R ((reveal_iff scalar coins u s reads drawn).mp hit), Option.map_some, view_publish,
        bmrPart_view scalar coins u s τ]

/-- **Route M's P45 part at a source.** -/
theorem perSource (scalar : NonZeroScalar) (u : AffineInput) (valid : validate u = true) (Q : Point)
    (s : Kriterion.CRT.Entry.Source) :
    ((swappedTableLaw crtLayout).bind (bodyOf scalar u Q s)).map (Option.map (H8.bmrPart Tb u)) =
      BmrSplit.coinLaw.bind fun coins =>
        (PMF.uniformOfFintype (BMR.Visible Tb u)).bind fun vis => G scalar u coins (BmrOff.srcOf s, vis) := by
  rw [BmrSplit.crtKernel.law, PMF.bind_bind, PMF.map_bind]
  have perTargets : ∀ τ : TargetLaw.Targets,
      ((BmrSplit.crtKernel.given τ).bind (bodyOf scalar u Q s)).map (Option.map (H8.bmrPart Tb u)) =
        BmrSplit.coinLaw.bind fun coins => G scalar u coins (BmrOff.srcOf s, visOf u τ) := by
    intro τ
    rw [PMF.map_bind, bind_congr_supp _ _ _ fun t member => bodyOf_map scalar u valid Q s
      (Prod.ext (BmrSplit.crtKernel.reads τ t member).1 (BmrSplit.crtKernel.reads τ t member).2), PMF.bind_comm]
    refine congrArg (PMF.bind BmrSplit.coinLaw) (funext fun coins => ?_)
    unfold G
    by_cases R : BmrSplit.revealP45 scalar coins u (BmrOff.srcOf s, visOf u τ)
    · simp only [if_pos R]
      exact PMF.bind_const _ _
    · simp only [if_neg R]
      have inner : ∀ t : TagTable,
          (drawAll (fun c => (sampleOf ((oI scalar coins u s τ).2.2.1 c)).map some) collectorList).map
            (Option.map fun drawn => BmrSplit.bmrOf u (oI scalar coins u s τ)
              (BmrSplit.restrictBmr u (H8.programmedTable t drawn))) =
          ((drawAll (fun c => (sampleOf ((oI scalar coins u s τ).2.2.1 c)).map some) collectorList).map
            (Option.map fun drawn => BmrSplit.restrictBmr u (H8.programmedTable t drawn))).map
              (Option.map (BmrSplit.bmrOf u (oI scalar coins u s τ))) := by
        intro t
        rw [PMF.map_comp]
        refine congrArg (fun f => PMF.map f _) (funext fun o => ?_)
        rcases o with _ | drawn <;> rfl
      simp only [inner]
      rw [← PMF.map_bind]
      have heart := programmed_given u valid τ (oI scalar coins u s τ).2.2.1
      rw [show BmrSplit.crtKernel.given = BmrSplit.BmrKernel.given from rfl, heart, PMF.map_comp]
      unfold BmrSplit.bmrLaw
      rw [show BMR.idealOut (BmrEntry.bmrContextOf scalar coins) u (BmrOff.srcOf s, visOf u τ) =
        oI scalar coins u s τ from rfl, ← merged_kernel scalar coins u s τ, PMF.map_comp, PMF.map_comp]
      rfl
  rw [funext perTargets, PMF.bind_comm]
  refine congrArg (PMF.bind BmrSplit.coinLaw) (funext fun coins => ?_)
  rw [← uniform_visOf u, PMF.bind_map]
  rfl

end Assembly

end

end Kriterion.CRT.Privacy.BmrIdealP4

namespace Kriterion.CRT.Privacy.BmrSplit

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance

/-- **`M'`'s P45 part on the curve** (`IdealReading` at the swapped table's kernel). -/
theorem idealReading : ∀ [FieldCertificate] [GroupCertificate], IdealReading crtKernel := by
  intro _ _ scalar u Q defined
  have valid : validate u = true := (validate_eq_true_iff u).mpr (onCurve_of_function defined)
  rw [BmrIdealP4.idealCore_eq, PMF.map_bind]
  simp only [BmrIdealP4.perSource scalar u valid Q]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind coinLaw) (funext fun coins => ?_)
  exact BmrIdealP4.uniform_cells u (BmrIdealP4.G scalar u coins)

end Kriterion.CRT.Privacy.BmrSplit
