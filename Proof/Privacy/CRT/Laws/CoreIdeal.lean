/-
**The ideal view law factors**.

`Laws.IdealFactorOn T` and `Laws.IdealFactorOff T` (`Laws/CoreParts.lean`) say that the ideal core at `some v` is the
product of the uniform source's marginals of `crtX`, `crtY` and `exception`, the rest law (labels and the swapped table
at the rest tags) and the ideal P45 marginal.

**What the reveals read** (section 6 item 1 of the finish log, checked first). `crtRevealOn` and `crtRevealOff` read
the source and the table only through `replayCrtValues`, which `replayCrtValues_x`, `replayCrtValues_y` rewrite to
`BMR.evalInt` at the joins the records carry (`bmrJoinsOf`, reading `recX`, `recY` only) and the cold pads of the table
(`bmrColdOf`, body tags of family `6`). The route-M collector masks read `out.delivered` (P45 by
`crtReplayDelivered`) and `out.masks` (the table at the mask tags of family `7`, whatever the key) and the row
constants. So the reveals read only P45 data and the equalities hold.

**The proof.**

* `factor` (generic in the draw `D` and the table the view shows, `vis`): per source `s` and table `t`, the view law at
  `some v` is the indicator of the non-P45 parts times the P45 kernel `kernel s t` at `bmrPart v`
  (`viewParts_eq_iff`); the kernel reads only the source's `curve`, `rows`, `recX`, `recY` and the table off the rest
  positions (hypothesis `hkb`); the table at the rest positions is independent of the table off them
  (`indep_swapped_read`); four lenses on the source (`crtX` from `joins 0, pins 0`, `crtY` from `joins 1, pins 1`,
  `exception`, the label keys) split the source (`LabelsSplitProof.split_sum`).
* On the curve: `idealCore` is `lawOf` of `drawsOn` with the programmed table (`idealCore_eq`), which agrees with the
  table at the rest tags (`prog_rest`); the kernel congruence is `kernelOn_congr`.
* Off the curve: `idealCoreOff` is `lawOf` of a point draw with the table itself (`idealCoreOff_eq`); the kernel
  congruence is `kernelOff_congr`.
-/

import Proof.Privacy.CRT.Laws.CoreParts
import Proof.Privacy.CRT.Laws.LabelsSplit
import Proof.Privacy.CRT.Laws.TableIndep
import Proof.Privacy.CRT.Core.ReplayDelivered
import Proof.Privacy.CRT.Glue.ContainParts
import Proof.Privacy.CRT.Core.BmrSplit
import Proof.Privacy.CRT.Swap.PadLaw

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.Laws.CoreIdeal

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-! ### 1. Indicators, points of pushforwards, lenses, the table split -/

/-- The indicator of a proposition. -/
def ind (p : Prop) : ℝ≥0∞ := by classical exact if p then 1 else 0

theorem ind_pos {p : Prop} (h : p) : ind p = 1 := by
  unfold ind
  exact if_pos h

theorem ind_neg {p : Prop} (h : ¬ p) : ind p = 0 := by
  unfold ind
  exact if_neg h

theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases hp : p
  · by_cases hq : q
    · rw [ind_pos ⟨hp, hq⟩, ind_pos hp, ind_pos hq, one_mul]
    · rw [ind_neg fun h => hq h.2, ind_pos hp, ind_neg hq, one_mul]
  · rw [ind_neg fun h => hp h.1, ind_neg hp, zero_mul]

/-- **A pushforward at a point is an indicator times another pushforward**, when the preimages match. -/
theorem map_apply_ind {Ω A B : Type} (μ : PMF Ω) (f : Ω → A) (g : Ω → B) (a : A) (b : B) (c : Prop)
    (h : ∀ ω, f ω = a ↔ (c ∧ g ω = b)) : (μ.map f) a = ind c * (μ.map g) b := by
  by_cases hc : c
  · rw [ind_pos hc, one_mul]
    exact map_apply_eq_of_iff μ f g a b fun ω => (h ω).trans (and_iff_right hc)
  · rw [ind_neg hc, zero_mul, PMF.map_apply]
    exact ENNReal.tsum_eq_zero.mpr fun ω => if_neg fun e => hc ((h ω).mp e.symm).1

/-- **A lens splits a uniform law**: a function `L` of the coordinate `get` has the law of `L` and is independent of
every weight the setter does not change. -/
theorem lens_point {X Z Y : Type} [Fintype X] [Nonempty X] [Finite Z]
    (get : X → Z) (set : X → Z → X) (get_set : ∀ x z, get (set x z) = z) (set_get : ∀ x, set x (get x) = x)
    (set_set : ∀ x z z', set (set x z) z' = set x z')
    (f : X → ℝ≥0∞) (hf : ∀ x z, f (set x z) = f x) (L : X → Y) (hL : ∀ x x', get x = get x' → L x = L x')
    (y : Y) :
    ∑ x, PMF.uniformOfFintype X x * (ind (L x = y) * f x) =
      ((PMF.uniformOfFintype X).map L) y * ∑ x, PMF.uniformOfFintype X x * f x := by
  let _ : Fintype Z := Fintype.ofFinite Z
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have _ : Nonempty Z := ⟨get x₀⟩
  have back : ∀ x, L (set x₀ (get x)) = L x := fun x => hL _ _ (get_set x₀ (get x))
  let g : Z → ℝ≥0∞ := fun z => ind (L (set x₀ z) = y)
  have main : ∑ x, PMF.uniformOfFintype X x * (f x * g (get x)) =
      (∑ x, PMF.uniformOfFintype X x * f x) * ∑ z, PMF.uniformOfFintype Z z * g z :=
    LabelsSplitProof.split_sum get set get_set set_get set_set f hf g
  have one : ∑ x, PMF.uniformOfFintype X x * (1 * g (get x)) =
      (∑ x, PMF.uniformOfFintype X x * 1) * ∑ z, PMF.uniformOfFintype Z z * g z :=
    LabelsSplitProof.split_sum get set get_set set_get set_set (fun _ => 1) (fun _ _ => rfl) g
  have law : ((PMF.uniformOfFintype X).map L) y = ∑ x, PMF.uniformOfFintype X x * (1 * g (get x)) := by
    rw [PMF.map_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun x _ => ?_
    show _ = _ * (1 * ind (L (set x₀ (get x)) = y))
    rw [back, one_mul]
    by_cases hx : L x = y
    · rw [if_pos hx.symm, ind_pos hx, mul_one]
    · rw [if_neg fun e => hx e.symm, ind_neg hx, mul_zero]
  have total : ∑ x, PMF.uniformOfFintype X x * 1 = 1 := by
    simp only [mul_one]
    exact LabelsSplitProof.sum_uniform_one
  calc ∑ x, PMF.uniformOfFintype X x * (ind (L x = y) * f x)
        = ∑ x, PMF.uniformOfFintype X x * (f x * g (get x)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          show _ = _ * (f x * ind (L (set x₀ (get x)) = y))
          rw [back, mul_comm (f x)]
    _ = _ := main
    _ = _ := by rw [law, one, total, one_mul, mul_comm]

/-- **The table split at a point**: under an independent read, the indicator of the read's value factors out of every
kernel that ignores the read's positions. -/
theorem indep_point {V β : Type} {μ : PMF TagTable} {P : Set (Fin (2 ^ 40))} {ν : PMF V} {read : TagTable → V}
    (indep : IndepS μ P ν read) (K : TagTable → PMF (Option β)) (hK : Ignores P K) (r : V) (b : β) :
    ∑' t, μ t * (ind (read t = r) * K t (some b)) = ν r * ∑' t, μ t * K t (some b) := by
  classical
  let G : V → TagTable → PMF (Option β) := fun r' t => if r' = r then K t else PMF.pure none
  have ig : ∀ r', r' ∈ ν.support → Ignores P (G r') := by
    intro r' _ T T' agree
    by_cases h : r' = r
    · simp only [G, if_pos h]
      exact hK T T' agree
    · simp only [G, if_neg h]
  have law := congrArg (fun q : PMF (Option β) => q (some b)) (indep (Option β) G ig)
  simp only [PMF.bind_apply] at law
  have none_b : (PMF.pure (none : Option β)) (some b) = 0 := PMF.pure_apply_of_ne _ _ (Option.some_ne_none _)
  have lhs : ∀ t, G (read t) t (some b) = ind (read t = r) * K t (some b) := fun t => by
    by_cases h : read t = r
    · simp only [G, if_pos h, ind_pos h, one_mul]
    · simp only [G, if_neg h, ind_neg h, zero_mul]
      exact none_b
  simp only [lhs] at law
  rw [law, tsum_eq_single r]
  · simp only [G, if_pos rfl]
  · intro r' ne
    simp only [G, if_neg ne, none_b, mul_zero, tsum_zero]

/-- The joint law of a function of the source and a function of the table is the product. -/
theorem bind_map_pair {S A B : Type} (μ : PMF S) (ν : PMF TagTable) (L : S → A) (R : TagTable → B) :
    (μ.bind fun s => ν.map fun t => (L s, R t)) = prodLaw (μ.map L) (ν.map R) := by
  unfold prodLaw
  rw [PMF.bind_map]
  refine congrArg _ (funext fun s => ?_)
  exact (PMF.map_comp _ _ _).symm

/-! ### 2. Positions: rest tags, body tags, mask tags -/

/-- The rest positions at `u` (the visible tags of families `0` to `5` and `8`). -/
def restFin (T : CrtTable) (u : AffineInput) : Finset (Fin (2 ^ 40)) :=
  Finset.univ.filter fun p => visTag T u p.val = true ∧ (tagFamily p.val ≤ 5 ∨ tagFamily p.val = 8)

/-- The rest positions, as a set. -/
def restPos (T : CrtTable) (u : AffineInput) : Set (Fin (2 ^ 40)) := ↑(restFin T u)

theorem mem_restPos {T : CrtTable} {u : AffineInput} {p : Fin (2 ^ 40)} :
    p ∈ restPos T u ↔ visTag T u p.val = true ∧ (tagFamily p.val ≤ 5 ∨ tagFamily p.val = 8) := by
  unfold restPos restFin
  simp

/-- A position of family `6`, `7` or `10` is not a rest position. -/
theorem not_mem_restPos {T : CrtTable} {u : AffineInput} {p : Fin (2 ^ 40)}
    (fam : tagFamily p.val = 6 ∨ tagFamily p.val = 7 ∨ tagFamily p.val = 10) : p ∉ restPos T u := by
  rw [mem_restPos]
  rintro ⟨_, low | eight⟩ <;> omega

/-- The table at the rest tags. -/
def restRead (T : CrtTable) (u : AffineInput) (t : TagTable) : RestTags T u → Block × Block := fun tag => t tag.1.1

/-- **The rest read is independent of the table off the rest positions.** -/
theorem restIndep (T : CrtTable) (u : AffineInput) :
    IndepS (swappedTableLaw crtLayout) (restPos T u) ((swappedTableLaw crtLayout).map (restRead T u))
      (restRead T u) :=
  indep_swapped_read crtLayout (restFin T u)
    (fun _ hp => restPos_away (mem_restPos.mp (Finset.mem_coe.mpr hp)).2) (restRead T u)
    fun _ _ agree => funext fun tag => agree tag.1.1 (Finset.mem_coe.mp (mem_restPos.mpr ⟨tag.1.2, tag.2⟩))

/-- A body tag in range has family `6`. -/
theorem body_family {κ i ρ j : ℕ} (hκ : κ < 2) (hi : i < 128) (hρ : ρ < 65536) (hj : j < 64) :
    tagFamily (tagCode Family.body κ i 0 0 ρ j % 2 ^ 40) = 6 := by
  have range : TagInRange κ i 0 0 ρ j := ⟨hκ, hi, by norm_num, by norm_num, hρ, hj⟩
  have small : tagCode Family.body κ i 0 0 ρ j < 2 ^ 40 := by
    unfold tagCode Family.body
    omega
  rw [Nat.mod_eq_of_lt small]
  exact tagFamily_tagCode range

/-- A mask tag in range has family `7`. -/
theorem mask_family {st site part : ℕ} (hst : st < 4) (hsite : site < 65536) (hpart : part < 64) :
    tagFamily (maskTag st site part % 2 ^ 40) = 7 := by
  have range : TagInRange 0 0 st 0 site part := ⟨by norm_num, by norm_num, hst, by norm_num, hsite, hpart⟩
  have small : maskTag st site part < 2 ^ 40 := by
    unfold maskTag tagCode Family.mask
    omega
  rw [Nat.mod_eq_of_lt small]
  exact tagFamily_tagCode range

/-- **The cold pads read the table only at body tags.** -/
theorem cold_congr (u : AffineInput) (t t' : TagTable) (agree : ∀ p : Fin (2 ^ 40), tagFamily p.val = 6 → t p = t' p) :
    bmrColdOf t u = bmrColdOf t' u := by
  funext i e ρ
  have hi : i.val < 85 := PadLaw.count_eq ▸ i.isLt
  have hρ : ρ.1.val < Kriterion.CRT.Entry.table.modulus i := ZMod.val_lt ρ.1
  have facts : ∀ κ, κ < 2 → Layout.padModulus i.val < 65536 ∧ Layout.padCount κ i.val < 64 := fun κ hκ =>
    ⟨(Layout.tableFacts κ hκ i.val hi).2.2.2.2.1, (Layout.tableFacts κ hκ i.val hi).2.2.2.2.2⟩
  rw [PadLaw.padModulus_eq] at facts
  cases e with
  | inl x =>
      show padValues t 0 i ρ.1.val _ = padValues t' 0 i ρ.1.val _
      unfold padValues
      congr 1
      funext j
      exact agree _ (body_family (by norm_num) (by omega) (lt_trans hρ (facts 0 (by norm_num)).1)
        (lt_trans j.isLt (facts 0 (by norm_num)).2))
  | inr y =>
      show padValues t 1 i ρ.1.val _ = padValues t' 1 i ρ.1.val _
      unfold padValues
      congr 1
      funext j
      exact agree _ (body_family (by norm_num) (by omega) (lt_trans hρ (facts 1 (by norm_num)).1)
        (lt_trans j.isLt (facts 1 (by norm_num)).2))

/-- The programmed table agrees with the table at the rest tags (the collector tags have family `7`). -/
theorem prog_rest (T : CrtTable) (u : AffineInput) (t : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (tag : RestTags T u) :
    programmedTable t drawn tag.1.1 = t tag.1.1 :=
  Contain.programmedTable_off _ drawn t fun e _ j hj same => by
    have fam := (Contain.collectorTag_fields (lt_trans (Contain.collectorIndex_lt e.1) (by norm_num))
      (by omega : j < 64)).1
    rw [← same] at fam
    rcases tag.2 with h | h <;> omega

/-! ### 3. The general factorization -/

section Factor

variable [FieldCertificate] [GroupCertificate]

/-- Two sources with the same P45 fields. -/
def SameB (s s' : Kriterion.CRT.Entry.Source) : Prop :=
  s.curve = s'.curve ∧ s.rows = s'.rows ∧ s.signs = s'.signs ∧ s.recX = s'.recX ∧ s.recY = s'.recY

omit [FieldCertificate] [GroupCertificate] in
theorem SameB.refl (s : Kriterion.CRT.Entry.Source) : SameB s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The view built from a source, a table and a draw. -/
def viewOf (T : CrtTable) (u : AffineInput) {α : Type} (vis : TagTable → α → TagTable) (s : (view).Source)
    (t : TagTable) (a : α) : CoreView crtEntry T u :=
  ((view).publish s, (view).labels s u, fun tag => vis t a tag.1)

/-- The law of the views of a draw. -/
def lawOf (T : CrtTable) (u : AffineInput) {α : Type} (D : (view).Source → TagTable → PMF (Option α))
    (vis : TagTable → α → TagTable) : PMF (Option (CoreView crtEntry T u)) :=
  letI := (view).sourceFintype
  haveI := (view).sourceNonempty
  (PMF.uniformOfFintype (view).Source).bind fun s => (swappedTableLaw crtLayout).bind fun t =>
    (D s t).map (Option.map (viewOf T u vis s t))

/-- **The P45 kernel** of a source and a table. -/
def kernel (T : CrtTable) (u : AffineInput) {α : Type} (D : (view).Source → TagTable → PMF (Option α))
    (vis : TagTable → α → TagTable) (s : (view).Source) (t : TagTable) : PMF (Option (BmrPartT T u)) :=
  (D s t).map (Option.map fun a => bmrPart T u (viewOf T u vis s t a))

/-! #### Lenses on the source -/

/-- The conversion coordinate `κ` of a source: its joins and pins. -/
abbrev ConvKeys := (Fin Kriterion.CRT.Entry.joinCount → Label) ×
  ((k : Fin Kriterion.CRT.Entry.pinCount) → Lanes (Kriterion.CRT.Entry.pinWidth k))

def convGet (κ : Fin 2) (s : Kriterion.CRT.Entry.Source) : ConvKeys := (s.joins κ, s.pins κ)

def convSet (κ : Fin 2) (s : Kriterion.CRT.Entry.Source) (z : ConvKeys) : Kriterion.CRT.Entry.Source :=
  { s with joins := Function.update s.joins κ z.1, pins := Function.update s.pins κ z.2 }

omit [FieldCertificate] [GroupCertificate] in
theorem convGet_convSet (κ : Fin 2) (s : Kriterion.CRT.Entry.Source) (z : ConvKeys) :
    convGet κ (convSet κ s z) = z := by
  unfold convGet convSet
  dsimp only
  rw [Function.update_self, Function.update_self]

omit [FieldCertificate] [GroupCertificate] in
theorem convSet_convGet (κ : Fin 2) (s : Kriterion.CRT.Entry.Source) : convSet κ s (convGet κ s) = s := by
  unfold convGet convSet
  dsimp only
  rw [Function.update_eq_self, Function.update_eq_self]

omit [FieldCertificate] [GroupCertificate] in
theorem convSet_convSet (κ : Fin 2) (s : Kriterion.CRT.Entry.Source) (z z' : ConvKeys) :
    convSet κ (convSet κ s z) z' = convSet κ s z' := by
  unfold convSet
  dsimp only
  rw [Function.update_idem, Function.update_idem]

omit [FieldCertificate] [GroupCertificate] in
theorem conv_congr (κ : Fin 2) (s s' : Kriterion.CRT.Entry.Source) (h : convGet κ s = convGet κ s') :
    s.conv κ = s'.conv κ := by
  have hj : s.joins κ = s'.joins κ := congrArg Prod.fst h
  have hp : s.pins κ = s'.pins κ := congrArg Prod.snd h
  unfold Kriterion.CRT.Entry.Source.conv Kriterion.CRT.Entry.Source.joinAt Kriterion.CRT.Entry.Source.pinBlockAt
  rw [hj, hp]

omit [FieldCertificate] [GroupCertificate] in
theorem convGet_other (κ κ' : Fin 2) (ne : κ' ≠ κ) (s : Kriterion.CRT.Entry.Source) (z : ConvKeys) :
    convGet κ' (convSet κ s z) = convGet κ' s := by
  unfold convGet convSet
  dsimp only
  rw [Function.update_of_ne ne, Function.update_of_ne ne]

theorem publish_crtX (s : Kriterion.CRT.Entry.Source) :
    ((view).publish s).crtX = Kriterion.CRT.Entry.convVector (s.conv 0) := rfl

theorem publish_crtY (s : Kriterion.CRT.Entry.Source) :
    ((view).publish s).crtY = Kriterion.CRT.Entry.convVector (s.conv 1) := rfl

theorem publish_exception (s : Kriterion.CRT.Entry.Source) :
    ((view).publish s).exception = Vector.ofFn s.exception := rfl

def excSet (s : Kriterion.CRT.Entry.Source) (z : Fin digitCount → Exception.Entry) : Kriterion.CRT.Entry.Source :=
  { s with exception := z }

theorem labels_keys (s : Kriterion.CRT.Entry.Source) (u : AffineInput) :
    (view).labels s u = LabelsSplitProof.labelsFrom (LabelsSplitProof.sourceKeys s) u := rfl

/-! #### The factorization -/

/-- The table a view shows at the rest tags. -/
def restTarget (T : CrtTable) (u : AffineInput) (v : CoreView crtEntry T u) : RestTags T u → Block × Block :=
  fun tag => v.2.2 tag.1

/-- The P45 mass of a source at a P45 part: the kernel's weight, averaged over the table. -/
def mass (T : CrtTable) (u : AffineInput) {α : Type} (D : (view).Source → TagTable → PMF (Option α))
    (vis : TagTable → α → TagTable) (b : BmrPartT T u) (s : (view).Source) : ℝ≥0∞ :=
  ∑' t, swappedTableLaw crtLayout t * kernel T u D vis s t (some b)

set_option linter.style.haveILetI false in
/-- **The ideal view law of a draw factors**, when the view shows the table itself at the rest tags and the P45 kernel
reads only the P45 fields of the source and the table off the rest positions. -/
theorem factor (T : CrtTable) (u : AffineInput) {α : Type} (D : (view).Source → TagTable → PMF (Option α))
    (vis : TagTable → α → TagTable) (hrest : ∀ t a (tag : RestTags T u), vis t a tag.1.1 = t tag.1.1)
    (hkb : ∀ s s' t t', SameB s s' → (∀ p, p ∉ restPos T u → t p = t' p) →
      kernel T u D vis s t = kernel T u D vis s' t')
    (v : CoreView crtEntry T u) :
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    lawOf T u D vis (some v) =
      ((PMF.uniformOfFintype (view).Source).map fun s => ((view).publish s).crtX) v.1.crtX *
        (((PMF.uniformOfFintype (view).Source).map fun s => ((view).publish s).crtY) v.1.crtY *
        (((PMF.uniformOfFintype (view).Source).map fun s => ((view).publish s).exception) v.1.exception *
        (((PMF.uniformOfFintype (view).Source).bind fun s =>
          (swappedTableLaw crtLayout).map fun t => ((view).labels s u, fun tag : RestTags T u => t tag.1.1))
            (restOf T u v) *
        ((lawOf T u D vis).map (Option.map (bmrPart T u))) (some (bmrPart T u v))))) := by
  letI := (view).sourceFintype
  haveI := (view).sourceNonempty
  -- (1) one source and one table
  have inner : ∀ s t, ((D s t).map (Option.map (viewOf T u vis s t))) (some v) =
      ind (((view).publish s).crtX = v.1.crtX ∧ ((view).publish s).crtY = v.1.crtY ∧
          ((view).publish s).exception = v.1.exception ∧ (view).labels s u = v.2.1) *
        (ind (restRead T u t = restTarget T u v) * kernel T u D vis s t (some (bmrPart T u v))) := by
    intro s t
    rw [← mul_assoc, ← ind_and]
    unfold kernel
    refine map_apply_ind _ _ _ _ _ _ fun ω => ?_
    cases ω with
    | none => simp
    | some a =>
        have hr : (fun tag : RestTags T u => vis t a tag.1.1) = restRead T u t := funext (hrest t a)
        simp only [Option.map_some, Option.some.injEq]
        rw [viewParts_eq_iff T u]
        simp only [viewParts, restOf, viewOf, Prod.mk.injEq, hr, and_assoc]
        exact Iff.rfl
  -- (2) the law at `some v`
  have lhs : lawOf T u D vis (some v) =
      ∑' s, PMF.uniformOfFintype (view).Source s * (ind (((view).publish s).crtX = v.1.crtX ∧
          ((view).publish s).crtY = v.1.crtY ∧ ((view).publish s).exception = v.1.exception ∧
          (view).labels s u = v.2.1) *
        ∑' t, swappedTableLaw crtLayout t *
          (ind (restRead T u t = restTarget T u v) * kernel T u D vis s t (some (bmrPart T u v)))) := by
    unfold lawOf
    rw [PMF.bind_apply]
    refine tsum_congr fun s => congrArg (_ * ·) ?_
    rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun t => ?_
    rw [inner s t]
    ring
  -- (3) the table split, per source
  have split : ∀ s, ∑' t, swappedTableLaw crtLayout t *
      (ind (restRead T u t = restTarget T u v) * kernel T u D vis s t (some (bmrPart T u v))) =
      ((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) * mass T u D vis (bmrPart T u v) s :=
    fun s => indep_point (restIndep T u) (kernel T u D vis s)
      (fun t t' agree => hkb s s t t' (SameB.refl s) agree) (restTarget T u v) (bmrPart T u v)
  -- (4) the P45 marginal
  have marg : ((lawOf T u D vis).map (Option.map (bmrPart T u))) (some (bmrPart T u v)) =
      ∑' s, PMF.uniformOfFintype (view).Source s * mass T u D vis (bmrPart T u v) s := by
    unfold lawOf mass
    rw [PMF.map_bind, PMF.bind_apply]
    refine tsum_congr fun s => congrArg (_ * ·) ?_
    rw [PMF.map_bind, PMF.bind_apply]
    refine tsum_congr fun t => congrArg (_ * ·) ?_
    rw [PMF.map_comp]
    unfold kernel
    refine congrArg (fun F => PMF.map F (D s t) (some (bmrPart T u v))) (funext fun ω => ?_)
    cases ω <;> rfl
  -- (5) the rest law
  have rest : ((PMF.uniformOfFintype (view).Source).bind fun s =>
        (swappedTableLaw crtLayout).map fun t => ((view).labels s u, fun tag : RestTags T u => t tag.1.1))
          (restOf T u v) =
        ((PMF.uniformOfFintype (view).Source).map fun s => (view).labels s u) v.2.1 *
          ((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) := by
    have pair := bind_map_pair (PMF.uniformOfFintype (view).Source) (swappedTableLaw crtLayout)
      (fun s => (view).labels s u) (restRead T u)
    have restOfEq : restOf T u v = (v.2.1, restTarget T u v) := rfl
    rw [restOfEq]
    exact (congrArg (fun q : PMF _ => q (v.2.1, restTarget T u v)) pair).trans (prodLaw_apply _ _ _ _)
  -- (6) the mass reads only the P45 fields
  have massSame : ∀ s s', SameB s s' → mass T u D vis (bmrPart T u v) s = mass T u D vis (bmrPart T u v) s' :=
    fun s s' same => by
      unfold mass
      simp only [hkb s s' _ _ same fun _ _ => rfl]
  -- (7) the source split
  have lensX := lens_point (X := (view).Source) (convGet 0) (convSet 0) (convGet_convSet 0) (convSet_convGet 0)
    (convSet_convSet 0)
    (fun s => ind (((view).publish s).crtY = v.1.crtY) * (ind (((view).publish s).exception = v.1.exception) *
      (ind ((view).labels s u = v.2.1) *
        (((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) * mass T u D vis (bmrPart T u v) s))))
    (fun s z => by
      have hy : ((view).publish (convSet 0 s z)).crtY = ((view).publish s).crtY := by
        show Kriterion.CRT.Entry.convVector ((convSet 0 s z).conv 1) = Kriterion.CRT.Entry.convVector (s.conv 1)
        rw [conv_congr 1 _ _ (convGet_other 0 1 (by decide) s z)]
      have hm := massSame (convSet 0 s z) s ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [hy, hm]
      try rfl)
    (fun s => ((view).publish s).crtX)
    (fun s s' h => by
      show Kriterion.CRT.Entry.convVector (s.conv 0) = Kriterion.CRT.Entry.convVector (s'.conv 0)
      rw [conv_congr 0 s s' h]) v.1.crtX
  have lensY := lens_point (X := (view).Source) (convGet 1) (convSet 1) (convGet_convSet 1) (convSet_convGet 1)
    (convSet_convSet 1)
    (fun s => ind (((view).publish s).exception = v.1.exception) * (ind ((view).labels s u = v.2.1) *
        (((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) * mass T u D vis (bmrPart T u v) s)))
    (fun s z => by
      have hm := massSame (convSet 1 s z) s ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [hm]
      try rfl)
    (fun s => ((view).publish s).crtY)
    (fun s s' h => by
      show Kriterion.CRT.Entry.convVector (s.conv 1) = Kriterion.CRT.Entry.convVector (s'.conv 1)
      rw [conv_congr 1 s s' h]) v.1.crtY
  have lensE := lens_point (X := (view).Source) (fun s : Kriterion.CRT.Entry.Source => s.exception) excSet
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun s => ind ((view).labels s u = v.2.1) *
        (((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) * mass T u D vis (bmrPart T u v) s))
    (fun s z => by
      have hm := massSame (excSet s z) s ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [hm]
      try rfl)
    (fun s => ((view).publish s).exception)
    (fun s s' h => by
      show Vector.ofFn s.exception = Vector.ofFn s'.exception
      rw [h]) v.1.exception
  have lensL := lens_point (X := (view).Source) LabelsSplitProof.sourceKeys LabelsSplitProof.withSourceKeys
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun s => ((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) * mass T u D vis (bmrPart T u v) s)
    (fun s z => by
      have hm := massSame (LabelsSplitProof.withSourceKeys s z) s ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [hm])
    (fun s => (view).labels s u)
    (fun s s' h => by
      show LabelsSplitProof.labelsFrom (LabelsSplitProof.sourceKeys s) u =
        LabelsSplitProof.labelsFrom (LabelsSplitProof.sourceKeys s') u
      rw [h]) v.2.1
  beta_reduce at lensX lensY lensE lensL
  rw [lhs, marg, rest]
  simp only [split]
  rw [tsum_fintype, tsum_fintype]
  have expand : ∀ s, ind (((view).publish s).crtX = v.1.crtX ∧ ((view).publish s).crtY = v.1.crtY ∧
      ((view).publish s).exception = v.1.exception ∧ (view).labels s u = v.2.1) *
        (((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) * mass T u D vis (bmrPart T u v) s) =
      ind (((view).publish s).crtX = v.1.crtX) * (ind (((view).publish s).crtY = v.1.crtY) *
        (ind (((view).publish s).exception = v.1.exception) * (ind ((view).labels s u = v.2.1) *
          (((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) *
            mass T u D vis (bmrPart T u v) s)))) := by
    intro s
    rw [ind_and, ind_and, ind_and]
    ring
  simp only [expand]
  rw [lensX, lensY, lensE, lensL]
  have pull : ∑ s, PMF.uniformOfFintype (view).Source s *
      (((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) * mass T u D vis (bmrPart T u v) s) =
      ((swappedTableLaw crtLayout).map (restRead T u)) (restTarget T u v) *
        ∑ s, PMF.uniformOfFintype (view).Source s * mass T u D vis (bmrPart T u v) s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [pull]
  ring

end Factor

/-! ### 4. What the P45 kernel reads -/

section Reads

variable [FieldCertificate] [GroupCertificate]

theorem recX_congr {s s' : Kriterion.CRT.Entry.Source} (h : s.recX = s'.recX) :
    ((view).publish s).recX = ((view).publish s').recX := by
  show (Kriterion.CRT.Entry.publish s).recX = (Kriterion.CRT.Entry.publish s').recX
  unfold Kriterion.CRT.Entry.publish
  dsimp only
  rw [h]

theorem recY_congr {s s' : Kriterion.CRT.Entry.Source} (h : s.recY = s'.recY) :
    ((view).publish s).recY = ((view).publish s').recY := by
  show (Kriterion.CRT.Entry.publish s).recY = (Kriterion.CRT.Entry.publish s').recY
  unfold Kriterion.CRT.Entry.publish
  dsimp only
  rw [h]

theorem rows_congr {s s' : Kriterion.CRT.Entry.Source} (h : s.rows = s'.rows) (hs : s.signs = s'.signs) :
    ((view).publish s).rows = ((view).publish s').rows := by
  show (Kriterion.CRT.Entry.publish s).rows = (Kriterion.CRT.Entry.publish s').rows
  have same : s.normRow = s'.normRow := by
    funext d
    unfold Kriterion.CRT.Entry.Source.normRow
    rw [h, hs]
  unfold Kriterion.CRT.Entry.publish
  dsimp only
  rw [same]

/-- **The joins the reveal reads are the records' joins.** -/
theorem joins_congr {s s' : Kriterion.CRT.Entry.Source} (same : SameB s s') :
    bmrJoinsOf ((view).publish s) = bmrJoinsOf ((view).publish s') := by
  unfold bmrJoinsOf
  rw [recX_congr same.2.2.2.1, recY_congr same.2.2.2.2]

theorem gamma_congr {s s' : Kriterion.CRT.Entry.Source} (same : SameB s s') :
    (view).gammaOf ((view).publish s) = (view).gammaOf ((view).publish s') := by
  show Kriterion.CRT.Entry.gammaOf (Kriterion.CRT.Entry.publish s) =
    Kriterion.CRT.Entry.gammaOf (Kriterion.CRT.Entry.publish s')
  unfold Kriterion.CRT.Entry.gammaOf
  have hr : (Kriterion.CRT.Entry.publish s).rows = (Kriterion.CRT.Entry.publish s').rows :=
    rows_congr same.2.1 same.2.2.1
  rw [hr]

/-- **The CRT values of the reveal read only the records' joins and the cold pads** (`replayCrtValues_x`, `_y`). -/
theorem values_congr (s s' : (view).Source) (u : AffineInput) (X X' : TagTable)
    (hJ : bmrJoinsOf ((view).publish s) = bmrJoinsOf ((view).publish s')) (hC : bmrColdOf X u = bmrColdOf X' u) :
    replayCrtValues s u X = replayCrtValues s' u X' := by
  refine Prod.ext (funext fun x' => ?_) (funext fun y' => ?_)
  · have h1 := replayCrtValues_x s u X (BMR.xEncEquiv.symm x')
    have h2 := replayCrtValues_x s' u X' (BMR.xEncEquiv.symm x')
    have flat : BMR.xFlat (BMR.xEncEquiv.symm x') = x' := BMR.xEncEquiv.apply_symm_apply x'
    rw [flat] at h1 h2
    rw [h1, h2, hJ, hC]
  · have h1 := replayCrtValues_y s u X (BMR.yEncEquiv.symm y')
    have h2 := replayCrtValues_y s' u X' (BMR.yEncEquiv.symm y')
    have flat : BMR.yFlat (BMR.yEncEquiv.symm y') = y' := BMR.yEncEquiv.apply_symm_apply y'
    rw [flat] at h1 h2
    rw [h1, h2, hJ, hC]

theorem wraps_congr (s s' : (view).Source) (u : AffineInput) (X X' : TagTable)
    (hJ : bmrJoinsOf ((view).publish s) = bmrJoinsOf ((view).publish s')) (hC : bmrColdOf X u = bmrColdOf X' u)
    (hR : s.rows = s'.rows) :
    replayWraps s u X ↔ replayWraps s' u X' := by
  unfold replayWraps replayWindow normBadSrc
  rw [values_congr s s' u X X' hJ hC, hR]

/-- The replay's output on a table. -/
def outOf (s : (view).Source) (u : AffineInput) (t : TagTable) : ReplayOut :=
  ((view).replayProgram ((view).publish s) u ((view).labels s u)).eval (tagHash t)

/-- **The delivered values are P45's** (`crtReplayDelivered`). -/
theorem outOf_delivered (s : (view).Source) (u : AffineInput) (t : TagTable) (valid : validate u = true) :
    (outOf s u t).delivered = BMR.deliveredIdeal u (bmrJoinsOf ((view).publish s)) (bmrColdOf t u) := by
  unfold outOf
  exact crtReplayDelivered s u t valid

omit [FieldCertificate] [GroupCertificate] in
theorem siteAnswers_tagHash (t : TagTable) (K : Block) (st site count : ℕ) :
    siteAnswers (tagHash t) K st site count =
      fun part => t ⟨maskTag st site part.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ := by
  funext part
  exact ReplayDelivered.tagHash_hashInput t K _

/-- The pair masks a table holds. -/
def maskPairOf (t : TagTable) (d : ℕ) : Fin (pairSites d) → BaseField × BaseField := fun k =>
  readPair fun part => t ⟨maskTag 1 k.val part.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- The single mask a table holds. -/
def maskSingleOf (t : TagTable) (d : ℕ) : BaseField :=
  if singleSites d = 1 then
    readSingle fun part => t ⟨maskTag 1 (pairSites d) part.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩
  else 0

omit [FieldCertificate] [GroupCertificate] in
theorem pair_tagHash (t : TagTable) (K : Block) (d : ℕ) : (maskValues (tagHash t) K d).pair = maskPairOf t d := by
  funext k
  show readPair (siteAnswers (tagHash t) K 1 k.val 3) = _
  rw [siteAnswers_tagHash]
  rfl

omit [GroupCertificate] in
theorem single_tagHash (t : TagTable) (K : Block) (d : ℕ) :
    (maskValues (tagHash t) K d).single = maskSingleOf t d := by
  show (if singleSites d = 1 then readSingle (siteAnswers (tagHash t) K 1 (pairSites d) 2) else 0) = _
  rw [siteAnswers_tagHash]
  rfl

omit [FieldCertificate] [GroupCertificate] in
theorem routeM_pairs (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature) (H : HashN) :
    ((Kriterion.CRT.Entry.replayRouteM pub u labels).eval H).pairs =
      (maskValues H ((Kriterion.CRT.Entry.replayRouteM pub u labels).eval H).key digitCount).pair := by
  simp only [Kriterion.CRT.Entry.replayRouteM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_nonCollectorMasksM]

omit [FieldCertificate] [GroupCertificate] in
theorem routeM_single (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : LamportSignature) (H : HashN) :
    ((Kriterion.CRT.Entry.replayRouteM pub u labels).eval H).single =
      (maskValues H ((Kriterion.CRT.Entry.replayRouteM pub u labels).eval H).key digitCount).single := by
  simp only [Kriterion.CRT.Entry.replayRouteM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_nonCollectorMasksM]

/-- The route-M masks a table holds. -/
def maskOut (t : TagTable) : BMR.NonCollector → BaseField :=
  toMasks (Kriterion.CRT.Entry.maskFunction
    (Kriterion.CRT.EntryReading.nonCollectorValues (maskPairOf t digitCount, maskSingleOf t digitCount)))

/-- **The replay's masks are the table's mask answers, whatever the key.** -/
theorem outOf_masks (s : (view).Source) (u : AffineInput) (t : TagTable) : (outOf s u t).masks = maskOut t := by
  unfold outOf
  rw [view_replayProgram_eval]
  dsimp only
  rw [routeM_pairs, routeM_single, pair_tagHash, single_tagHash]
  rfl

omit [FieldCertificate] [GroupCertificate] in
theorem pairSites_small : pairSites digitCount < 65536 := by decide

omit [GroupCertificate] in
/-- **The mask answers read the table only at mask tags.** -/
theorem maskOut_congr (t t' : TagTable) (agree : ∀ p : Fin (2 ^ 40), tagFamily p.val = 7 → t p = t' p) :
    maskOut t = maskOut t' := by
  have pairs : maskPairOf t digitCount = maskPairOf t' digitCount := by
    funext k
    unfold maskPairOf
    congr 1
    funext part
    exact agree _ (mask_family (by norm_num) (lt_trans k.isLt pairSites_small) (by omega))
  have single : maskSingleOf t digitCount = maskSingleOf t' digitCount := by
    unfold maskSingleOf
    congr 2
    funext part
    exact agree _ (mask_family (by norm_num) pairSites_small (by omega))
  unfold maskOut
  rw [pairs, single]

omit [FieldCertificate] [GroupCertificate] in
theorem collectorMasks_congr (u : AffineInput) (o o' : ReplayOut) (gamma : Fin 91 → NormRow)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) (hd : o.delivered = o'.delivered) (hm : o.masks = o'.masks) :
    collectorMasks u o gamma targets = collectorMasks u o' gamma targets := by
  unfold collectorMasks replayRowValues
  rw [hd, hm]

end Reads

/-! ### 5. On the curve -/

section On

variable [FieldCertificate] [GroupCertificate]

open Classical in
/-- **The on-curve draw**: the target rows, then the collector draws at route M's masks, flagged by the reveal. -/
def drawsOn (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) (s : (view).Source) (t : TagTable) :
    PMF (Option (List (BMR.Collector × ((Block × Block × Block) × Block)))) :=
  ((view).realRows scalar u Q).bind fun drawnRows => match drawnRows with
    | none => PMF.pure none
    | some targets =>
      (collectorDrawsOf crtEntry (collectorMasks u (outOf s u t) ((view).gammaOf ((view).publish s)) targets)).map
        fun drawn => match drawn with
          | none => none
          | some drawn => if crtRevealOn s u targets (programmedTable t drawn) then none else some drawn

/-- **`idealCore` is the law of the on-curve draw**, the view showing the programmed table. -/
theorem idealCore_eq (T : CrtTable) (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) :
    idealCore crtEntry T crtRevealOn scalar u Q = lawOf T u (drawsOn scalar u Q) programmedTable := by
  unfold idealCore lawOf drawsOn outOf
  refine congrArg (PMF.bind _) (funext fun s => congrArg (PMF.bind _) (funext fun t => ?_))
  rw [PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun dr => ?_)
  cases dr with
  | none =>
      dsimp only
      rw [PMF.pure_map, Option.map_none]
  | some targets =>
      dsimp only
      rw [PMF.map_comp]
      refine congrArg (fun F => PMF.map F _) (funext fun drawn => ?_)
      cases drawn with
      | none => rfl
      | some drawn =>
          by_cases h : crtRevealOn s u targets (programmedTable t drawn)
          · simp only [Function.comp_apply, if_pos h, Option.map_none]
          · simp only [Function.comp_apply, if_neg h, Option.map_some]
            rfl

/-- **The on-curve P45 kernel reads only the P45 fields and the table off the rest positions.** -/
theorem kernelOn_congr (T : CrtTable) (scalar : NonZeroScalar) (u : AffineInput) (Q : Point)
    (valid : validate u = true) (s s' : (view).Source) (t t' : TagTable) (same : SameB s s')
    (agree : ∀ p, p ∉ restPos T u → t p = t' p) :
    kernel T u (drawsOn scalar u Q) programmedTable s t = kernel T u (drawsOn scalar u Q) programmedTable s' t' := by
  have cold : bmrColdOf t u = bmrColdOf t' u := cold_congr u t t' fun p fam => agree p (not_mem_restPos (Or.inl fam))
  have masks : ∀ targets, collectorMasks u (outOf s u t) ((view).gammaOf ((view).publish s)) targets =
      collectorMasks u (outOf s' u t') ((view).gammaOf ((view).publish s')) targets := fun targets => by
    rw [gamma_congr same]
    refine collectorMasks_congr u _ _ _ targets ?_ ?_
    · rw [outOf_delivered s u t valid, outOf_delivered s' u t' valid, joins_congr same, cold]
    · rw [outOf_masks, outOf_masks]
      exact maskOut_congr t t' fun p fam => agree p (not_mem_restPos (Or.inr (Or.inl fam)))
  have progAgree : ∀ drawn, ∀ p, p ∉ restPos T u → programmedTable t drawn p = programmedTable t' drawn p :=
    fun drawn => Contain.programmedTable_agree (restPos T u) drawn t t' agree
  have reveal : ∀ targets drawn, crtRevealOn s u targets (programmedTable t drawn) ↔
      crtRevealOn s' u targets (programmedTable t' drawn) := fun targets drawn => by
    show rowsDoubling targets ∨ replayWraps s u (programmedTable t drawn) ↔
      rowsDoubling targets ∨ replayWraps s' u (programmedTable t' drawn)
    rw [wraps_congr s s' u _ _ (joins_congr same)
      (cold_congr u _ _ fun p fam => progAgree drawn p (not_mem_restPos (Or.inl fam))) same.2.1]
  have out : ∀ drawn, bmrPart T u (viewOf T u programmedTable s t drawn) =
      bmrPart T u (viewOf T u programmedTable s' t' drawn) := fun drawn => by
    have e1 : ((view).publish s).curve = ((view).publish s').curve := same.1
    have e5 : (fun tag : BmrTags T u => programmedTable t drawn tag.1.1) =
        fun tag => programmedTable t' drawn tag.1.1 :=
      funext fun tag => progAgree drawn _ (not_mem_restPos tag.2)
    simp only [bmrPart, viewOf]
    rw [e1, rows_congr same.2.1 same.2.2.1, recX_congr same.2.2.2.1, recY_congr same.2.2.2.2, e5]
  unfold kernel drawsOn
  rw [PMF.map_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun dr => ?_)
  cases dr with
  | none =>
      dsimp only
      rw [PMF.pure_map, PMF.pure_map, Option.map_none, Option.map_none]
  | some targets =>
      dsimp only
      rw [masks targets, PMF.map_comp, PMF.map_comp]
      refine congrArg (fun F => PMF.map F _) (funext fun drawn => ?_)
      cases drawn with
      | none => simp only [Function.comp_apply, Option.map_none]
      | some drawn =>
          by_cases h : crtRevealOn s u targets (programmedTable t drawn)
          · simp only [Function.comp_apply, if_pos h, if_pos ((reveal targets drawn).mp h), Option.map_none]
          · simp only [Function.comp_apply, if_neg h, if_neg fun h' => h ((reveal targets drawn).mpr h'),
              Option.map_some, out drawn]

end On

/-! ### 6. Off the curve -/

section Off

variable [FieldCertificate] [GroupCertificate]

open Classical in
/-- **The off-curve draw**: a point mass, flagged by the reveal. -/
def drawsOff (u : AffineInput) (s : (view).Source) (t : TagTable) : PMF (Option Unit) :=
  PMF.pure (if crtRevealOff s u t then none else some ())

/-- **`idealCoreOff` is the law of the off-curve draw**, the view showing the table itself. -/
theorem idealCoreOff_eq (T : CrtTable) (u : AffineInput) :
    idealCoreOff crtEntry T crtRevealOff u = lawOf T u (drawsOff u) (fun t _ => t) := by
  unfold idealCoreOff lawOf
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  rw [← PMF.bind_pure_comp]
  refine congrArg (PMF.bind _) (funext fun t => ?_)
  unfold drawsOff
  rw [PMF.pure_map]
  by_cases h : crtRevealOff s u t
  · simp only [Function.comp_apply, if_pos h, Option.map_none]
  · simp only [Function.comp_apply, if_neg h, Option.map_some]
    rfl

/-- **The off-curve P45 kernel reads only the P45 fields and the table off the rest positions.** -/
theorem kernelOff_congr (T : CrtTable) (u : AffineInput) (s s' : (view).Source) (t t' : TagTable)
    (same : SameB s s') (agree : ∀ p, p ∉ restPos T u → t p = t' p) :
    kernel T u (drawsOff u) (fun t _ => t) s t = kernel T u (drawsOff u) (fun t _ => t) s' t' := by
  have cold : bmrColdOf t u = bmrColdOf t' u := cold_congr u t t' fun p fam => agree p (not_mem_restPos (Or.inl fam))
  have reveal : crtRevealOff s u t ↔ crtRevealOff s' u t' := wraps_congr s s' u t t' (joins_congr same) cold same.2.1
  have out : bmrPart T u (viewOf T u (fun t _ => t) s t ()) = bmrPart T u (viewOf T u (fun t _ => t) s' t' ()) := by
    have e1 : ((view).publish s).curve = ((view).publish s').curve := same.1
    have e5 : (fun tag : BmrTags T u => t tag.1.1) = fun tag => t' tag.1.1 :=
      funext fun tag => agree _ (not_mem_restPos tag.2)
    simp only [bmrPart, viewOf]
    rw [e1, rows_congr same.2.1 same.2.2.1, recX_congr same.2.2.2.1, recY_congr same.2.2.2.2, e5]
  unfold kernel drawsOff
  rw [PMF.pure_map, PMF.pure_map]
  by_cases h : crtRevealOff s u t
  · rw [if_pos h, if_pos (reveal.mp h), Option.map_none, Option.map_none]
  · rw [if_neg h, if_neg fun h' => h (reveal.mpr h')]
    simp only [Option.map_some, out]

end Off

/-! ### 7. The named inputs -/

section Named

theorem crtX_fun [FieldCertificate] [GroupCertificate] :
    (fun source : (view).Source => if (0 : Fin 2) = 0 then ((view).publish source).crtX
      else ((view).publish source).crtY) = fun source => ((view).publish source).crtX :=
  funext fun _ => if_pos rfl

theorem crtY_fun [FieldCertificate] [GroupCertificate] :
    (fun source : (view).Source => if (1 : Fin 2) = 0 then ((view).publish source).crtX
      else ((view).publish source).crtY) = fun source => ((view).publish source).crtY :=
  funext fun _ => if_neg (by decide)

/-- **`IdealFactorOn` at every table.** -/
theorem idealFactorOn_of (T : CrtTable) : IdealFactorOn T := by
  intro _ _ scalar u Q output v
  have valid : validate u = true := (validate_eq_true_iff u).mpr (BmrSplit.onCurve_of_function output)
  have main := factor T u (drawsOn scalar u Q) programmedTable (prog_rest T u)
    (fun s s' t t' same agree => kernelOn_congr T scalar u Q valid s s' t t' same agree) v
  rw [idealCore_eq T scalar u Q, crtX_fun, crtY_fun]
  exact main

/-- **`IdealFactorOff` at every table.** -/
theorem idealFactorOff_of (T : CrtTable) : IdealFactorOff T := by
  intro _ _ scalar u _ v
  have main := factor T u (drawsOff u) (fun t _ => t) (fun _ _ _ => rfl)
    (fun s s' t t' same agree => kernelOff_congr T u s s' t t' same agree) v
  rw [idealCoreOff_eq T u, crtX_fun, crtY_fun]
  exact main

end Named

end

end Kriterion.CRT.Privacy.Laws.CoreIdeal

namespace Kriterion.CRT.Privacy.Laws

/-- **The on-curve factorization** (`Laws.IdealFactorOn Entry.table`): on the curve the ideal core at `some v` is the product of the source's
marginals of `crtX`, `crtY`, `exception`, the rest law and the ideal P45 marginal. -/
theorem idealFactorOn : IdealFactorOn Kriterion.CRT.Entry.table :=
  @CoreIdeal.idealFactorOn_of Kriterion.CRT.Entry.table

/-- **The off-curve factorization** (`Laws.IdealFactorOff Entry.table`): the same off the curve, with `crtRevealOff`. -/
theorem idealFactorOff : IdealFactorOff Kriterion.CRT.Entry.table :=
  @CoreIdeal.idealFactorOff_of Kriterion.CRT.Entry.table

end Kriterion.CRT.Privacy.Laws
