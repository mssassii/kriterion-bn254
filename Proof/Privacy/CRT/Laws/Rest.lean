/-
**(C): `CrtRestSplit` from the labels split** (no chunk joins).

`CrtRestSplit T` (`Core/H8.lean`) says that under the swapped tape, off doubling, the labels of `u` and the table at
the visible tags of families `0` to `5` and `8` are distributed as the source's labels and the swapped table there,
independently of everything that reads the coins off the input labels and the table off those tags and the hot
chunk-tree tags (`restHidden`). The actual labels absorb the chunk joins, so they read the coins' label keys and the
table's chunk-tree answers; the statement splits into a statement about the labels and one about the table:

* `LabelsSplit` (named input): under the swapped tape, off doubling, the labels are distributed as the source's
  labels and are independent of every weight on the tape invariant under `SameOffLabels` that reads the table off
  the hot chunk-tree tags;
* the table part: the visible rest tags are non-site positions (families `6`, `7` are the sites), so the table there
  is independent of the rest (`indep_swapped_read`);
* **`crtRestSplit_of`**: the composition.
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Laws.TableIndep
import Proof.Privacy.CRT.Laws.RefillFacts
import Proof.Privacy.CRT.NoJoins.Law

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-! ### 1. Laws of maps and products -/

theorem map_apply_inj {X Y : Type} (μ : PMF X) {φ : X → Y} (inj : Function.Injective φ) (x : X) :
    (μ.map φ) (φ x) = μ x := by
  rw [PMF.map_apply, tsum_eq_single x]
  · rw [if_pos rfl]
  · intro x' ne
    rw [if_neg fun same => ne (inj same).symm]

theorem map_apply_notMem {X Y : Type} (μ : PMF X) (φ : X → Y) (y : Y) (off : ∀ x, φ x ≠ y) : (μ.map φ) y = 0 := by
  rw [PMF.map_apply]
  exact ENNReal.tsum_eq_zero.mpr fun x => if_neg fun same => off x same.symm

theorem prodLaw_apply {A B : Type} (ν₁ : PMF A) (ν₂ : PMF B) (a : A) (b : B) :
    prodLaw ν₁ ν₂ (a, b) = ν₁ a * ν₂ b := by
  unfold prodLaw
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [map_apply_inj ν₂ (fun _ _ h => congrArg Prod.snd h) b]
  · intro a' ne
    rw [map_apply_notMem _ _ _ fun x h => ne (congrArg Prod.fst h), mul_zero]

theorem bind_pair_eq {A B : Type} (μ : PMF A) (ν : PMF B) :
    μ.bind (fun c => ν.map fun b => (c, b)) =
      ((μ.bind fun c => ν.map fun b => (c, b)).map Prod.fst).bind fun c => ν.map fun b => (c, b) := by
  have hconst : ∀ c : A, (ν.map fun b => (c, b)).map Prod.fst = PMF.pure c := fun c => by
    rw [PMF.map_comp]
    exact PMF.map_const ν c
  rw [PMF.map_bind]
  simp only [hconst, PMF.bind_pure]

/-! ### 2. The coin law and the labels split -/

/-- The coin law of the swapped tape. -/
def coinLaw : PMF crtEntry.Coins := (swappedTableTape crtEntry).map Prod.fst

theorem swappedTableTape_eq :
    swappedTableTape crtEntry = coinLaw.bind fun c => (swappedTableLaw crtLayout).map fun table => (c, table) := by
  unfold coinLaw swappedTableTape
  exact bind_pair_eq _ _

theorem tape_map_apply {γ : Type} (F : TableTape crtEntry → γ) (z : γ) :
    ((swappedTableTape crtEntry).map F) z =
      ∑' c, coinLaw c * ((swappedTableLaw crtLayout).map fun table => F (c, table)) z := by
  rw [swappedTableTape_eq, PMF.map_bind, PMF.bind_apply]
  refine tsum_congr fun c => ?_
  rw [PMF.map_comp]
  rfl

/-- The labels of `u` under the real key of a tape. -/
def tapeLabels [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (tape : TableTape crtEntry) : LamportSignature :=
  (crtEntry.scheme inferInstance inferInstance).encode (realGarbled crtEntry parameter scalar tape).2 u

/-- The empty table. -/
def zeroTable : TagTable := fun _ => (0, 0)

/-- The hot chunk-tree tags at `u` (family `0`, hot): the tags whose answers the actual labels absorb. -/
def hotTreeTag (u : AffineInput) (tag : Fin (2 ^ 40)) : Prop :=
  tagFamily tag.val = 0 ∧ hotTag Entry.table u tag.val = true

open Classical in
/-- **P2b's statement** (no chunk joins): under the swapped tape, off doubling, the labels of `u` are distributed as
the source's labels and are independent of every weight on the tape that is invariant under `SameOffLabels` and does
not read the hot chunk-tree tags at `u`. -/
def LabelsSplit : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    ∀ (H : TableTape crtEntry → ℝ≥0∞), (∀ tape tape' : TableTape crtEntry, SameOffLabels tape.1 tape'.1 →
        (∀ tag, ¬ hotTreeTag u tag → tape.2 tag = tape'.2 tag) → H tape = H tape') → ∀ ℓ : LamportSignature,
      ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u ∨
          tapeLabels parameter scalar u tape ≠ ℓ then 0 else H tape) =
        ((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u) ℓ *
          ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u then 0 else H tape)

/-! ### 3. The table part and the composition -/

/-- The rest tags are non-site positions: the sites are families `6` and `7`. -/
theorem restPos_away {p : Fin (2 ^ 40)} (fam : tagFamily p.val ≤ 5 ∨ tagFamily p.val = 8) :
    ∀ site ∈ crtLayout.sites, p ∉ (siteTags crtLayout site).map tagPos := by
  intro site member hit
  obtain ⟨famLt, inRange⟩ := RefillLayout.fields_inRange member
  rw [RefillLayout.siteTags_eq, List.map_map] at hit
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hit
  rw [List.mem_range] at hj
  simp only [Function.comp_apply] at fam
  rw [RefillLayout.tagPos_tagCode famLt (inRange j hj), tagFamily_tagCode (inRange j hj)] at fam
  cases site <;> simp [RefillLayout.siteFields, Family.body, Family.mask] at fam

/-- The mass of the swapped tape at a pair. -/
theorem swappedTableTape_apply (c : crtEntry.Coins) (tb : TagTable) :
    swappedTableTape crtEntry (c, tb) = coinLaw c * swappedTableLaw crtLayout tb := by
  rw [swappedTableTape_eq]
  exact NoJoins.product_apply coinLaw (swappedTableLaw crtLayout) c tb

/-- A sum against the swapped tape, coins first. -/
theorem tsum_tape (G : TableTape crtEntry → ℝ≥0∞) :
    ∑' tape, swappedTableTape crtEntry tape * G tape =
      ∑' c, coinLaw c * ∑' tb, swappedTableLaw crtLayout tb * G (c, tb) := by
  rw [ENNReal.tsum_prod (f := fun c tb => swappedTableTape crtEntry (c, tb) * G (c, tb))]
  refine tsum_congr fun c => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun tb => ?_
  rw [swappedTableTape_apply, mul_assoc]

open Classical in
/-- The mass of `some y` in a pushforward, as a sum. -/
theorem map_some_apply_sum {X Y : Type} (μ : PMF X) (F : X → Option Y) (y : Y) :
    (μ.map F) (some y) = ∑' x, μ x * (if F x = some y then 1 else 0) := by
  classical
  rw [PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases h : F x = some y
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg fun e => h e.symm, if_neg h, mul_zero]

open Classical in
/-- The mass of a point in a pushforward, as a sum. -/
theorem map_apply_sum {X Y : Type} (μ : PMF X) (F : X → Y) (y : Y) :
    (μ.map F) y = ∑' x, μ x * (if F x = y then 1 else 0) := by
  classical
  rw [PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases h : F x = y
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg fun e => h e.symm, if_neg h, mul_zero]

open Classical in
/-- **(C): the rest split from the labels split.** -/
theorem crtRestSplit_of (labelsSplit : LabelsSplit) : CrtRestSplit Entry.table := by
  intro _ _ parameter scalar u
  let _ : Fintype (view).Source := (view).sourceFintype
  have _ : Nonempty (view).Source := (view).sourceNonempty
  intro α g reads b a
  obtain ⟨ℓ, t⟩ := b
  let restRead : TagTable → (RestTags Entry.table u → Block × Block) := fun table tag => table tag.1.1
  let Ps : Finset (Fin (2 ^ 40)) :=
    Finset.univ.filter fun p => visTag Entry.table u p.val = true ∧ (tagFamily p.val ≤ 5 ∨ tagFamily p.val = 8)
  have indep : IndepS (swappedTableLaw crtLayout) ↑Ps ((swappedTableLaw crtLayout).map restRead) restRead :=
    indep_swapped_read crtLayout Ps (fun p hp => restPos_away (Finset.mem_filter.mp hp).2.2) restRead
      fun T₁ T₂ agree => funext fun tag => agree tag.1.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, tag.1.2, tag.2⟩)
  have sameRefl : ∀ c : crtEntry.Coins, SameOffLabels c c := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ignoresG : ∀ c, Ignores ↑Ps (fun table => g (c, table)) := fun c table table' agree =>
    reads (c, table) (c, table') (sameRefl c) fun tag hidden =>
      agree tag fun mem => hidden (Or.inl (Finset.mem_filter.mp mem).2)
  -- a visible rest tag is not a hot chunk-tree tag
  have restNotHot : ∀ tag : RestTags Entry.table u, ¬ hotTreeTag u tag.1.1 := by
    intro tag hot
    have vis := tag.1.2
    unfold visTag at vis
    rw [hot.1] at vis
    simp only [hot.2, Bool.not_true, Bool.false_eq_true] at vis
  -- the weight of the labels split
  -- (classical decidability: the equality of tables would otherwise be decided by enumerating tags)
  let H : TableTape crtEntry → ℝ≥0∞ := fun tape =>
    @ite _ (restRead tape.2 = t ∧ g tape = a) (Classical.propDecidable _) 1 0
  have Hinv : ∀ tape tape' : TableTape crtEntry, SameOffLabels tape.1 tape'.1 →
      (∀ tag, ¬ hotTreeTag u tag → tape.2 tag = tape'.2 tag) → H tape = H tape' := by
    intro tape tape' same agree
    have hr : restRead tape.2 = restRead tape'.2 := funext fun tag => agree tag.1.1 (restNotHot tag)
    have hg : g tape = g tape' := reads tape tape' same fun tag notHidden =>
      agree tag fun hot => notHidden (Or.inr hot)
    dsimp only [H]
    rw [hr, hg]
  have split := labelsSplit parameter scalar u H Hinv ℓ
  -- the left side
  have lhs : ((swappedTableTape crtEntry).map fun tape => if Doubling crtEntry scalar tape u then none
      else some ((tapeLabels parameter scalar u tape, restRead tape.2), g tape)) (some ((ℓ, t), a)) =
      ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u ∨
        tapeLabels parameter scalar u tape ≠ ℓ then 0 else H tape) := by
    rw [map_some_apply_sum]
    refine tsum_congr fun tape => congrArg _ ?_
    by_cases D : Doubling crtEntry scalar tape u
    · rw [if_pos D, if_pos (Or.inl D), if_neg (by simp)]
    · rw [if_neg D]
      by_cases L : tapeLabels parameter scalar u tape = ℓ
      · rw [if_neg (show ¬(Doubling crtEntry scalar tape u ∨ tapeLabels parameter scalar u tape ≠ ℓ) by
          rintro (h | h); exacts [D h, h L])]
        show _ = @ite _ (restRead tape.2 = t ∧ g tape = a) (Classical.propDecidable _) 1 0
        by_cases h : restRead tape.2 = t ∧ g tape = a
        · rw [if_pos h, if_pos (by rw [L, h.1, h.2])]
        · rw [if_neg h, if_neg]
          intro e
          have e' := Prod.mk.inj (Option.some.inj e)
          exact h ⟨(Prod.mk.inj e'.1).2, e'.2⟩
      · rw [if_pos (Or.inr L), if_neg]
        intro e
        exact L (Prod.mk.inj (Prod.mk.inj (Option.some.inj e)).1).1
  -- the right side's mass
  have rhs : ((swappedTableTape crtEntry).map fun tape => if Doubling crtEntry scalar tape u then none
      else some (g tape)) (some a) =
      ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u then 0 else
        (if g tape = a then 1 else 0)) := by
    rw [map_some_apply_sum]
    refine tsum_congr fun tape => congrArg _ ?_
    by_cases D : Doubling crtEntry scalar tape u
    · rw [if_pos D, if_pos D, if_neg (by simp)]
    · rw [if_neg D, if_neg D]
      by_cases h : g tape = a
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg fun e => h (Option.some.inj e)]
  -- the table part splits off the weight
  have table : ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u then 0 else H tape) =
      ((swappedTableLaw crtLayout).map restRead) t *
        ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u then 0 else
          (if g tape = a then 1 else 0)) := by
    rw [tsum_tape, tsum_tape, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun c => ?_
    by_cases D : ∃ o, crtEntry.exceptional scalar c o = some u
    · have hD : ∀ tb, Doubling crtEntry scalar (c, tb) u := fun tb => D
      have e1 : ∑' tb, swappedTableLaw crtLayout tb * (if Doubling crtEntry scalar (c, tb) u then 0 else H (c, tb)) =
          0 := by
        exact (tsum_congr fun tb => by rw [if_pos (hD tb), mul_zero]).trans tsum_zero
      have e2 : ∑' tb, swappedTableLaw crtLayout tb * (if Doubling crtEntry scalar (c, tb) u then 0 else
          (if g (c, tb) = a then 1 else 0)) = 0 := by
        exact (tsum_congr fun tb => by rw [if_pos (hD tb), mul_zero]).trans tsum_zero
      rw [e1, e2]
      simp only [mul_zero]
    · have hD : ∀ tb, ¬ Doubling crtEntry scalar (c, tb) u := fun tb => D
      have e1 : ∑' tb, swappedTableLaw crtLayout tb * (if Doubling crtEntry scalar (c, tb) u then 0 else H (c, tb)) =
          ∑' tb, swappedTableLaw crtLayout tb * H (c, tb) := tsum_congr fun tb => by rw [if_neg (hD tb)]
      have e2 : ∑' tb, swappedTableLaw crtLayout tb * (if Doubling crtEntry scalar (c, tb) u then 0 else
          (if g (c, tb) = a then 1 else 0)) = ∑' tb, swappedTableLaw crtLayout tb * (if g (c, tb) = a then 1 else 0) :=
        tsum_congr fun tb => by rw [if_neg (hD tb)]
      rw [e1, e2]
      have e := congrArg (fun q : PMF ((RestTags Entry.table u → Block × Block) × α) => q (t, a))
        (indep.joint (fun table => g (c, table)) (ignoresG c))
      rw [prodLaw_apply] at e
      have jointSum : ∑' tb, swappedTableLaw crtLayout tb * H (c, tb) =
          ((swappedTableLaw crtLayout).map restRead) t *
            ∑' tb, swappedTableLaw crtLayout tb * (if g (c, tb) = a then 1 else 0) := by
        rw [← map_apply_sum (swappedTableLaw crtLayout) (fun table => g (c, table)) a, ← e, map_apply_sum]
        refine tsum_congr fun tb => congrArg _ ?_
        show @ite _ (restRead tb = t ∧ g (c, tb) = a) (Classical.propDecidable _) 1 0 = _
        by_cases h : restRead tb = t ∧ g (c, tb) = a
        · rw [if_pos h, if_pos (by rw [h.1, h.2])]
        · rw [if_neg h, if_neg fun e => h ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩]
      rw [jointSum, mul_left_comm]
  -- the ideal law
  have idealEq : ((PMF.uniformOfFintype (view).Source).bind fun source =>
      (swappedTableLaw crtLayout).map fun table => ((view).labels source u, fun tag : RestTags Entry.table u =>
        table tag.1.1)) =
        prodLaw ((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u)
          ((swappedTableLaw crtLayout).map restRead) := by
    unfold prodLaw
    rw [PMF.bind_map]
    refine congrArg _ (funext fun source => ?_)
    exact (PMF.map_comp _ _ _).symm
  calc _ = ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u ∨
          tapeLabels parameter scalar u tape ≠ ℓ then 0 else H tape) := lhs
    _ = ((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u) ℓ *
          ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u then 0 else H tape) := split
    _ = prodLaw ((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u)
          ((swappedTableLaw crtLayout).map restRead) (ℓ, t) *
        ((swappedTableTape crtEntry).map fun tape => if Doubling crtEntry scalar tape u then none
          else some (g tape)) (some a) := by
        rw [table, prodLaw_apply, rhs]
        ring
    _ = _ := by rw [idealEq]

end

end Kriterion.CRT.Privacy.Laws
