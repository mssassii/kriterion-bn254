/-
**(C): `CrtRestSplit` from the labels split**.

`CrtRestSplit T` (`Core/H8.lean`) says that under the swapped tape, off doubling, the labels of `u` and the table at
the visible tags of families `0` to `5` and `8` are distributed as the source's labels and the swapped table there,
independently of everything that reads the coins off the input labels and the table off those tags. The swapped tape
is uniform coins times the swapped table, so the statement splits into a statement about the coins and one about the
table:

* `LabelsSplit` (named input): the labels read only the coins, and under the coin law, off doubling,
  they are distributed as the source's labels and are independent of every weight invariant under `SameOffLabels`;
* the table part: those tags are non-site positions (families `6`, `7` are the sites), so the table there is
  independent of the rest (`indep_swapped_read`);
* **`crtRestSplit_of`**: the composition.
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Laws.TableIndep
import Proof.Privacy.CRT.Laws.RefillFacts

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

/-- The empty table (the labels read no table). -/
def zeroTable : TagTable := fun _ => (0, 0)

open Classical in
/-- **P2b's coin statement**: the labels of `u` read only the coins; under the coin law, off doubling,
they are distributed as the source's labels and are independent of every weight on the coins that is invariant under
`SameOffLabels`. -/
def LabelsSplit : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    (∀ c (table : TagTable), tapeLabels parameter scalar u (c, table) = tapeLabels parameter scalar u (c, zeroTable)) ∧
    ∀ (H : crtEntry.Coins → ℝ≥0∞), (∀ c c', SameOffLabels c c' → H c = H c') → ∀ ℓ : LamportSignature,
      ∑' c, coinLaw c * (if (∃ o, crtEntry.exceptional scalar c o = some u) ∨
          tapeLabels parameter scalar u (c, zeroTable) ≠ ℓ then 0 else H c) =
        ((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u) ℓ *
          ∑' c, coinLaw c * (if ∃ o, crtEntry.exceptional scalar c o = some u then 0 else H c)

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

open Classical in
/-- **(C): the rest split from the labels split.** -/
theorem crtRestSplit_of (T : CrtTable) (labelsSplit : LabelsSplit) : CrtRestSplit T := by
  intro _ _ parameter scalar u
  let _ : Fintype (view).Source := (view).sourceFintype
  have _ : Nonempty (view).Source := (view).sourceNonempty
  intro α g reads b a
  obtain ⟨ℓ, t⟩ := b
  obtain ⟨onCoins, split⟩ := labelsSplit parameter scalar u
  let restRead : TagTable → (RestTags T u → Block × Block) := fun table tag => table tag.1.1
  let Ps : Finset (Fin (2 ^ 40)) :=
    Finset.univ.filter fun p => visTag T u p.val = true ∧ (tagFamily p.val ≤ 5 ∨ tagFamily p.val = 8)
  have indep : IndepS (swappedTableLaw crtLayout) ↑Ps ((swappedTableLaw crtLayout).map restRead) restRead :=
    indep_swapped_read crtLayout Ps (fun p hp => restPos_away (Finset.mem_filter.mp hp).2.2) restRead
      fun T₁ T₂ agree => funext fun tag => agree tag.1.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, tag.1.2, tag.2⟩)
  let gOf : crtEntry.Coins → TagTable → α := fun c table => g (c, table)
  have sameRefl : ∀ c : crtEntry.Coins, SameOffLabels c c := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ignoresG : ∀ c, Ignores ↑Ps (gOf c) := fun c table table' agree =>
    reads (c, table) (c, table') (sameRefl c) fun tag hidden => agree tag fun mem => hidden (Finset.mem_filter.mp mem).2
  have sameInv : ∀ c c', SameOffLabels c c' → gOf c = gOf c' := fun c c' same =>
    funext fun table => reads (c, table) (c', table) same fun _ _ => rfl
  let H : crtEntry.Coins → ℝ≥0∞ := fun c => ((swappedTableLaw crtLayout).map (gOf c)) a
  have Hinv : ∀ c c', SameOffLabels c c' → H c = H c' := fun c c' same => by
    simp only [H, sameInv c c' same]
  have pointLHS : ∀ c, ((swappedTableLaw crtLayout).map fun table =>
      if Doubling crtEntry scalar (c, table) u then none
      else some ((tapeLabels parameter scalar u (c, table), restRead table), g (c, table))) (some ((ℓ, t), a)) =
        ((swappedTableLaw crtLayout).map restRead) t * (if (∃ o, crtEntry.exceptional scalar c o = some u) ∨
          tapeLabels parameter scalar u (c, zeroTable) ≠ ℓ then 0 else H c) := by
    intro c
    by_cases D : ∃ o, crtEntry.exceptional scalar c o = some u
    · have hF : (fun table : TagTable => if Doubling crtEntry scalar (c, table) u then none
          else some ((tapeLabels parameter scalar u (c, table), restRead table), g (c, table))) =
            Function.const TagTable (none : Option ((LamportSignature × (RestTags T u → Block × Block)) × α)) :=
        funext fun table => if_pos D
      rw [hF, PMF.map_const, if_pos (Or.inl D), mul_zero]
      exact PMF.pure_apply_of_ne _ _ (Option.some_ne_none _)
    · have hF : (fun table : TagTable => if Doubling crtEntry scalar (c, table) u then none
          else some ((tapeLabels parameter scalar u (c, table), restRead table), g (c, table))) =
            (fun p : (RestTags T u → Block × Block) × α =>
              some ((tapeLabels parameter scalar u (c, zeroTable), p.1), p.2)) ∘
              fun table => (restRead table, gOf c table) :=
        funext fun table => by
          show (if Doubling crtEntry scalar (c, table) u then none else _) = _
          rw [if_neg (show ¬ Doubling crtEntry scalar (c, table) u from D), onCoins c table]
          rfl
      rw [hF, ← PMF.map_comp, indep.joint (gOf c) (ignoresG c)]
      by_cases L : tapeLabels parameter scalar u (c, zeroTable) = ℓ
      · rw [if_neg (by rintro (h | h); exacts [D h, h L])]
        rw [← L]
        rw [map_apply_inj _ (fun p q h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact Prod.ext h.1.2 h.2) (t, a), prodLaw_apply]
      · rw [if_pos (Or.inr L), mul_zero]
        exact map_apply_notMem _ _ _ fun p h => L (by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.1.1)
  have pointRHS : ∀ c, ((swappedTableLaw crtLayout).map fun table =>
      if Doubling crtEntry scalar (c, table) u then none else some (g (c, table))) (some a) =
        (if ∃ o, crtEntry.exceptional scalar c o = some u then 0 else H c) := by
    intro c
    by_cases D : ∃ o, crtEntry.exceptional scalar c o = some u
    · have hF : (fun table : TagTable => if Doubling crtEntry scalar (c, table) u then none else some (g (c, table))) =
          Function.const TagTable (none : Option α) := funext fun table => if_pos D
      rw [hF, PMF.map_const, if_pos D]
      exact PMF.pure_apply_of_ne _ _ (Option.some_ne_none _)
    · have hF : (fun table : TagTable => if Doubling crtEntry scalar (c, table) u then none else some (g (c, table))) =
          some ∘ gOf c := funext fun table => if_neg D
      rw [hF, ← PMF.map_comp, if_neg D]
      exact map_apply_inj _ (Option.some_injective _) a
  have idealEq : ((PMF.uniformOfFintype (view).Source).bind fun source =>
      (swappedTableLaw crtLayout).map fun table => ((view).labels source u, fun tag : RestTags T u => table tag.1.1)) =
        prodLaw ((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u) ((swappedTableLaw crtLayout).map restRead) := by
    unfold prodLaw
    rw [PMF.bind_map]
    refine congrArg _ (funext fun source => ?_)
    exact (PMF.map_comp _ _ _).symm
  rw [tape_map_apply, tape_map_apply, idealEq, prodLaw_apply]
  calc _ = ∑' c, coinLaw c * (((swappedTableLaw crtLayout).map restRead) t * (if (∃ o, crtEntry.exceptional scalar c o = some u) ∨
          tapeLabels parameter scalar u (c, zeroTable) ≠ ℓ then 0 else H c)) :=
        tsum_congr fun c => congrArg (coinLaw c * ·) (pointLHS c)
    _ = ((swappedTableLaw crtLayout).map restRead) t * ∑' c, coinLaw c * (if (∃ o, crtEntry.exceptional scalar c o = some u) ∨
          tapeLabels parameter scalar u (c, zeroTable) ≠ ℓ then 0 else H c) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun c => by ring
    _ = ((swappedTableLaw crtLayout).map restRead) t * (((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u) ℓ *
          ∑' c, coinLaw c * (if ∃ o, crtEntry.exceptional scalar c o = some u then 0 else H c)) := by
        rw [split H Hinv ℓ]
    _ = _ := by
        rw [← mul_assoc, mul_comm (((swappedTableLaw crtLayout).map restRead) t)]
        exact congrArg (_ * ·) (tsum_congr fun c => congrArg (coinLaw c * ·) (pointRHS c).symm)

end

end Kriterion.CRT.Privacy.Laws
