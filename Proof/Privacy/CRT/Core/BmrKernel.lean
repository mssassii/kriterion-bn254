/-
**The swapped table as uniform targets and a kernel** (`TableKernel` and
`KernelOff`).

`crtKernel`'s kernel is the swapped table conditioned on its targets (`TargetLaw.condLaw`), and the targets are
uniform (`swapped_targets_uniform`), so `law` and `reads` hold. For `visible`: a site that holds a visible P45 tag
at `u` (`BmrKernel.visible_site`) is either a pad site whose slot is not `u`'s hot residue, whose digits are all cold,
or a mask site, visible only on the curve. Such a site's event depends only on the cold pads and the masks
(`BmrKernel.cold_match`), so `swapped_event_eq` gives the same answers at the visible tags. Off the curve no mask
site holds a visible tag, so the cold pads alone decide them (`crtKernel_off`).
-/

import Proof.Privacy.CRT.Core.BmrSplit
import Proof.Privacy.CRT.Swap.TargetLaw

namespace Kriterion.CRT.Privacy.BmrSplit

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance Kriterion.CRT.Privacy.TargetLaw
open scoped ENNReal

noncomputable section

namespace BmrKernel

/-- The targets of the swapped table are uniform. -/
theorem targets_uniform : (swappedTableLaw crtLayout).map bmrTargetsOf = PMF.uniformOfFintype Targets :=
  swapped_targets_uniform

/-- **The kernel**: the swapped table conditioned on its targets. -/
def given (τ : Targets) : PMF TagTable := condLaw (swappedTableLaw crtLayout) bmrTargetsOf targets_uniform τ

/-- **A site that holds a visible P45 tag** is a pad site whose slot is not the hot residue of its coordinate, or a
mask site on the curve. -/
theorem visible_site (u : AffineInput) {s : SiteId} (member : s ∈ crtLayout.sites) (tag : H8.BmrTags Tb u)
    (inside : tag.1.1 ∈ Laws.sitePos crtLayout s) :
    (∃ κ i ρ, s = .pad κ i ρ ∧ ∀ h : i < Tb.count, ρ < Tb.modulus ⟨i, h⟩ ∧ ρ ≠ coordValue u κ % Tb.modulus ⟨i, h⟩) ∨
      (∃ st k, s = .mask st k ∧ validate u = true) := by
  obtain ⟨code, codeIn, at_pos⟩ := List.mem_map.mp inside
  rw [Laws.RefillLayout.siteTags_eq] at codeIn
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp codeIn
  obtain ⟨famLt, inRange⟩ := Laws.RefillLayout.fields_inRange member
  have range := inRange j (List.mem_range.mp hj)
  have val := Laws.RefillLayout.tagPos_tagCode famLt range
  rw [at_pos] at val
  have vis : H8.visTag Tb u tag.1.1.val = true := tag.1.2
  rw [val] at vis
  cases s with
  | pad κ i ρ =>
    left
    refine ⟨κ, i, ρ, rfl, fun h => ⟨?_, ?_⟩⟩
    · rcases List.mem_append.mp member with pad | mask
      · obtain ⟨κ', i', ρ', same, -, -, hρ⟩ := Layout.mem_padSites pad
        cases same
        rw [← PadLaw.padModulus_eq ⟨i, h⟩]
        exact hρ
      · rcases Layout.mem_maskSites mask with ⟨k, same, -⟩ | ⟨k, same, -⟩ <;> cases same
    · change TagInRange κ i 0 0 ρ j at range
      change H8.visTag Tb u (tagCode Family.body κ i 0 0 ρ j) = true at vis
      have hfam : tagFamily (tagCode Family.body κ i 0 0 ρ j) = 6 := tagFamily_tagCode range
      have hcoord : tagCoord (tagCode Family.body κ i 0 0 ρ j) = κ := tagCoord_tagCode range
      have hidx : tagIdx (tagCode Family.body κ i 0 0 ρ j) = i := tagIdx_tagCode range
      have hslot : tagSlot (tagCode Family.body κ i 0 0 ρ j) = ρ := tagSlot_tagCode range
      unfold H8.visTag hotTag at vis
      simp only [hfam, hcoord, hidx, hslot, dif_pos h] at vis
      have key : (ρ == coordValue u κ % Tb.modulus ⟨i, h⟩) = false := by simpa using vis
      intro same
      simp [same] at key
  | mask st k =>
    right
    refine ⟨st, k, rfl, ?_⟩
    change TagInRange 0 0 st 0 k j at range
    change H8.visTag Tb u (tagCode Family.mask 0 0 st 0 k j) = true at vis
    have hfam : tagFamily (tagCode Family.mask 0 0 st 0 k j) = 7 := tagFamily_tagCode range
    unfold H8.visTag at vis
    simp only [hfam] at vis
    exact vis

/-- **A cold pad site's event depends on the cold pads only.** -/
theorem cold_match (u : AffineInput) (τ τ' : Targets) (cold : coldOfPads u τ.1 = coldOfPads u τ'.1) {κ i ρ : ℕ}
    (away : ∀ h : i < Tb.count, ρ < Tb.modulus ⟨i, h⟩ ∧ ρ ≠ coordValue u κ % Tb.modulus ⟨i, h⟩) :
    PadLaw.matchSite τ.1 (.pad κ i ρ) = PadLaw.matchSite τ'.1 (.pad κ i ρ) := by
  have same : ∀ (h : i < Tb.count) (e : BMR.Enc), BMR.coordOf e = κ →
      τ.1 ⟨i, h⟩ (ρ : ZMod (Tb.modulus ⟨i, h⟩)) e = τ'.1 ⟨i, h⟩ (ρ : ZMod (Tb.modulus ⟨i, h⟩)) e := by
    intro h e coord
    obtain ⟨lt, ne⟩ := away h
    have hne : (ρ : ZMod (Tb.modulus ⟨i, h⟩)) ≠ BMR.hotRes Tb u e ⟨i, h⟩ := by
      intro eq
      have vals := congrArg ZMod.val eq
      unfold BMR.hotRes at vals
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt lt, coord] at vals
      exact ne vals
    exact congrFun (congrFun (congrFun cold ⟨i, h⟩) e) ⟨_, hne⟩
  simp only [PadLaw.matchSite]
  split_ifs with h zero one
  · subst zero
    ext a
    simp only [Set.mem_ofPred_eq]
    exact forall_congr' fun x => by rw [same h (.inl x) rfl]
  · subst one
    ext a
    simp only [Set.mem_ofPred_eq]
    exact forall_congr' fun y => by rw [same h (.inr y) rfl]
  · rfl
  · rfl

/-- The kernel's answers at the visible tags agree when the targets agree at every site holding a visible tag. -/
theorem given_map_eq (u : AffineInput) (τ τ' : Targets)
    (agree : ∀ s ∈ crtLayout.sites, (∃ tag : H8.BmrTags Tb u, tag.1.1 ∈ Laws.sitePos crtLayout s) →
      matchT τ s = matchT τ' s) :
    (given τ).map (restrictBmr u) = (given τ').map (restrictBmr u) := by
  refine map_condLaw _ _ targets_uniform (restrictBmr u) τ τ' fun z => ?_
  have e : ∀ σ : Targets, {x | restrictBmr u x = z ∧ bmrTargetsOf x = σ} =
      {t | (∀ tag : H8.BmrTags Tb u, t tag.1.1 = z tag) ∧ bmrTargetsOf t = σ} := by
    intro σ
    ext t
    simp only [Set.mem_ofPred_eq, restrictBmr, funext_iff]
  rw [e, e]
  exact swapped_event_eq (fun tag : H8.BmrTags Tb u => tag.1.1) z τ τ' agree

/-- On the curve: the cold pads and the masks decide every site holding a visible tag. -/
theorem agree_on (u : AffineInput) (τ τ' : Targets) (cold : coldOfPads u τ.1 = coldOfPads u τ'.1)
    (masks : τ.2 = τ'.2) :
    ∀ s ∈ crtLayout.sites, (∃ tag : H8.BmrTags Tb u, tag.1.1 ∈ Laws.sitePos crtLayout s) →
      matchT τ s = matchT τ' s := by
  rintro s member ⟨tag, inside⟩
  rcases visible_site u member tag inside with ⟨κ, i, ρ, rfl, away⟩ | ⟨st, k, rfl, -⟩
  · show PadLaw.matchSite τ.1 _ ∩ _ = PadLaw.matchSite τ'.1 _ ∩ _
    rw [cold_match u τ τ' cold away]
    rfl
  · show PadLaw.matchSite τ.1 _ ∩ maskMatch (maskInv τ.2) _ = PadLaw.matchSite τ'.1 _ ∩ maskMatch (maskInv τ'.2) _
    rw [masks]
    rfl

/-- Off the curve: the cold pads alone decide every site holding a visible tag. -/
theorem agree_off (u : AffineInput) (τ τ' : Targets) (off : validate u = false)
    (cold : coldOfPads u τ.1 = coldOfPads u τ'.1) :
    ∀ s ∈ crtLayout.sites, (∃ tag : H8.BmrTags Tb u, tag.1.1 ∈ Laws.sitePos crtLayout s) →
      matchT τ s = matchT τ' s := by
  rintro s member ⟨tag, inside⟩
  rcases visible_site u member tag inside with ⟨κ, i, ρ, rfl, away⟩ | ⟨st, k, rfl, on⟩
  · show PadLaw.matchSite τ.1 _ ∩ _ = PadLaw.matchSite τ'.1 _ ∩ _
    rw [cold_match u τ τ' cold away]
    rfl
  · rw [off] at on
    cases on

end BmrKernel

/-- **The swapped table as uniform targets and a kernel**. -/
def crtKernel : TableKernel where
  given := BmrKernel.given
  law := (bind_condLaw _ _ BmrKernel.targets_uniform).symm
  reads τ table inside := by
    have same := condLaw_support _ _ BmrKernel.targets_uniform τ table inside
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
  visible u τ τ' cold masks := BmrKernel.given_map_eq u τ τ' (BmrKernel.agree_on u τ τ' cold masks)

/-- Off the curve the kernel's answers at the visible P45 tags depend only on the cold pads. -/
def KernelOff (K : TableKernel) : Prop :=
  ∀ (u : AffineInput) (τ τ' : Targets), validate u = false → coldOfPads u τ.1 = coldOfPads u τ'.1 →
    (K.given τ).map (restrictBmr u) = (K.given τ').map (restrictBmr u)

/-- **`KernelOff` for the kernel.** -/
theorem crtKernel_off : KernelOff crtKernel := fun u τ τ' off cold =>
  BmrKernel.given_map_eq u τ τ' (BmrKernel.agree_off u τ τ' off cold)

end

end Kriterion.CRT.Privacy.BmrSplit
