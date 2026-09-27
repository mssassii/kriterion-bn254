/-
**The key, the masks and the digest are `Tagged`**: the key query (family 10), the mask
sites (family 7, one label `K` per site), the digest labels (family 8) and finals (family 9).
-/

import Proof.Privacy.CRT.Paths.Garbler
import Construction.CRT.Mask
import Construction.CRT.Digest

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC

/-! ### The key -/

/-- The key's one key. -/
def keyKey : TagKey := ⟨10, 0, 0, 0, 0, 0, 0⟩

theorem keyKey_range : keyKey.InRange := by
  unfold keyKey TagKey.InRange
  norm_num

/-- **The key query**: one labelled query of family 10. -/
theorem keyM_tagged (t : BN254.BaseField) : Tagged ({keyKey} : Set TagKey) (keyM t) := by
  unfold keyM maskKeyInput
  exact Tagged.bind_pure (Tagged.askN ({keyKey} : Set TagKey) _ maskKeyTag keyKey rfl rfl keyKey_range) _

/-! ### Mask sites -/

/-- The keys of mask site `(stage, site)`, `count` answers. -/
def maskSiteKeys (stage site count : Nat) : Set TagKey :=
  {k | k.fam = 7 ∧ k.coord = 0 ∧ k.idx = 0 ∧ k.stage = stage ∧ k.level = 0 ∧ k.slot = site ∧ k.part < count}

/-- The keys of the mask sites of `stage` below `sites`, `count` answers each. -/
def maskStageKeys (stage sites count : Nat) : Set TagKey :=
  {k | k.fam = 7 ∧ k.coord = 0 ∧ k.idx = 0 ∧ k.stage = stage ∧ k.level = 0 ∧ k.slot < sites ∧ k.part < count}

/-- **One mask site**: `count ≤ 64` answers at the label `K`. -/
theorem siteAnswersM_tagged (K : Block) (stage site count : Nat) (stageLt : stage < 4) (siteLt : site < 65536)
    (countLe : count ≤ 64) : Tagged (maskSiteKeys stage site count) (siteAnswersM K stage site count) := by
  unfold siteAnswersM
  refine (Tagged.oneLabelTable K _ count (fun part => ⟨7, 0, 0, stage, 0, site, part⟩) (fun _ _ => rfl)
    (fun part small => ⟨by norm_num, by norm_num, by norm_num, stageLt, by norm_num, siteLt,
      show part < 64 by omega⟩)
    fun i j _ _ same => by cases same; rfl).mono ?_
  rintro k ⟨part, small, same⟩
  rw [same]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, small⟩

/-- The mask sites of one stage, `count` answers each. -/
theorem maskSites_tagged {α : Type} (K : Block) (stage sites count : Nat) (stageLt : stage < 4)
    (sitesLe : sites ≤ 65536) (countLe : count ≤ 64) (read : (Fin count → Block × Block) → α) :
    Tagged (maskStageKeys stage sites count)
      (CRT.tableM sites fun site => siteAnswersM K stage site.val count >>= fun answers => pure (read answers)) := by
  refine (Tagged.tableM (S := fun site => maskSiteKeys stage site count) sites
    (fun site => Tagged.bind_pure (siteAnswersM_tagged K stage site.val count stageLt (by omega) countLe) _)
    fun i j _ _ different => ⟨?_, ?_⟩).mono ?_
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [maskSiteKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · intro k inI k' inJ sameSite
    simp only [maskSiteKeys, Set.mem_setOf_eq] at inI inJ
    rw [site_mask inI.1, site_mask inJ.1] at sameSite
    simp only [Option.some.injEq, Privacy.SiteId.mask.injEq] at sameSite
    omega
  · rintro k ⟨site, small, inS⟩
    simp only [maskSiteKeys, maskStageKeys, Set.mem_setOf_eq] at inS ⊢
    omega

/-- Mask keys of different (stage, site) ranges share no site. -/
theorem maskKeys_siteDisjoint {S S' : Set TagKey} (hS : ∀ k ∈ S, k.fam = 7) (hS' : ∀ k ∈ S', k.fam = 7)
    (different : ∀ k ∈ S, ∀ k' ∈ S', k.stage ≠ k'.stage ∨ k.slot ≠ k'.slot) : SiteDisjoint S S' := by
  intro k inS k' inS' sameSite
  rw [site_mask (hS k inS), site_mask (hS' k' inS')] at sameSite
  simp only [Option.some.injEq, Privacy.SiteId.mask.injEq] at sameSite
  rcases different k inS k' inS' with stage | slot
  · exact absurd sameSite.1 stage
  · exact absurd sameSite.2 slot

/-- The keys of the non-collector mask sites (stage 1: the pairs, three answers, then the single site, two, if
there is one). -/
def nonCollectorKeys (digits : Nat) : Set TagKey :=
  maskStageKeys 1 (pairSites digits) 3 ∪ maskSiteKeys 1 (pairSites digits) (2 * singleSites digits)

/-- **The non-collector masks** (route M's replay part). -/
theorem nonCollectorMasksM_tagged (K : Block) (digits : Nat) (small : pairSites digits < 65536) :
    Tagged (nonCollectorKeys digits) (nonCollectorMasksM K digits) := by
  unfold nonCollectorMasksM pairMasksM singleMaskM
  refine Tagged.bind' (maskSites_tagged K 1 (pairSites digits) 3 (by norm_num) (by omega) (by norm_num) _)
    (S' := maskSiteKeys 1 (pairSites digits) (2 * singleSites digits)) (fun pairs => ?_) ?_ ?_ le_rfl
  · refine Tagged.bind_empty (Tagged.ite (fun one => ?_) fun _ => (Tagged.pure _ _).mono (Set.empty_subset _))
      fun _ => Tagged.pure _ _
    rw [one]
    exact Tagged.bind_pure (siteAnswersM_tagged K 1 _ 2 (by norm_num) small (by norm_num)) _
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [maskStageKeys, maskSiteKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · refine maskKeys_siteDisjoint (fun k inS => inS.1) (fun k inS => inS.1) fun k inS k' inS' => Or.inr ?_
    simp only [maskStageKeys, maskSiteKeys, Set.mem_setOf_eq] at inS inS'
    omega

/-- The keys of every mask site: the collectors (stage 0, two answers) and the non-collector sites. -/
def maskKeys (digits : Nat) : Set TagKey :=
  maskStageKeys 0 (collectorSites digits) 2 ∪ nonCollectorKeys digits

/-- **Every mask answer** (the garbler's masks). -/
theorem maskAnswersM_tagged (K : Block) (digits : Nat) (collectors : collectorSites digits ≤ 65536)
    (small : pairSites digits < 65536) : Tagged (maskKeys digits) (maskAnswersM K digits) := by
  unfold maskAnswersM collectorMasksM
  refine Tagged.bind' (maskSites_tagged K 0 (collectorSites digits) 2 (by norm_num) collectors (by norm_num) _)
    (fun collector => Tagged.bind_pure (nonCollectorMasksM_tagged K digits small) _) ?_ ?_ le_rfl
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inI inJ
    omega
  · refine maskKeys_siteDisjoint (fun k inS => inS.1) (fun k inS => ?_) fun k inS k' inS' => Or.inl ?_
    · simp only [nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inS
      omega
    · simp only [nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inS inS'
      omega

/-! ### The digest -/

/-- The keys of the digest labels (family 8): coordinate, position below `bits`, bit. -/
def digestLabelKeys (bits : Nat) : Set TagKey :=
  {k | k.fam = 8 ∧ k.coord < 2 ∧ k.idx = 0 ∧ k.stage = 0 ∧ k.level = 0 ∧ k.slot < bits ∧ k.part < 2}

/-- The keys of the digest finals (family 9): the final site below `2 * digits`. -/
def digestFinalKeys (digits : Nat) : Set TagKey :=
  {k | k.fam = 9 ∧ k.coord = 0 ∧ k.idx = 0 ∧ k.stage = 0 ∧ k.level = 0 ∧ k.slot < 2 * digits ∧ k.part = 0}

/-- The keys of digit `o`'s two final sites, `2 o` and `2 o + 1`. -/
def finalDigitKeys (o : Nat) : Set TagKey :=
  {k | k.fam = 9 ∧ k.coord = 0 ∧ k.idx = 0 ∧ k.stage = 0 ∧ k.level = 0 ∧ k.slot / 2 = o ∧ k.part = 0}

/-- The keys of one digest position (both bits). -/
def positionKeys (coord position : Nat) : Set TagKey :=
  {k | k.fam = 8 ∧ k.coord = coord ∧ k.idx = 0 ∧ k.stage = 0 ∧ k.level = 0 ∧ k.slot = position ∧ k.part < 2}

/-- Both digest labels of one position. -/
theorem digestPosition_tagged (coord position : Nat) (coordLt : coord < 2) (positionLt : position < 65536)
    (first second : Block) :
    Tagged (positionKeys coord position)
      (h128M first (digestLabelTag coord position 0) >>= fun a =>
        h128M second (digestLabelTag coord position 1) >>= fun b => pure (a, b)) := by
  have key0 : (⟨8, coord, 0, 0, 0, position, 0⟩ : TagKey).InRange :=
    ⟨by norm_num, coordLt, by norm_num, by norm_num, by norm_num, positionLt, by norm_num⟩
  have key1 : (⟨8, coord, 0, 0, 0, position, 1⟩ : TagKey).InRange :=
    ⟨by norm_num, coordLt, by norm_num, by norm_num, by norm_num, positionLt, by norm_num⟩
  have mem0 : (⟨8, coord, 0, 0, 0, position, 0⟩ : TagKey) ∈ positionKeys coord position :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by norm_num⟩
  have mem1 : (⟨8, coord, 0, 0, 0, position, 1⟩ : TagKey) ∈ positionKeys coord position :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by norm_num⟩
  refine Tagged.bind' (Tagged.h128M ({⟨8, coord, 0, 0, 0, position, 0⟩} : Set TagKey) first
    (digestLabelTag coord position 0) ⟨8, coord, 0, 0, 0, position, 0⟩ rfl rfl key0)
    (fun a => Tagged.bind_pure (Tagged.h128M ({⟨8, coord, 0, 0, 0, position, 1⟩} : Set TagKey) second
      (digestLabelTag coord position 1) ⟨8, coord, 0, 0, 0, position, 1⟩ rfl rfl key1) _) (Set.disjoint_singleton.mpr fun same => by cases same) (siteDisjoint_of_fam fun k inS => by
        rw [Set.mem_singleton_iff.mp inS]; exact ⟨by norm_num, by norm_num⟩) ?_
  rintro k (inS | inS)
  · rw [Set.mem_singleton_iff.mp inS]; exact mem0
  · rw [Set.mem_singleton_iff.mp inS]; exact mem1

/-- **The garbler's digest table**: both labels of every position of both coordinates. -/
theorem digestTableM_tagged (bits : Nat) (bitsLe : bits ≤ 65536) (zero : Fin 2 → Fin bits → Block)
    (delta : Fin 2 → Block) : Tagged (digestLabelKeys bits) (digestTableM bits zero delta) := by
  unfold digestTableM
  have coordTable : ∀ coord : Fin 2, Tagged {k | ∃ i < bits, k ∈ positionKeys coord.val i}
      (CRT.tableM bits fun position =>
        h128M (zero coord position) (digestLabelTag coord.val position.val 0) >>= fun first =>
          h128M (zero coord position ^^^ delta coord) (digestLabelTag coord.val position.val 1) >>= fun second =>
            pure (first, second)) := fun coord =>
    Tagged.tableM (S := fun position => positionKeys coord.val position) bits
      (fun position => digestPosition_tagged coord.val position.val coord.isLt
        (lt_of_lt_of_le position.isLt bitsLe) _ _)
      fun i j _ _ different => ⟨Set.disjoint_left.mpr fun k inI inJ => by
          simp only [positionKeys, Set.mem_setOf_eq] at inI inJ; omega,
        siteDisjoint_of_fam fun k inS => by
          simp only [positionKeys, Set.mem_setOf_eq] at inS; omega⟩
  refine (Tagged.tableM (S := fun coord => {k | ∃ i < bits, k ∈ positionKeys coord i}) 2 coordTable
    fun i j _ _ different => ⟨?_, ?_⟩).mono ?_
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    obtain ⟨_, _, inI⟩ := inI
    obtain ⟨_, _, inJ⟩ := inJ
    simp only [positionKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      obtain ⟨_, _, inS⟩ := inS
      simp only [positionKeys, Set.mem_setOf_eq] at inS
      omega
  · rintro k ⟨coord, coordLt, ⟨position, positionLt, inS⟩⟩
    simp only [positionKeys, digestLabelKeys, Set.mem_setOf_eq] at inS ⊢
    omega

/-- **The garbler's entry of one digit**: nothing for a zero digit, the two finals of its kinds otherwise. -/
theorem garbleEntryM_tagged {bits : Nat} (table : Fin 2 → Fin bits → Block × Block) (o : Nat) (oLt : o < 32768)
    (digit : Digit) (offset : BN254.AffineInput) (pad : Exception.Entry) :
    Tagged (finalDigitKeys o) (garbleEntryM table o digit offset pad) := by
  have key0 : (⟨9, 0, 0, 0, 0, 2 * o, 0⟩ : TagKey).InRange :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, show 2 * o < 65536 by omega, by norm_num⟩
  have key1 : (⟨9, 0, 0, 0, 0, 2 * o + 1, 0⟩ : TagKey).InRange :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, show 2 * o + 1 < 65536 by omega,
      by norm_num⟩
  unfold garbleEntryM
  split
  · exact Tagged.pure _ _
  · unfold finalMaskM
    dsimp only
    refine Tagged.bind' (Tagged.bind_pure (Tagged.h128M ({⟨9, 0, 0, 0, 0, 2 * o, 0⟩} : Set TagKey) _
        (digestFinalTag (2 * o)) ⟨9, 0, 0, 0, 0, 2 * o, 0⟩ rfl rfl key0) _)
      (S' := {⟨9, 0, 0, 0, 0, 2 * o + 1, 0⟩})
      (fun _ => Tagged.bind_pure (Tagged.bind_pure (Tagged.h128M ({⟨9, 0, 0, 0, 0, 2 * o + 1, 0⟩} : Set TagKey)
        _ (digestFinalTag (2 * o + 1)) ⟨9, 0, 0, 0, 0, 2 * o + 1, 0⟩ rfl rfl key1) _) _)
      (Set.disjoint_singleton.mpr fun same => by simp only [TagKey.mk.injEq] at same; omega)
      (siteDisjoint_of_fam fun k inS => by rw [Set.mem_singleton_iff.mp inS]; exact ⟨by norm_num, by norm_num⟩) ?_
    rintro k (inS | inS) <;> rw [Set.mem_singleton_iff.mp inS]
    · exact ⟨rfl, rfl, rfl, rfl, rfl, show 2 * o / 2 = o by omega, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, show (2 * o + 1) / 2 = o by omega, rfl⟩

/-- **The garbler's digest**: the table, then the two finals of every nonzero digit. -/
theorem digestGarbleM_tagged (bits digits : Nat) (bitsLe : bits ≤ 65536) (digitsLe : digits ≤ 32768)
    (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block) (digitOf : Fin digits → Digit)
    (offsetOf : Fin digits → BN254.AffineInput) (padOf : Fin digits → Exception.Entry) :
    Tagged (digestLabelKeys bits ∪ digestFinalKeys digits)
      (digestGarbleM bits digits zero delta digitOf offsetOf padOf) := by
  unfold digestGarbleM
  refine Tagged.bind' (digestTableM_tagged bits bitsLe zero delta) (fun table => ?_) ?_ ?_ le_rfl
  · refine (Tagged.tableM (S := finalDigitKeys) digits
      (fun o => garbleEntryM_tagged table o.val (by have := o.isLt; omega) _ _ _)
      fun i j _ _ different => ⟨Set.disjoint_left.mpr fun k inI inJ => by
          simp only [finalDigitKeys, Set.mem_setOf_eq] at inI inJ; omega,
        siteDisjoint_of_fam fun k inS => by
          simp only [finalDigitKeys, Set.mem_setOf_eq] at inS; omega⟩).mono ?_
    rintro k ⟨o, small, inS⟩
    simp only [finalDigitKeys, digestFinalKeys, Set.mem_setOf_eq] at inS ⊢
    omega
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [digestLabelKeys, digestFinalKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [digestLabelKeys, Set.mem_setOf_eq] at inS
      omega

end Kriterion.CRT.Paths
