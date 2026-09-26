/-
**The configuration-E garbler is `Tagged`**: along every path of `Entry.garbleCM`, every query is a
labelled input `hashInput label (tagCode …)` with its fields in range, the tags are pairwise distinct, and each site
is asked at one label (`garbleCM_tagged`).
-/

import Proof.Privacy.CRT.Paths.Gadgets
import Proof.Privacy.CRT.Paths.Table
import Construction.CRT.Entry

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-! ### Sites of two key sets -/

/-- Two key sets share no site when their pad keys differ in the pad fields and their mask keys in the mask fields. -/
theorem siteDisjoint_of_fields {S S' : Set TagKey}
    (pads : ∀ k ∈ S, ∀ k' ∈ S', k.fam = 6 → k'.fam = 6 → k.coord ≠ k'.coord ∨ k.idx ≠ k'.idx ∨ k.slot ≠ k'.slot)
    (masks : ∀ k ∈ S, ∀ k' ∈ S', k.fam = 7 → k'.fam = 7 → k.stage ≠ k'.stage ∨ k.slot ≠ k'.slot) :
    SiteDisjoint S S' := by
  intro k inS k' inS' same
  rcases site_cases k with ⟨six, hk⟩ | ⟨seven, hk⟩ | ⟨_, _, none⟩
  · rcases site_cases k' with ⟨six', hk'⟩ | ⟨_, hk'⟩ | ⟨_, _, none'⟩
    · rw [hk, hk'] at same
      simp only [Option.some.injEq, Privacy.SiteId.pad.injEq] at same
      rcases pads k inS k' inS' six six' with c | c | c <;> simp_all
    · rw [hk, hk'] at same
      simp at same
    · rw [hk, none'] at same
      simp at same
  · rcases site_cases k' with ⟨_, hk'⟩ | ⟨seven', hk'⟩ | ⟨_, _, none'⟩
    · rw [hk, hk'] at same
      simp at same
    · rw [hk, hk'] at same
      simp only [Option.some.injEq, Privacy.SiteId.mask.injEq] at same
      rcases masks k inS k' inS' seven seven' with c | c <;> simp_all
    · rw [hk, none'] at same
      simp at same
  · exact none

/-! ### The garbler -/

/-- The digest keys of the entry (254 positions, 91 digits). -/
def digestKeys : Set TagKey := digestLabelKeys coordinateBitCount ∪ digestFinalKeys digitCount

/-- The keys of the garbler after the coordinates: the key, the masks, the digest. -/
def tailKeys : Set TagKey := {keyKey} ∪ (maskKeys digitCount ∪ digestKeys)

/-- **The keys of the garbler.** -/
def garblerKeys : Set TagKey := coordKeys 0 ∪ (coordKeys 1 ∪ tailKeys)

theorem tail_fams : ∀ k ∈ tailKeys, 7 ≤ k.fam := by
  rintro k (inKey | inMask | inDigest)
  · rw [Set.mem_singleton_iff.mp inKey]; decide
  · simp only [maskKeys, nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq]
      at inMask
    omega
  · simp only [digestKeys, digestLabelKeys, digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at inDigest
    omega

/-- **The configuration-E garbler is `Tagged`.** -/
theorem garbleCM_tagged (scalar : BN254.NonZeroScalar) (coins : Entry.Coins) :
    Tagged garblerKeys (Entry.garbleCM scalar coins) := by
  unfold Entry.garbleCM
  dsimp only
  have ranges : ∀ S, S ≤ 1000 → TableRanges Entry.table S := bn254_ranges
  refine Tagged.bind' (coordGarbleM_tagged Entry.table Entry.xCount 0 (ranges _ (by decide)) (by norm_num) _ _)
    (S' := coordKeys 1 ∪ tailKeys) (fun gx => ?_) ?_ ?_ le_rfl
  · refine Tagged.bind' (coordGarbleM_tagged Entry.table Entry.yCount 1 (ranges _ (by decide)) (by norm_num) _ _)
      (S' := tailKeys) (fun gy => ?_) ?_ ?_ le_rfl
    · refine Tagged.bind' (keyM_tagged _) (S' := maskKeys digitCount ∪ digestKeys) (fun K => ?_) ?_ ?_ le_rfl
      · refine Tagged.bind' (maskAnswersM_tagged K digitCount (by decide) (by decide)) (S' := digestKeys)
          (fun masks => Tagged.bind_pure (digestGarbleM_tagged coordinateBitCount digitCount (by decide)
            (by decide) _ _ _ _ _) _) ?_ ?_ le_rfl
        · refine Set.disjoint_left.mpr fun k inM inD => ?_
          simp only [maskKeys, nonCollectorKeys, maskStageKeys, maskSiteKeys, digestKeys, digestLabelKeys,
            digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at inM inD
          omega
        · refine siteDisjoint_of_fields (fun k _ k' inD _ six' => ?_) (fun k _ k' inD _ seven' => ?_)
          · simp only [digestKeys, digestLabelKeys, digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at inD
            omega
          · simp only [digestKeys, digestLabelKeys, digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at inD
            omega
      · refine Set.disjoint_left.mpr fun k inK inR => ?_
        rw [Set.mem_singleton_iff.mp inK] at inR
        simp only [keyKey, maskKeys, nonCollectorKeys, maskStageKeys, maskSiteKeys, digestKeys, digestLabelKeys,
          digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at inR
        omega
      · exact siteDisjoint_of_fam fun k inK => by
          rw [Set.mem_singleton_iff.mp inK]; exact ⟨by decide, by decide⟩
    · refine Set.disjoint_left.mpr fun k inC inT => ?_
      have := tail_fams k inT
      simp only [coordKeys, Set.mem_setOf_eq] at inC
      omega
    · refine siteDisjoint_of_fields (fun k _ k' inT _ six' => ?_) (fun k inC k' _ seven _ => ?_)
      · have := tail_fams k' inT
        omega
      · simp only [coordKeys, Set.mem_setOf_eq] at inC
        omega
  · refine Set.disjoint_left.mpr fun k inC inR => ?_
    simp only [coordKeys, Set.mem_setOf_eq] at inC
    rcases inR with inC' | inT
    · simp only [coordKeys, Set.mem_setOf_eq] at inC'
      omega
    · have := tail_fams k inT
      omega
  · refine siteDisjoint_of_fields (fun k inC k' inR six six' => ?_) (fun k inC k' _ seven _ => ?_)
    · simp only [coordKeys, Set.mem_setOf_eq] at inC
      rcases inR with inC' | inT
      · simp only [coordKeys, Set.mem_setOf_eq] at inC'
        left
        omega
      · have := tail_fams k' inT
        omega
    · simp only [coordKeys, Set.mem_setOf_eq] at inC
      omega

end Kriterion.CRT.Paths
