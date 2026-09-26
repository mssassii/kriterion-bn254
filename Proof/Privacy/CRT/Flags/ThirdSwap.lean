/-
**P8, the off-curve third swap** (`CrtThirdSwap`; xinshu's `MiddleOff` pattern, with the table in place of the tape).

`M'` and `M` differ only off the curve, in how the shadow's program is answered from the empty oracle: `M'` draws one
table from the swapped layout law and answers every fresh point by its tag (`tableRun`), `M` answers lazily
(`lazyRun`). So:

* **data processing** (`middleGame_table_etvDist_le`): two table laws give games within the laws' distance;
* **a uniform table is the lazy oracle** (`uniform_runTable`), for a program that never asks two different points with
  one tag (`DistinctTagsFrom`): a fresh point's tag has not been read, so its table value is a fresh uniform answer
  (the table off that tag is untouched, `runTable_congr`, and splits off by `uniform_update`);
* the swapped law is within `padSwapError` of the uniform table (`etvDist_swappedTableLaw_le` and
  `SwapLayoutFacts.total`).

`crtThirdSwap_of`: `CrtThirdSwap E shadow` from the layout's swap facts and the distinct-tags fact of the shadow's
off-curve program (for `crtEntry`, `Entry.reachCM`'s path: a query-structure fact).
-/

import Proof.Privacy.CRT.PublicFirst.Obligation
import Proof.Privacy.CRT.PublicFirst.Coupling
import Proof.Privacy.CRT.Refill.Presample
import Proof.Privacy.CRT.Swap.Hop
import Proof.Privacy.CRT.Refill.Hop
import Proof.Privacy.CRT.Paths.Tags

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst
open Kriterion.CRT.Privacy.Refill (hashCode lookup_hash_eq hashQuery_eq lazyReader_eq uniform_update)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le_const etvDist_map_le')
open scoped ENNReal

noncomputable section

/-! ### 1. Distinct tags along a path -/

/-- **Along every path, two different asked points never share a tag** (`used`: the points asked, or stored, so
far). -/
def DistinctTagsFrom {α : Type} : List BaseField → CM α → Prop
  | _, .pure _ => True
  | used, .query input next =>
    (∀ y ∈ used, tagOfInput y = tagOfInput (input : BaseField) → y = (input : BaseField)) ∧
      ∀ answer, DistinctTagsFrom ((input : BaseField) :: used) (next answer)

/-! ### 2. The table reader and the lazy reader, point by point -/

section Readers

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

theorem tableReader_stored (table : TagTable) (input : ℕ) (σ : LazyOracle.State FI EI)
    (v : Fin (Fintype.card (Block × Block))) (found : σ.hash.lookup (input : BaseField) = some v) :
    tableReader table input σ = PMF.pure (hashCode.symm v, σ) := by
  unfold tableReader
  rw [lookup_hash_eq, found]
  rfl

theorem tableReader_fresh (table : TagTable) (input : ℕ) (σ : LazyOracle.State FI EI)
    (fresh : σ.hash.lookup (input : BaseField) = none) :
    tableReader table input σ = PMF.pure (table (tagOfInput (input : BaseField)),
      (LazyOracle.program (.hash (input : BaseField)) (table (tagOfInput (input : BaseField))) σ).getD σ) := by
  unfold tableReader
  rw [lookup_hash_eq, fresh]
  rfl

theorem lazyReader_stored (input : ℕ) (σ : LazyOracle.State FI EI) (v : Fin (Fintype.card (Block × Block)))
    (found : σ.hash.lookup (input : BaseField) = some v) :
    lazyReader input σ = PMF.pure (hashCode.symm v, σ) := by
  rw [lazyReader_eq, hashQuery_eq]
  simp only [HashTable.query, found, Draw.distribution, PMF.pure_map]

/-- The program of a fresh point prepends it. -/
theorem program_fresh (σ : LazyOracle.State FI EI) (x : BaseField) (a : Block × Block)
    (fresh : σ.hash.lookup x = none) :
    (LazyOracle.program (.hash x) a σ).getD σ = { σ with hash := (x, hashCode a) :: σ.hash } := by
  unfold LazyOracle.program
  simp only
  rw [if_pos fresh]
  rfl

theorem lazyReader_fresh (input : ℕ) (σ : LazyOracle.State FI EI)
    (fresh : σ.hash.lookup (input : BaseField) = none) :
    lazyReader input σ = (PMF.uniformOfFintype (Block × Block)).map fun a : Block × Block =>
      (a, (LazyOracle.program (.hash (input : BaseField)) a σ).getD σ) := by
  rw [lazyReader_eq, hashQuery_eq]
  simp only [HashTable.query, fresh, Draw.distribution, PMF.map_comp]
  rw [← uniformOfFintype_map_equiv hashCode.symm, PMF.map_comp]
  congr 1
  funext v
  simp only [Function.comp_apply, program_fresh σ _ _ fresh, Equiv.apply_symm_apply]

theorem stored_program_fresh (σ : LazyOracle.State FI EI) (x : BaseField) (a : Block × Block)
    (fresh : σ.hash.lookup x = none) :
    storedPoints ((LazyOracle.program (.hash x) a σ).getD σ) = x :: storedPoints σ := by
  rw [program_fresh σ x a fresh]
  rfl

end Readers

/-! ### 3. A uniform table is the lazy oracle -/

section Uniform

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- **The table is read only at the tags of fresh points**: two tables that agree off the tag of a stored, used
point give the same run. -/
theorem runTable_congr (T T' : TagTable) (tx : Fin (2 ^ 40)) (agree : ∀ tag, tag ≠ tx → T tag = T' tag)
    {α : Type} : ∀ (R : CM α) (used : List BaseField) (σ : LazyOracle.State FI EI) (x : BaseField),
      x ∈ used → tagOfInput x = tx → x ∈ storedPoints σ → DistinctTagsFrom used R →
        runReader (tableReader T) R σ = runReader (tableReader T') R σ
  | .pure _, _, _, _, _, _, _, _ => rfl
  | .query input next, used, σ, x, xUsed, xTag, xStored, distinct => by
    obtain ⟨freshOk, rest⟩ := distinct
    cases found : σ.hash.lookup (input : BaseField) with
    | some v =>
      simp only [runReader, tableReader_stored T input σ v found, tableReader_stored T' input σ v found,
        PMF.pure_bind]
      exact runTable_congr T T' tx agree (next _) ((input : BaseField) :: used) σ x
        (List.mem_cons_of_mem _ xUsed) xTag xStored (rest _)
    | none =>
      have different : x ≠ (input : BaseField) := by
        intro same
        have known := lookup_isSome_of_mem σ.hash x xStored
        rw [same, found] at known
        exact Bool.noConfusion known
      have tagDifferent : tagOfInput (input : BaseField) ≠ tx := fun same =>
        different (freshOk x xUsed (xTag.trans same.symm))
      simp only [runReader, tableReader_fresh T input σ found, tableReader_fresh T' input σ found,
        agree _ tagDifferent, PMF.pure_bind]
      refine runTable_congr T T' tx agree (next _) ((input : BaseField) :: used) _ x
        (List.mem_cons_of_mem _ xUsed) xTag ?_ (rest _)
      rw [stored_program_fresh σ _ _ found]
      exact List.mem_cons_of_mem _ xStored

/-- **A uniform table is the lazy oracle** for a program that never asks two different points with one tag. -/
theorem uniform_runTable {α : Type} : ∀ (R : CM α) (used : List BaseField) (σ : LazyOracle.State FI EI),
    (∀ y ∈ storedPoints σ, y ∈ used) → DistinctTagsFrom used R →
      (PMF.uniformOfFintype TagTable).bind (fun T => runReader (tableReader T) R σ) = runReader lazyReader R σ
  | .pure value, _, σ, _, _ => by
    simp only [runReader]
    exact PMF.bind_const _ _
  | .query input next, used, σ, sub, distinct => by
    obtain ⟨_, rest⟩ := distinct
    cases found : σ.hash.lookup (input : BaseField) with
    | some v =>
      simp only [runReader, tableReader_stored _ input σ v found, lazyReader_stored input σ v found,
        PMF.pure_bind]
      exact uniform_runTable (next _) ((input : BaseField) :: used) σ
        (fun y member => List.mem_cons_of_mem _ (sub y member)) (rest _)
    | none =>
      let after : (Block × Block) → LazyOracle.State FI EI := fun a =>
        (LazyOracle.program (.hash (input : BaseField)) a σ).getD σ
      have storedAfter : ∀ a, storedPoints (after a) = (input : BaseField) :: storedPoints σ := fun a =>
        stored_program_fresh σ _ a found
      have subAfter : ∀ a, ∀ y ∈ storedPoints (after a), y ∈ (input : BaseField) :: used := by
        intro a y member
        rw [storedAfter a] at member
        rcases List.mem_cons.mp member with same | old
        · rw [same]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (sub y old)
      have left : (PMF.uniformOfFintype TagTable).bind
          (fun T => runReader (tableReader T) (.query input next) σ) =
          (PMF.uniformOfFintype TagTable).bind fun T0 => (PMF.uniformOfFintype (Block × Block)).bind fun a =>
            runReader (tableReader T0) (next a) (after a) := by
        simp only [runReader, tableReader_fresh _ input σ found, PMF.pure_bind]
        conv_lhs => rw [← uniform_update (tagOfInput (input : BaseField))]
        rw [PMF.bind_bind]
        refine congrArg _ (funext fun T0 => ?_)
        rw [PMF.bind_map]
        refine congrArg _ (funext fun a => ?_)
        simp only [Function.comp_apply, Function.update_self]
        exact runTable_congr (Function.update T0 (tagOfInput (input : BaseField)) a) T0
          (tagOfInput (input : BaseField)) (fun tag different => Function.update_of_ne different a T0) (next a)
          ((input : BaseField) :: used) (after a) (input : BaseField) List.mem_cons_self rfl
          (by rw [storedAfter a]; exact List.mem_cons_self) (rest a)
      rw [left, PMF.bind_comm]
      have right : runReader lazyReader (.query input next) σ =
          (PMF.uniformOfFintype (Block × Block)).bind fun a => runReader lazyReader (next a) (after a) := by
        simp only [runReader, lazyReader_fresh input σ found]
        rw [PMF.bind_map]
        rfl
      rw [right]
      refine congrArg _ (funext fun a => ?_)
      exact uniform_runTable (next a) ((input : BaseField) :: used) (after a) (subAfter a) (rest a)

/-- **With a uniform table, `tableRun` is `lazyRun`.** -/
theorem tableRun_uniform (program : CM Unit) (distinct : DistinctTagsFrom [] program) :
    tableRun (FI := FI) (EI := EI) (PMF.uniformOfFintype TagTable) program = lazyRun program :=
  uniform_runTable program [] LazyOracle.empty (fun _ member => by simp [storedPoints, LazyOracle.empty] at member)
    distinct

end Uniform

/-! ### 4. The games -/

variable {FI EI : Type} (E : CrtEntry FI EI)

section Games

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **Data processing**: two table laws give middle games within the laws' distance. -/
theorem middleGame_table_etvDist_le (shadow : CrtShadow (viewHere E).Source FI EI) (first second : PMF TagTable)
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) :
    (middleGame E shadow (tableRun first) adversary parameter scalar).etvDist
        (middleGame E shadow (tableRun second) adversary parameter scalar) ≤ first.etvDist second := by
  unfold middleGame
  refine etvDist_bind_left_le_const _ _ _ _ fun source => ?_
  refine etvDist_bind_left_le_const _ _ _ _ fun selected => ?_
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  generalize (E.scheme inferInstance inferInstance).function scalar selected.1.1 = output
  cases output with
  | some target =>
    simp only [middleStage2, PMF.etvDist_self]
    exact zero_le
  | none =>
    simp only [middleStage2]
    refine etvDist_bind_left_le_const _ _ _ _ fun coin => ?_
    refine le_trans (etvDist_map_le' _ _ _) ?_
    exact PMF.etvDist_bind_right_le _ _ _

/-- **With a uniform table, `M'` is `M`.** -/
theorem middleGame_uniform (shadow : CrtShadow (viewHere E).Source FI EI)
    (distinct : ∀ source u coin, DistinctTagsFrom [] (shadow.offCurve source u coin))
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) :
    middleGame E shadow (tableRun (PMF.uniformOfFintype TagTable)) adversary parameter scalar =
      middleGame E shadow lazyRun adversary parameter scalar := by
  unfold middleGame middleStage2
  simp only [tableRun_uniform _ (distinct _ _ _)]

/-- **The third swap at one instance.** -/
theorem middleGame_swap_etvDist_le (facts : SwapLayoutFacts E.layout)
    (shadow : CrtShadow (viewHere E).Source FI EI)
    (distinct : ∀ source u coin, DistinctTagsFrom [] (shadow.offCurve source u coin))
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) :
    (middleGame E shadow (tableRun (swappedTableLaw E.layout)) adversary parameter scalar).etvDist
        (middleGame E shadow lazyRun adversary parameter scalar) ≤ ENNReal.ofReal padSwapError := by
  rw [← middleGame_uniform E shadow distinct]
  calc _ ≤ (swappedTableLaw E.layout).etvDist (PMF.uniformOfFintype TagTable) :=
        middleGame_table_etvDist_le E shadow _ _ adversary parameter scalar
    _ = (PMF.uniformOfFintype TagTable).etvDist (swappedTableLaw E.layout) := PMF.etvDist_comm _ _
    _ ≤ (E.layout.sites.map facts.bias).sum := etvDist_swappedTableLaw_le E.layout facts
    _ ≤ ENNReal.ofReal padSwapError := facts.total

end Games

/-- **`CrtThirdSwap`** (P8) from the layout's swap facts and the distinct-tags fact of the shadow's off-curve
program. -/
theorem crtThirdSwap_of [fixedFinite : Finite FI] [encFinite : Finite EI] (facts : SwapLayoutFacts E.layout)
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI)
    (distinct : ∀ [FieldCertificate] [GroupCertificate] (source : (viewHere E).Source) (u : AffineInput)
      (coin : shadow.Coin), DistinctTagsFrom [] (shadow.offCurve source u coin)) :
    CrtThirdSwap E shadow := by
  intro field group adversary parameter scalar _
  letI := field
  letI := group
  letI := @Fintype.ofFinite FI fixedFinite
  letI := @Fintype.ofFinite EI encFinite
  letI := Classical.decEq FI
  letI := Classical.decEq EI
  have bound := middleGame_swap_etvDist_le E facts shadow (fun source u coin => distinct source u coin)
    adversary parameter scalar
  calc _ ≤ (ENNReal.ofReal padSwapError).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
    _ = padSwapError := ENNReal.toReal_ofReal padSwapError_nonneg

/-! ### 5. Distinct tags from `Tagged` -/

section Tagged

open Kriterion.CRT.Paths

/-- The tag of a labelled input in range is its tag. -/
theorem tagOfInput_hashInput (label : Block) (code : ℕ) (small : code < 2 ^ 40) :
    tagOfInput ((hashInput label code : ℕ) : BaseField) = ⟨code, small⟩ := by
  have bound : hashInput label code < baseFieldModulus :=
    lt_trans (Refill.point_lt label.isLt small) Refill.baseFieldModulus_gt
  apply Fin.ext
  show ((hashInput label code : ℕ) : BaseField).val / 2 ^ 128 % 2 ^ 40 = code
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt bound]
  unfold hashInput
  rw [Refill.point_div label.isLt, Nat.mod_eq_of_lt small]

/-- The points of a key history. -/
def seenPoints (seen : List (TagKey × Block)) : List BaseField :=
  seen.map fun p => ((hashInput p.2 p.1.code : ℕ) : BaseField)

/-- **A tag run asks pairwise distinct tags.** -/
theorem distinct_of_keyRun {α : Type} {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop}
    {seen : List (TagKey × Block)} {R : CM α} (run : KeyRun S Q seen R) :
    (∀ p ∈ seen, p.1.InRange) → DistinctTagsFrom (seenPoints seen) R := by
  induction run with
  | pure seen value post =>
    intro _
    trivial
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
    intro ranges
    refine ⟨?_, fun answer => ?_⟩
    · intro y yMember sameTag
      exfalso
      obtain ⟨p, pMember, rfl⟩ := List.mem_map.mp yMember
      rw [tagOfInput_hashInput _ _ (TagKey.code_lt (ranges p pMember)), ← coded,
        tagOfInput_hashInput _ _ (TagKey.code_lt range)] at sameTag
      have same : p.1 = key := TagKey.code_injective (ranges p pMember) range (Fin.mk.inj_iff.mp sameTag)
      exact fresh (same ▸ List.mem_map_of_mem pMember)
    · have next' := ih answer fun p member => by
        rcases List.mem_cons.mp member with same | old
        · rw [same]
          exact range
        · exact ranges p old
      have points : seenPoints ((key, label) :: seen) =
          ((hashInput label tag : ℕ) : BaseField) :: seenPoints seen := by
        simp only [seenPoints, List.map_cons, coded]
      rw [points] at next'
      exact next'

/-- **A `Tagged` program asks pairwise distinct tags.** -/
theorem distinctTagsFrom_of_tagged {α : Type} {S : Set TagKey} {R : CM α} (tagged : Tagged S R) :
    DistinctTagsFrom [] R :=
  distinct_of_keyRun tagged fun _ member => absurd member List.not_mem_nil

/-- **`CrtThirdSwap`** from the layout's swap facts and `Tagged` for the shadow's off-curve program. -/
theorem crtThirdSwap_of_tagged {FI EI : Type} (E : CrtEntry FI EI) [Finite FI] [Finite EI]
    (facts : SwapLayoutFacts E.layout)
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI)
    (tagged : ∀ [FieldCertificate] [GroupCertificate] (source : (viewHere E).Source) (u : AffineInput)
      (coin : shadow.Coin), ∃ S : Set TagKey, Tagged S (shadow.offCurve source u coin)) :
    CrtThirdSwap E shadow :=
  crtThirdSwap_of E facts shadow fun source u coin =>
    distinctTagsFrom_of_tagged (tagged source u coin).choose_spec

end Tagged

end

end Kriterion.CRT.Privacy.Flags
