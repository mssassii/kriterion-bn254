/-
**P6a2 for H8: `CrtUpperFactor`** (`Core/H8.lean`, row (A)).

`CrtUpperFactor E T` says that `G1U°`'s stage-2 mass, averaged over the swapped tape, is at least the law of the real
view (`realCore`, flagged on doubling) integrated against the view's stage-2 weight (`viewWeight`: the reach's entries
at the visible tags, read on the view's table, installed into the stage-1 state). This file proves it from one named
fact of the entry, `ViewEntriesPerm`: off doubling, the entries `G1U°` installs (`designedEntries`) are the view's
entries up to order, hash entries at pairwise distinct inputs. The fact is the containment of the designed rule in the
reach (H5) read with the tag rule (`crtDesigned_eq_visTag`) and the view table (the reach's visible points do not depend
on its invisible answers); it is discharged on the concrete entry.

* `upperWeight_eq_viewWeight`: per tape off doubling, `upperWeight` is the view's weight (`installEntries_perm`,
  `run_lookup_congr`);
* `crtUpperFactor_of`: push the tape sum forward to the view.
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Laws.ReplayOff

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.H8
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

/-- **The named fact behind P6a2**: off doubling, the entries `G1U°` installs at `u` are the view's entries up to
order, and they are hash entries at pairwise distinct inputs. -/
def ViewEntriesPerm (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput),
    ¬ Doubling E scalar tape u →
      (designedEntries E T parameter scalar tape u).Perm (viewEntries E T u (realView E T parameter scalar u tape)) ∧
        HashEntries (designedEntries E T parameter scalar tape u) ∧
        ((designedEntries E T parameter scalar tape u).map entryInput).Nodup

section Weights

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **Per tape off doubling, `G1U°`'s stage-2 weight is the view's.** -/
theorem upperWeight_eq_viewWeight (T : CrtTable) (facts : ViewEntriesPerm E T) (parameter : ℕ)
    (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput) (planted : LazyOracle.State FI EI)
    {budget : ℕ} (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (b : Bool) (noDoubling : ¬ Doubling E scalar tape u) :
    upperWeight E T parameter scalar tape u planted decide b =
      viewWeight E T u (realView E T parameter scalar u tape) planted decide b := by
  obtain ⟨perm, hashes, distinct⟩ := facts parameter scalar tape u noDoubling
  have same := run_lookup_congr (decide (realView E T parameter scalar u tape).1
      (realView E T parameter scalar u tape).2.1) _ _
    (installEntries_perm perm hashes distinct planted)
  unfold upperWeight viewWeight
  exact congrFun (congrArg DFunLike.coe same) b

end Weights

/-- The visibility of an entry by its tag (`false` for a non-hash entry). -/
def entryVisible (T : CrtTable) (u : AffineInput) (entry : Entry FI EI) : Bool :=
  match entry.1 with
  | .hash x => visTag T u (x.val / 2 ^ 128)
  | _ => false

/-- **`ViewEntriesPerm` from primitive facts**: every garbler entry is a hash entry whose tag family is at most 10
(so the designed rule is the tag rule off doubling, `crtDesigned_eq_visTag`); the garbler's inputs are pairwise
distinct and so are the view's entries; and off doubling the garbler's visible entries are exactly the view's entries
(containment of the designed rule in the reach, H5, with its converse on the curve, and the reach's visible points
read the same on the view table). -/
theorem viewEntriesPerm_of (T : CrtTable)
    (small : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
      (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E),
      ∀ entry ∈ garblerEntries E parameter scalar tape, ∃ x, entry.1 = .hash x ∧ tagFamily (x.val / 2 ^ 128) ≤ 10)
    (distinct : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
      (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E),
      ((garblerEntries E parameter scalar tape).map entryInput).Nodup)
    (viewOnce : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
      (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput),
      (viewEntries E T u (realView E T parameter scalar u tape)).Nodup)
    (sameVisible : ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI]
      [DecidableEq EI] (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput),
      ¬ Doubling E scalar tape u → ∀ entry,
        (entry ∈ garblerEntries E parameter scalar tape ∧ entryVisible T u entry = true) ↔
          entry ∈ viewEntries E T u (realView E T parameter scalar u tape)) :
    ViewEntriesPerm E T := by
  intro _ _ _ _ _ _ parameter scalar tape u noDoubling
  have ruleEq : designedEntries E T parameter scalar tape u =
      (garblerEntries E parameter scalar tape).filter (entryVisible T u) := by
    unfold designedEntries
    refine List.filter_congr fun entry member => ?_
    obtain ⟨x, hx, fam⟩ := small parameter scalar tape entry member
    obtain ⟨q, answer⟩ := entry
    simp only at hx
    subst hx
    rw [crtDesigned_eq_visTag T _ scalar _ u x answer fam fun o same => noDoubling ⟨o, same⟩]
    rfl
  have garblerHash : HashEntries (garblerEntries E parameter scalar tape) := fun entry member => by
    obtain ⟨x, hx, -⟩ := small parameter scalar tape entry member
    exact ⟨x, hx⟩
  have garblerNodup : (garblerEntries E parameter scalar tape).Nodup :=
    (distinct parameter scalar tape).of_map _
  rw [ruleEq]
  refine ⟨(List.perm_ext_iff_of_nodup (garblerNodup.filter _) (viewOnce parameter scalar tape u)).mpr
      fun entry => ?_, fun entry member => garblerHash entry (List.mem_of_mem_filter member),
    (distinct parameter scalar tape).sublist (List.Sublist.map _ List.filter_sublist)⟩
  rw [List.mem_filter]
  exact sameVisible parameter scalar tape u noDoubling entry

/-- **P6a2: `CrtUpperFactor` from the named fact.** -/
theorem crtUpperFactor_of (T : CrtTable) (facts : ViewEntriesPerm E T) : CrtUpperFactor E T := by
  intro _ _ _ _ _ _ parameter scalar u planted budget decide weight b
  classical
  -- push the view law back to the tape
  have pushed : ∀ f : Option (CoreView E T u) → ℝ≥0∞,
      ∑' v, realCore E T parameter scalar u v * f v = ∑' tape, swappedTableTape E tape *
        f (if Doubling E scalar tape u then none else some (realView E T parameter scalar u tape)) := by
    intro f
    unfold realCore
    exact tsum_map_mul _ _ f
  have lhs := pushed fun v => match v with
    | none => 0
    | some v => weight v.1 * viewWeight E T u v planted decide b
  have someSum : ∑' v, realCore E T parameter scalar u (some v) * (weight v.1 * viewWeight E T u v planted decide b) =
      ∑' v : Option (CoreView E T u), realCore E T parameter scalar u v * (match v with
        | none => 0
        | some v => weight v.1 * viewWeight E T u v planted decide b) := by
    rw [tsum_option _ ENNReal.summable]
    simp
  rw [someSum, lhs]
  refine ENNReal.tsum_le_tsum fun tape => ?_
  gcongr
  by_cases doubling : Doubling E scalar tape u
  · rw [if_pos doubling]
    exact zero_le
  · rw [if_neg doubling]
    show weight (realView E T parameter scalar u tape).1 *
        viewWeight E T u (realView E T parameter scalar u tape) planted decide b ≤ _
    rw [← upperWeight_eq_viewWeight E T facts parameter scalar tape u planted decide b doubling]
    rfl

end

end Kriterion.CRT.Privacy.Laws
