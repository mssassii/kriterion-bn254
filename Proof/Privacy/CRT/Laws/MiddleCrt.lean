/-
**(B) for the CRT entry**.

`crtMiddleFactor_of` at `crtEntry`, `Entry.table`, `crtShadow` and the CRT reveals, with every input discharged that
is proved: the paths (`Paths/Refill.lean`), the layout facts (`crtLayout_refill`, `crtLayout_points`),
the on-curve flag (`crtOnFlag`) and the off-curve flag (`crtOffFlag`, from `crtRevealOff_final_iff` and `tableRunOff_empty`). Two inputs remain: the on-curve decomposition `OnDecomp`
and the off-curve decomposition `OffSplit`.
-/

import Proof.Privacy.CRT.Laws.MiddleOff
import Proof.Privacy.CRT.Flags.WrapBridge

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open Kriterion.CRT.Privacy.PublicFirst (viewHere CrtShadow)

noncomputable section

/-- **The off-curve flag of the CRT entry.** -/
theorem crtOffFlag [FieldCertificate] [GroupCertificate]
    (source : (viewHere crtEntry).Source) (u : AffineInput) : OffFlag crtEntry crtShadow crtRevealOff source u := by
  intro coin table revealed
  have member : (((crtShadowOffCurve source u).eval (offAnswer table),
      offFinal table (crtShadowOffCurve source u) LazyOracle.empty) : Unit × LazyOracle.State Empty Empty) ∈
      (runReader (PublicFirst.tableReader table) (crtShadowOffCurve source u) LazyOracle.empty).support := by
    rw [(tableRunOff_empty table _).1]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have key := (Flags.crtRevealOff_final_iff source u table _ member).mp revealed
  dsimp only [crtShadow, offFinOf]
  dsimp only at key
  exact key

/-- **(B) for the CRT entry**, from the on-curve and the off-curve decompositions. -/
theorem crtEntry_middleFactor
    (decomp : ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
      (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
        ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField),
          OnDecomp crtEntry Kriterion.CRT.Entry.table crtRevealOn source u P ds)
    (offSplit : ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput),
      (crtEntry.scheme inferInstance inferInstance).function scalar u = none →
        ∀ source, OffSplit crtEntry Kriterion.CRT.Entry.table crtShadow crtRevealOff source u) :
    CrtMiddleFactor crtEntry Kriterion.CRT.Entry.table crtShadow crtRevealOn crtRevealOff := by
  refine @crtMiddleFactor_of Empty Empty crtEntry Kriterion.CRT.Entry.table @crtShadow @crtRevealOn @crtRevealOff ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact crtLayout_refill
  · exact crtLayout_points
  · intro _ _ source u conv
    exact Paths.replay_keyNonSite ((viewHere crtEntry).publish source) u conv
  · intro _ _ first second source u
    have one : first = instDecidableEqEmpty := Subsingleton.elim _ _
    have two : second = instDecidableEqEmpty := Subsingleton.elim _ _
    subst one two
    exact Paths.replay_refillPath ((viewHere crtEntry).publish source) u ((viewHere crtEntry).labels source u) _
  · intro _ _ source u
    exact Paths.replay_canonical ((viewHere crtEntry).publish source) u ((viewHere crtEntry).labels source u)
  · intro _ _ f₁ f₂ first second scalar u Q onCurve source
    have one : first = instDecidableEqEmpty := Subsingleton.elim _ _
    have two : second = instDecidableEqEmpty := Subsingleton.elim _ _
    have three : f₁ = Fintype.instEmpty := Subsingleton.elim _ _
    have four : f₂ = Fintype.instEmpty := Subsingleton.elim _ _
    subst one two three four
    exact decomp scalar u Q onCurve source
  · intro _ _ _ _ first second scalar u Q _ source
    have one : first = instDecidableEqEmpty := Subsingleton.elim _ _
    have two : second = instDecidableEqEmpty := Subsingleton.elim _ _
    subst one two
    exact Flags.crtOnFlag source u
  · intro _ _ f₁ f₂ first second scalar u _ source
    have one : first = instDecidableEqEmpty := Subsingleton.elim _ _
    have two : second = instDecidableEqEmpty := Subsingleton.elim _ _
    have three : f₁ = Fintype.instEmpty := Subsingleton.elim _ _
    have four : f₂ = Fintype.instEmpty := Subsingleton.elim _ _
    subst one two three four
    exact crtOffFlag source u
  · intro _ _ f₁ f₂ first second scalar u offCurve source
    have one : first = instDecidableEqEmpty := Subsingleton.elim _ _
    have two : second = instDecidableEqEmpty := Subsingleton.elim _ _
    have three : f₁ = Fintype.instEmpty := Subsingleton.elim _ _
    have four : f₂ = Fintype.instEmpty := Subsingleton.elim _ _
    subst one two three four
    exact offSplit scalar u offCurve source

end

end Kriterion.CRT.Privacy.Laws
