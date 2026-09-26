/-
**P7, the public-first hop, part 7: the real layout is well sized**, so `CrtMiddleBelow` holds for every entry
whose layout is `crtLayout`.

`WellSized layout` (`Coupling.lean`) asks, at **every** site (also the sites `siteOf` decodes that are not in
`crtLayout.sites`), that every answer list the site law can draw has at least `layout.answers site` answers. For
`crtLayout` every site law is a map of `List.ofFn` at exactly `layoutAnswers site` answers (the pad fibre law or
uniform answers, the mask fibre laws), or `PMF.pure []` at 0 answers (a mask stage above 1).
-/

import Proof.Privacy.CRT.PublicFirst.Below
import Proof.Privacy.CRT.Swap.Layout

namespace Kriterion.CRT.Privacy.PublicFirst

open BN254 Cryptography Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.Layout

noncomputable section

namespace WellSizedCrt

theorem length_of_ofFn {n : ℕ} (μ : PMF (Fin n → Block × Block)) {answers : List (Block × Block)}
    (member : answers ∈ (μ.map List.ofFn).support) : answers.length = n := by
  rw [PMF.support_map] at member
  obtain ⟨f, -, rfl⟩ := member
  exact List.length_ofFn

end WellSizedCrt

open WellSizedCrt in
/-- **The real layout is well sized.** -/
theorem wellSized_crtLayout : WellSized crtLayout := by
  intro site answers support
  cases site with
  | pad κ i ρ =>
    change answers ∈ (padSiteLaw (padS κ) (padModulus i) (padCount κ i)).support at support
    show padCount κ i ≤ answers.length
    unfold padSiteLaw at support
    split at support
    · exact (length_of_ofFn _ support).ge
    · exact (length_of_ofFn _ support).ge
  | mask st k =>
    rcases st with _ | _ | st
    · change answers ∈ singleSiteLaw.support at support
      exact (length_of_ofFn _ support).ge
    · change answers ∈ (if k = 227 then singleSiteLaw else pairSiteLaw).support at support
      show (if k = 227 then 2 else 3) ≤ answers.length
      split at support
      · rw [if_pos (by assumption)]
        exact (length_of_ofFn _ support).ge
      · rw [if_neg (by assumption)]
        exact (length_of_ofFn _ support).ge
    · exact Nat.zero_le _

/-- **`CrtMiddleBelow` for an entry on the real layout.** -/
theorem crtMiddleBelow_of_layout {FI EI : Type} (E : CrtEntry FI EI) (layout : E.layout = crtLayout)
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI) :
    CrtMiddleBelow E shadow :=
  crtMiddleBelow_of E (layout ▸ wellSized_crtLayout) shadow

end

end Kriterion.CRT.Privacy.PublicFirst
