/-
**H7's case `convHot`**.

A stage-2 guess at a tag `τ` of family at most 6 that is hot at `u` touches the garbler's input there. On two tapes
with the same fine view the garbler's question lists are related (`DeltaView.garbler_rel`): at the same position the
same tag, and at a hot tag the labels differ by `Δ_κ ⊕ Δ'_κ` (`κ` the tag's coordinate). The garbler asks each tag
once (its question run is tagged, `keyRun_tags`), so two such tapes that both ask the same input `N` at `τ` have the same
`Δ_κ` (`delta_unique`): `Δ_κ` is fixed by the fine view on the event. `DeltaView.delta_guess_le` then bounds the event
by `2^-128` given the stage-2 view.

`convHot_case` discharges the two hypotheses with `coord_relational` (`Core/CoordRelational.lean`) and
`tailRel` (`Hidden/DeltaTail.lean`).
-/

import Proof.Privacy.CRT.Hidden.DeltaViewFD
import Proof.Privacy.CRT.Hidden.DeltaTail
import Proof.Privacy.CRT.Core.CoordRelational

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Kriterion.CRT.Privacy.DeltaView

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.Align (asked asked_of_tagged)
open scoped ENNReal

noncomputable section

/-! ### 1. A tagged program asks each tag once -/

/-- **A tag run asks pairwise distinct tags**, none of them among the history's. -/
theorem keyRun_tags {α : Type} {S : Set Paths.TagKey} {Q : α → List (Paths.TagKey × Block) → Prop} (H : HashN) :
    ∀ {seen : List (Paths.TagKey × Block)} {program : CM α}, Paths.KeyRun S Q seen program →
      (∀ p ∈ seen, p.1.InRange) →
        ((asked H program).map (· / 2 ^ 128)).Nodup ∧
          ∀ n ∈ asked H program, ∀ p ∈ seen, n / 2 ^ 128 ≠ p.1.code
  | _, _, .pure seen value _, _ => ⟨List.nodup_nil, fun n inside => absurd inside List.not_mem_nil⟩
  | _, _, .query seen label tag key next coded member range fresh sameLabel rest, ranges => by
      have ranges' : ∀ p ∈ (key, label) :: seen, p.1.InRange := fun p inside => by
        rcases List.mem_cons.mp inside with first | old
        · rw [first]; exact range
        · exact ranges p old
      obtain ⟨nodup, away⟩ := keyRun_tags H (rest (H (hashInput label tag))) ranges'
      have unfolded : asked H (FreeQuery.query (hashInput label tag) next) =
          hashInput label tag :: asked H (next (H (hashInput label tag))) := rfl
      rw [unfolded]
      refine ⟨?_, fun n inside p pSeen => ?_⟩
      · rw [List.map_cons]
        refine List.nodup_cons.mpr ⟨fun inRest => ?_, nodup⟩
        obtain ⟨m, mIn, same⟩ := List.mem_map.mp inRest
        rw [hashInput_tag] at same
        exact away m mIn (key, label) List.mem_cons_self (same.trans coded.symm)
      · rcases List.mem_cons.mp inside with first | later
        · subst first
          rw [hashInput_tag, ← coded]
          intro same
          exact fresh (List.mem_map.mpr ⟨p, pSeen, Paths.TagKey.code_injective (ranges p pSeen) range same.symm⟩)
        · exact away n later p (List.mem_cons_of_mem _ pSeen)

/-- **The garbler asks each tag once.** -/
theorem garbler_tags_nodup (scalar : NonZeroScalar) (coins : Entry.Coins) (H : HashN) :
    ((asked H (Entry.garbleCM scalar coins)).map (· / 2 ^ 128)).Nodup :=
  (keyRun_tags H (Paths.garbleCM_tagged scalar coins) fun _ inside => absurd inside List.not_mem_nil).1

/-! ### 2. A hot input fixes `Δ` -/

/-- Related lists: an element of the first has a partner of the same tag in the second. -/
theorem RelAsked.partner {hot : ℕ → Prop} {δ : Block} {A B : List ℕ} (rel : RelAsked hot δ A B) {n : ℕ}
    (inside : n ∈ A) : ∃ m ∈ B, m / 2 ^ 128 = n / 2 ^ 128 := by
  induction rel with
  | nil => exact absurd inside List.not_mem_nil
  | @cons a b rest rest' head _ ih =>
    rcases List.mem_cons.mp inside with first | later
    · subst first
      exact ⟨b, List.mem_cons_self, head.1.symm⟩
    · obtain ⟨m, mIn, same⟩ := ih later
      exact ⟨m, List.mem_cons_of_mem _ mIn, same⟩

/-- **A hot input asked on both sides of related lists forces the shift to vanish** (the second list asks each tag
once). -/
theorem RelAsked.shift_zero {hot : ℕ → Prop} {δ : Block} {A B : List ℕ} (rel : RelAsked hot δ A B)
    (nodup : (B.map (· / 2 ^ 128)).Nodup) {N : ℕ} (hN : hot (N / 2 ^ 128)) (inA : N ∈ A) (inB : N ∈ B) :
    δ = 0 := by
  induction rel with
  | nil => exact absurd inA List.not_mem_nil
  | @cons a b rest rest' head tail ih =>
    obtain ⟨tag, _, shifted⟩ := head
    rw [List.map_cons] at nodup
    obtain ⟨fresh, nodup'⟩ := List.nodup_cons.mp nodup
    rcases List.mem_cons.mp inA with first | later
    · -- `N` is the head of the first list
      rw [← first] at tag shifted
      rcases List.mem_cons.mp inB with second | inRest
      · rw [← second] at shifted
        have eq := shifted hN
        calc δ = BitVec.ofNat 128 N ^^^ (BitVec.ofNat 128 N ^^^ δ) := by
              rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
          _ = BitVec.ofNat 128 N ^^^ BitVec.ofNat 128 N := by rw [← eq]
          _ = 0 := BitVec.xor_self
      · exact absurd (List.mem_map.mpr ⟨N, inRest, tag⟩) fresh
    · rcases List.mem_cons.mp inB with second | inRest
      · obtain ⟨m, mIn, sameTag⟩ := RelAsked.partner tail later
        rw [second] at sameTag
        exact absurd (List.mem_map.mpr ⟨m, mIn, sameTag⟩) fresh
      · exact ih nodup' later inRest

section Case

variable [FieldCertificate] [GroupCertificate]

/-- **On two tapes with the same fine view that ask the same hot input, `Δ_κ` agrees.** -/
theorem delta_unique (rel : CoordRelational) (tail : TailRel) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (κ : Fin 2) {tape tape' : TableTape crtEntry}
    (same : fine parameter scalar u κ tape = fine parameter scalar u κ tape') {N : ℕ} (hN : Shifted u κ (N / 2 ^ 128))
    (h1 : N ∈ StageTwo.gAsked scalar tape) (h2 : N ∈ StageTwo.gAsked scalar tape') :
    res κ tape = res κ tape' := by
  have relG : RelAsked (Shifted u κ) (res κ tape ^^^ res κ tape') (StageTwo.gAsked scalar tape)
      (StageTwo.gAsked scalar tape') := (garbler_rel rel tail parameter scalar u κ same).1
  have zero := RelAsked.shift_zero relG (garbler_tags_nodup scalar tape'.1 _) hN h1 h2
  calc res κ tape = res κ tape ^^^ 0 := BitVec.xor_zero.symm
    _ = res κ tape ^^^ (res κ tape ^^^ res κ tape') := by rw [zero]
    _ = res κ tape' := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The coordinate of a tag, as `Fin 2`. -/
def coordFin (τ : ℕ) : Fin 2 := ⟨tagCoord τ, by unfold tagCoord; omega⟩

end Case

open Classical in
/-- **H7's case `convHot`**, from `coord_relational` and `TailRel`. -/
theorem convHot_case_of (rel : CoordRelational) (tail : TailRel) :
    StageTwo.GuessCase StageTwo.convHot StageTwo.noExtra ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  intro field group parameter scalar u view N hot
  let κ := coordFin (N / 2 ^ 128)
  have shifted : Shifted u κ (N / 2 ^ 128) := ⟨rfl, Or.inl hot⟩
  let S : Set (TableTape crtEntry) := {tape | N ∈ StageTwo.gAsked scalar tape ∧ StageTwo.noExtra scalar u N tape}
  let X : WType → Block := fun w =>
    if h : ∃ tape, fine parameter scalar u κ tape = w ∧ N ∈ StageTwo.gAsked scalar tape then res κ h.choose else 0
  have hS : ∀ tape ∈ S, res κ tape = X (fine parameter scalar u κ tape) ^^^ 0 := by
    intro tape inside
    have exists_ : ∃ tape', fine parameter scalar u κ tape' = fine parameter scalar u κ tape ∧
        N ∈ StageTwo.gAsked scalar tape' := ⟨tape, rfl, inside.1⟩
    have spec := exists_.choose_spec
    show res κ tape = (if h : ∃ tape', fine parameter scalar u κ tape' = fine parameter scalar u κ tape ∧
        N ∈ StageTwo.gAsked scalar tape' then res κ h.choose else 0) ^^^ 0
    have z : ∀ x : Block, x ^^^ 0 = x := fun x => BitVec.xor_zero
    rw [dif_pos exists_, z]
    exact delta_unique rel tail parameter scalar u κ spec.1.symm shifted inside.1 spec.2
  exact delta_guess_le rel tail parameter scalar u κ view S X 0 hS

/-- The case's error is within the hidden charge. -/
theorem inv_le_charge : ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ ENNReal.ofReal crtHiddenCharge := by
  have real : (1 : ℝ) / 2 ^ 128 ≤ crtHiddenCharge := by
    rw [crtHiddenCharge_eq]
    have pos : 0 ≤ 1 / ((BN254.baseFieldModulus : ℝ) - 1) := by
      unfold BN254.baseFieldModulus
      norm_num
    have four : (1 : ℝ) / 2 ^ 128 ≤ 4 / 2 ^ 128 := by norm_num
    linarith
  calc ((2 : ℝ≥0∞) ^ 128)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal crtHiddenCharge := ENNReal.ofReal_le_ofReal real

/-- `coord_relational` is the hypothesis `CoordRelational`. -/
theorem coordRelational : CoordRelational :=
  fun H₁ H₂ S coord hS hcoord u Δ₁ Δ₂ Z₁ Z₂ hE hpub hagree =>
    Align.coord_relational H₁ H₂ S coord hS hcoord u Δ₁ Δ₂ Z₁ Z₂ hE hpub hagree

/-- **H7's case `convHot`.** -/
theorem convHot_case : StageTwo.GuessCase StageTwo.convHot StageTwo.noExtra ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
  convHot_case_of coordRelational tailRel


end

end Kriterion.CRT.Privacy.DeltaView
