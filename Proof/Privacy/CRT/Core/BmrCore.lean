/-
**The P45 core with route M's flags** (H8's `CrtBmrSplit`, part (d)).

At a valid input and a fixed context, the law of the ideal outputs at uniform cells, flagged wherever an encoding's
CRT value lies in the two-sided wrap window, is below the law of the real outputs at uniform coins (`core_below`).
Each unflagged cell is the image under `bmrEquiv` of `|Residual|` coin vectors, none of which wraps
(`hint_false_of_window`), and at each of them the real output is the ideal output of the cell (`bmr_real_eq_ideal`).
-/

import Proof.Privacy.CRT.Core.BmrFlags
import Proof.Privacy.CRT.Core.BodyMaskRowJoint

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)] [FieldCertificate]

/-- `bmrEquiv`'s first component reads the joins and the cold pads of the coins. -/
theorem bmrEquiv_join (ctx : Context) (u : AffineInput) (onCurve : OnCurve u) (c : Coins T) :
    (bmrEquiv T ctx u onCurve c).1.1.1 = join ctx c ∧ (bmrEquiv T ctx u onCurve c).1.2.1 = coldOf u c :=
  ⟨rfl, rfl⟩

/-- A pushforward's mass at `b` is below another's at `b'` when `f a = b` forces `f' a = b'`. -/
theorem map_le_map_of_imp {α β γ : Type*} (p : PMF α) (f : α → β) (f' : α → γ) (b : β) (b' : γ)
    (imp : ∀ a, f a = b → f' a = b') : p.map f b ≤ p.map f' b' := by
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  exact MeasureTheory.OuterMeasure.mono _ fun a member => imp a member

/-- **The P45 core with the window flag.** -/
theorem core_below (facts : TableFacts T) (ctx : Context) (u : AffineInput) (onCurve : OnCurve u)
    (flag : Source T × Visible T u → Prop) [DecidablePred flag]
    (window : ∀ cells, ¬ flag cells → ∀ e, ¬ InWindow T (evalInt u cells.1.1 cells.2.1 e)) (o : Out T u) :
    (PMF.uniformOfFintype (Source T × Visible T u)).map
        (fun cells => if flag cells then none else some (idealOut ctx u cells)) (some o) ≤
      (PMF.uniformOfFintype (Coins T)).map (fun c => some (realOut ctx u c)) (some o) := by
  set e := bmrEquiv T ctx u onCurve
  have same : ∀ cells res, ¬ flag cells → realOut ctx u (e.symm (cells, res)) = idealOut ctx u cells := by
    intro cells res flagged
    have image : e (e.symm (cells, res)) = (cells, res) := e.apply_symm_apply _
    have noWrap : ∀ enc, hint (e.symm (cells, res)) enc = false := by
      intro enc
      apply hint_false_of_window facts ctx u
      have parts := bmrEquiv_join ctx u onCurve (e.symm (cells, res))
      rw [← parts.1, ← parts.2]
      show ¬ InWindow T (evalInt u (e (e.symm (cells, res))).1.1.1 (e (e.symm (cells, res))).1.2.1 enc)
      rw [image]
      exact window cells flagged enc
    rw [bmr_real_eq_ideal T facts ctx u onCurve _ noWrap]
    show idealOut ctx u (e (e.symm (cells, res))).1 = _
    rw [image]
  rw [← uniform_map_fst (A := Source T × Visible T u) (B := Residual), PMF.map_comp,
    ← uniform_map_equiv e.symm, PMF.map_comp]
  refine map_le_map_of_imp _ _ _ _ _ fun x hit => ?_
  obtain ⟨cells, res⟩ := x
  simp only [Function.comp_apply] at hit ⊢
  by_cases flagged : flag cells
  · rw [if_pos flagged] at hit
    exact absurd hit (Option.some_ne_none o).symm
  · rw [if_neg flagged] at hit
    rw [same cells res flagged, hit]

end Kriterion.CRT.Privacy.BMR
