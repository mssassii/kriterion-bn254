/-
**CRT privacy core (P3, P5a): a uniform answer table split into its cold part and its hot readings.**

Generic facts about uniform tables `A : ι → X` over a finite index set (the tag table of the chain, `TagTable`):

* `uniform_restrict`: read at injectively indexed positions, a uniform table is uniform (any finite codomain; the
  `Bool` case is `uniform_map_restrict`);
* `table_split_uniform`: the values off a set of positions and the values read along an injective family inside the
  set are independent and uniform;
* `pi_map_uniform`, `prod_map_uniform`: independent coordinates, each pushed through a map that preserves the uniform
  law, give the uniform law.

The conversion core reads the hot positions of a coordinate this way (`ConvRead.lean`), and the digest core its
hidden finals.
-/

import Proof.Privacy.Phase3.Basic
import Proof.Privacy.PGS.DaviesMeyerUniform

namespace Kriterion.CRT.Privacy.Split

open scoped ENNReal

noncomputable section

section Restrict

variable {ι κ X : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype X] [Nonempty X]

open Classical in
/-- Overwrite a table at the positions `pos k` with `f k`. -/
def overwrite (pos : κ → ι) (f : κ → X) (A : ι → X) : ι → X := fun i =>
  if h : ∃ k, pos k = i then f (Classical.choose h) else A i

theorem overwrite_comp (pos : κ → ι) (inj : Function.Injective pos) (f : κ → X) (A : ι → X) :
    overwrite pos f A ∘ pos = f := by
  funext k
  have h : ∃ k', pos k' = pos k := ⟨k, rfl⟩
  show (if h' : ∃ k', pos k' = pos k then f (Classical.choose h') else A (pos k)) = f k
  rw [dif_pos h, inj (Classical.choose_spec h)]

theorem overwrite_overwrite (pos : κ → ι) (f g : κ → X) (A : ι → X) :
    overwrite pos f (overwrite pos g A) = overwrite pos f A := by
  funext i
  unfold overwrite
  by_cases h : ∃ k, pos k = i
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, dif_neg h]

theorem overwrite_self (pos : κ → ι) (A : ι → X) : overwrite pos (A ∘ pos) A = A := by
  funext i
  unfold overwrite
  by_cases h : ∃ k, pos k = i
  · rw [dif_pos h]
    exact congrArg A (Classical.choose_spec h)
  · rw [dif_neg h]

/-- **A uniform table read at injectively indexed positions is uniform.** -/
theorem uniform_restrict [DecidableEq X] (pos : κ → ι) (inj : Function.Injective pos) :
    (PMF.uniformOfFintype (ι → X)).map (fun A => A ∘ pos) = PMF.uniformOfFintype (κ → X) := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun f1 f2 => ?_
  exact {
    toFun := fun A => ⟨overwrite pos f2 A.1, overwrite_comp pos inj f2 A.1⟩
    invFun := fun A => ⟨overwrite pos f1 A.1, overwrite_comp pos inj f1 A.1⟩
    left_inv := fun A => by
      apply Subtype.ext
      show overwrite pos f1 (overwrite pos f2 A.1) = A.1
      rw [overwrite_overwrite]
      have key := overwrite_self pos A.1
      rw [A.2] at key
      exact key
    right_inv := fun A => by
      apply Subtype.ext
      show overwrite pos f2 (overwrite pos f1 A.1) = A.1
      rw [overwrite_overwrite]
      have key := overwrite_self pos A.1
      rw [A.2] at key
      exact key }

end Restrict

section SplitTable

variable {ι R X : Type} [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] [Fintype X] [Nonempty X]
  [DecidableEq X]

/-- **A uniform table split**: its values off a set of positions and its values read along an injective family of
positions inside the set are independent and uniform. -/
theorem table_split_uniform (cold : ι → Prop) [DecidablePred cold] (read : R → ι) (inj : Function.Injective read)
    (hot : ∀ r, ¬ cold (read r)) :
    (PMF.uniformOfFintype (ι → X)).map (fun A => ((fun i : {i // cold i} => A i.1), A ∘ read)) =
      PMF.uniformOfFintype (({i // cold i} → X) × (R → X)) := by
  classical
  let pos : {i // cold i} ⊕ R → ι := Sum.elim Subtype.val read
  have posInj : Function.Injective pos := by
    rintro (a | a) (b | b) same <;> simp only [pos, Sum.elim_inl, Sum.elim_inr] at same
    · exact congrArg Sum.inl (Subtype.ext same)
    · exact absurd (same ▸ a.2) (hot b)
    · exact absurd (same.symm ▸ b.2) (hot a)
    · exact congrArg Sum.inr (inj same)
  have factor : (fun A : ι → X => ((fun i : {i // cold i} => A i.1), A ∘ read)) =
      (Equiv.sumArrowEquivProdArrow {i // cold i} R X) ∘ (fun A => A ∘ pos) := by
    funext A
    rfl
  rw [factor, ← PMF.map_comp, uniform_restrict pos posInj,
    Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]

end SplitTable

section Pi

/-- A map that pushes the uniform law to the uniform law has fibres of equal size. -/
theorem fibre_card_eq {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [DecidableEq B] (f : A → B)
    (uniform : (PMF.uniformOfFintype A).map f = PMF.uniformOfFintype B) (b b' : B) :
    Fintype.card {x : A // f x = b} = Fintype.card {x : A // f x = b'} := by
  classical
  have e : ((PMF.uniformOfFintype A).map f) b = ((PMF.uniformOfFintype A).map f) b' := by
    rw [uniform, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  rw [Kriterion.ArgoMAC.Security.Phase3.uniform_map_apply f b,
    Kriterion.ArgoMAC.Security.Phase3.uniform_map_apply f b'] at e
  have hA : (Fintype.card A : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hA' : (Fintype.card A : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact_mod_cast (ENNReal.mul_left_inj hA hA').mp e

/-- **Independent coordinates pushed through uniform-preserving maps** give the uniform law. -/
theorem pi_map_uniform {I : Type} [Fintype I] [DecidableEq I] {A B : I → Type} [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)] [∀ i, DecidableEq (B i)]
    (f : ∀ i, A i → B i) (uniform : ∀ i, (PMF.uniformOfFintype (A i)).map (f i) = PMF.uniformOfFintype (B i)) :
    (PMF.uniformOfFintype (∀ i, A i)).map (fun a i => f i (a i)) = PMF.uniformOfFintype (∀ i, B i) := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun b b' => ?_
  let fibre : ∀ b : ∀ i, B i, {a : ∀ i, A i // (fun i => f i (a i)) = b} ≃ ∀ i, {x : A i // f i x = b i} :=
    fun b => {
      toFun := fun a i => ⟨a.1 i, congrFun a.2 i⟩
      invFun := fun g => ⟨fun i => (g i).1, funext fun i => (g i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (fibre b).trans ((Equiv.piCongrRight fun i =>
    Fintype.equivOfCardEq (fibre_card_eq (f i) (uniform i) (b i) (b' i))).trans (fibre b').symm)

/-- **Two independent parts pushed through uniform-preserving maps** give the uniform law. -/
theorem prod_map_uniform {A B C D : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C]
    [Fintype D] [Nonempty D] [DecidableEq C] [DecidableEq D] (f : A → C) (g : B → D)
    (uf : (PMF.uniformOfFintype A).map f = PMF.uniformOfFintype C)
    (ug : (PMF.uniformOfFintype B).map g = PMF.uniformOfFintype D) :
    (PMF.uniformOfFintype (A × B)).map (fun p => (f p.1, g p.2)) = PMF.uniformOfFintype (C × D) := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun b b' => ?_
  let fibre : ∀ b : C × D, {p : A × B // (f p.1, g p.2) = b} ≃ {x : A // f x = b.1} × {y : B // g y = b.2} :=
    fun b => {
      toFun := fun p => (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2, congrArg Prod.snd p.2⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1), Prod.ext q.1.2 q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (fibre b).trans ((Equiv.prodCongr (Fintype.equivOfCardEq (fibre_card_eq f uf b.1 b'.1))
    (Fintype.equivOfCardEq (fibre_card_eq g ug b.2 b'.2))).trans (fibre b').symm)

end Pi

end

end Kriterion.CRT.Privacy.Split
