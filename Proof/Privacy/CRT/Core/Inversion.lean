/-
**CRT privacy core: the left-inverse inversion lemma.**

The conversion core must not
be stated as a triangular family `J_g = h_g ⊕ F_g(earlier)`, because a fused extraction stage has no triangular
order in the point reading of its answers. The statement that covers every gadget is the left-inverse form:

* a map between two finite types of the same cardinality that has a left inverse is a bijection
  (`bijective_of_leftInverse`);
* such a map pushes the uniform law to the uniform law (`map_uniform_of_leftInverse`);
* the form the core uses: for every value `r` of the rest of the view (zero labels, `Δ`, cold answers, coins) let
  `f r` send the hidden answers to the published values and let `g r` be a left inverse of it (the evaluator's
  solve, or any other function of the published values and `r`). Then drawing `r` from any law and the hidden
  answers uniformly gives the published values uniform and independent of `r`
  (`bind_map_uniform_of_leftInverse`).

The lemma never asks for an order among gadgets, so the fused extraction stage is one gadget whose hidden part is a
tuple (`Proof.Privacy.CRT.Core.ExtractStage`).

This file imports Mathlib only, so it can move to `` unchanged.
-/

import Mathlib.Probability.Distributions.Uniform

namespace Kriterion.CRT.Privacy

open scoped ENNReal

noncomputable section

section Generic

variable {Hidden Published : Type*} [Fintype Hidden] [Fintype Published]

/-- **Left-inverse inversion, the set statement.** A map between finite types of the same cardinality that has a
left inverse is a bijection. -/
theorem bijective_of_leftInverse {f : Hidden → Published} {g : Published → Hidden}
    (left : Function.LeftInverse g f) (card : Fintype.card Hidden = Fintype.card Published) :
    Function.Bijective f :=
  (Fintype.bijective_iff_injective_and_card f).2 ⟨left.injective, card⟩

/-- The same with injectivity in place of an explicit left inverse (a left inverse exists classically). -/
theorem bijective_of_injective_card {f : Hidden → Published} (injective : Function.Injective f)
    (card : Fintype.card Hidden = Fintype.card Published) : Function.Bijective f :=
  (Fintype.bijective_iff_injective_and_card f).2 ⟨injective, card⟩

/-- A bijection pushes the uniform law to the uniform law. -/
theorem map_uniform_of_bijective [Nonempty Hidden] [Nonempty Published] {f : Hidden → Published}
    (bij : Function.Bijective f) :
    (PMF.uniformOfFintype Hidden).map f = PMF.uniformOfFintype Published := by
  classical
  let e : Hidden ≃ Published := Equiv.ofBijective f bij
  have apply_symm : ∀ b, f (e.symm b) = b := fun b => Equiv.ofBijective_apply_symm_apply f bij b
  refine PMF.ext fun b => ?_
  rw [PMF.map_apply, tsum_eq_single (e.symm b) (fun a other => ?_)]
  · rw [apply_symm b, if_pos rfl, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
      Fintype.card_congr e]
  · have miss : b ≠ f a := by
      intro hit
      apply other
      have : e a = b := hit.symm
      rw [← this, Equiv.symm_apply_apply]
    rw [if_neg miss]

/-- **Left-inverse inversion, the law statement.** A map between finite types of the same cardinality with a left
inverse pushes the uniform law to the uniform law. -/
theorem map_uniform_of_leftInverse [Nonempty Hidden] [Nonempty Published] {f : Hidden → Published}
    {g : Published → Hidden} (left : Function.LeftInverse g f)
    (card : Fintype.card Hidden = Fintype.card Published) :
    (PMF.uniformOfFintype Hidden).map f = PMF.uniformOfFintype Published :=
  map_uniform_of_bijective (bijective_of_leftInverse left card)

/-- The self-map case (hidden and published values of the same type), where the cardinality condition is
automatic. -/
theorem map_uniform_of_leftInverse_self [Nonempty Hidden] {f g : Hidden → Hidden}
    (left : Function.LeftInverse g f) :
    (PMF.uniformOfFintype Hidden).map f = PMF.uniformOfFintype Hidden :=
  map_uniform_of_leftInverse left rfl

/-- **Left-inverse inversion, the form the core uses.** For each value `r` of the rest of the view, `f r` sends
the hidden answers to the published values and has a left inverse `g r`. Then, whatever the law of `r`, drawing
the hidden answers uniformly makes the published values uniform and independent of `r`. -/
theorem bind_map_uniform_of_leftInverse {Rest : Type*} [Nonempty Hidden] [Nonempty Published]
    (rest : PMF Rest) (f : Rest → Hidden → Published) (g : Rest → Published → Hidden)
    (left : ∀ r, Function.LeftInverse (g r) (f r))
    (card : Fintype.card Hidden = Fintype.card Published) :
    (rest.bind fun r => (PMF.uniformOfFintype Hidden).map fun h => (r, f r h))
      = rest.bind fun r => (PMF.uniformOfFintype Published).map fun b => (r, b) := by
  congr 1
  funext r
  have split : (fun h => (r, f r h)) = (Prod.mk r) ∘ (f r) := rfl
  rw [split, ← PMF.map_comp, map_uniform_of_leftInverse (left r) card]

/-- The same with injectivity of each `f r` in place of explicit left inverses. -/
theorem bind_map_uniform_of_injective {Rest : Type*} [Nonempty Hidden] [Nonempty Published]
    (rest : PMF Rest) (f : Rest → Hidden → Published) (injective : ∀ r, Function.Injective (f r))
    (card : Fintype.card Hidden = Fintype.card Published) :
    (rest.bind fun r => (PMF.uniformOfFintype Hidden).map fun h => (r, f r h))
      = rest.bind fun r => (PMF.uniformOfFintype Published).map fun b => (r, b) := by
  congr 1
  funext r
  have split : (fun h => (r, f r h)) = (Prod.mk r) ∘ (f r) := rfl
  rw [split, ← PMF.map_comp, map_uniform_of_bijective (bijective_of_injective_card (injective r) card)]

end Generic

/-! ### Chains of gadgets

On the answer-table reading a gadget's published values depend on its own
hidden answers and on the rest, which includes the hidden answers of earlier gadgets (through its input masks). The
gadgets then compose in gadget order: each step is one application of the left-inverse lemma with the earlier hidden
answers inside the rest. `injective_chain` is that composition for two gadgets; iterating it (or nesting the product)
covers a whole layer. The order is between gadgets only; inside a gadget the left-inverse form needs none. -/

section Chain

variable {H₁ H₂ P₁ P₂ : Type*}

/-- Two gadgets in sequence: if the first is injective in its hidden part and the second is injective in its own
hidden part for every value of the first one's, the pair is injective in the pair of hidden parts. -/
theorem injective_chain {f₁ : H₁ → P₁} {f₂ : H₁ → H₂ → P₂} (inj₁ : Function.Injective f₁)
    (inj₂ : ∀ h₁, Function.Injective (f₂ h₁)) :
    Function.Injective fun h : H₁ × H₂ => (f₁ h.1, f₂ h.1 h.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ same
  simp only [Prod.mk.injEq] at same
  obtain ⟨first, second⟩ := same
  have ha : a = a' := inj₁ first
  subst ha
  rw [inj₂ a second]

/-- The law form of the chain: with the rest drawn from any law and both hidden parts uniform, the two published
parts are uniform and independent of the rest and of each other. -/
theorem bind_map_uniform_chain [Fintype H₁] [Fintype H₂] [Fintype P₁] [Fintype P₂]
    [Nonempty H₁] [Nonempty H₂] [Nonempty P₁] [Nonempty P₂] {Rest : Type*} (rest : PMF Rest)
    (f₁ : Rest → H₁ → P₁) (f₂ : Rest → H₁ → H₂ → P₂)
    (inj₁ : ∀ r, Function.Injective (f₁ r)) (inj₂ : ∀ r h₁, Function.Injective (f₂ r h₁))
    (card₁ : Fintype.card H₁ = Fintype.card P₁) (card₂ : Fintype.card H₂ = Fintype.card P₂) :
    (rest.bind fun r => (PMF.uniformOfFintype (H₁ × H₂)).map fun h => (r, (f₁ r h.1, f₂ r h.1 h.2)))
      = rest.bind fun r => (PMF.uniformOfFintype (P₁ × P₂)).map fun b => (r, b) :=
  bind_map_uniform_of_injective rest (fun r (h : H₁ × H₂) => (f₁ r h.1, f₂ r h.1 h.2))
    (fun r => injective_chain (inj₁ r) (inj₂ r))
    (by rw [Fintype.card_prod, Fintype.card_prod, card₁, card₂])

end Chain

end

end Kriterion.CRT.Privacy
