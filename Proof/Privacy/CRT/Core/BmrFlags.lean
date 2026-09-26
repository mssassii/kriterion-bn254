/-
**Flag soundness for P45 at the entry** (H8's `CrtBmrSplit`, part (d); `Core/H8.lean` section 4).

Route M's middle game cannot see `a_e v`, so it flags the two-sided window of the CRT values (`replayWraps`). This
file proves, at the level of P45's coins, that the window covers the wrap event: the evaluator's CRT integer is
`w = (O_e + a_e v) mod M` (`evalInt_eq`), and if `O_e > M − B` (the hint) then `w` lies in `[0, B − 1)` or in
`(M − B, M)` (`hint_false_of_window`). So an ideal cell outside the window has a preimage that does not wrap.

`evalInt_uniform`: for fixed joins, under uniform cold pads the evaluator's CRT integer of any encoding is uniform on
`[0, M)` (the residue is affine in the cold pads with a unit coefficient at the slot after the hot one). It bounds
route M's wrap reveal and the key label.
-/

import Proof.Privacy.CRT.Core.BodyMaskRowParts
import Proof.Privacy.CRT.Core.WrapMass

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.CRT

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- The two-sided wrap window of a CRT value: `w + 1 < B` or `M − B < w`. -/
def InWindow (T : CrtTable) (w : ℕ) : Prop := w + 1 < T.wrapBound ∨ T.product - T.wrapBound < w

/-- **The evaluator's CRT integer** is `(O_e + a_e v) mod M`. -/
theorem evalInt_eq (facts : TableFacts T) (ctx : Context) (u : AffineInput) (c : Coins T) (e : Enc) :
    evalInt u (join ctx c) (coldOf u c) e =
      (offset c e + (slope ctx c e).val * coordValue u (coordOf e)) % T.product := by
  have hpos := facts.pos
  have hco : Pairwise (Function.onFun Nat.Coprime T.modulus) := fun i j hij => facts.coprime i j hij
  have cong : ∀ j, (evalResidue u (join ctx c) (coldOf u c) e j).val ≡
      (readout c e j).val + (slope ctx c e).val * coordValue u (coordOf e) [MOD T.modulus j] := by
    intro j
    rw [← ZMod.natCast_eq_natCast_iff, evalResidue_eq]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    simp only [hotRes]
    ring
  unfold evalInt offset
  rw [tableCrt_eq, tableCrt_eq, SliceC.crt_add hpos hco _ _ _ cong]
  rfl

/-- **Window soundness**: if the evaluator's CRT integer lies outside the two-sided window, the coins do not wrap. -/
theorem hint_false_of_window (facts : TableFacts T) (ctx : Context) (u : AffineInput) (c : Coins T) (e : Enc)
    (outside : ¬ InWindow T (evalInt u (join ctx c) (coldOf u c) e)) : hint c e = false := by
  set a := slope ctx c e
  set v := coordValue u (coordOf e)
  have hv : v < baseFieldModulus := by
    simp only [v, coordValue]
    split_ifs <;> exact ZMod.val_lt _
  have hu : a.val * v < T.wrapBound := by
    rw [facts.wrapBound_eq]
    unfold wrapBound
    have ha : a.val ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt a)
    have hv' : v ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt hv
    rw [sq]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul ha hv')
  have room := facts.wrap_room
  have hO : offset c e < T.product := by
    unfold offset
    rw [tableCrt_eq]
    exact SliceC.crt_lt facts.pos _
  have hw := evalInt_eq facts ctx u c e
  unfold InWindow at outside
  unfold hint wrapHint
  by_contra wraps
  simp only [Bool.not_eq_false, decide_eq_true_eq] at wraps
  rw [hw] at outside
  by_cases small : offset c e + a.val * v < T.product
  · rw [Nat.mod_eq_of_lt small] at outside
    omega
  · have big : T.product ≤ offset c e + a.val * v := Nat.le_of_not_lt small
    have below : offset c e + a.val * v - T.product < T.product := by omega
    rw [show (offset c e + a.val * v) % T.product = offset c e + a.val * v - T.product from by
      rw [Nat.mod_eq_sub_mod big, Nat.mod_eq_of_lt below]] at outside
    omega

open WrapMass in
/-- The cold part of the evaluator's residue, as an additive map on the cold pads. -/
def coldHom (u : AffineInput) (e : Enc) : Cold T u →+ Residues T :=
  AddMonoidHom.mk' (fun cold i => ∑ ρ : {ρ : ZMod (T.modulus i) // ρ ≠ hotRes T u e i},
      (ρ.1 - hotRes T u e i) * cold i e ρ) fun first second => by
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

open WrapMass in
theorem coldHom_surjective (u : AffineInput) (e : Enc) : Function.Surjective (coldHom (T := T) u e) := by
  classical
  intro target
  refine ⟨fun i e' ρ => if e' = e ∧ ρ.1 = hotRes T u e i + 1 then target i else 0, ?_⟩
  funext i
  simp only [coldHom, AddMonoidHom.mk'_apply, true_and, mul_ite, mul_zero]
  by_cases trivial : hotRes T u e i + 1 = hotRes T u e i
  · have one : (1 : ZMod (T.modulus i)) = 0 := by
      have := congrArg (· - hotRes T u e i) trivial
      simpa using this
    have sub : Subsingleton (ZMod (T.modulus i)) := subsingleton_of_zero_eq_one one.symm
    exact Subsingleton.elim _ _
  · rw [Finset.sum_eq_single ⟨hotRes T u e i + 1, trivial⟩]
    · simp
    · intro ρ _ other
      rw [if_neg]
      intro same
      exact other (Subtype.ext same)
    · intro absent
      exact absent.elim (Finset.mem_univ _)

/-- The evaluator's residue is the cold part plus `h J`. -/
theorem evalResidue_coldHom (u : AffineInput) (J : Joins T) (cold : Cold T u) (e : Enc) :
    (fun i => evalResidue u J cold e i) = coldHom u e cold + fun i => hotRes T u e i * J e i := by
  funext i
  simp only [evalResidue, coldHom, AddMonoidHom.mk'_apply, Pi.add_apply, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

open WrapMass in
/-- **The evaluator's CRT integer is uniform on `[0, M)`** under uniform cold pads, for fixed joins. -/
theorem evalInt_uniform (facts : TableFacts T) (u : AffineInput) (J : Joins T) (e : Enc) :
    (PMF.uniformOfFintype (Cold T u)).map (fun cold => crtFin facts fun i => evalResidue u J cold e i) =
      @PMF.uniformOfFintype (Fin T.product) _ ⟨⟨0, by rw [← card_residues]; exact Fintype.card_pos⟩⟩ := by
  haveI : Nonempty (Fin T.product) := ⟨⟨0, by rw [← card_residues]; exact Fintype.card_pos⟩⟩
  classical
  have step : (fun cold => crtFin facts fun i => evalResidue u J cold e i) =
      crtFin facts ∘ (fun r => r + fun i => hotRes T u e i * J e i) ∘ coldHom (T := T) u e := by
    funext cold
    simp only [Function.comp_apply, evalResidue_coldHom]
  have translate : (fun r : Residues T => r + fun i => hotRes T u e i * J e i) =
      ⇑(Equiv.addRight fun i => hotRes T u e i * J e i) := rfl
  rw [step, ← PMF.map_comp, ← PMF.map_comp, uniform_map_addHom _ (coldHom_surjective u e), translate,
    uniform_map_equiv (Equiv.addRight fun i => hotRes T u e i * J e i)]
  exact map_uniform_of_bijective ((Fintype.bijective_iff_injective_and_card _).2
    ⟨crtFin_injective facts, by rw [card_residues, Fintype.card_fin]⟩)

open WrapMass in
theorem crtFin_evalResidue (facts : TableFacts T) (u : AffineInput) (J : Joins T) (cold : Cold T u) (e : Enc) :
    (crtFin facts fun i => evalResidue u J cold e i).val = evalInt u J cold e := rfl

end Kriterion.CRT.Privacy.BMR
