/-
**P45.c: the wrap event's mass** (row T4).

Under the uniform coins, every CRT offset `O_e` is uniform on `[0, M)`: the readout `V ↦ Σ_ρ ρ V_ρ[e]` is a
surjective additive map onto the residue tuples (slot `ρ = 1` has coefficient `1`), a surjective additive map
pushes the uniform law to the uniform law, and the CRT map is a bijection from residue tuples onto `Fin M`. So the
wrap event `O_e > M − B` has mass at most `(B − 1)/M`, and the union over the 733 encodings gives
`733 (B − 1)/M`.
-/

import Proof.Privacy.CRT.Core.BodyMaskRowParts
import Proof.Privacy.CRT.Core.Inversion

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

noncomputable section

namespace WrapMass

/-- The pushforward mass of a point is its fibre's share. -/
theorem uniform_map_apply {A B : Type*} [Fintype A] [Nonempty A] [DecidableEq B] (g : A → B) (point : B) :
    ((PMF.uniformOfFintype A).map g) point
      = (Fintype.card {x : A // g x = point} : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [tsum_fintype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [eq_comm]

/-- **Equinumerous fibres push uniform to uniform** (xinshu's `uniform_map_of_fibre_equiv`, `Basic.lean:100`). -/
theorem uniform_map_of_fibre_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [DecidableEq B] (g : A → B) (shift : ∀ first second : B, {x : A // g x = first} ≃ {x : A // g x = second}) :
    (PMF.uniformOfFintype A).map g = PMF.uniformOfFintype B := by
  classical
  obtain ⟨base⟩ := (inferInstance : Nonempty B)
  have fibreCard : ∀ point : B,
      Fintype.card {x : A // g x = point} = Fintype.card {x : A // g x = base} :=
    fun point => Fintype.card_congr (shift point base)
  have total : Fintype.card A = Fintype.card B * Fintype.card {x : A // g x = base} := by
    calc Fintype.card A = Fintype.card (Σ point : B, {x : A // g x = point}) :=
          Fintype.card_congr (Equiv.sigmaFiberEquiv g).symm
      _ = ∑ point : B, Fintype.card {x : A // g x = point} := Fintype.card_sigma
      _ = ∑ _point : B, Fintype.card {x : A // g x = base} :=
          Finset.sum_congr rfl fun point _ => fibreCard point
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have fibrePos : 0 < Fintype.card {x : A // g x = base} := by
    rcases Nat.eq_zero_or_pos (Fintype.card {x : A // g x = base}) with zero | pos
    · have : Fintype.card A = 0 := by rw [total, zero, mul_zero]
      exact absurd this Fintype.card_ne_zero
    · exact pos
  refine PMF.ext fun point => ?_
  rw [uniform_map_apply, PMF.uniformOfFintype_apply, fibreCard point, total, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm ((Fintype.card B : ℝ≥0∞)⁻¹), ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr fibrePos.ne') (ENNReal.natCast_ne_top _), one_mul]

/-- A surjective additive map pushes the uniform law to the uniform law. -/
theorem uniform_map_addHom {G H : Type*} [AddCommGroup G] [Fintype G] [Nonempty G] [AddCommGroup H] [Fintype H]
    [Nonempty H] [DecidableEq H] (φ : G →+ H) (surj : Function.Surjective φ) :
    (PMF.uniformOfFintype G).map φ = PMF.uniformOfFintype H := by
  refine uniform_map_of_fibre_equiv φ fun first second => ?_
  let g0 := Classical.choose (surj (second - first))
  have hg0 : φ g0 = second - first := Classical.choose_spec (surj (second - first))
  exact {
    toFun := fun x => ⟨x.1 + g0, by rw [map_add, x.2, hg0]; abel⟩
    invFun := fun x => ⟨x.1 - g0, by rw [map_sub, x.2, hg0]; abel⟩
    left_inv := fun x => by simp
    right_inv := fun x => by simp }

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- The residue tuples of the table. -/
abbrev Residues (T : CrtTable) := (i : Fin T.count) → ZMod (T.modulus i)

/-- The readout of encoding `e` as an additive map on the pads. -/
def readoutHom (e : Enc) : Pads T →+ Residues T :=
  AddMonoidHom.mk' (fun pads i => ∑ ρ : ZMod (T.modulus i), ρ * pads i ρ e) fun first second => by
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem readoutHom_surjective (e : Enc) : Function.Surjective (readoutHom (T := T) e) := by
  classical
  intro target
  refine ⟨fun i ρ e' => if ρ = 1 ∧ e' = e then target i else 0, ?_⟩
  funext i
  simp only [readoutHom, AddMonoidHom.mk'_apply, and_true, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (1 : ZMod (T.modulus i)), if_pos (Finset.mem_univ _), one_mul]

/-- The CRT map of residue tuples onto `Fin M`. -/
def crtFin (facts : TableFacts T) (r : Residues T) : Fin T.product :=
  ⟨T.crt fun i => (r i).val, by
    rw [tableCrt_eq]
    exact SliceC.crt_lt facts.pos _⟩

theorem crtFin_injective (facts : TableFacts T) : Function.Injective (crtFin facts) := by
  intro r r' same
  have hco : Pairwise (Function.onFun Nat.Coprime T.modulus) := fun i j hij => facts.coprime i j hij
  have eq : T.crt (fun i => (r i).val) = T.crt (fun i => (r' i).val) := congrArg Fin.val same
  funext j
  have h1 := SliceC.crt_spec facts.pos hco (fun i => (r i).val) j
  have h2 := SliceC.crt_spec facts.pos hco (fun i => (r' i).val) j
  rw [← tableCrt_eq, eq, tableCrt_eq, h2] at h1
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h1
  exact ZMod.val_injective _ h1.symm

theorem card_residues : Fintype.card (Residues T) = T.product := by
  simp only [Fintype.card_pi, ZMod.card, CrtTable.product]

/-- **Every CRT offset is uniform on `[0, M)`** under the uniform pads. -/
theorem offset_uniform (facts : TableFacts T) (e : Enc) :
    (PMF.uniformOfFintype (Pads T)).map (fun pads => crtFin facts (readoutHom e pads)) =
      @PMF.uniformOfFintype (Fin T.product) _ ⟨⟨0, by rw [← card_residues]; exact Fintype.card_pos⟩⟩ := by
  haveI : Nonempty (Fin T.product) := ⟨⟨0, by rw [← card_residues]; exact Fintype.card_pos⟩⟩
  have step : (fun pads => crtFin facts (readoutHom e pads)) = crtFin facts ∘ readoutHom (T := T) e := rfl
  rw [step, ← PMF.map_comp, uniform_map_addHom _ (readoutHom_surjective e)]
  exact map_uniform_of_bijective ((Fintype.bijective_iff_injective_and_card _).2
    ⟨crtFin_injective facts, by rw [card_residues, Fintype.card_fin]⟩)

/-- At most `B − 1` points of `Fin M` exceed `M − B`. -/
theorem card_wrap_le (M B : ℕ) : Fintype.card {x : Fin M // M - B < x.val} ≤ B - 1 := by
  have : Fintype.card {x : Fin M // M - B < x.val} ≤ Fintype.card (Fin (B - 1)) :=
    Fintype.card_le_of_injective (fun x => ⟨x.1.val - (M - B + 1), by have := x.1.isLt; have := x.2; omega⟩)
      (by
        intro x y same
        have hx := x.2
        have hy := y.2
        have : x.1.val - (M - B + 1) = y.1.val - (M - B + 1) := congrArg Fin.val same
        exact Subtype.ext (Fin.ext (by omega)))
  simpa using this

end WrapMass

open WrapMass in
/-- **(P45.c)** The wrap event has mass at most `733 (B − 1) / M` under the uniform coins. -/
theorem bmr_wrap_mass (T : CrtTable) [∀ i, NeZero (T.modulus i)] (facts : TableFacts T) :
    ((PMF.uniformOfFintype (Coins T)).toOuterMeasure {c | ∃ e, hint c e = true}).toReal ≤
      (Fintype.card Enc : ℝ) * ((T.wrapBound : ℝ) - 1) / T.product := by
  classical
  have : Nonempty (Fin T.product) := ⟨⟨0, by rw [← card_residues]; exact Fintype.card_pos⟩⟩
  have hM : 0 < T.product := by rw [← card_residues]; exact Fintype.card_pos
  have hB : 1 ≤ T.wrapBound := by rw [facts.wrapBound_eq]; unfold wrapBound; omega
  -- one encoding
  have single : ∀ e : Enc, (PMF.uniformOfFintype (Coins T)).toOuterMeasure {c | hint c e = true} ≤
      ((T.wrapBound - 1 : ℕ) : ℝ≥0∞) / T.product := by
    intro e
    have law : (PMF.uniformOfFintype (Coins T)).map (fun c => crtFin facts (readoutHom e c.pads)) =
        PMF.uniformOfFintype (Fin T.product) := by
      have split : (fun c : Coins T => crtFin facts (readoutHom e c.pads)) =
          (fun pads => crtFin facts (readoutHom e pads)) ∘ Prod.fst := rfl
      rw [split, ← PMF.map_comp, uniform_map_fst, offset_uniform facts e]
    have event : {c : Coins T | hint c e = true} ⊆
        (fun c => crtFin facts (readoutHom e c.pads)) ⁻¹' {x : Fin T.product | T.product - T.wrapBound < x.val} := by
      intro c hc
      have wrapped : T.product - T.wrapBound < offset c e := by
        simpa [hint, wrapHint] using hc
      exact wrapped
    refine (MeasureTheory.measure_mono event).trans ?_
    rw [← PMF.toOuterMeasure_map_apply, law, PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_fin]
    have card : Fintype.card {x : Fin T.product | T.product - T.wrapBound < x.val} ≤ T.wrapBound - 1 :=
      (Fintype.card_congr (Equiv.refl _)).le.trans (card_wrap_le T.product T.wrapBound)
    exact ENNReal.div_le_div_right (by exact_mod_cast card) _
  -- the union
  have union : (PMF.uniformOfFintype (Coins T)).toOuterMeasure {c | ∃ e, hint c e = true} ≤
      ∑ _e : Enc, ((T.wrapBound - 1 : ℕ) : ℝ≥0∞) / T.product := by
    have set : {c : Coins T | ∃ e, hint c e = true} = ⋃ e, {c | hint c e = true} := by
      ext c; simp
    rw [set]
    exact (MeasureTheory.measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun e _ => single e)
  have finite : ∑ _e : Enc, ((T.wrapBound - 1 : ℕ) : ℝ≥0∞) / T.product ≠ ⊤ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hM.ne'))
  refine (ENNReal.toReal_mono finite union).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast, Nat.cast_sub hB, Nat.cast_one]
  ring

end

end Kriterion.CRT.Privacy.BMR
