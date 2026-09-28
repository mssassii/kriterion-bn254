/-
CRT slice, delivery part 3: the body (L15) on the programs
`bodyGarbleM`/`bodyEvalM` (`Construction/CRT/Body.lean`) at `.eval H`, and the CRT specification of
the table's idempotent combination (`crtWith T.product T.idempotent`) that feeds L16.

* `body_correct` (L15): with the evaluator's final one-hot the garbler's XOR `Δ` at `hot` and the
  residue join `(pad sum + a) mod m`, the evaluator's residue is `R + hot·a` modulo `m`.
* `table_crt_mod`, `table_crt_lt`: `crtWith T.product (stored T.idempotent)` has the CRT
  specification for positive, pairwise coprime moduli (proved from coprimality, no evaluation).
-/

import Proof.Correctness.CRT.ChunkStep

namespace Kriterion.CRT.SliceC

open scoped BigOperators Function
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

/-! ### Sums with the hot slot left out -/

theorem sum_split_hot {M : Type} [AddCommMonoid M] {m : Nat} (hot : Nat) (hhot : hot < m)
    (f : Fin m → M) :
    ∑ ρ : Fin m, f ρ = ∑ ρ : Fin m, (if ρ.val = hot then 0 else f ρ) + f ⟨hot, hhot⟩ := by
  have h1 : ∀ ρ : Fin m, f ρ = (if ρ.val = hot then 0 else f ρ) + (if ρ = ⟨hot, hhot⟩ then f ρ else 0) := by
    intro ρ
    by_cases hρ : ρ.val = hot
    · have : ρ = ⟨hot, hhot⟩ := Fin.ext hρ
      rw [if_pos hρ, if_pos this, zero_add]
    · have : ρ ≠ ⟨hot, hhot⟩ := fun h => hρ (by rw [h])
      rw [if_neg hρ, if_neg this, add_zero]
  conv_lhs => rw [Finset.sum_congr rfl (fun ρ _ => h1 ρ)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-! ### L15: the body -/

theorem eval_padVectorM (H : HashN) (m S q : Nat) (label : Label) (tagOf : Nat → Nat) :
    (padVectorM m S q label tagOf).eval H =
      fun e => digit m (fractionValue m S q (hlong H (embed label) tagOf q)) e.val := by
  simp [padVectorM]

/-- **L15** `body_correct`: if the evaluator's final one-hot is the garbler's XOR `Δ` at `hot` and the
residue joins are the garbler's pad sums plus the slopes modulo `m`, the evaluator's residue of
every encoding is congruent to the garbler's residue plus `slope·hot` modulo `m`. -/
theorem body_correct (H : HashN) (m S q coord i : Nat) (hm : 0 < m) (final finalE : Fin m → Label)
    (Δ : Label) (hot : Nat) (hhot : hot < m)
    (hE : ∀ ρ, finalE ρ = final ρ ^^^ (if ρ.val = hot then Δ else 0))
    (slopes joins : Fin S → Nat)
    (hJ : ∀ e, joins e = (((bodyGarbleM m S q coord i final).eval H).padSum e + slopes e) % m)
    (e : Fin S) :
    (bodyEvalM m S q coord i finalE hot joins).eval H e ≡
      ((bodyGarbleM m S q coord i final).eval H).residue e + slopes e * hot [MOD m] := by
  haveI : NeZero m := ⟨hm.ne'⟩
  set V : Fin m → Fin S → Nat := fun ρ e =>
    digit m (fractionValue m S q (hlong H (embed (final ρ)) (bodyTag coord i ρ.val) q)) e.val with hV
  have hg : (bodyGarbleM m S q coord i final).eval H =
      { residue := fun e => (∑ ρ : Fin m, (ρ.val : ZMod m) * (V ρ e : ZMod m)).val
        padSum := fun e => (∑ ρ : Fin m, (V ρ e : ZMod m)).val } := by
    simp [bodyGarbleM, eval_padVectorM, V]
  have hcold : ∀ ρ : Fin m, ρ.val ≠ hot →
      digit m (fractionValue m S q (hlong H (embed (finalE ρ)) (bodyTag coord i ρ.val) q)) e.val = V ρ e := by
    intro ρ hρ
    rw [hE, if_neg hρ, xor_zero_block]
  obtain rfl : joins = fun e => (((bodyGarbleM m S q coord i final).eval H).padSum e + slopes e) % m :=
    funext hJ
  rw [hg]
  simp only [bodyEvalM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq,
    eval_ite_pure', eval_padVectorM]
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  push_cast
  rw [ZMod.natCast_mod, ZMod.natCast_zmod_val]
  have hknown : ∑ ρ : Fin m, (if ρ.val = hot then (0 : ZMod m) else
      (((if ρ.val = hot then (fun _ => 0 : Fin S → Nat) else
        fun e => digit m (fractionValue m S q (hlong H (embed (finalE ρ)) (bodyTag coord i ρ.val) q)) e.val) e : Nat) : ZMod m)) =
      ∑ ρ : Fin m, (if ρ.val = hot then (0 : ZMod m) else (V ρ e : ZMod m)) := by
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hρ : ρ.val = hot
    · rw [if_pos hρ, if_pos hρ]
    · rw [if_neg hρ, if_neg hρ, if_neg hρ, hcold ρ hρ]
  have hweighted : ∑ ρ : Fin m, (if ρ.val = hot then (0 : ZMod m) else (ρ.val : ZMod m) *
      (((if ρ.val = hot then (fun _ => 0 : Fin S → Nat) else
        fun e => digit m (fractionValue m S q (hlong H (embed (finalE ρ)) (bodyTag coord i ρ.val) q)) e.val) e : Nat) : ZMod m)) =
      ∑ ρ : Fin m, (if ρ.val = hot then (0 : ZMod m) else (ρ.val : ZMod m) * (V ρ e : ZMod m)) := by
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hρ : ρ.val = hot
    · rw [if_pos hρ, if_pos hρ]
    · rw [if_neg hρ, if_neg hρ, if_neg hρ, hcold ρ hρ]
  rw [hknown, hweighted, sum_split_hot hot hhot (fun ρ => (V ρ e : ZMod m)),
    sum_split_hot hot hhot (fun ρ => (ρ.val : ZMod m) * (V ρ e : ZMod m))]
  simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  ring

/-! ### The table's CRT combination -/

theorem idempotent_cast (T : CrtTable) (hpos : ∀ i, 0 < T.modulus i)
    (hco : Pairwise (Nat.Coprime on T.modulus)) (i j : Fin T.count) :
    ((T.idempotent i : Nat) : ZMod (T.modulus j)) = if i = j then 1 else 0 := by
  have hdvd : T.modulus j ∣ T.product := dvd_crtModulus T.modulus j
  have h := idem_cast hpos hco i j
  unfold CrtTable.idempotent CrtTable.inverseMod
  simp only
  rw [← ZMod.natCast_mod _ (T.modulus j), Nat.mod_mod_of_dvd _ hdvd, ZMod.natCast_mod]
  exact h

/-- The table's CRT combination has the CRT specification (L16's hypothesis). -/
theorem table_crt_mod (T : CrtTable) (hpos : ∀ i, 0 < T.modulus i)
    (hco : Pairwise (Nat.Coprime on T.modulus)) (r : Fin T.count → Nat) (j : Fin T.count) :
    crtWith T.product (stored T.idempotent) r % T.modulus j = r j % T.modulus j := by
  have h1 : crtWith T.product (stored T.idempotent) r ≡
      ∑ i, r i * T.idempotent i [MOD T.modulus j] :=
    (Nat.mod_modEq _ _).of_dvd (dvd_crtModulus T.modulus j)
  refine h1.trans ?_
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  simp only [idempotent_cast T hpos hco, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem table_crt_lt (T : CrtTable) (hpos : ∀ i, 0 < T.modulus i) (r : Fin T.count → Nat) :
    crtWith T.product (stored T.idempotent) r < T.product :=
  Nat.mod_lt _ (crtModulus_pos hpos)

end Kriterion.CRT.SliceC
