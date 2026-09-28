/-
CRT slice, prove-ahead arithmetic (lemmas L7, L11, L16, L17).

Everything here is stated on `Nat`, `ZMod` and `BitVec` against the lane definitions
(`Construction/CRT/Lanes.lean`: `deltaLanes`, `laneBit`, `peelDiv`) and the frozen interface (`wrapHint`, `wrapDecode`,
`wrapBound`). The sample CRT combination (`crtModulus`, `idem`, `crt`) is local; L16 is stated
for any combination with the CRT specification (`crt_add_of_spec`), so it instantiates with
the construction's.

* L7  `laneBit_add_shift`, `laneBit_add_smul_delta_zero`: adding `2^n * t` on the lanes where `Δ` is set
  flips lane bit `n` exactly where `Δ` is set and `t` is odd.
* L11 `peelDiv_label`: the peel is exact, `peelDiv (R + σ•Δ⃗) (U + (σ % 2^w)•Δ⃗) w
  = peelDiv R U w + (σ / 2^w)•Δ⃗`, with no divisibility hypothesis on `R - U`.
* L16 `crt_modEq`, `crt_lt`, `crt_add`: reconstruction by idempotents, proved from pairwise
  coprimality (no evaluation of the inverses).
* L17 `wrapDecode_exact`, `wrapDecode_crt`: the wrap hint `[O > M - B]` and the decoding
  "add `M` when the hint is set and `w < B`" return `u + O` exactly for every `u < B`, `O < M`
  when `2B ≤ M + 1`.
-/

import Construction.CRT.Lanes
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Batteries.Data.BitVec

namespace Kriterion.CRT.SliceC

open scoped BigOperators Function
open Cryptography Kriterion.CRT

/-! `Label`, `Lanes`, `laneCount`, `wrapHint`, `wrapDecode` are the frozen ones of
`Construction/CRT/Interface.lean`; `deltaLanes`, `laneBit`, `peelDiv` are those of
`Construction/CRT/Lanes.lean`. -/

/-! ### L7: the lane-bit shift -/

/-- Nat core of L7: adding `2^n * t` flips bit `n` exactly when `t` is odd. -/
theorem testBit_add_two_pow_mul (a t n : Nat) :
    (a + 2 ^ n * t).testBit n = xor (a.testBit n) (t.testBit 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ n) with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one t with h' | h' <;>
    simp [Nat.add_mod, h, h']

/-- `ZMod` form of L7: for `n < w`, bit `n` of `(a + 2^n t).val` is bit `n` of `a.val` xor `t` odd. -/
theorem val_testBit_add_shift {w n : Nat} (hn : n < w) (a : ZMod (2 ^ w)) (t : Nat) :
    (a + ((2 ^ n * t : Nat) : ZMod (2 ^ w))).val.testBit n = xor (a.val.testBit n) (t.testBit 0) := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, Nat.testBit_mod_two_pow]
  simp only [hn, decide_true, Bool.true_and]
  exact testBit_add_two_pow_mul _ _ _

/-- L7 on labels: adding `(2^n t)•Δ⃗` flips lane bit `n` on the lanes where `Δ` is set, when `t` is odd. -/
theorem laneBit_add_shift {l n : Nat} (hn : n < l) (A : Lanes l) (Δ : Label) (t : Nat) :
    laneBit (A + ((2 ^ n * t : Nat) : ZMod (2 ^ l)) • deltaLanes l Δ) n =
      laneBit A n ^^^ (if t.testBit 0 then Δ else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [laneBit, BitVec.getLsbD_xor, BitVec.getLsbD_ofFnLE, hi, dite_true, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, deltaLanes]
  by_cases hΔ : Δ.getLsbD i
  · simp only [hΔ, if_true, mul_one]
    rw [val_testBit_add_shift hn]
    by_cases ht : t.testBit 0 <;> simp [ht, hΔ]
  · simp only [hΔ]
    by_cases ht : t.testBit 0 <;> simp [ht, hΔ]

/-- L7 at `n = 0`: `laneBit (A + σ•Δ⃗) 0 = laneBit A 0 ⊕ (σ mod 2)·Δ`. -/
theorem laneBit_add_smul_delta_zero {l : Nat} (hl : 0 < l) (A : Lanes l) (Δ : Label) (σ : Nat) :
    laneBit (A + (σ : ZMod (2 ^ l)) • deltaLanes l Δ) 0 =
      laneBit A 0 ^^^ (if σ % 2 = 1 then Δ else 0) := by
  have h := laneBit_add_shift hl A Δ σ
  simp only [pow_zero, one_mul, Nat.testBit_zero] at h
  rw [h]
  by_cases hσ : σ % 2 = 1 <;> simp [hσ]

/-! ### L11: the exact peel -/

/-- Nat core of L11: for `w ≤ rb`, `(x mod 2^rb) / 2^w ≡ x / 2^w (mod 2^(rb - w))`. -/
theorem natCast_mod_two_pow_div {rb w : Nat} (hw : w ≤ rb) (x : Nat) :
    (((x % 2 ^ rb) / 2 ^ w : Nat) : ZMod (2 ^ (rb - w))) = ((x / 2 ^ w : Nat) : ZMod (2 ^ (rb - w))) := by
  have hsplit : 2 ^ rb = 2 ^ w * 2 ^ (rb - w) := by
    rw [← pow_add, Nat.add_sub_cancel' hw]
  rw [hsplit, Nat.mod_mul_right_div_self, ZMod.natCast_mod]

/-- Lane core of L11: adding `2^w k` before the peel adds `k` after it. -/
theorem peel_lane_add {rb w : Nat} (hw : w ≤ rb) (d : ZMod (2 ^ rb)) (k : Nat) :
    (((d + ((2 ^ w * k : Nat) : ZMod (2 ^ rb))).val / 2 ^ w : Nat) : ZMod (2 ^ (rb - w))) =
      ((d.val / 2 ^ w : Nat) : ZMod (2 ^ (rb - w))) + (k : ZMod (2 ^ (rb - w))) := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, natCast_mod_two_pow_div hw,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos w)]
  push_cast
  ring

/-- L11 in difference form: shifting `R` by `(2^w k)•Δ⃗` shifts the peel by `k•Δ⃗`. -/
theorem peelDiv_add_shift {rb w : Nat} (hw : w ≤ rb) (R U : Lanes rb) (Δ : Label) (k : Nat) :
    peelDiv (R + ((2 ^ w * k : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ) U w =
      peelDiv R U w + (k : ZMod (2 ^ (rb - w))) • deltaLanes (rb - w) Δ := by
  funext i
  simp only [peelDiv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, deltaLanes]
  by_cases hΔ : Δ.getLsbD i.1
  · simp only [hΔ, if_true, mul_one]
    rw [show R i + ((2 ^ w * k : Nat) : ZMod (2 ^ rb)) - U i
        = (R i - U i) + ((2 ^ w * k : Nat) : ZMod (2 ^ rb)) by ring]
    exact peel_lane_add hw _ _
  · rw [if_neg hΔ, if_neg hΔ]
    simp

/-- **L11** `peelDiv_label`: if the evaluator holds `R + σ•Δ⃗` and `U + s•Δ⃗` with `s = σ mod 2^w`,
its peel is the garbler's peel plus `⌊σ / 2^w⌋•Δ⃗`. No hypothesis on `R - U` is needed. -/
theorem peelDiv_label {rb w : Nat} (hw : w ≤ rb) (R U : Lanes rb) (Δ : Label) (σ : Nat) :
    peelDiv (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) (U + ((σ % 2 ^ w : Nat) : ZMod (2 ^ rb)) •
        deltaLanes rb Δ) w =
      peelDiv R U w + ((σ / 2 ^ w : Nat) : ZMod (2 ^ (rb - w))) • deltaLanes (rb - w) Δ := by
  have hσ : (σ : ZMod (2 ^ rb)) = ((σ % 2 ^ w : Nat) : ZMod (2 ^ rb)) +
      ((2 ^ w * (σ / 2 ^ w) : Nat) : ZMod (2 ^ rb)) := by
    rw [← Nat.cast_add, Nat.mod_add_div]
  have hdiff : R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ -
      (U + ((σ % 2 ^ w : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ) =
      (R + ((2 ^ w * (σ / 2 ^ w) : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ) - U := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hσ]
    ring
  have hpeel : ∀ R₁ U₁ R₂ U₂ : Lanes rb, R₁ - U₁ = R₂ - U₂ → peelDiv R₁ U₁ w = peelDiv R₂ U₂ w := by
    intro R₁ U₁ R₂ U₂ h
    funext i
    simp only [peelDiv, h]
  rw [hpeel _ _ _ _ hdiff, peelDiv_add_shift hw]

/-! ### L16: CRT reconstruction by idempotents -/

section CRT

variable {k : Nat}

/-- `M = Π m_i`. -/
def crtModulus (m : Fin k → Nat) : Nat := ∏ i, m i

/-- `ε_i = (M / m_i) · ((M / m_i)⁻¹ mod m_i)`. -/
def idem (m : Fin k → Nat) (i : Fin k) : Nat :=
  (crtModulus m / m i) * ((crtModulus m / m i : Nat) : ZMod (m i))⁻¹.val

/-- `crt r = (Σ_i r_i · ε_i) mod M`. -/
def crt (m : Fin k → Nat) (r : Fin k → Nat) : Nat := (∑ i, r i * idem m i) % crtModulus m

theorem crtModulus_pos {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) : 0 < crtModulus m :=
  Finset.prod_pos fun i _ => hpos i

theorem crtModulus_div_eq {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) (i : Fin k) :
    crtModulus m / m i = ∏ j ∈ Finset.univ.erase i, m j := by
  unfold crtModulus
  rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i),
    Nat.mul_div_cancel_left _ (hpos i)]

theorem dvd_crtModulus (m : Fin k → Nat) (i : Fin k) : m i ∣ crtModulus m :=
  Finset.dvd_prod_of_mem m (Finset.mem_univ i)

/-- The idempotents, generically from pairwise coprimality: `ε_i ≡ [i = j] (mod m_j)`. -/
theorem idem_cast {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m))
    (i j : Fin k) : ((idem m i : Nat) : ZMod (m j)) = if i = j then 1 else 0 := by
  have : NeZero (m j) := ⟨(hpos j).ne'⟩
  split_ifs with hij
  · subst hij
    have hcop : Nat.Coprime (crtModulus m / m i) (m i) := by
      rw [crtModulus_div_eq hpos]
      exact Nat.Coprime.prod_left fun j hj => hco (Finset.ne_of_mem_erase hj)
    simp only [idem, Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  · have hdvd : m j ∣ crtModulus m / m i := by
      rw [crtModulus_div_eq hpos]
      exact Finset.dvd_prod_of_mem m (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    simp only [idem, Nat.cast_mul]
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdvd, zero_mul]

/-- **L16**, residue part: `crt r ≡ r_j (mod m_j)`. -/
theorem crt_modEq {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m))
    (r : Fin k → Nat) (j : Fin k) : crt m r ≡ r j [MOD m j] := by
  have h1 : crt m r ≡ ∑ i, r i * idem m i [MOD m j] :=
    (Nat.mod_modEq _ _).of_dvd (dvd_crtModulus m j)
  refine h1.trans ?_
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  simp only [idem_cast hpos hco, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- **L16**, range part: `crt r < M`. -/
theorem crt_lt {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) (r : Fin k → Nat) : crt m r < crtModulus m :=
  Nat.mod_lt _ (crtModulus_pos hpos)

/-- Congruence modulo every `m_j` gives congruence modulo `M` (pairwise coprime). -/
theorem modEq_crtModulus_of_forall {m : Fin k → Nat} (hco : Pairwise (Nat.Coprime on m)) {a b : Nat}
    (h : ∀ j, a ≡ b [MOD m j]) : a ≡ b [MOD crtModulus m] := by
  have co : (List.finRange k).Pairwise (Nat.Coprime on m) :=
    List.Nodup.pairwise_of_forall_ne (List.nodup_finRange k) fun i _ j _ hij => hco hij
  unfold crtModulus
  rw [Fin.prod_univ_def]
  exact (Nat.modEq_list_map_prod_iff co).mpr fun j _ => h j

/-- **L16**, generic form: any combination function `crt` with the CRT specification
(`crt r ≡ r_j (mod m_j)` for every `j`, and `crt r < M`) turns evaluator residues congruent to the
garbler's plus `x` into `(crt R + x) mod M`. The construction's reconstruction is one such function. -/
theorem crt_add_of_spec {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m))
    (crtF : (Fin k → Nat) → Nat) (hmod : ∀ r j, crtF r % m j = r j % m j)
    (hlt : ∀ r, crtF r < ∏ i, m i)
    (L R : Fin k → Nat) (x : Nat) (h : ∀ j, L j ≡ R j + x [MOD m j]) :
    crtF L = (crtF R + x) % ∏ i, m i := by
  have hM : 0 < ∏ i, m i := crtModulus_pos hpos
  apply Nat.ModEq.eq_of_lt_of_lt _ (hlt L) (Nat.mod_lt _ hM)
  apply modEq_crtModulus_of_forall hco
  intro j
  have h1 : crtF L ≡ L j [MOD m j] := hmod L j
  have h2 : crtF R ≡ R j [MOD m j] := hmod R j
  have h3 : (crtF R + x) % crtModulus m ≡ crtF R + x [MOD m j] :=
    (Nat.mod_modEq _ _).of_dvd (dvd_crtModulus m j)
  exact h1.trans ((h j).trans ((h2.symm.add_right x).trans h3.symm))

/-- **L16**, the idempotent combination of this file satisfies the specification. -/
theorem crt_spec {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m))
    (r : Fin k → Nat) (j : Fin k) : crt m r % m j = r j % m j :=
  crt_modEq hpos hco r j

/-- **L16**, the form the evaluator uses, for the idempotent combination of this file. -/
theorem crt_add {m : Fin k → Nat} (hpos : ∀ i, 0 < m i) (hco : Pairwise (Nat.Coprime on m))
    (L R : Fin k → Nat) (x : Nat) (h : ∀ j, L j ≡ R j + x [MOD m j]) :
    crt m L = (crt m R + x) % crtModulus m :=
  crt_add_of_spec hpos hco (crt m) (crt_spec hpos hco) (crt_lt hpos) L R x h

end CRT

/-! ### L17: the wrap hint

`wrapHint` (strict `M - B < O`) and `wrapDecode` are the frozen definitions of `Interface.lean`. -/

/-- The core of L17 for any `u < B`; the hypothesis `2B ≤ M + 1` is the weakest that works. -/
theorem wrapDecode_exact {M B u O : Nat} (hu : u < B) (hO : O < M) (hMB : 2 * B ≤ M + 1) :
    wrapDecode M B (wrapHint M B O) ((u + O) % M) = u + O := by
  unfold wrapDecode wrapHint
  by_cases hlt : u + O < M
  · rw [Nat.mod_eq_of_lt hlt]
    by_cases hh : M - B < O
    · have hnb : ¬ (u + O < B) := by omega
      simp [hh, hnb]
    · simp [hh]
  · have hge : M ≤ u + O := Nat.le_of_not_lt hlt
    have hmod : (u + O) % M = u + O - M := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    have hh : M - B < O := by omega
    have hw : u + O - M < B := by omega
    rw [hmod]
    simp only [hh, hw, decide_true, Bool.and_self, if_true]
    omega

/-- **L17** `wrapHint_exact`, the frozen statement: for naturals `a * x < B`, `O < M` and `2B ≤ M`,
the decoding of `w = (a * x + O) mod M` with the hint of `O` is `a * x + O`. -/
theorem wrapHint_exact {M B a x O : Nat} (hax : a * x < B) (hO : O < M) (hMB : 2 * B ≤ M) :
    wrapDecode M B (wrapHint M B O) ((a * x + O) % M) = a * x + O :=
  wrapDecode_exact hax hO (by omega)

/-- **L16 + L17**: with any CRT combination satisfying the specification, the evaluator's decoded
integer is `u + O` for the garbler's CRT offset `O = crt R`, whenever each evaluator residue is
congruent to the garbler's plus `u`. -/
theorem wrapDecode_crt {k : Nat} {m : Fin k → Nat} (hpos : ∀ i, 0 < m i)
    (hco : Pairwise (Nat.Coprime on m)) (crtF : (Fin k → Nat) → Nat)
    (hmod : ∀ r j, crtF r % m j = r j % m j) (hlt : ∀ r, crtF r < ∏ i, m i)
    {B u : Nat} (hu : u < B) (hMB : 2 * B ≤ (∏ i, m i) + 1)
    (L R : Fin k → Nat) (h : ∀ j, L j ≡ R j + u [MOD m j]) :
    wrapDecode (∏ i, m i) B (wrapHint (∏ i, m i) B (crtF R)) (crtF L) = crtF R + u := by
  rw [crt_add_of_spec hpos hco crtF hmod hlt L R u h, Nat.add_comm (crtF R) u,
    wrapDecode_exact hu (hlt R) hMB]

/-- The field reading of L17: with `u = a.val * v.val` and `B = wrapBound p = (p - 1)^2 + 1`, the
decoded integer read in `ZMod p` is `a * v + O`. -/
theorem wrapDecode_field {p M O : Nat} [NeZero p] (a v : ZMod p) (hO : O < M)
    (hMB : 2 * wrapBound p ≤ M) :
    ((wrapDecode M (wrapBound p) (wrapHint M (wrapBound p) O)
        ((a.val * v.val + O) % M) : Nat) : ZMod p) = a * v + (O : ZMod p) := by
  have ha : a.val ≤ p - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt a)
  have hv : v.val ≤ p - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt v)
  have hu : a.val * v.val < wrapBound p := by
    unfold wrapBound; rw [sq]; exact Nat.lt_succ_of_le (Nat.mul_le_mul ha hv)
  rw [wrapHint_exact hu hO hMB]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]

end Kriterion.CRT.SliceC
