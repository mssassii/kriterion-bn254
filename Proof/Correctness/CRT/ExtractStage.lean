/-
CRT slice, package C3: the round invariant of one fused extraction stage (lemmas L8 to L10 of section 5), generic in the stage width `w` and the cast width `rb`.

The stage is Duty-Free's fused `word_to_bin_up`
as executed by `ext_stage_garble` / `ext_stage_eval` of `harness/tricks/n86_crt_spec.py`. In table T9
both fused stages have cast width equal to the remainder width (stage 0: `w = 7`, `rb = ℓ`; stage 1:
`w = ℓ - 8`, `rb = ℓ - 7`), so one width `rb` serves both. The tree material and the casts are
arbitrary functions (`StageParams.mat`, `StageParams.castF`); instantiated with the hash of the layer
at the frozen tags they give the statement for every `H : HashN`, hence on every answer table.

The definitions are `Construction/CRT/ExtractSpec.lean` (namespace
`Kriterion.CRT.ExtractSpec`), which is this file's earlier local text copied verbatim
(`reduceTo`, `deltaLanes`, `laneBit`, `peelDiv` from `Construction/CRT/Lanes.lean`):

* garbler: tree nodes by recursion on the level (`gNode`: level 0 is the root `Δ`, whose step
  material is the free bit mask `b_0`, so level 1 is the free pair `(b_0 ⊕ Δ, b_0)`); leaves, casts,
  class sums `res_n`, bit masks, level sums, joins, pin, upcast and peeled remainder;
* evaluator: the rounds of `ext_stage_eval` as a course-of-values recursion `eRounds` carrying the
  active label and the labels of the closed siblings; every other node is recomputed from its
  closed branch point by `offPath` (the pure content of `expand`).

Main statement `stage_invariant` (L10): leaves `E_α = G_α ⊕ [α = s]·Δ`, bits `b^E_n = b_n ⊕ s_n·Δ`,
upcast `U^E = res_w + s•Δ⃗`, and the peeled remainder `R'^E = R' + ⌊σ/2^w⌋•Δ⃗`.
-/

import Proof.Correctness.CRT.Arith
import Construction.CRT.ExtractSpec

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec

/-! ### XOR sums and XOR algebra -/

theorem xsum_congr {ι : Type} {s : Finset ι} {f g : ι → Label} (h : ∀ x ∈ s, f x = g x) :
    xsum s f = xsum s g :=
  Finset.fold_congr h

theorem xsum_erase {ι : Type} [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∈ s) (f : ι → Label) :
    xsum s f = f a ^^^ xsum (s.erase a) f := by
  unfold xsum
  conv_lhs => rw [← Finset.insert_erase ha]
  rw [Finset.fold_insert (Finset.notMem_erase a s)]

theorem xor_zero_block {width : Nat} (a : BitVec width) : a ^^^ (0 : BitVec width) = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp

theorem xor_cancel_mid {width : Nat} (a b c : BitVec width) : (a ^^^ c) ^^^ (b ^^^ c) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem xor_hot_solve {width : Nat} (b d t e : BitVec width) : (b ^^^ d) ^^^ ((t ^^^ e) ^^^ b) ^^^ e = t ^^^ d := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases b.getLsbD i <;> cases d.getLsbD i <;> cases t.getLsbD i <;> cases e.getLsbD i <;> rfl

theorem xor_swap_right {width : Nat} (a b c : BitVec width) : (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-! ### Bits of naturals modulo powers of two -/

theorem mod_two_pow_mod_of_le {x a b : Nat} (h : a ≤ b) : x % 2 ^ b % 2 ^ a = x % 2 ^ a :=
  Nat.mod_mod_of_dvd x (pow_dvd_pow 2 h)

theorem testBit_eq_of_mod_eq {x s n i : Nat} (h : x % 2 ^ n = s % 2 ^ n) (hi : i < n) :
    x.testBit i = s.testBit i := by
  have := congrArg (fun y => y.testBit i) h
  simpa [Nat.testBit_mod_two_pow, hi] using this

theorem mod_succ_eq_of {x s n : Nat} (h : x % 2 ^ n = s % 2 ^ n) (hb : x.testBit n = s.testBit n) :
    x % 2 ^ (n + 1) = s % 2 ^ (n + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow]
  by_cases hi : i < n + 1
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · rw [testBit_eq_of_mod_eq h hi']
    · subst hi'; rw [hb]
  · simp [hi]

/-! ### Reduction of lanes -/

theorem reduceTo_lane_eq_castHom {l t : Nat} (h : t ≤ l) (x : ZMod (2 ^ l)) :
    ((x.val : Nat) : ZMod (2 ^ t)) = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ t)) x := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem reduceTo_sub {l w : Nat} (h : w ≤ l) (A B : Lanes l) :
    reduceTo w (A - B) = reduceTo w A - reduceTo w B := by
  funext i
  simp only [reduceTo, Pi.sub_apply, reduceTo_lane_eq_castHom h, map_sub]

/-- Below the reduced width, lane bits are unchanged by the reduction. -/
theorem laneBit_reduceTo {l w n : Nat} (hn : n < w) (A : Lanes l) :
    laneBit (reduceTo w A) n = laneBit A n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [laneBit, BitVec.getLsbD_ofFnLE, hi, dite_true, reduceTo]
  rw [ZMod.val_natCast, Nat.testBit_mod_two_pow]
  simp [hn]

section Stage

variable {rb : Nat} (sp : StageParams rb)

/-! ### L9: off-path nodes agree with the garbler's -/

/-- The closed labels up to round `N` are the garbler's siblings of the active path. -/
def ClosedOK (b0 Δ : Label) (s : Nat) (cl : Nat → Label) (N : Nat) : Prop :=
  ∀ j < N, ∀ x, x % 2 ^ j = s % 2 ^ j → x.testBit j ≠ s.testBit j → cl j = gNode sp b0 Δ (j + 1) x

theorem stepMat_succ (b0 : Label) (n x : Nat) (lab : Label) :
    stepMat sp b0 (n + 1) x lab = sp.mat (n + 1) x lab :=
  rfl

theorem offPath_succ (s : Nat) (cl : Nat → Label) (n x : Nat) :
    offPath sp s cl (n + 1) x =
      if x % 2 ^ n = s % 2 ^ n then cl n
      else if x.testBit n then sp.mat n (x % 2 ^ n) (offPath sp s cl n (x % 2 ^ n))
      else offPath sp s cl n (x % 2 ^ n) ^^^ sp.mat n (x % 2 ^ n) (offPath sp s cl n (x % 2 ^ n)) :=
  rfl

theorem gNode_succ (b0 Δ : Label) (n x : Nat) :
    gNode sp b0 Δ (n + 1) x =
      if x.testBit n then stepMat sp b0 n (x % 2 ^ n) (gNode sp b0 Δ n (x % 2 ^ n))
      else gNode sp b0 Δ n (x % 2 ^ n) ^^^ stepMat sp b0 n (x % 2 ^ n) (gNode sp b0 Δ n (x % 2 ^ n)) :=
  rfl

/-- **L9** `offPath_eq`: every node that branches off the active path before level `N` has the
garbler's label, once the closed labels up to round `N` do. -/
theorem offPath_eq (b0 Δ : Label) (s : Nat) (cl : Nat → Label) (N : Nat)
    (hcl : ClosedOK sp b0 Δ s cl N) :
    ∀ n x, x % 2 ^ (min n N) ≠ s % 2 ^ (min n N) → offPath sp s cl n x = gNode sp b0 Δ n x := by
  intro n
  induction n with
  | zero => intro x hx; simp [Nat.mod_one] at hx
  | succ n ih =>
    intro x hx
    by_cases hp : x % 2 ^ n = s % 2 ^ n
    · -- the parent is on the active path: `x` is the closed sibling of round `n`
      have hnN : n < N := by
        by_contra hle
        have hmin : min (n + 1) N = N := Nat.min_eq_right (by omega)
        rw [hmin] at hx
        apply hx
        rw [← mod_two_pow_mod_of_le (x := x) (Nat.le_of_not_lt hle),
          ← mod_two_pow_mod_of_le (x := s) (Nat.le_of_not_lt hle), hp]
      have hmin : min (n + 1) N = n + 1 := Nat.min_eq_left hnN
      rw [hmin] at hx
      have hbit : x.testBit n ≠ s.testBit n := fun hb => hx (mod_succ_eq_of hp hb)
      rw [offPath_succ, if_pos hp]
      exact hcl n hnN x hp hbit
    · -- the parent is off the path: descend from it
      have hpar : (x % 2 ^ n) % 2 ^ (min n N) ≠ s % 2 ^ (min n N) := by
        by_cases hnN : n < N
        · rw [Nat.min_eq_left (Nat.le_of_lt hnN), Nat.mod_mod]; exact hp
        · have h1 : min n N = N := Nat.min_eq_right (by omega)
          have h2 : min (n + 1) N = N := Nat.min_eq_right (by omega)
          rw [h1, mod_two_pow_mod_of_le (by omega)]
          rw [h2] at hx; exact hx
      have ihp := ih (x % 2 ^ n) hpar
      cases n with
      | zero => exact absurd (by simp [Nat.mod_one]) hp
      | succ n =>
        rw [offPath_succ, if_neg hp, ihp, gNode_succ sp b0 Δ (n + 1) x, stepMat_succ]

/-! ### L8: the class sums -/

/-- **L8** `classSum_eval`: with the closed labels correct up to round `n` (`n ≤ w`) and the
garbler's pin, `R_n + q_n • (P - T_n) = res_n + q_n • Δ⃗`. -/
theorem eRes_eq (R : Lanes rb) (Δ : Label) (s : Nat) (cl : Nat → Label) (n : Nat) (hn : n ≤ sp.w)
    (hcl : ClosedOK sp (gBit0 sp R) Δ s cl n) :
    eRes sp s cl (gPin sp R Δ) n =
      gRes sp R Δ n + ((s % 2 ^ n : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ := by
  have hcast : ∀ α ∈ eClass sp s n, eCast sp s cl α = gCast sp R Δ α := by
    intro α hα
    have hα' : α % 2 ^ n ≠ s % 2 ^ n := (Finset.mem_filter.mp hα).2
    unfold eCast gCast gLeaf
    rw [offPath_eq sp (gBit0 sp R) Δ s cl n hcl sp.w α (by rw [Nat.min_eq_right hn]; exact hα')]
  have hsum1 : ∑ α ∈ eClass sp s n, ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • eCast sp s cl α =
      ∑ α ∈ eClass sp s n, ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • gCast sp R Δ α :=
    Finset.sum_congr rfl fun α hα => by rw [hcast α hα]
  have hsum2 : ∑ α ∈ eClass sp s n, eCast sp s cl α = ∑ α ∈ eClass sp s n, gCast sp R Δ α :=
    Finset.sum_congr rfl hcast
  unfold eRes
  rw [hsum1, hsum2]
  -- split the leaves into the closed classes and the active class
  set p : Nat → Prop := fun α => α % 2 ^ n ≠ s % 2 ^ n with hpdef
  have hact : ∑ α ∈ (Finset.range (2 ^ sp.w)).filter (fun α => ¬ p α),
      ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • gCast sp R Δ α =
      ∑ α ∈ (Finset.range (2 ^ sp.w)).filter (fun α => ¬ p α),
      ((s % 2 ^ n : Nat) : ZMod (2 ^ rb)) • gCast sp R Δ α := by
    apply Finset.sum_congr rfl
    intro α hα
    have h := (Finset.mem_filter.mp hα).2
    simp only [hpdef, ne_eq, not_not] at h
    rw [h]
  have hres := Finset.sum_filter_add_sum_filter_not (Finset.range (2 ^ sp.w)) p
    (fun α => ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • gCast sp R Δ α)
  have hpin := Finset.sum_filter_add_sum_filter_not (Finset.range (2 ^ sp.w)) p
    (fun α => gCast sp R Δ α)
  unfold gRes gPin
  rw [← hres, ← hpin, hact]
  unfold eClass
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [← Finset.mul_sum]
  ring

/-! ### The bit labels (L7 applied through L8) -/

theorem gBit_succ (R : Lanes rb) (Δ : Label) (n : Nat) (hn : n < sp.w) (hn0 : n ≠ 0) :
    gBit sp R Δ n = laneBit (R - gRes sp R Δ n) n := by
  unfold gBit
  rw [if_neg hn0, ← reduceTo_sub sp.hw, laneBit_reduceTo hn]

/-- The evaluator's bit label of round `n < w` is the garbler's mask XOR `s_n · Δ`. -/
theorem eBit_eq (R : Lanes rb) (Δ : Label) (σ s : Nat) (hs : s = σ % 2 ^ sp.w) (cl : Nat → Label)
    (n : Nat) (hn : n < sp.w) (hcl : ClosedOK sp (gBit0 sp R) Δ s cl n) :
    eBit sp (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) s cl (gPin sp R Δ) n =
      gBit sp R Δ n ^^^ (if s.testBit n then Δ else 0) := by
  have hrb : n < rb := Nat.lt_of_lt_of_le hn sp.hw
  have hsn : s.testBit n = σ.testBit n := by
    rw [hs, Nat.testBit_mod_two_pow]; simp [hn]
  by_cases hn0 : n = 0
  · subst hn0
    unfold eBit gBit gBit0
    simp only [if_true]
    rw [laneBit_reduceTo hn, laneBit_reduceTo hn, laneBit_add_smul_delta_zero hrb]
    have : s.testBit 0 = decide (σ % 2 = 1) := by rw [hsn, Nat.testBit_zero]
    by_cases hσ : σ % 2 = 1 <;> simp [hσ, this]
  · unfold eBit
    rw [if_neg hn0, ← reduceTo_sub sp.hw, laneBit_reduceTo hn, eRes_eq sp R Δ s cl n (Nat.le_of_lt hn) hcl,
      gBit_succ sp R Δ n hn hn0]
    have hq : s % 2 ^ n = σ % 2 ^ n := by
      rw [hs]; exact mod_two_pow_mod_of_le (Nat.le_of_lt hn)
    have hsplit : R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ -
        (gRes sp R Δ n + ((s % 2 ^ n : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ) =
        (R - gRes sp R Δ n) + ((2 ^ n * (σ / 2 ^ n) : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ := by
      have hσ : (σ : ZMod (2 ^ rb)) = ((σ % 2 ^ n : Nat) : ZMod (2 ^ rb)) +
          ((2 ^ n * (σ / 2 ^ n) : Nat) : ZMod (2 ^ rb)) := by
        rw [← Nat.cast_add, Nat.mod_add_div]
      rw [hq]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hσ]
      ring
    rw [hsplit, laneBit_add_shift hrb, Nat.testBit_div_two_pow, Nat.zero_add, hsn]

/-! ### Level sums -/

theorem gLevelSum_eq (R : Lanes rb) (Δ : Label) (s : Nat) (cl : Nat → Label) (n : Nat)
    (hcl : ClosedOK sp (gBit0 sp R) Δ s cl n) :
    gLevelSum sp R Δ n =
      sp.mat n (s % 2 ^ n) (gNode sp (gBit0 sp R) Δ n (s % 2 ^ n)) ^^^ eLevelSum sp s cl n := by
  unfold gLevelSum eLevelSum
  rw [xsum_erase (Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos n)))]
  congr 1
  apply xsum_congr
  intro x hx
  have hxne := Finset.ne_of_mem_erase hx
  have hxlt := Finset.mem_range.mp (Finset.mem_of_mem_erase hx)
  rw [offPath_eq sp (gBit0 sp R) Δ s cl n hcl n x (by
    rw [Nat.min_self, Nat.mod_eq_of_lt hxlt]; exact hxne)]

/-! ### L10: the rounds -/

/-- The solved hot material of round `n < w` is the garbler's step material at the active slot,
XOR `s_n · Δ`. -/
theorem eHot_eq (R : Lanes rb) (Δ : Label) (σ s : Nat) (hs : s = σ % 2 ^ sp.w) (cl : Nat → Label)
    (n : Nat) (hn : n < sp.w) (hcl : ClosedOK sp (gBit0 sp R) Δ s cl n) :
    eHot sp (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) s (gJoin sp R Δ) (gPin sp R Δ) cl n =
      stepMat sp (gBit0 sp R) n (s % 2 ^ n) (gNode sp (gBit0 sp R) Δ n (s % 2 ^ n)) ^^^
        (if s.testBit n then Δ else 0) := by
  have hb := eBit_eq sp R Δ σ s hs cl n hn hcl
  unfold eHot
  by_cases hn0 : n = 0
  · subst hn0
    simp only [if_true]
    rw [hb]
    rfl
  · rw [if_neg hn0, hb]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    unfold gJoin
    rw [gLevelSum_eq sp R Δ s cl (m + 1) hcl]
    simp only [stepMat]
    exact xor_hot_solve _ _ _ _

/-- **L10**, the round invariant: after `n ≤ w` rounds the active label is the garbler's active
node XOR `Δ`, and the closed labels are the garbler's siblings. -/
theorem eRounds_spec (R : Lanes rb) (Δ : Label) (σ s : Nat) (hs : s = σ % 2 ^ sp.w) :
    ∀ n ≤ sp.w,
      (eRounds sp (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) s (gJoin sp R Δ) (gPin sp R Δ) n).1 =
          gNode sp (gBit0 sp R) Δ n (s % 2 ^ n) ^^^ Δ ∧
        ClosedOK sp (gBit0 sp R) Δ s
          (eRounds sp (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) s (gJoin sp R Δ) (gPin sp R Δ) n).2 n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    show (0 : Label) = Δ ^^^ Δ
    rw [BitVec.xor_self]
    rfl
  | succ n ih =>
    intro hn
    obtain ⟨hact, hcl⟩ := ih (Nat.le_of_succ_le hn)
    have hy := eHot_eq sp R Δ σ s hs _ n (Nat.lt_of_succ_le hn) hcl
    set st := eRounds sp (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) s (gJoin sp R Δ) (gPin sp R Δ) n
      with hst
    set q := s % 2 ^ n with hq
    set Y := stepMat sp (gBit0 sp R) n q (gNode sp (gBit0 sp R) Δ n q) with hY
    have hsq : (s % 2 ^ (n + 1)) % 2 ^ n = q := mod_two_pow_mod_of_le (Nat.le_succ n)
    have hsb : (s % 2 ^ (n + 1)).testBit n = s.testBit n := by
      rw [Nat.testBit_mod_two_pow]; simp
    have hGs : gNode sp (gBit0 sp R) Δ (n + 1) (s % 2 ^ (n + 1)) =
        if s.testBit n then Y else gNode sp (gBit0 sp R) Δ n q ^^^ Y := by
      rw [gNode_succ, hsq, hsb]
    refine ⟨?_, ?_⟩
    · show (if s.testBit n then eHot sp _ s _ _ st.2 n else st.1 ^^^ eHot sp _ s _ _ st.2 n) = _
      rw [hy, hGs, hact]
      cases s.testBit n
      · simp only [Bool.false_eq_true, if_false]
        rw [xor_zero_block]
        exact xor_swap_right _ _ _
      · simp only [if_true]
    · intro j hj x hxj hxb
      show (if j = n then (if s.testBit n then st.1 ^^^ eHot sp _ s _ _ st.2 n
        else eHot sp _ s _ _ st.2 n) else st.2 j) = _
      by_cases hjn : j = n
      · subst hjn
        rw [if_pos rfl, hy, hact, gNode_succ, hxj]
        have hxb' : x.testBit j = !s.testBit j := by
          cases h1 : x.testBit j <;> cases h2 : s.testBit j <;> simp_all
        rw [hxb']
        cases s.testBit j
        · simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true]
          exact xor_zero_block _
        · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
          exact xor_cancel_mid _ _ _
      · rw [if_neg hjn]
        exact hcl j (by omega) x hxj hxb

/-! ### L10: the stage invariant -/

/-- **L10** `stage_invariant`: for every tree material and cast function, every remainder mask
`R`, offset `Δ` and value `σ`, the evaluator run on `R^E = R + σ•Δ⃗` with the garbler's joins and pin
and the stage value `s = σ mod 2^w` holds: the leaf labels `G_α ⊕ [α = s]·Δ`; the bit labels
`b_n ⊕ s_n·Δ` for `n < w`; the upcast `res_w + s•Δ⃗`; and the peeled remainder
`R' + ⌊σ / 2^w⌋•Δ⃗`, an arithmetic label of the next remainder value. -/
theorem stage_invariant (hw1 : 1 ≤ sp.w) (R : Lanes rb) (Δ : Label) (σ s : Nat)
    (hs : s = σ % 2 ^ sp.w) :
    let RE := R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ
    (∀ α < 2 ^ sp.w, eLeaf sp RE s (gJoin sp R Δ) (gPin sp R Δ) α =
        gLeaf sp R Δ α ^^^ (if α = s then Δ else 0)) ∧
      (∀ n < sp.w, eBitOut sp RE s (gJoin sp R Δ) (gPin sp R Δ) n =
        gBit sp R Δ n ^^^ (if s.testBit n then Δ else 0)) ∧
      eUp sp RE s (gJoin sp R Δ) (gPin sp R Δ) =
        gRes sp R Δ sp.w + (s : ZMod (2 ^ rb)) • deltaLanes rb Δ ∧
      eNext sp RE s (gJoin sp R Δ) (gPin sp R Δ) =
        gNext sp R Δ + ((σ / 2 ^ sp.w : Nat) : ZMod (2 ^ (rb - sp.w))) • deltaLanes (rb - sp.w) Δ := by
  intro RE
  have _ := hw1
  have hslt : s < 2 ^ sp.w := by rw [hs]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsmod : s % 2 ^ sp.w = s := Nat.mod_eq_of_lt hslt
  obtain ⟨hact, hcl⟩ := eRounds_spec sp R Δ σ s hs sp.w le_rfl
  have hup : eUp sp RE s (gJoin sp R Δ) (gPin sp R Δ) =
      gRes sp R Δ sp.w + (s : ZMod (2 ^ rb)) • deltaLanes rb Δ := by
    unfold eUp
    rw [eRes_eq sp R Δ s _ sp.w le_rfl hcl, hsmod]
  refine ⟨?_, ?_, hup, ?_⟩
  · intro α hα
    unfold eLeaf gLeaf
    by_cases has : α = s
    · subst has
      rw [if_pos rfl, if_pos rfl, hact, hsmod]
    · rw [if_neg has, if_neg has, xor_zero_block]
      exact offPath_eq sp (gBit0 sp R) Δ s _ sp.w hcl sp.w α (by
        rw [Nat.min_self, Nat.mod_eq_of_lt hα, hsmod]; exact has)
  · intro n hn
    unfold eBitOut
    exact eBit_eq sp R Δ σ s hs _ n hn (eRounds_spec sp R Δ σ s hs n (Nat.le_of_lt hn)).2
  · unfold eNext gNext
    rw [hup, hs]
    exact peelDiv_label sp.hw R (gRes sp R Δ sp.w) Δ σ

end Stage

/-! ### The per-wire form over the layer's hash -/

/-- One fused stage over the hash of the layer: tree material `hLabel H label (treeTag level slot)`
and leaf casts `castLanes rb (hlong H (embed label) (castTag leaf) (castAnswers rb))` (D11). At the frozen
tags, `treeTag = fun n x => tagCode Family.extTree κ i st n x 0` and
`castTag = fun α j => tagCode Family.extCast κ i st 0 α j`. -/
def hashStage (H : HashN) {rb : Nat} (w : Nat) (hw : w ≤ rb) (treeTag castTag : Nat → Nat → Nat) :
    StageParams rb where
  w := w
  hw := hw
  mat := fun n x lab => hLabel H lab (treeTag n x)
  castF := fun α lab => castLanes rb (hlong H (embed lab) (castTag α) (castAnswers rb))

/-- **C3, per-wire form**: `stage_invariant` for every hash `H : HashN` and every tag assignment;
with `H = tableHash T` it is the statement on an answer table `T`, with hot positions overridden
by `Function.update`s of `T`. -/
theorem stage_invariant_hash (H : HashN) {rb : Nat} (w : Nat) (hw : w ≤ rb) (hw1 : 1 ≤ w)
    (treeTag castTag : Nat → Nat → Nat) (R : Lanes rb) (Δ : Label) (σ s : Nat) (hs : s = σ % 2 ^ w) :
    let sp := hashStage H w hw treeTag castTag
    let RE := R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ
    (∀ α < 2 ^ sp.w, eLeaf sp RE s (gJoin sp R Δ) (gPin sp R Δ) α =
        gLeaf sp R Δ α ^^^ (if α = s then Δ else 0)) ∧
      (∀ n < sp.w, eBitOut sp RE s (gJoin sp R Δ) (gPin sp R Δ) n =
        gBit sp R Δ n ^^^ (if s.testBit n then Δ else 0)) ∧
      eUp sp RE s (gJoin sp R Δ) (gPin sp R Δ) =
        gRes sp R Δ sp.w + (s : ZMod (2 ^ rb)) • deltaLanes rb Δ ∧
      eNext sp RE s (gJoin sp R Δ) (gPin sp R Δ) =
        gNext sp R Δ + ((σ / 2 ^ sp.w : Nat) : ZMod (2 ^ (rb - sp.w))) • deltaLanes (rb - sp.w) Δ :=
  stage_invariant (hashStage H w hw treeTag castTag) hw1 R Δ σ s hs

end Kriterion.CRT.SliceC
