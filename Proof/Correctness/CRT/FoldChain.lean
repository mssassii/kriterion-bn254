/-
CRT slice, conversion chain part C: reindex (L12), folds (L13) and the pin codec, on the
programs (`Construction/CRT/Fold.lean`, `Interface.lean`) at `.eval H`, for every `H : HashN`.

* `reindex_invariant` (L12): the class XORs of a one-hot of `h < 2^n` form a one-hot of `h mod m`.
* `foldEvalM_correct`, `foldsEvalM_correct` (L13): a fold with bit `β` moves the hot index from
  `hot` to `(hot + β·(2^j mod m)) mod m`; iterated from `keep` to `ell - 1` on a value `σ < 2^ell`
  from the hot index `(σ mod 2^keep) mod m`, the hot index ends at `σ mod m` (`foldHot_final`).
  No hypothesis on `m` beyond `0 < m` (odd `m` is not needed for correctness).
* `pinOfBlocks_pinBlocks`: the dense pin codec round-trips.
-/

import Proof.Correctness.CRT.StageProgram

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

/-! ### Folds over `Fin` as `xsum` -/

theorem foldl_ite_eq_xorFold {c : Nat} (P : Fin c → Prop) [DecidablePred P] (f : Fin c → Block) :
    Fin.foldl c (fun acc x => if P x then acc ^^^ f x else acc) 0 =
      xorFold (fun x => if P x then f x else 0) := by
  unfold xorFold
  congr 1
  funext acc x
  by_cases h : P x
  · simp only [h, if_true]
  · simp only [h, if_false, xor_zero_block]

theorem xsum_indicator (N h : Nat) (hh : h < N) (v : Block) :
    xsum (Finset.range N) (fun x => if x = h then v else 0) = v := by
  rw [xsum_erase (Finset.mem_range.mpr hh), if_pos rfl]
  rw [xsum_congr (g := fun _ => (0 : Block)) (fun x hx => if_neg (Finset.ne_of_mem_erase hx)),
    xsum_zero_fun, xor_zero_block]

/-! ### L12: reindex -/

/-- **L12** `reindex_invariant`: if the evaluator's one-hot of `2^n` labels is the garbler's XOR
`Δ` at `h < 2^n`, its reindex modulo `m` is the garbler's XOR `Δ` at `h mod m`. -/
theorem reindex_invariant (n m : Nat) (G E : Fin (2 ^ n) → Block) (Δ : Block) (h : Nat)
    (hh : h < 2 ^ n) (hE : ∀ x, E x = G x ^^^ (if x.val = h then Δ else 0)) (ρ : Fin m) :
    reindex n E m ρ = reindex n G m ρ ^^^ (if ρ.val = h % m then Δ else 0) := by
  unfold reindex
  simp only [stored_eq]
  rw [foldl_ite_eq_xorFold, foldl_ite_eq_xorFold, xorFold_eq_xsum, xorFold_eq_xsum]
  have hsplit : ∀ x ∈ Finset.range (2 ^ n),
      (if hx : x < 2 ^ n then (if (⟨x, hx⟩ : Fin (2 ^ n)).val % m = ρ.val then E ⟨x, hx⟩ else 0) else 0) =
        (if hx : x < 2 ^ n then (if (⟨x, hx⟩ : Fin (2 ^ n)).val % m = ρ.val then G ⟨x, hx⟩ else 0) else 0) ^^^
          (if x = h then (if h % m = ρ.val then Δ else 0) else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    rw [dif_pos hx', dif_pos hx', hE]
    simp only
    by_cases hxh : x = h
    · subst hxh
      by_cases hr : x % m = ρ.val
      · simp [hr]
      · simp [hr, xor_zero_block]
    · by_cases hr : x % m = ρ.val
      · simp [hr, hxh, xor_zero_block]
      · simp [hr, hxh, xor_zero_block]
  rw [xsum_congr hsplit, xsum_xor, xsum_indicator _ _ hh]
  congr 1
  by_cases hr : h % m = ρ.val
  · rw [if_pos hr, if_pos hr.symm]
  · rw [if_neg hr, if_neg (fun e => hr e.symm)]

/-! ### L13: one fold -/

theorem foldSource_val {m : Nat} (ρ : Fin m) (shift : Nat) :
    (foldSource ρ shift).val = (ρ.val + m - shift % m) % m := rfl

/-- The source of slot `ρ` is `hot` exactly when `ρ` is `hot + shift` modulo `m`. -/
theorem foldSource_eq_iff {m : Nat} (ρ : Fin m) (shift hot : Nat) (hhot : hot < m) :
    (foldSource ρ shift).val = hot ↔ ρ.val = (hot + shift) % m := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) ρ.isLt
  have hs : shift % m < m := Nat.mod_lt _ hm
  rw [foldSource_val]
  have hle : shift % m ≤ ρ.val + m := by omega
  constructor
  · intro h
    have hz : ((ρ.val + m - shift % m : Nat) : ZMod m) = (hot : ZMod m) := by
      rw [ZMod.natCast_eq_natCast_iff', h, Nat.mod_eq_of_lt hhot]
    rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_mod] at hz
    have hz' : (ρ.val : ZMod m) = ((hot + shift : Nat) : ZMod m) := by
      rw [Nat.cast_add, ← hz]; ring
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ρ.isLt] at hz'
    exact hz'
  · intro h
    have hz : (ρ.val : ZMod m) = ((hot + shift : Nat) : ZMod m) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ρ.isLt, h]
    have hz' : ((ρ.val + m - shift % m : Nat) : ZMod m) = (hot : ZMod m) := by
      rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_mod, hz,
        Nat.cast_add]
      ring
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hhot] at hz'
    exact hz'

theorem foldl_skip_eq_xorFoldExcept {m : Nat} (hot : Nat) (hhot : hot < m) (f : Fin m → Block) :
    Fin.foldl m (fun acc other => if other.val = hot then acc else acc ^^^ f other) 0 =
      xorFoldExcept ⟨hot, hhot⟩ f := by
  unfold xorFoldExcept
  congr 1
  funext acc other
  by_cases h : other.val = hot
  · rw [if_pos h, if_pos (Fin.ext h)]
  · rw [if_neg h, if_neg (fun e => h (congrArg Fin.val e))]

theorem eval_foldGarbleM (H : HashN) (m : Nat) (tagOf : Nat → Nat) (shift : Nat) (bitMask : Block)
    (labels : Fin m → Block) :
    (foldGarbleM m tagOf shift bitMask labels).eval H =
      (fun ρ => labels ρ ^^^ h128 H (labels ρ) (tagOf ρ.val) ^^^
          h128 H (labels (foldSource ρ shift)) (tagOf (foldSource ρ shift).val),
        xorFold (fun ρ => h128 H (labels ρ) (tagOf ρ.val)) ^^^ bitMask) := by
  simp [foldGarbleM]

/-- The evaluator's cold fold materials (the program's table). -/
def foldColdE (H : HashN) (m : Nat) (tagOf : Nat → Nat) (hot : Nat) (labels : Fin m → Block)
    (ρ : Fin m) : Block :=
  if ρ.val = hot then 0 else h128 H (labels ρ) (tagOf ρ.val)

/-- The evaluator's fold materials, the hot one solved from the join. -/
def foldMatE (H : HashN) (m : Nat) (tagOf : Nat → Nat) (hot : Nat) (bitLabel join : Block)
    (labels : Fin m → Block) (ρ : Fin m) : Block :=
  if ρ.val = hot then
    bitLabel ^^^ join ^^^
      Fin.foldl m (fun acc other => if other.val = hot then acc else
        acc ^^^ foldColdE H m tagOf hot labels other) 0
  else foldColdE H m tagOf hot labels ρ

theorem eval_ite_pure (H : HashN) (c : Prop) [Decidable c] (a : Block) (p : CM Block) :
    (if c then (pure a : CM Block) else p).eval H = if c then a else p.eval H := by
  split <;> rfl

theorem eval_foldEvalM (H : HashN) (m : Nat) (tagOf : Nat → Nat) (shift hot : Nat)
    (bitLabel join : Block) (labels : Fin m → Block) (ρ : Fin m) :
    (foldEvalM m tagOf shift hot bitLabel join labels).eval H ρ =
      labels ρ ^^^ foldMatE H m tagOf hot bitLabel join labels ρ ^^^
        foldMatE H m tagOf hot bitLabel join labels (foldSource ρ shift) := by
  unfold foldMatE foldColdE
  simp only [foldEvalM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq,
    eval_ite_pure, eval_h128M]

/-- **L13** for one fold: the evaluator's fold (hot at `hot`, bit label the mask XOR `β·Δ`, the
garbler's join) is the garbler's fold XOR `Δ` at `(hot + β·shift) mod m`. -/
theorem foldEvalM_correct (H : HashN) (m : Nat) (tagOf : Nat → Nat) (shift : Nat) (G E : Fin m → Block)
    (Δ : Block) (hot : Nat) (hhot : hot < m) (β : Bool) (bitMask : Block)
    (hE : ∀ ρ, E ρ = G ρ ^^^ (if ρ.val = hot then Δ else 0)) (ρ : Fin m) :
    (foldEvalM m tagOf shift hot (bitMask ^^^ (if β then Δ else 0))
        ((foldGarbleM m tagOf shift bitMask G).eval H).2 E).eval H ρ =
      ((foldGarbleM m tagOf shift bitMask G).eval H).1 ρ ^^^
        (if ρ.val = (hot + (if β then shift else 0)) % m then Δ else 0) := by
  rw [eval_foldEvalM, eval_foldGarbleM]
  simp only
  set u : Fin m → Block := fun ρ => h128 H (G ρ) (tagOf ρ.val) with hu
  have hcold : ∀ ρ : Fin m, ρ.val ≠ hot → E ρ = G ρ := by
    intro ρ h; rw [hE, if_neg h, xor_zero_block]
  -- the evaluator's materials are the garbler's XOR `β·Δ` at `hot`
  have hmat : ∀ ρ : Fin m,
      foldMatE H m tagOf hot (bitMask ^^^ (if β then Δ else 0)) (xorFold u ^^^ bitMask) E ρ =
        u ρ ^^^ (if ρ.val = hot ∧ β = true then Δ else 0) := by
    intro ρ
    unfold foldMatE
    by_cases hρ : ρ.val = hot
    · rw [if_pos hρ, foldl_skip_eq_xorFoldExcept hot hhot,
        xorFoldExcept_congr _ _ u (by
          intro o ho
          have ho' : o.val ≠ hot := fun e => ho (Fin.ext e)
          unfold foldColdE
          rw [if_neg ho', hcold o ho']), xorFoldExcept_eq]
      have hρ' : ρ = ⟨hot, hhot⟩ := Fin.ext hρ
      subst hρ'
      cases β
      · simp only [Bool.false_eq_true, if_false, and_false, xor_zero_block]
        xor_norm
      · simp only [if_true, and_self]
        xor_norm
    · rw [if_neg hρ]
      unfold foldColdE
      rw [if_neg hρ, hcold ρ hρ]
      simp only [hρ, false_and, if_false, xor_zero_block]
      rfl
  rw [hmat ρ, hmat (foldSource ρ shift), hE]
  simp only [hu]
  have hsrc := foldSource_eq_iff ρ shift hot hhot
  cases β
  · simp only [Bool.false_eq_true, and_false, if_false, xor_zero_block, Nat.add_zero,
      Nat.mod_eq_of_lt hhot]
    split_ifs <;> xor_norm
  · simp only [and_true, if_true]
    by_cases h1 : ρ.val = hot <;> by_cases h2 : (foldSource ρ shift).val = hot
    · rw [if_pos h1, if_pos h2, if_pos (hsrc.mp h2)]; xor_norm
    · rw [if_pos h1, if_neg h2, if_neg (fun e => h2 (hsrc.mpr e))]; xor_norm
    · rw [if_neg h1, if_pos h2, if_pos (hsrc.mp h2)]; xor_norm
    · rw [if_neg h1, if_neg h2, if_neg (fun e => h2 (hsrc.mpr e))]; xor_norm

/-! ### L13 iterated -/

/-- The hot index after the folds at positions `position, ..., position + count - 1`. -/
def foldHot (m value : Nat) : Nat → Nat → Nat → Nat
  | 0, _, hot => hot
  | count + 1, position, hot =>
      foldHot m value count (position + 1)
        ((hot + (if value.testBit position then foldShift m position else 0)) % m)

theorem eval_foldsGarbleM_succ (H : HashN) (m : Nat) (tagOf : Nat → Nat → Nat) (bitMask : Nat → Block)
    (count position : Nat) (labels : Fin m → Block) :
    (foldsGarbleM m tagOf bitMask (count + 1) position labels).eval H =
      let step := (foldGarbleM m (tagOf position) (foldShift m position) (bitMask position) labels).eval H
      let rest := (foldsGarbleM m tagOf bitMask count (position + 1) step.1).eval H
      (rest.1, fun at_ => if at_ = position then step.2 else rest.2 at_) := by
  simp only [foldsGarbleM, FreeQuery.eval_bind, FreeQuery.eval_pure]

/-- **L13 iterated** `foldsEvalM_correct`. -/
theorem foldsEvalM_correct (H : HashN) (m : Nat) (tagOf : Nat → Nat → Nat) (value : Nat) (Δ : Block)
    (bitMask bitLabel join : Nat → Block) :
    ∀ count position hot (G E : Fin m → Block), hot < m →
      (∀ ρ, E ρ = G ρ ^^^ (if ρ.val = hot then Δ else 0)) →
      (∀ j, position ≤ j → j < position + count →
        bitLabel j = bitMask j ^^^ (if value.testBit j then Δ else 0)) →
      (∀ j, position ≤ j → j < position + count →
        join j = ((foldsGarbleM m tagOf bitMask count position G).eval H).2 j) →
      ((foldsEvalM m tagOf value bitLabel join count position hot E).eval H).2 =
          foldHot m value count position hot ∧
        ∀ ρ, ((foldsEvalM m tagOf value bitLabel join count position hot E).eval H).1 ρ =
          ((foldsGarbleM m tagOf bitMask count position G).eval H).1 ρ ^^^
            (if ρ.val = foldHot m value count position hot then Δ else 0) := by
  intro count
  induction count with
  | zero =>
    intro position hot G E _ hE _ _
    exact ⟨rfl, hE⟩
  | succ c ih =>
    intro position hot G E hhot hE hbit hjoin
    have hjoin' := hjoin position le_rfl (by omega)
    rw [eval_foldsGarbleM_succ] at hjoin'
    simp only [if_pos rfl] at hjoin'
    simp only [foldsEvalM, FreeQuery.eval_bind]
    rw [hbit position le_rfl (by omega), hjoin']
    have hstep := foldEvalM_correct H m (tagOf position) (foldShift m position) G E Δ hot hhot
      (value.testBit position) (bitMask position) hE
    have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hhot
    have hhot' : (hot + (if value.testBit position then foldShift m position else 0)) % m < m :=
      Nat.mod_lt _ hm
    have hrest := ih (position + 1) _ _ _ hhot' hstep
      (fun j h1 h2 => hbit j (by omega) (by omega))
      (by
        intro j h1 h2
        rw [hjoin j (by omega) (by omega), eval_foldsGarbleM_succ]
        simp only
        rw [if_neg (by omega)])
    rw [eval_foldsGarbleM_succ]
    exact hrest

/-- The folds end at `σ mod m`: from the hot index `(σ mod 2^p) mod m`, the folds at positions
`p .. p + c - 1` reach `(σ mod 2^(p + c)) mod m`. -/
theorem foldHot_eq (m value : Nat) (hm : 0 < m) :
    ∀ c p hot, hot = value % 2 ^ p % m → foldHot m value c p hot = value % 2 ^ (p + c) % m := by
  intro c
  induction c with
  | zero => intro p hot h; show hot = _; rw [h, Nat.add_zero]
  | succ c ih =>
    intro p hot h
    simp only [foldHot]
    rw [ih (p + 1) _ ?_]
    · rw [show p + 1 + c = p + (c + 1) by omega]
    · rw [h, mod_two_pow_succ_split, foldShift]
      cases value.testBit p
      · simp
      · simp only [if_true]
        exact (Nat.add_mod _ _ _).symm

/-! ### The pin codec -/

theorem digits_lt {B : Nat} (hB : 0 < B) :
    ∀ (k : Nat) (d : Fin k → Nat), (∀ i, d i < B) → ∑ i : Fin k, d i * B ^ i.val < B ^ k := by
  intro k
  induction k with
  | zero => intro d _; simp
  | succ k ih =>
    intro d hd
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i => d i.castSucc) (fun i => hd _)
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    have h2 : d (Fin.last k) + 1 ≤ B := hd _
    calc ∑ i : Fin k, d i.castSucc * B ^ i.val + d (Fin.last k) * B ^ k
        < B ^ k + d (Fin.last k) * B ^ k := by omega
      _ = (d (Fin.last k) + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ h2
      _ = B ^ (k + 1) := by ring

theorem digits_get {B : Nat} (hB : 0 < B) :
    ∀ (k : Nat) (d : Fin k → Nat), (∀ i, d i < B) → ∀ j : Fin k,
      (∑ i : Fin k, d i * B ^ i.val) / B ^ j.val % B = d j := by
  intro k
  induction k with
  | zero => intro d _ j; exact j.elim0
  | succ k ih =>
    intro d hd j
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlow := digits_lt hB k (fun i => d i.castSucc) (fun i => hd _)
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.val_last]
      rw [Nat.add_mul_div_right _ _ (Nat.pow_pos hB), Nat.div_eq_of_lt hlow, Nat.zero_add,
        Nat.mod_eq_of_lt (hd _)]
    | cast j =>
      simp only [Fin.val_castSucc]
      have hjk : j.val < k := j.isLt
      have hsplit : d (Fin.last k) * B ^ k = (d (Fin.last k) * B ^ (k - j.val)) * B ^ j.val := by
        rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hjk)]
      have hkj : k - j.val = (k - j.val - 1) + 1 := by omega
      rw [hsplit, Nat.add_mul_div_right _ _ (Nat.pow_pos hB), hkj, pow_succ,
        show d (Fin.last k) * (B ^ (k - j.val - 1) * B) = B * (d (Fin.last k) * B ^ (k - j.val - 1)) by
          ring,
        Nat.add_mul_mod_self_left]
      exact ih (fun i => d i.castSucc) (fun i => hd _) j

theorem blocks_reassemble (N : Nat) :
    ∀ c : Nat, ∑ k : Fin c, (N / 2 ^ (128 * k.val) % 2 ^ 128) * 2 ^ (128 * k.val) = N % 2 ^ (128 * c) := by
  intro c
  induction c with
  | zero => simp [Nat.mod_one]
  | succ c ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, show 128 * (c + 1) = 128 * c + 128 by ring, pow_add, Nat.mod_mul]
    ring

/-- The dense pin codec round-trips: `pinOfBlocks width (pinBlocks P) = P`. -/
theorem pinOfBlocks_pinBlocks {width : Nat} (hw : 0 < width) (P : Lanes width) :
    pinOfBlocks width (pinBlocks P) = P := by
  have hB : 0 < 2 ^ width := Nat.two_pow_pos width
  have hpow : ∀ i : Nat, 2 ^ (width * i) = (2 ^ width) ^ i := fun i => by rw [pow_mul]
  have hdig : ∀ i : Fin laneCount, (P i).val < 2 ^ width := fun i => ZMod.val_lt (P i)
  have hN : pinNat P < 2 ^ (128 * width) := by
    have h := digits_lt hB laneCount (fun i => (P i).val) hdig
    unfold pinNat
    simp only [hpow]
    calc _ < (2 ^ width) ^ laneCount := h
      _ = 2 ^ (128 * width) := by rw [← pow_mul, Nat.mul_comm]
  funext lane
  unfold pinOfBlocks pinBlocks
  have hval : ∑ index : Fin width, (BitVec.ofNat 128 (pinNat P >>> (128 * index.val))).toNat *
      2 ^ (128 * index.val) = pinNat P := by
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [blocks_reassemble, Nat.mod_eq_of_lt hN]
  rw [hval, Nat.shiftRight_eq_div_pow]
  have hget := digits_get hB laneCount (fun i => (P i).val) hdig lane
  unfold pinNat
  simp only [hpow]
  rw [← ZMod.natCast_mod _ (2 ^ width), hget, ZMod.natCast_zmod_val]

end Kriterion.CRT.SliceC
