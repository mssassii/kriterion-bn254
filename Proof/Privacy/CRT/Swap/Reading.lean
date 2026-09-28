/-
**CRT privacy: the readings of uniform answers.**

Three facts the pad swap `G0 → G0U` and the conversion core need about how the construction reads hash answers
(`Construction/CRT/Interface.lean`):

1. **Casts (D11).** The block-aligned cast reading of uniform answers is uniform on `Lanes l`
   (`castLanes_uniform`): the answers pack into a uniform natural below `2 ^ (256 * castAnswers l)`
   (`packEquiv`), a uniform natural is a uniform bit vector (`bitsEquiv`), the lanes read disjoint bit ranges
   (`lanePos_injective`), a restriction of a uniform bit vector to an injectively indexed set of positions is uniform
   (`uniform_map_restrict`), and a lane vector is its bit array (`laneBitsEquiv`).
2. **Pads (D6), odd modulus.** For a uniform natural `u` below `2 ^ (256 q)`, the fraction reading
   `X = ⌊u * m ^ S / 2 ^ (256 q)⌋` is within `(2 ^ (256 q) mod m ^ S) / 2 ^ (256 q) ≤ m ^ S / 2 ^ (256 q)` of uniform
   below `m ^ S` (`fraction_etvDist_le`: every value has at least `⌊2 ^ (256 q) / m ^ S⌋` preimages), and the digits
   `(X / m ^ e mod m)_{e < S}` are a bijection onto `Fin S → ZMod m` (`digitsEquiv`), so the pad vector of uniform
   answers is within `m ^ S / 2 ^ (256 q)` of uniform (`padVector_etvDist_le`).
3. **Pads, the modulus `2 ^ k`** with `k * S ≤ 256 q`: the pad vector is exactly uniform (`padVector_uniform_pow2`).

Distances are `PMF.etvDist` (VCV-io), as in xinshu's `Phase3` files; the counting step is xinshu's
`etvDist_eq_tsum_tsub`.
-/

import Construction.CRT.Interface
import Proof.Privacy.Phase3.Basic

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy

open Cryptography
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_eq_tsum_tsub uniform_map_apply etvDist_map_le')
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv card_block)
open scoped ENNReal

noncomputable section

/-! ### Answers packed into one natural -/

theorem answerNat_lt (a : Block × Block) : answerNat a < 2 ^ 256 := by
  have h1 : a.1.toNat < 2 ^ 128 := a.1.isLt
  have h2 : a.2.toNat < 2 ^ 128 := a.2.isLt
  have h3 : answerNat a < 2 ^ 128 * (a.2.toNat + 1) := by
    unfold answerNat
    rw [Nat.mul_succ]
    omega
  calc answerNat a < 2 ^ 128 * (a.2.toNat + 1) := h3
    _ ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul_left _ h2
    _ = 2 ^ 256 := by rw [← pow_add]

theorem answerNat_injective : Function.Injective answerNat := by
  intro a b same
  have h1 : a.1.toNat < 2 ^ 128 := a.1.isLt
  have h2 : b.1.toNat < 2 ^ 128 := b.1.isLt
  unfold answerNat at same
  have low : a.1.toNat = b.1.toNat := by
    have key : (a.1.toNat + 2 ^ 128 * a.2.toNat) % 2 ^ 128
        = (b.1.toNat + 2 ^ 128 * b.2.toNat) % 2 ^ 128 := by rw [same]
    rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2] at key
  have high : a.2.toNat = b.2.toNat := by
    have key : (a.1.toNat + 2 ^ 128 * a.2.toNat) / 2 ^ 128
        = (b.1.toNat + 2 ^ 128 * b.2.toNat) / 2 ^ 128 := by rw [same]
    rwa [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128),
      Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2, zero_add, zero_add] at key
  exact Prod.ext (BitVec.eq_of_toNat_eq low) (BitVec.eq_of_toNat_eq high)

theorem packAnswers_succ (n : Nat) (answers : Fin (n + 1) → Block × Block) :
    packAnswers (n + 1) answers
      = packAnswers n (fun j => answers j.castSucc) + 2 ^ (256 * n) * answerNat (answers (Fin.last n)) := by
  unfold packAnswers
  rw [Fin.sum_univ_castSucc]
  simp

theorem packAnswers_lt : ∀ (n : Nat) (answers : Fin n → Block × Block),
    packAnswers n answers < 2 ^ (256 * n)
  | 0, answers => by simp [packAnswers]
  | n + 1, answers => by
      rw [packAnswers_succ]
      have ih := packAnswers_lt n (fun j => answers j.castSucc)
      have top := answerNat_lt (answers (Fin.last n))
      calc packAnswers n (fun j => answers j.castSucc) + 2 ^ (256 * n) * answerNat (answers (Fin.last n))
          < 2 ^ (256 * n) + 2 ^ (256 * n) * answerNat (answers (Fin.last n)) := by omega
        _ = 2 ^ (256 * n) * (answerNat (answers (Fin.last n)) + 1) := by ring
        _ ≤ 2 ^ (256 * n) * 2 ^ 256 := Nat.mul_le_mul_left _ top
        _ = 2 ^ (256 * (n + 1)) := by rw [← pow_add]; ring_nf

theorem packAnswers_injective : ∀ n : Nat, Function.Injective (packAnswers n)
  | 0 => fun a b _ => funext fun j => j.elim0
  | n + 1 => by
      intro a b same
      rw [packAnswers_succ, packAnswers_succ] at same
      have la := packAnswers_lt n (fun j => a j.castSucc)
      have lb := packAnswers_lt n (fun j => b j.castSucc)
      have pos : 0 < 2 ^ (256 * n) := Nat.two_pow_pos _
      have low : packAnswers n (fun j => a j.castSucc) = packAnswers n (fun j => b j.castSucc) := by
        have := congrArg (· % 2 ^ (256 * n)) same
        simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt la, Nat.mod_eq_of_lt lb] using this
      have high : answerNat (a (Fin.last n)) = answerNat (b (Fin.last n)) := by
        have := congrArg (· / 2 ^ (256 * n)) same
        simp only [Nat.add_mul_div_left _ _ pos, Nat.div_eq_of_lt la, Nat.div_eq_of_lt lb,
          zero_add] at this
        exact this
      have init := packAnswers_injective n low
      have last := answerNat_injective high
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact last
      · exact congrFun init i

theorem card_answers (n : Nat) : Fintype.card (Fin n → Block × Block) = 2 ^ (256 * n) := by
  rw [Fintype.card_fun, Fintype.card_prod, card_block, Fintype.card_fin, ← pow_add, ← pow_mul]

/-- `count` answers are one natural below `2 ^ (256 * count)`, bijectively. -/
def packEquiv (n : Nat) : (Fin n → Block × Block) ≃ Fin (2 ^ (256 * n)) :=
  Equiv.ofBijective (fun answers => ⟨packAnswers n answers, packAnswers_lt n answers⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b same => packAnswers_injective n (congrArg Fin.val same), by
        rw [card_answers, Fintype.card_fin]⟩)

@[simp] theorem packEquiv_val (n : Nat) (answers : Fin n → Block × Block) :
    (packEquiv n answers).val = packAnswers n answers := rfl

/-- Uniform answers pack to a uniform natural. -/
theorem packAnswers_uniform (n : Nat) :
    (PMF.uniformOfFintype (Fin n → Block × Block)).map (packEquiv n)
      = PMF.uniformOfFintype (Fin (2 ^ (256 * n))) :=
  uniformOfFintype_map_equiv (packEquiv n)

/-! ### Naturals as bit vectors -/

private theorem eq_of_testBit_lt {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (bits : ∀ t, t < n → a.testBit t = b.testBit t) : a = b := by
  refine Nat.eq_of_testBit_eq fun t => ?_
  by_cases small : t < n
  · exact bits t small
  · have hle : n ≤ t := Nat.le_of_not_lt small
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hle)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hle))]

/-- A natural below `2 ^ n` is its `n` low bits. -/
def bitsEquiv (n : Nat) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  Equiv.ofBijective (fun value t => value.val.testBit t.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b same => Fin.ext (eq_of_testBit_lt a.isLt b.isLt fun t ht => congrFun same ⟨t, ht⟩), by
        rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]⟩)

@[simp] theorem bitsEquiv_apply (n : Nat) (value : Fin (2 ^ n)) (t : Fin n) :
    bitsEquiv n value t = value.val.testBit t.val := rfl

/-- A lane vector is its array of bits (lane, bit). -/
def laneBitsEquiv (l : Nat) : Lanes l ≃ (Fin laneCount × Fin l → Bool) :=
  Equiv.ofBijective (fun lanes pair => (lanes pair.1).val.testBit pair.2.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b same => by
        funext lane
        refine ZMod.val_injective _ (eq_of_testBit_lt (ZMod.val_lt _) (ZMod.val_lt _) fun t ht => ?_)
        exact congrFun same (lane, ⟨t, ht⟩), by
        rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_bool, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]⟩)

@[simp] theorem laneBitsEquiv_apply (l : Nat) (lanes : Lanes l) (pair : Fin laneCount × Fin l) :
    laneBitsEquiv l lanes pair = (lanes pair.1).val.testBit pair.2.val := rfl

/-! ### Restricting a uniform bit vector to some positions -/

section Restrict

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Overwrite the positions in the range of `pos` with `f`. -/
private def overwritePositions (pos : κ → ι) (f : κ → Bool) (g : ι → Bool) : ι → Bool :=
  fun t => if h : ∃ k, pos k = t then f h.choose else g t

private theorem overwritePositions_comp (pos : κ → ι) (inj : Function.Injective pos) (f : κ → Bool) (g : ι → Bool) :
    overwritePositions pos f g ∘ pos = f := by
  funext k
  have h : ∃ k', pos k' = pos k := ⟨k, rfl⟩
  simp only [Function.comp, overwritePositions, dif_pos h]
  exact congrArg f (inj h.choose_spec)

private theorem overwritePositions_overwritePositions (pos : κ → ι) (f f' : κ → Bool) (g : ι → Bool) :
    overwritePositions pos f (overwritePositions pos f' g) = overwritePositions pos f g := by
  funext t
  unfold overwritePositions
  by_cases h : ∃ k, pos k = t
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, dif_neg h]

private theorem overwritePositions_self (pos : κ → ι) (g : ι → Bool) : overwritePositions pos (g ∘ pos) g = g := by
  funext t
  unfold overwritePositions
  by_cases h : ∃ k, pos k = t
  · rw [dif_pos h]
    exact congrArg g h.choose_spec
  · rw [dif_neg h]

/-- **A uniform bit vector read at injectively indexed positions is uniform.** -/
theorem uniform_map_restrict (pos : κ → ι) (inj : Function.Injective pos) :
    (PMF.uniformOfFintype (ι → Bool)).map (fun g => g ∘ pos) = PMF.uniformOfFintype (κ → Bool) := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun f1 f2 => ?_
  exact {
    toFun := fun g => ⟨overwritePositions pos f2 g.1, overwritePositions_comp pos inj f2 g.1⟩
    invFun := fun g => ⟨overwritePositions pos f1 g.1, overwritePositions_comp pos inj f1 g.1⟩
    left_inv := fun g => by
      apply Subtype.ext
      show overwritePositions pos f1 (overwritePositions pos f2 g.1) = g.1
      rw [overwritePositions_overwritePositions]
      have key := overwritePositions_self pos g.1
      rw [g.2] at key
      exact key
    right_inv := fun g => by
      apply Subtype.ext
      show overwritePositions pos f2 (overwritePositions pos f1 g.1) = g.1
      rw [overwritePositions_overwritePositions]
      have key := overwritePositions_self pos g.1
      rw [g.2] at key
      exact key }

end Restrict

/-! ### The lane positions of a block-aligned cast -/

section Cast

variable (l : Nat)

theorem lanesPerBlock_pos (hl : 0 < l) (hl' : l ≤ 128) : 0 < lanesPerBlock l :=
  Nat.div_pos hl' hl

theorem lanesPerBlock_mul_le : l * lanesPerBlock l ≤ 128 := Nat.mul_div_le 128 l

/-- Bit `j` of lane `lane` sits at `laneOffset l lane + j`. -/
theorem lane_bit_lt (hl : 0 < l) (hl' : l ≤ 128) (lane : Fin laneCount) (j : Fin l) :
    laneOffset l lane.val + j.val < 256 * castAnswers l := by
  have per := lanesPerBlock_pos l hl hl'
  have fits := lanesPerBlock_mul_le l
  set k := lanesPerBlock l with hk
  have inBlock : l * (lane.val % k) + j.val < 128 := by
    have hmod : lane.val % k + 1 ≤ k := Nat.mod_lt _ per
    have : l * (lane.val % k + 1) ≤ l * k := Nat.mul_le_mul_left l hmod
    have hj := j.isLt
    rw [Nat.mul_succ] at this
    omega
  have blocks : lane.val / k < castBlocks l := by
    unfold castBlocks
    rw [← hk]
    have hlane : lane.val < labelBits := lane.isLt
    apply (Nat.lt_div_iff_mul_lt per).mpr
    · have := Nat.div_mul_le_self lane.val k
      omega
  have answers : castBlocks l ≤ 2 * castAnswers l := by
    unfold castAnswers
    omega
  unfold laneOffset
  rw [← hk]
  calc 128 * (lane.val / k) + l * (lane.val % k) + j.val
      < 128 * (lane.val / k) + 128 := by omega
    _ = 128 * (lane.val / k + 1) := by ring
    _ ≤ 128 * castBlocks l := Nat.mul_le_mul_left _ blocks
    _ ≤ 256 * castAnswers l := by omega

/-- The bit positions of a cast, as a map into the bits of its answers. -/
def lanePos (hl : 0 < l) (hl' : l ≤ 128) (pair : Fin laneCount × Fin l) : Fin (256 * castAnswers l) :=
  ⟨laneOffset l pair.1.val + pair.2.val, lane_bit_lt l hl hl' pair.1 pair.2⟩

theorem lanePos_injective (hl : 0 < l) (hl' : l ≤ 128) : Function.Injective (lanePos l hl hl') := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ same
  have per := lanesPerBlock_pos l hl hl'
  have fits := lanesPerBlock_mul_le l
  set k := lanesPerBlock l with hk
  have eq : 128 * (i.val / k) + (l * (i.val % k) + j.val)
      = 128 * (i'.val / k) + (l * (i'.val % k) + j'.val) := by
    have := congrArg Fin.val same
    simp only [lanePos, laneOffset] at this
    rw [← hk] at this
    omega
  have small : ∀ (a : Fin laneCount) (b : Fin l), l * (a.val % k) + b.val < 128 := by
    intro a b
    have hmod : a.val % k + 1 ≤ k := Nat.mod_lt _ per
    have : l * (a.val % k + 1) ≤ l * k := Nat.mul_le_mul_left l hmod
    have hb := b.isLt
    rw [Nat.mul_succ] at this
    omega
  have s1 := small i j
  have s2 := small i' j'
  have block : i.val / k = i'.val / k := by omega
  have inner : l * (i.val % k) + j.val = l * (i'.val % k) + j'.val := by omega
  have slot : i.val % k = i'.val % k := by
    have a1 := congrArg (· / l) inner
    rwa [Nat.mul_add_div hl, Nat.mul_add_div hl, Nat.div_eq_of_lt j.isLt, Nat.div_eq_of_lt j'.isLt,
      add_zero, add_zero] at a1
  have bit : j.val = j'.val := by
    have a2 := congrArg (· % l) inner
    rwa [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at a2
  have lane : i.val = i'.val := by
    rw [← Nat.div_add_mod i.val k, ← Nat.div_add_mod i'.val k, block, slot]
  exact Prod.ext (Fin.ext lane) (Fin.ext bit)

/-- Bit `j` of a lane read by `castLanes` is bit `laneOffset + j` of the cast natural. -/
theorem castLanes_testBit (value : Nat) (lane : Fin laneCount) (j : Nat) (hj : j < l) :
    ((castLanes l value) lane).val.testBit j = value.testBit (laneOffset l lane.val + j) := by
  unfold castLanes
  rw [ZMod.val_natCast, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hj]

/-- **The D11 cast reading of uniform answers is uniform on `Lanes l`.** -/
theorem castLanes_uniform (hl : 0 < l) (hl' : l ≤ 128) :
    (PMF.uniformOfFintype (Fin (castAnswers l) → Block × Block)).map
        (fun answers => castLanes l (packAnswers (castAnswers l) answers))
      = PMF.uniformOfFintype (Lanes l) := by
  have factor : (fun answers => castLanes l (packAnswers (castAnswers l) answers))
      = (laneBitsEquiv l).symm ∘ (fun g => g ∘ lanePos l hl hl') ∘ (bitsEquiv (256 * castAnswers l))
          ∘ (packEquiv (castAnswers l)) := by
    funext answers
    apply (laneBitsEquiv l).injective
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
    funext pair
    rw [laneBitsEquiv_apply, castLanes_testBit l _ pair.1 pair.2.val pair.2.isLt]
    rfl
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, ← PMF.map_comp, packAnswers_uniform,
    uniformOfFintype_map_equiv, uniform_map_restrict _ (lanePos_injective l hl hl'),
    uniformOfFintype_map_equiv]

end Cast


/-! ### The fraction reading of pads (D6) -/

section Fraction

/-- **A map whose every fibre has at least `q` points** pushes the uniform law on `A`, of size `N q + r`, to within
`r / (N q + r)` of the uniform law on a codomain of size `N`. (xinshu's `etvDist_reduction_le`, for any finite
codomain instead of `ZMod p`.) -/
theorem etvDist_fibre_le {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [DecidableEq B]
    (N q r : Nat) (g : A → B) (cardB : Fintype.card B = N) (cardA : Fintype.card A = N * q + r)
    (fibres : ∀ y : B, q ≤ Fintype.card {x : A // g x = y}) :
    ((PMF.uniformOfFintype A).map g).etvDist (PMF.uniformOfFintype B)
      ≤ (r : ℝ≥0∞) / (N * q + r : Nat) := by
  have Npos : 0 < N := cardB ▸ Fintype.card_pos
  have sizePos : 0 < Fintype.card A := Fintype.card_pos
  have sizeNe : (Fintype.card A : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr sizePos.ne'
  have sizeTop : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have modNe : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Npos.ne'
  have modTop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have lower : ∀ y : B,
      (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ ≤ ((PMF.uniformOfFintype A).map g) y := by
    intro y
    rw [uniform_map_apply]
    exact mul_le_mul_left (Nat.cast_le.mpr (fibres y)) _
  have termwise : ∀ y : B,
      (PMF.uniformOfFintype B) y - ((PMF.uniformOfFintype A).map g) y
        ≤ (N : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
    intro y
    rw [PMF.uniformOfFintype_apply, cardB]
    exact tsub_le_tsub_left (lower y) _
  rw [etvDist_eq_tsum_tsub]
  calc (∑' y : B, ((PMF.uniformOfFintype B) y - ((PMF.uniformOfFintype A).map g) y))
      ≤ ∑' _y : B, ((N : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹) :=
        ENNReal.tsum_le_tsum termwise
    _ = (N : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, cardB, nsmul_eq_mul]
    _ = (r : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_sub (fun _ _ => modTop), ENNReal.mul_inv_cancel modNe modTop, ← mul_assoc]
        refine (ENNReal.sub_eq_of_eq_add
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top modTop (ENNReal.natCast_ne_top q))
            (ENNReal.inv_ne_top.mpr sizeNe)) ?_)
        rw [← add_mul]
        have total : ((r : ℝ≥0∞) + (N : ℝ≥0∞) * (q : ℝ≥0∞)) = (Fintype.card A : ℝ≥0∞) := by
          rw [cardA]
          push_cast
          ring
        rw [total, ENNReal.mul_inv_cancel sizeNe sizeTop]
    _ = (r : ℝ≥0∞) / (N * q + r : Nat) := by
        rw [ENNReal.div_eq_inv_mul, mul_comm, cardA]

variable (m S q : Nat) [NeZero m]

theorem fractionValue_lt (u : Nat) (hu : u < 2 ^ (256 * q)) : fractionValue m S q u < m ^ S := by
  unfold fractionValue
  have hpos : 0 < m ^ S := pow_pos (NeZero.pos m) S
  apply Nat.div_lt_of_lt_mul
  calc u * m ^ S < 2 ^ (256 * q) * m ^ S := mul_lt_mul_of_pos_right hu hpos
    _ = 2 ^ (256 * q) * m ^ S := rfl

/-- The fraction reading as a map from the pad natural to `Fin (m ^ S)`. -/
def fractionMap (u : Fin (2 ^ (256 * q))) : Fin (m ^ S) :=
  ⟨fractionValue m S q u.val, fractionValue_lt m S q u.val u.isLt⟩

instance instNonemptyFinPow : Nonempty (Fin (m ^ S)) := ⟨⟨0, pow_pos (NeZero.pos m) S⟩⟩

/-- The arithmetic of one fibre: with `c = ⌈X D / N⌉`, every `c + k` for `k < ⌊D / N⌋` lies in `[X D, (X + 1) D)` after
multiplication by `N`, and below `D`. -/
private theorem fibre_arith (N D X k : Nat) (Npos : 0 < N) (hX : X < N) (hk : k < D / N) :
    X * D ≤ ((X * D + N - 1) / N + k) * N ∧ ((X * D + N - 1) / N + k) * N < (X + 1) * D
      ∧ (X * D + N - 1) / N + k < D := by
  have split := Nat.div_add_mod (X * D + N - 1) N
  have remLt := Nat.mod_lt (X * D + N - 1) Npos
  generalize hc : (X * D + N - 1) / N = c at split ⊢
  have cLow : X * D ≤ N * c := by omega
  have cHigh : N * c ≤ X * D + N - 1 := by omega
  have kle : (k + 1) * N ≤ D := le_trans (Nat.mul_le_mul_right N hk) (Nat.div_mul_le_self D N)
  have e1 : (c + k) * N = N * c + k * N := by ring
  have e2 : (k + 1) * N = k * N + N := by ring
  have e3 : (X + 1) * D = X * D + D := by ring
  have lo : X * D ≤ (c + k) * N := by omega
  have hi : (c + k) * N < (X + 1) * D := by omega
  refine ⟨lo, hi, ?_⟩
  have top : (X + 1) * D ≤ N * D := Nat.mul_le_mul_right D hX
  have lt : (c + k) * N < D * N := by
    calc (c + k) * N < (X + 1) * D := hi
      _ ≤ N * D := top
      _ = D * N := mul_comm N D
  exact Nat.lt_of_mul_lt_mul_right lt

/-- **Every value of the fraction reading has at least `⌊2 ^ (256 q) / m ^ S⌋` preimages**: the naturals
`c, c + 1, ...` from `c = ⌈X 2 ^ (256 q) / m ^ S⌉`. -/
theorem fraction_fibre (X : Fin (m ^ S)) :
    2 ^ (256 * q) / m ^ S ≤ Fintype.card {u : Fin (2 ^ (256 * q)) // fractionMap m S q u = X} := by
  have Npos : 0 < m ^ S := pow_pos (NeZero.pos m) S
  let embed : Fin (2 ^ (256 * q) / m ^ S) → {u : Fin (2 ^ (256 * q)) // fractionMap m S q u = X} :=
    fun k =>
      ⟨⟨(X.val * 2 ^ (256 * q) + m ^ S - 1) / m ^ S + k.val,
        (fibre_arith (m ^ S) (2 ^ (256 * q)) X.val k.val Npos X.isLt k.isLt).2.2⟩, by
        apply Fin.ext
        show ((X.val * 2 ^ (256 * q) + m ^ S - 1) / m ^ S + k.val) * m ^ S / 2 ^ (256 * q) = X.val
        have h := fibre_arith (m ^ S) (2 ^ (256 * q)) X.val k.val Npos X.isLt k.isLt
        exact Nat.div_eq_of_lt_le h.1 h.2.1⟩
  have injective : Function.Injective embed := by
    intro a b same
    have := congrArg (fun u : {u : Fin (2 ^ (256 * q)) // fractionMap m S q u = X} => u.1.val) same
    simp only [embed] at this
    exact Fin.ext (by omega)
  have card := Fintype.card_le_of_injective embed injective
  rwa [Fintype.card_fin] at card

/-- **The fraction-reading bias.** The fraction reading of a uniform natural below `2 ^ (256 q)` is within
`(2 ^ (256 q) mod m ^ S) / 2 ^ (256 q)` of uniform below `m ^ S`. -/
theorem fraction_etvDist_le :
    ((PMF.uniformOfFintype (Fin (2 ^ (256 * q)))).map (fractionMap m S q)).etvDist
        (PMF.uniformOfFintype (Fin (m ^ S)))
      ≤ ((2 ^ (256 * q) % m ^ S : Nat) : ℝ≥0∞) / (2 ^ (256 * q) : Nat) := by
  have bound := etvDist_fibre_le (m ^ S) (2 ^ (256 * q) / m ^ S) (2 ^ (256 * q) % m ^ S)
    (fractionMap m S q) (Fintype.card_fin _) (by rw [Fintype.card_fin, Nat.div_add_mod])
    (fraction_fibre m S q)
  rwa [Nat.div_add_mod] at bound

/-- The digits of a natural below `m ^ S`, as a vector over `ZMod m` (digit `e` is `X / m ^ e mod m`). -/
def digitMap (X : Fin (m ^ S)) : Fin S → ZMod m := fun e => ((digit m X.val e.val : Nat) : ZMod m)

theorem digitMap_injective : Function.Injective (digitMap m S) := by
  intro X Y same
  have each : ∀ e : Fin S, X.val / m ^ e.val % m = Y.val / m ^ e.val % m := by
    intro e
    have := congrArg ZMod.val (congrFun same e)
    simpa [digitMap, digit, ZMod.val_natCast, Nat.mod_mod] using this
  have symmEq : (finFunctionFinEquiv (m := m) (n := S)).symm X
      = (finFunctionFinEquiv (m := m) (n := S)).symm Y := by
    funext e
    apply Fin.ext
    have hx : ((finFunctionFinEquiv (m := m) (n := S)).symm X e).val = X.val / m ^ e.val % m := rfl
    have hy : ((finFunctionFinEquiv (m := m) (n := S)).symm Y e).val = Y.val / m ^ e.val % m := rfl
    rw [hx, hy, each e]
  exact (finFunctionFinEquiv (m := m) (n := S)).symm.injective symmEq

/-- **The digits are a bijection** `Fin (m ^ S) ≃ (Fin S → ZMod m)`. -/
def digitsEquiv : Fin (m ^ S) ≃ (Fin S → ZMod m) :=
  Equiv.ofBijective (digitMap m S)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨digitMap_injective m S, by rw [Fintype.card_fin, Fintype.card_fun, ZMod.card, Fintype.card_fin]⟩)

/-- The pad vector the construction reads from `q` answers: `S` digits of the fraction reading. -/
def padVector (answers : Fin q → Block × Block) : Fin S → ZMod m :=
  fun e => ((digit m (fractionValue m S q (packAnswers q answers)) e.val : Nat) : ZMod m)

theorem padVector_factor :
    padVector m S q = digitsEquiv m S ∘ fractionMap m S q ∘ packEquiv q := rfl

/-- **The pad vector of uniform answers, exact bias**: within `(2 ^ (256 q) mod m ^ S) / 2 ^ (256 q)` of uniform. -/
theorem padVector_etvDist_le_mod :
    ((PMF.uniformOfFintype (Fin q → Block × Block)).map (padVector m S q)).etvDist
        (PMF.uniformOfFintype (Fin S → ZMod m))
      ≤ ((2 ^ (256 * q) % m ^ S : Nat) : ℝ≥0∞) / (2 ^ (256 * q) : Nat) := by
  rw [padVector_factor, ← PMF.map_comp, ← PMF.map_comp, packAnswers_uniform,
    ← uniformOfFintype_map_equiv (digitsEquiv m S)]
  exact le_trans (etvDist_map_le' _ _ _) (fraction_etvDist_le m S q)

/-- **The pad vector of uniform answers is within `m ^ S / 2 ^ (256 q)` of uniform on `(ZMod m) ^ S`**, the per-vector
term of `padSwapError`. -/
theorem padVector_etvDist_le :
    ((PMF.uniformOfFintype (Fin q → Block × Block)).map (padVector m S q)).etvDist
        (PMF.uniformOfFintype (Fin S → ZMod m))
      ≤ ((m ^ S : Nat) : ℝ≥0∞) / (2 ^ (256 * q) : Nat) := by
  refine le_trans (padVector_etvDist_le_mod m S q) (ENNReal.div_le_div_right ?_ _)
  exact Nat.cast_le.mpr (Nat.mod_lt _ (pow_pos (NeZero.pos m) S)).le

end Fraction

/-! ### The power-of-two modulus: exact -/

/-- **For the modulus `2 ^ k` with `k * S ≤ 256 q` the pad vector of uniform answers is exactly uniform.** -/
theorem padVector_uniform_pow2 (k S q : Nat) (fits : k * S ≤ 256 * q) :
    (PMF.uniformOfFintype (Fin q → Block × Block)).map (padVector (2 ^ k) S q)
      = PMF.uniformOfFintype (Fin S → ZMod (2 ^ k)) := by
  have zero : 2 ^ (256 * q) % (2 ^ k) ^ S = 0 := by
    rw [← pow_mul]
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 fits)
  have bound := padVector_etvDist_le_mod (2 ^ k) S q
  rw [zero, Nat.cast_zero, ENNReal.zero_div, nonpos_iff_eq_zero] at bound
  exact PMF.etvDist_eq_zero_iff.mp bound

/-- The frozen count for the power-of-two modulus fits: `k * S ≤ 256 * padAnswersPow2 S k`. -/
theorem padAnswersPow2_fits (S k : Nat) : k * S ≤ 256 * padAnswersPow2 S k := by
  unfold padAnswersPow2
  rw [Nat.mul_comm k S]
  omega

/-- **The frozen modulus 256** (`k = 8`, `padAnswersPow2 S 8` answers per slot): its pad vector is exactly uniform. -/
theorem padVector_uniform_256 (S : Nat) :
    (PMF.uniformOfFintype (Fin (padAnswersPow2 S 8) → Block × Block)).map
        (padVector (2 ^ 8) S (padAnswersPow2 S 8))
      = PMF.uniformOfFintype (Fin S → ZMod (2 ^ 8)) :=
  padVector_uniform_pow2 8 S _ (padAnswersPow2_fits S 8)

end

end Kriterion.CRT.Privacy
