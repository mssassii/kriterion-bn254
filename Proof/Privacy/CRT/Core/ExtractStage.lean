/-
**CRT privacy core: the left-inverse inversion lemma for one fused extraction stage.**

A fused extraction stage has no triangular order: the stage is one gadget whose hidden part is the tuple
`(y_1, ..., y_{w-1}, A_s)`, the hot material of every tree level and the hot leaf's cast, and whose published part is
`(J_1, ..., J_{w-1}, P)`, the joins and the pin. This file proves that, for every value of everything else, the map
from the hidden tuple to the published tuple is injective (`publish_injective`), so it has a left inverse
(`solve_leftInverse`) and pushes the uniform law to the uniform law, independently of the rest
(`stage_published_uniform`, an instance of `Proof.Privacy.CRT.Core.Inversion`).

**The model.** Everything that is not hidden is a field of `Frame`: the reduced remainder mask `sub`, `Δ`, and the
cold answers as functions of the position *and the label queried there* (`tree n σ G`, `cast α G`). Letting the
cold answers depend on the label is the point reading, in which a hidden material moves the labels (and so the
cold answers) of every node below it and no gadget order is triangular. The answer-table reading,
where a cold answer depends on its position only, is the special case of a `Frame` whose functions
ignore the label, so both readings are covered by one statement.

Levels are indexed from `k = 0`: `level k` holds the `2 ^ (k + 1)` labels of tree level `n = k + 1`; the level-1
pair is `(b_0 ⊕ Δ, b_0)` with `b_0 = laneBit sub 0`; the material of slot `σ` at level `k + 1` is hidden exactly at
the hot slot `σ = s mod 2 ^ (k + 1)`; the leaves are `level (w - 1)`. Labels are total functions of a natural index
(junk outside the range), which keeps the recursion free of `Fin` casts.

**The proof** (the evaluator's round order, read as an injectivity induction):
1. `level_eq_of_agree`: the labels of level `k + 1` depend on the hidden materials of levels below it only.
2. `level_eq_off_class`: a node outside the active class of level `k + 1` (its index differs from `s` modulo
   `2 ^ (k + 1)`) has a label that depends on the hidden materials of levels `≤ k` only, at every deeper level.
3. `classSum_eq`: `res_n = q_n • (Σ_α A_α) + Σ_α ((α mod 2^n) − q_n) • A_α`, and the second sum does not see the
   active class; with the pin this makes `b_n` a function of `P` and of casts outside the active class.
4. Round `k`: the join `J_{k+1} = Y_{k+1} ⊕ b_{k+1}` then fixes `y_{k+1}`, since `Y_{k+1}` is `y_{k+1}` XOR materials
   that depend on lower levels only.
5. Last: every cold cast is now fixed, and the pin fixes `A_s`.

Nothing here uses a property of `laneBit`, `reduceTo` or `deltaLanes`; they are the construction's
definitions, kept concrete so that the statement can be matched against the definitions.
-/

import Mathlib.Data.ZMod.Basic
import Batteries.Data.BitVec
import Proof.Privacy.CRT.Core.Inversion

namespace Kriterion.CRT.Privacy.ExtractStage

open Kriterion.CRT.Privacy

/-! ### Label algebra -/

/-- Arithmetic labels: `L` lanes over `ZMod (2 ^ l)`. -/
abbrev Lanes (L l : ℕ) := Fin L → ZMod (2 ^ l)

/-- `Δ⃗`: lane `i` is bit `i` of `Δ`. -/
def deltaLanes {L : ℕ} (l : ℕ) (Δ : BitVec L) : Lanes L l :=
  fun i => if Δ.getLsbD i then 1 else 0

/-- The block of bit `n` of every lane. -/
def laneBit {L l : ℕ} (A : Lanes L l) (n : ℕ) : BitVec L :=
  BitVec.ofFnLE fun i => (A i).val.testBit n

/-- Reduction of every lane to width `w` (the value read modulo `2 ^ w`). -/
def reduceTo {L l : ℕ} (w : ℕ) (A : Lanes L l) : Lanes L w :=
  fun i => ((A i).val : ZMod (2 ^ w))

/-- The XOR of `f 0, ..., f (K - 1)`. -/
def xorUpTo {L : ℕ} (f : ℕ → BitVec L) : ℕ → BitVec L
  | 0 => 0#L
  | K + 1 => xorUpTo f K ^^^ f K

/-! ### One fused stage, garbler side, with the hidden answers as parameters -/

/-- Everything a stage reads that is not one of its hidden answers. `tree n σ G` is the answer at tree level `n`,
slot `σ`, queried at label `G`; `cast α G` the cast of leaf `α` queried at label `G`. -/
structure Frame (L w l : ℕ) where
  sub : Lanes L w
  delta : BitVec L
  tree : ℕ → ℕ → BitVec L → BitVec L
  cast : ℕ → BitVec L → Lanes L l

/-- The hidden tuple `(y_1, ..., y_{w-1}, A_s)`: entry `k` of the first component is the hot material of tree
level `k + 1`. -/
abbrev Hidden (L w l : ℕ) := (Fin (w - 1) → BitVec L) × Lanes L l

/-- The published tuple `(J_1, ..., J_{w-1}, P)`. -/
abbrev Published (L w l : ℕ) := (Fin (w - 1) → BitVec L) × Lanes L l

variable {L w l : ℕ}

section Garbler

variable (F : Frame L w l) (s : ℕ)

/-- The hot material of tree level `k + 1` (zero outside `k < w - 1`). -/
def hot (y : Fin (w - 1) → BitVec L) (k : ℕ) : BitVec L :=
  if hk : k < w - 1 then y ⟨k, hk⟩ else 0

/-- The materials of tree level `k + 1`, given its labels `G`: hidden at the hot slot, the cold answer elsewhere. -/
def material (y : Fin (w - 1) → BitVec L) (k : ℕ) (G : ℕ → BitVec L) (σ : ℕ) : BitVec L :=
  if σ = s % 2 ^ (k + 1) then hot y k else F.tree (k + 1) σ (G σ)

/-- `b_0 = laneBit sub 0`. -/
def bit0 : BitVec L := laneBit F.sub 0

/-- The labels of tree level `k + 1` (`2 ^ (k + 1)` slots). Level 1 is the pair `(b_0 ⊕ Δ, b_0)`; the next level
puts the left children `G_σ ⊕ y_σ` at `σ` and the right children `y_σ` at `σ + 2 ^ (k + 1)`. -/
def level (y : Fin (w - 1) → BitVec L) : ℕ → ℕ → BitVec L
  | 0 => fun i => if i = 0 then bit0 F ^^^ F.delta else bit0 F
  | k + 1 => fun i =>
      if i < 2 ^ (k + 1) then level y k i ^^^ material F s y k (level y k) i
      else material F s y k (level y k) (i - 2 ^ (k + 1))

/-- The cast of leaf `α`: hidden at the hot leaf `s`, the cold answer at the leaf's label elsewhere. -/
def castAt (h : Hidden L w l) (α : ℕ) : Lanes L l :=
  if α = s then h.2 else F.cast α (level F s h.1 (w - 1) α)

/-- `Σ_α A_α` over the `2 ^ w` leaves. -/
def castSum (h : Hidden L w l) : Lanes L l :=
  ∑ α ∈ Finset.range (2 ^ w), castAt F s h α

/-- The pin `P = Σ_α A_α + Δ⃗`. -/
def pin (h : Hidden L w l) : Lanes L l :=
  castSum F s h + deltaLanes l F.delta

/-- The class sum `res_n = Σ_α (α mod 2 ^ n) • A_α`. -/
def classSum (h : Hidden L w l) (n : ℕ) : Lanes L l :=
  ∑ α ∈ Finset.range (2 ^ w), (((α % 2 ^ n : ℕ) : ZMod (2 ^ l)) • castAt F s h α)

/-- The bit mask `b_n = laneBit (sub − reduce_w res_n) n`. -/
def bitMask (h : Hidden L w l) (n : ℕ) : BitVec L :=
  laneBit (F.sub - reduceTo w (classSum F s h n)) n

/-- `Y_{k+1}`, the XOR of the materials of tree level `k + 1`. -/
def levelSum (h : Hidden L w l) (k : ℕ) : BitVec L :=
  xorUpTo (material F s h.1 k (level F s h.1 k)) (2 ^ (k + 1))

/-- The join `J_{k+1} = Y_{k+1} ⊕ b_{k+1}`. -/
def join (h : Hidden L w l) (k : ℕ) : BitVec L :=
  levelSum F s h k ^^^ bitMask F s h (k + 1)

/-- The published tuple of the stage. -/
def publish (h : Hidden L w l) : Published L w l :=
  (fun k => join F s h k.val, pin F s h)

end Garbler

/-! ### XOR bookkeeping -/

theorem xorUpTo_xor (f g : ℕ → BitVec L) :
    ∀ K, xorUpTo (fun i => f i ^^^ g i) K = xorUpTo f K ^^^ xorUpTo g K
  | 0 => by simp [xorUpTo]
  | K + 1 => by
      simp only [xorUpTo, xorUpTo_xor f g K]
      ac_rfl

theorem xorUpTo_eq_zero (f : ℕ → BitVec L) :
    ∀ K, (∀ i < K, f i = 0#L) → xorUpTo f K = 0#L
  | 0, _ => rfl
  | K + 1, zero => by
      simp only [xorUpTo, xorUpTo_eq_zero f K (fun i hi => zero i (Nat.lt_succ_of_lt hi)),
        zero K (Nat.lt_succ_self K), BitVec.xor_zero]

theorem xorUpTo_single (f : ℕ → BitVec L) (q : ℕ) :
    ∀ K, q < K → (∀ i < K, i ≠ q → f i = 0#L) → xorUpTo f K = f q
  | 0, bad, _ => absurd bad (Nat.not_lt_zero q)
  | K + 1, lt, zero => by
      simp only [xorUpTo]
      rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt' | rfl
      · rw [xorUpTo_single f q K lt' (fun i hi ne => zero i (Nat.lt_succ_of_lt hi) ne),
          zero K (Nat.lt_succ_self K) (Nat.ne_of_gt lt'), BitVec.xor_zero]
      · rw [xorUpTo_eq_zero f q (fun i hi => zero i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi)),
          BitVec.zero_xor]

/-- Two families that agree off one index `q < K` and have the same XOR agree at `q` as well. -/
theorem eq_at_of_xorUpTo_eq (f g : ℕ → BitVec L) (q K : ℕ) (lt : q < K)
    (off : ∀ i < K, i ≠ q → f i = g i) (same : xorUpTo f K = xorUpTo g K) : f q = g q := by
  have single : xorUpTo (fun i => f i ^^^ g i) K = f q ^^^ g q :=
    xorUpTo_single (fun i => f i ^^^ g i) q K lt
      (fun i hi ne => by rw [off i hi ne, BitVec.xor_self])
  rw [xorUpTo_xor, same, BitVec.xor_self] at single
  have := congrArg (fun x => f q ^^^ x) single
  simp only [BitVec.xor_zero, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] at this
  exact this

/-! ### The injectivity induction -/

section Proof

variable (F : Frame L w l) (s : ℕ)

/-- **Step 1.** The labels of tree level `k + 1` depend on the hidden materials of lower levels only. -/
theorem level_eq_of_agree {y y' : Fin (w - 1) → BitVec L} :
    ∀ k, (∀ j < k, hot y j = hot y' j) → level F s y k = level F s y' k
  | 0, _ => rfl
  | k + 1, agree => by
      have prev := level_eq_of_agree k (fun j hj => agree j (Nat.lt_succ_of_lt hj))
      have hk := agree k (Nat.lt_succ_self k)
      funext i
      simp only [level, material, prev, hk]

/-- **Step 2.** A node outside the active class of tree level `k + 1` has, at every level `j + 1 ≥ k + 1`, a label
that depends on the hidden materials of levels `≤ k` only. -/
theorem level_eq_off_class {y y' : Fin (w - 1) → BitVec L} (k : ℕ)
    (agree : ∀ j < k, hot y j = hot y' j) :
    ∀ j, k ≤ j → ∀ i, i < 2 ^ (j + 1) → i % 2 ^ (k + 1) ≠ s % 2 ^ (k + 1) →
      level F s y j i = level F s y' j i := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => intro i _ _; rw [level_eq_of_agree F s k agree]
  | succ j hkj ih =>
    intro i hi hcls
    have dvd : 2 ^ (k + 1) ∣ 2 ^ (j + 1) := Nat.pow_dvd_pow 2 (by omega)
    have cold : ∀ t, t < 2 ^ (j + 1) → t % 2 ^ (k + 1) ≠ s % 2 ^ (k + 1) →
        material F s y j (level F s y j) t = material F s y' j (level F s y' j) t := by
      intro t ht htc
      have hne : t ≠ s % 2 ^ (j + 1) := by
        intro heq
        apply htc
        rw [heq, Nat.mod_mod_of_dvd _ dvd]
      simp only [material, if_neg hne, ih t ht htc]
    show (if i < 2 ^ (j + 1) then level F s y j i ^^^ material F s y j (level F s y j) i
          else material F s y j (level F s y j) (i - 2 ^ (j + 1)))
        = (if i < 2 ^ (j + 1) then level F s y' j i ^^^ material F s y' j (level F s y' j) i
          else material F s y' j (level F s y' j) (i - 2 ^ (j + 1)))
    by_cases hlt : i < 2 ^ (j + 1)
    · rw [if_pos hlt, if_pos hlt, ih i hlt hcls, cold i hlt hcls]
    · rw [if_neg hlt, if_neg hlt]
      have hi2 : i < 2 ^ (j + 1) * 2 := by rw [← pow_succ]; exact hi
      have ht : i - 2 ^ (j + 1) < 2 ^ (j + 1) := by omega
      obtain ⟨c, hc⟩ := dvd
      have split : i = (i - 2 ^ (j + 1)) + 2 ^ (k + 1) * c := by
        rw [← hc]; exact (Nat.sub_add_cancel (Nat.le_of_not_lt hlt)).symm
      have same : i % 2 ^ (k + 1) = (i - 2 ^ (j + 1)) % 2 ^ (k + 1) := by
        conv_lhs => rw [split]
        exact Nat.add_mul_mod_self_left _ _ _
      exact cold _ ht (by rw [← same]; exact hcls)

/-- A cast outside the active class of tree level `k + 1` depends on the hidden materials of levels `≤ k` only. -/
theorem castAt_eq_off_class {h h' : Hidden L w l} (k : ℕ) (hk : k < w - 1)
    (agree : ∀ j < k, hot h.1 j = hot h'.1 j) (α : ℕ) (hα : α < 2 ^ w)
    (hcls : α % 2 ^ (k + 1) ≠ s % 2 ^ (k + 1)) : castAt F s h α = castAt F s h' α := by
  have hne : α ≠ s := fun e => hcls (by rw [e])
  have hw : w - 1 + 1 = w := by omega
  unfold castAt
  rw [if_neg hne, if_neg hne,
    level_eq_off_class F s k agree (w - 1) (by omega) α (by rw [hw]; exact hα) hcls]

/-- **Step 3.** `res_n = q_n • Σ_α A_α + Σ_α ((α mod 2 ^ n) − q_n) • A_α`. -/
theorem classSum_eq (h : Hidden L w l) (n : ℕ) :
    classSum F s h n
      = ((s % 2 ^ n : ℕ) : ZMod (2 ^ l)) • castSum F s h
        + ∑ α ∈ Finset.range (2 ^ w),
            ((((α % 2 ^ n : ℕ) : ZMod (2 ^ l)) - ((s % 2 ^ n : ℕ) : ZMod (2 ^ l))) • castAt F s h α) := by
  unfold classSum castSum
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sub_smul]
  abel

/-- The class sum is fixed by the sum of all casts and the casts outside the active class. -/
theorem classSum_eq_of {h h' : Hidden L w l} (n : ℕ) (sums : castSum F s h = castSum F s h')
    (off : ∀ α < 2 ^ w, α % 2 ^ n ≠ s % 2 ^ n → castAt F s h α = castAt F s h' α) :
    classSum F s h n = classSum F s h' n := by
  rw [classSum_eq, classSum_eq, sums]
  congr 1
  refine Finset.sum_congr rfl fun α hα => ?_
  by_cases hc : α % 2 ^ n = s % 2 ^ n
  · rw [hc, sub_self, zero_smul, zero_smul]
  · rw [off α (Finset.mem_range.mp hα) hc]

/-- **Step 4, iterated.** Equal published tuples force equal hidden materials at every level. -/
theorem hot_agree_of_publish {h h' : Hidden L w l} (same : publish F s h = publish F s h') :
    ∀ k, ∀ j < k, hot h.1 j = hot h'.1 j := by
  have pins : pin F s h = pin F s h' := congrArg Prod.snd same
  have sums : castSum F s h = castSum F s h' := add_right_cancel pins
  have joins : ∀ k : Fin (w - 1), join F s h k.val = join F s h' k.val :=
    fun k => congrFun (congrArg Prod.fst same) k
  intro k
  induction k with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact ih j hlt
    · by_cases hk : j < w - 1
      · have lv : level F s h.1 j = level F s h'.1 j := level_eq_of_agree F s j ih
        have cls : classSum F s h (j + 1) = classSum F s h' (j + 1) :=
          classSum_eq_of F s (j + 1) sums (fun α hα hc => castAt_eq_off_class F s j hk ih α hα hc)
        have bm : bitMask F s h (j + 1) = bitMask F s h' (j + 1) := by
          unfold bitMask
          rw [cls]
        have ls : levelSum F s h j = levelSum F s h' j := by
          have hj := joins ⟨j, hk⟩
          unfold join at hj
          rw [bm] at hj
          exact (BitVec.xor_left_inj _).mp hj
        have atq := eq_at_of_xorUpTo_eq (material F s h.1 j (level F s h.1 j))
          (material F s h'.1 j (level F s h'.1 j)) (s % 2 ^ (j + 1)) (2 ^ (j + 1))
          (Nat.mod_lt _ (Nat.two_pow_pos _))
          (fun i _ ne => by simp only [material, if_neg ne, lv]) ls
        simpa only [material, ↓reduceIte] using atq
      · simp only [hot, dif_neg hk]

/-- **Step 5: the stage is injective in its hidden tuple.** For every frame and every stage value `s < 2 ^ w`,
the published joins and pin determine the hot materials of every level and the hot leaf's cast. -/
theorem publish_injective (hs : s < 2 ^ w) : Function.Injective (publish F s) := by
  intro h h' same
  have agree := hot_agree_of_publish F s same
  have ys : h.1 = h'.1 := funext fun k => by
    have := agree (k.val + 1) k.val (Nat.lt_succ_self _)
    simpa only [hot, dif_pos k.isLt] using this
  have casts : ∀ α, α ≠ s → castAt F s h α = castAt F s h' α := by
    intro α hα
    unfold castAt
    rw [if_neg hα, if_neg hα, ys]
  have sums : castSum F s h = castSum F s h' := add_right_cancel (congrArg Prod.snd same)
  have hmem : s ∈ Finset.range (2 ^ w) := Finset.mem_range.mpr hs
  unfold castSum at sums
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at sums
  have others : ∑ α ∈ (Finset.range (2 ^ w)).erase s, castAt F s h α
      = ∑ α ∈ (Finset.range (2 ^ w)).erase s, castAt F s h' α :=
    Finset.sum_congr rfl fun α hα => casts α (Finset.ne_of_mem_erase hα)
  rw [others] at sums
  have hot' : castAt F s h s = castAt F s h' s := add_right_cancel sums
  have As : h.2 = h'.2 := by simpa only [castAt, ↓reduceIte] using hot'
  exact Prod.ext ys As

/-- **The left inverse.** Any function that inverts `publish` on its image, for instance `Function.invFun`, is a
left inverse; the evaluator's round-ordered solve is another one (C3 proves that it
recovers the hidden tuple). -/
theorem solve_leftInverse (hs : s < 2 ^ w) :
    Function.LeftInverse (Function.invFun (publish F s)) (publish F s) :=
  Function.leftInverse_invFun (publish_injective F s hs)

end Proof

/-! ### The instance of the inversion lemma -/

/-- **One fused extraction stage publishes a uniform tuple, independent of everything else.** Draw the frame (the
reduced remainder mask, `Δ`, the cold answers as functions of position and label) from any law, and the hidden
tuple `(y_1, ..., y_{w-1}, A_s)` uniformly; the pair (frame, published tuple) then has the law "frame, then a
uniform published tuple". -/
theorem stage_published_uniform [Fintype (BitVec L)] {Rest : Type*} (rest : PMF Rest)
    (frame : Rest → Frame L w l) (s : ℕ) (hs : s < 2 ^ w) :
    (rest.bind fun r => (PMF.uniformOfFintype (Hidden L w l)).map fun h => (r, publish (frame r) s h))
      = rest.bind fun r => (PMF.uniformOfFintype (Published L w l)).map fun b => (r, b) :=
  bind_map_uniform_of_injective rest (fun r => publish (frame r) s)
    (fun r => publish_injective (frame r) s hs) rfl

/-- The same through the explicit left inverse, in the exact form of `bind_map_uniform_of_leftInverse`. -/
theorem stage_published_uniform' [Fintype (BitVec L)] {Rest : Type*} (rest : PMF Rest)
    (frame : Rest → Frame L w l) (s : ℕ) (hs : s < 2 ^ w) :
    (rest.bind fun r => (PMF.uniformOfFintype (Hidden L w l)).map fun h => (r, publish (frame r) s h))
      = rest.bind fun r => (PMF.uniformOfFintype (Published L w l)).map fun b => (r, b) :=
  bind_map_uniform_of_leftInverse rest (fun r => publish (frame r) s)
    (fun r => Function.invFun (publish (frame r) s))
    (fun r => solve_leftInverse (frame r) s hs) rfl

end Kriterion.CRT.Privacy.ExtractStage
