/-
**The finals are fresh off the curve** (`Flags.CrtOffFinalFresh`).

Off the curve the finals `xsOf source u t` are the points `hashInput (keyOf source u t) (digestFinalTag o)`, so a
given point `x` is among them only if the key `keyOf source u t` equals the low 128 bits of `x` (`mem_xsOf`). On the
table answer `offAnswer t` the key is the table key `keyT t u`, the XOR of the table's first blocks at `u`'s digest-label
positions (`keyOf_eq`). One such position `pos` lies outside every site, so under the swapped table its answer is
uniform and independent of the rest (`fresh_le`); the key is that answer's
first block XOR a part that ignores it (`keyT_update`), and the reveal off the curve reads only conversion positions,
of families at most 6, so it ignores `pos` (`reveal_ignores`). The mass is therefore at most `2^-128` times the mass
of no reveal.

The lemmas of sections 1 to 3 are copies of lemmas of `Core/FinalCoincide.lean`, kept in this file's own
namespace so that this file does not depend on that one.
-/

import Proof.Privacy.CRT.Flags.TouchSplit
import Proof.Privacy.CRT.Laws.Invisible
import Proof.Correctness.CRT.TreeSteps
import Proof.Privacy.Phase3.Glue.Uniform

namespace Kriterion.CRT.Privacy.OffFresh

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.PlanB (digitCount)
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.Laws (Ignores Indep IndepS indep_swapped_pos)
open scoped ENNReal

noncomputable section

/-! ### 1. Digest-label positions and the table key -/

/-- The table position of the digest label of coordinate `c`, position `p`, bit `b`. -/
def lpos (c : Fin 2) (p : Fin coordinateBitCount) (b : ℕ) : Fin (2 ^ 40) :=
  ⟨digestLabelTag c.val p.val b % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

theorem labelTag_lt (c : Fin 2) (p : Fin coordinateBitCount) {b : ℕ} (hb : b < 2) :
    digestLabelTag c.val p.val b < 2 ^ 40 :=
  Asks.tagCode_lt (by decide) ⟨c.isLt, by norm_num, by norm_num, by norm_num,
    lt_of_lt_of_le p.isLt (by decide), by omega⟩

theorem lpos_val (c : Fin 2) (p : Fin coordinateBitCount) {b : ℕ} (hb : b < 2) :
    (lpos c p b).val = digestLabelTag c.val p.val b :=
  Nat.mod_eq_of_lt (labelTag_lt c p hb)

theorem lpos_family (c : Fin 2) (p : Fin coordinateBitCount) {b : ℕ} (hb : b < 2) :
    tagFamily (lpos c p b).val = 8 := by
  rw [lpos_val c p hb]
  exact (Align.digestLabelTag_fields c.isLt (lt_of_lt_of_le p.isLt (by decide)) (by omega)).1

/-- **Distinct labels have distinct positions.** -/
theorem lpos_inj {c c' : Fin 2} {p p' : Fin coordinateBitCount} {b b' : ℕ} (hb : b < 2) (hb' : b' < 2)
    (same : lpos c p b = lpos c' p' b') : c = c' ∧ p = p' ∧ b = b' := by
  have e := congrArg Fin.val same
  rw [lpos_val c p hb, lpos_val c' p' hb'] at e
  obtain ⟨_, hc, hs, hpt⟩ := Align.digestLabelTag_fields (b := b) c.isLt (lt_of_lt_of_le p.isLt (by decide))
    (by omega)
  obtain ⟨_, hc', hs', hpt'⟩ := Align.digestLabelTag_fields (b := b') c'.isLt (lt_of_lt_of_le p'.isLt (by decide))
    (by omega)
  refine ⟨Fin.ext ?_, Fin.ext ?_, ?_⟩
  · rw [← hc, ← hc', e]
  · rw [← hs, ← hs', e]
  · rw [← hpt, ← hpt', e]

/-- **The digest labels lie away from every pad and mask site.** -/
theorem lpos_away (c : Fin 2) (p : Fin coordinateBitCount) {b : ℕ} (hb : b < 2) :
    ∀ site ∈ crtLayout.sites, lpos c p b ∉ (siteTags crtLayout site).map tagPos := by
  intro site mem hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  have fam := lpos_family c p hb
  rw [← heq] at fam
  have ne : ∀ {fam' coord idx stage level slot part : ℕ}, 5 < fam' → fam' < 8 →
      TagInRange coord idx stage level slot part →
      tagFamily (tagPos (tagCode fam' coord idx stage level slot part)).val ≠ 8 := by
    intro fam' coord idx stage level slot part h1 h2 hin
    simp only [tagPos]
    rw [Nat.mod_eq_of_lt (Asks.tagCode_lt (by omega) hin), tagFamily_tagCode hin]
    omega
  rcases List.mem_append.mp mem with pad | mask
  · obtain ⟨κ', i, ρ, rfl, hκ', hi, hρ⟩ := Layout.mem_padSites pad
    obtain ⟨-, -, -, -, hm, hq⟩ := Layout.tableFacts κ' hκ' i hi
    simp only [siteTags, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have hj' : j < Layout.padCount κ' i := hj
    exact ne (by decide) (by decide) ⟨hκ', by omega, by omega, by omega, by omega, by omega⟩ fam
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 2 := hj
      exact ne (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ fam
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 3 := by
        have : j < (if k = 227 then 2 else 3) := hj
        split at this <;> omega
      exact ne (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ fam

/-- **The table key of an input**: the XOR of the table's first blocks at the input's digest-label positions. -/
def keyT (T : TagTable) (v : AffineInput) : Block :=
  xorFold fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => (T (lpos c p (coordBit v c p.val))).1

/-! ### 2. The table key at one position -/

theorem xorFold_off {n : ℕ} (j : Fin n) (F G : Fin n → Block) (agree : ∀ i, i ≠ j → F i = G i) :
    xorFold F = xorFold G ^^^ G j ^^^ F j := by
  have e := SliceC.xorFoldExcept_congr j F G agree
  rw [SliceC.xorFoldExcept_eq, SliceC.xorFoldExcept_eq] at e
  rw [← e, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_cancel2 (X Y b a : Block) : X ^^^ Y ^^^ (Y ^^^ b ^^^ a) = X ^^^ b ^^^ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases X.getLsbD i <;> cases Y.getLsbD i <;> cases b.getLsbD i <;> cases a.getLsbD i <;> rfl

/-- Two double folds that agree off one entry. -/
theorem fold2_off (A B : Fin 2 → Fin coordinateBitCount → Block) (c0 : Fin 2) (p0 : Fin coordinateBitCount)
    (agree : ∀ c p, (c, p) ≠ (c0, p0) → A c p = B c p) :
    xorFold (fun c => xorFold (A c)) = xorFold (fun c => xorFold (B c)) ^^^ B c0 p0 ^^^ A c0 p0 := by
  rw [xorFold_off c0 (fun c => xorFold (A c)) (fun c => xorFold (B c)) fun c hc =>
      congrArg xorFold (funext fun p => agree c p fun h => hc (Prod.mk.inj h).1)]
  rw [xorFold_off p0 (A c0) (B c0) fun p hp => agree c0 p fun h => hp (Prod.mk.inj h).2]
  exact xor_cancel2 _ _ _ _

/-- **At the position of its own label, an input's key is that position's first block XOR the rest.** -/
theorem keyT_update (T : TagTable) (v : AffineInput) (c0 : Fin 2) (p0 : Fin coordinateBitCount)
    (a : Block × Block) :
    keyT (Function.update T (lpos c0 p0 (coordBit v c0 p0.val)) a) v =
      keyT (Function.update T (lpos c0 p0 (coordBit v c0 p0.val)) (0, 0)) v ^^^ a.1 := by
  have other : ∀ c p, (c, p) ≠ (c0, p0) →
      lpos c p (coordBit v c p.val) ≠ lpos c0 p0 (coordBit v c0 p0.val) := by
    intro c p ne same
    obtain ⟨hc, hp, -⟩ := lpos_inj (Paths.coordBit_lt v c p.val) (Paths.coordBit_lt v c0 p0.val) same
    exact ne (by rw [hc, hp])
  unfold keyT
  rw [fold2_off (fun c p => (Function.update T (lpos c0 p0 (coordBit v c0 p0.val)) a (lpos c p (coordBit v c p.val))).1)
    (fun c p => (Function.update T (lpos c0 p0 (coordBit v c0 p0.val)) (0, 0) (lpos c p (coordBit v c p.val))).1) c0 p0
    fun c p ne => by rw [Function.update_of_ne (other c p ne), Function.update_of_ne (other c p ne)]]
  rw [Function.update_self, Function.update_self]
  exact congrArg (· ^^^ a.1) BitVec.xor_zero

/-- **An input whose labels avoid a position has a key that ignores it.** -/
theorem keyT_ignores (v : AffineInput) (pos : Fin (2 ^ 40)) (reads : ∀ c p, lpos c p (coordBit v c p.val) ≠ pos) :
    Ignores {pos} (fun T => keyT T v) := by
  intro T T' agree
  unfold keyT
  refine congrArg xorFold (funext fun c => congrArg xorFold (funext fun p => ?_))
  rw [agree _ fun h => reads c p (Set.mem_singleton_iff.mp h)]

/-! ### 3. Freshness at one non-site position -/

theorem card_block : Fintype.card Block = 2 ^ 128 :=
  (Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ : Block ≃ Fin (2 ^ 128))).trans
    (Fintype.card_fin _)

/-- A uniform answer's first block hits a given block with mass `2^-128`. -/
theorem uniform_fst (b : Block) :
    ∑' a : Block × Block, PMF.uniformOfFintype (Block × Block) a * Flags.ind (a.1 = b) = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  calc ∑' a : Block × Block, PMF.uniformOfFintype (Block × Block) a * Flags.ind (a.1 = b)
      = ((PMF.uniformOfFintype (Block × Block)).map Prod.fst) b := by
        rw [PMF.map_apply]
        refine tsum_congr fun a => ?_
        unfold Flags.ind
        by_cases h : a.1 = b
        · rw [if_pos h, if_pos h.symm, mul_one]
        · rw [if_neg h, if_neg (fun h' => h h'.symm), mul_zero]
    _ = PMF.uniformOfFintype Block b := by rw [Kriterion.ArgoMAC.Phase3.Glue.uniform_map_fst]
    _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
        rw [PMF.uniformOfFintype_apply, card_block]
        norm_num

theorem xor_eq_iff' (k x y : Block) : (k ^^^ x = y) = (x = k ^^^ y) := by
  apply propext
  constructor
  · intro h
    rw [← h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · intro h
    rw [h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem update_agree (T T' : TagTable) (pos : Fin (2 ^ 40)) (a : Block × Block)
    (agree : ∀ q, q ∉ ({pos} : Set (Fin (2 ^ 40))) → T q = T' q) :
    Function.update T pos a = Function.update T' pos a := by
  funext q
  by_cases h : q = pos
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]
    exact agree q fun hq => h (Set.mem_singleton_iff.mp hq)

/-- **Freshness at one non-site position**: a key that is the position's first block XOR a part ignoring it hits a
target ignoring it with mass `2^-128` against every weight ignoring it, under the swapped table. -/
theorem fresh_le (pos : Fin (2 ^ 40)) (away : ∀ site ∈ crtLayout.sites, pos ∉ (siteTags crtLayout site).map tagPos)
    (G : TagTable → ℝ≥0∞) (hG : Ignores {pos} G) (K B : TagTable → Block) (hB : Ignores {pos} B)
    (hK : ∀ T a, K (Function.update T pos a) = K (Function.update T pos (0, 0)) ^^^ a.1) :
    ∑' T, swappedTableLaw crtLayout T * (G T * Flags.ind (K T = B T)) ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' T, swappedTableLaw crtLayout T * G T := by
  have indep := (indep_swapped_pos crtLayout pos away).toS
  have ign : ∀ a : Block × Block,
      Ignores {pos} (fun T => G T * Flags.ind (K (Function.update T pos a) = B T)) := by
    intro a T T' agree
    show G T * Flags.ind (K (Function.update T pos a) = B T) = G T' * Flags.ind (K (Function.update T' pos a) = B T')
    rw [hG T T' agree, hB T T' agree, update_agree T T' pos a agree]
  have law := Laws.IndepS.tsum indep (fun a T => G T * Flags.ind (K (Function.update T pos a) = B T)) ign
  simp only [Function.update_eq_self] at law
  have swap : (∑' a, PMF.uniformOfFintype (Block × Block) a *
        ∑' T, swappedTableLaw crtLayout T * (G T * Flags.ind (K (Function.update T pos a) = B T))) =
      ∑' T, swappedTableLaw crtLayout T * G T *
        ∑' a, PMF.uniformOfFintype (Block × Block) a * Flags.ind (a.1 = K (Function.update T pos (0, 0)) ^^^ B T) := by
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun T => tsum_congr fun a => ?_
    rw [hK T a, xor_eq_iff']
    ring
  rw [law, swap]
  refine le_of_eq ?_
  calc ∑' T, swappedTableLaw crtLayout T * G T *
        ∑' a, PMF.uniformOfFintype (Block × Block) a * Flags.ind (a.1 = K (Function.update T pos (0, 0)) ^^^ B T)
      = ∑' T, swappedTableLaw crtLayout T * G T * (2 ^ 128 : ℝ≥0∞)⁻¹ :=
        tsum_congr fun T => by rw [uniform_fst]
    _ = (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' T, swappedTableLaw crtLayout T * G T := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun T => mul_comm _ _

/-! ### 4. The key off the curve and the finals -/

/-- **On the table answer a digest label is answered by its position.** -/
theorem h128_off (t : TagTable) (label : Block) (c : Fin 2) (p : Fin coordinateBitCount) {b : ℕ} (hb : b < 2) :
    h128 (Laws.offAnswer t) label (digestLabelTag c.val p.val b) = (t (lpos c p b)).1 := by
  unfold h128 Laws.offAnswer
  rw [OffDecomp.tagOfInput_small (OffDecomp.small_hashInput label _ (labelTag_lt c p hb))]
  congr 2
  apply Fin.ext
  show hashInput label (digestLabelTag c.val p.val b) / 2 ^ 128 = (lpos c p b).val
  rw [hashInput_tag, lpos_val c p hb]

/-- **The key off the curve is the table key.** -/
theorem keyOf_eq [FieldCertificate] [GroupCertificate] (source : (PublicFirst.viewHere crtEntry).Source)
    (u : AffineInput) (t : TagTable) : OffDecomp.keyOf source u t = keyT t u := by
  unfold OffDecomp.keyOf digestKey keyT
  refine congrArg xorFold (funext fun c => congrArg xorFold (funext fun p => ?_))
  exact h128_off t _ c p (Paths.coordBit_lt u c p.val)

/-- The low 128 bits of a point. -/
def lowKey (x : BaseField) : Block := BitVec.ofNat 128 x.val

/-- **A final at key `k` has low bits `k`**: a point among the finals pins the key. -/
theorem mem_xsOf [FieldCertificate] [GroupCertificate] (source : (PublicFirst.viewHere crtEntry).Source)
    (u : AffineInput) (t : TagTable) (x : BaseField) (member : x ∈ OffDecomp.xsOf source u t) :
    keyT t u = lowKey x := by
  unfold OffDecomp.xsOf at member
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp member
  obtain ⟨small, -⟩ := OffDecomp.final_small _ n hn
  unfold OffDecomp.finalsAt at hn
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at hn
  obtain ⟨o, rfl⟩ := hn
  rw [← keyOf_eq source u t]
  unfold lowKey
  rw [small.1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  unfold hashInput
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (OffDecomp.keyOf source u t).isLt]

/-- **The reveal off the curve ignores every family-8 position.** -/
theorem reveal_ignores [FieldCertificate] [GroupCertificate] (source : (PublicFirst.viewHere crtEntry).Source)
    (u : AffineInput) (pos : Fin (2 ^ 40)) (fam : tagFamily pos.val = 8) :
    Ignores {pos} (fun t => Flags.ind (¬ H8.crtRevealOff source u t)) := by
  intro t t' agree
  have same : H8.crtRevealOff source u t ↔ H8.crtRevealOff source u t' := by
    refine Flags.replayWraps_congr source u t t' fun n hn => ?_
    obtain ⟨key, member, range, label, rfl⟩ :=
      Flags.keyRun_queries (Paths.replayConv_tagged ((Instance.view).publish source) u ((Instance.view).labels source u))
        _ n hn
    rw [ReplayDelivered.tagHash_hashInput, ReplayDelivered.tagHash_hashInput]
    refine agree _ fun hp => ?_
    have e := congrArg Fin.val (Set.mem_singleton_iff.mp hp)
    have low : key.code % 2 ^ 40 = key.code := Nat.mod_eq_of_lt (Paths.TagKey.code_lt range)
    have kf : tagFamily key.code = key.fam := Align.tagFamily_key range
    have := Paths.replayConvKeys_fam key member
    simp only at e
    rw [low] at e
    rw [← e, kf] at fam
    omega
  show Flags.ind (¬ H8.crtRevealOff source u t) = Flags.ind (¬ H8.crtRevealOff source u t')
  rw [propext (not_congr same)]

theorem ind_mono {P R : Prop} (imp : P → R) : Flags.ind P ≤ Flags.ind R := by
  unfold Flags.ind
  split_ifs <;> simp_all

theorem layout_eq : crtEntry.layout = crtLayout := rfl

theorem ofReal_inv : ENNReal.ofReal (1 / 2 ^ 128) = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

end

end Kriterion.CRT.Privacy.OffFresh

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.OffFresh
open scoped ENNReal

/-- **The finals are fresh off the curve.** -/
theorem crtOffFinalFresh : CrtOffFinalFresh := by
  intro field group source u _ x _
  set pos := lpos 0 0 (coordBit u 0 (0 : Fin coordinateBitCount).val) with hpos
  have hb := Paths.coordBit_lt u 0 (0 : Fin coordinateBitCount).val
  have pointwise : ∀ t, ind (¬ H8.crtRevealOff source u t) * ind (x ∈ OffDecomp.xsOf source u t) ≤
      ind (¬ H8.crtRevealOff source u t) * ind (keyT t u = lowKey x) := fun t =>
    mul_le_mul' le_rfl (OffFresh.ind_mono fun member => mem_xsOf source u t x member)
  rw [layout_eq, ofReal_inv]
  calc ∑' t, swappedTableLaw crtLayout t *
        (ind (¬ H8.crtRevealOff source u t) * ind (x ∈ OffDecomp.xsOf source u t))
      ≤ ∑' t, swappedTableLaw crtLayout t *
        (ind (¬ H8.crtRevealOff source u t) * ind (keyT t u = lowKey x)) :=
        ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl (pointwise t)
    _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' t, swappedTableLaw crtLayout t * ind (¬ H8.crtRevealOff source u t) :=
        fresh_le pos (lpos_away 0 0 hb) (fun t => ind (¬ H8.crtRevealOff source u t))
          (reveal_ignores source u pos (lpos_family 0 0 hb)) (fun t => keyT t u) (fun _ => lowKey x)
          (fun _ _ _ => rfl) (fun t a => keyT_update t u 0 0 a)

end Kriterion.CRT.Privacy.Flags
