/-
**P8's family-9 row: a hidden digest final that the reach asks** (`Flags.CrtFinalCoincide`, `Flags/CoincidenceSplit.lean`).

On the table oracle every hash is answered by its tag alone, so the garbler's final of site `o` (two per digit, one
per exceptional kind) is asked at `hashInput key_o (digestFinalTag o)` with `key_o` the XOR of the table's first blocks at `exc_o`'s digest-label
positions (`keyT T exc_o`), and the reach asks its finals at `keyT T u` (`garbler_final`, `reach_final`). A hidden
reached final therefore forces `keyT T exc_o = keyT T u` with `exc_o ≠ u` (`hidden_final`). The two inputs differ in
some bit `(c0, p0)`; at the position of `exc_o`'s label there, `keyT T exc_o` is that position's first block XOR a
part that ignores it (`keyT_update`), while `keyT T u` and the published value ignore it (`keyT_ignores`,
`view_ignores`: the published value reads the table only at families other than 8). The position lies outside every
site (`lpos_away`), so under the swapped table it is uniform and independent of the rest (`indep_swapped_pos`), and
the coincidence has conditional mass `2^-128` against every weight on the published value (`fresh_le`). A union over
the 182 final sites gives `182/2^128`.

* `keyT`, `lpos`: the table key of an input and the digest-label positions;
* `fresh_le`: the generic freshness bound at one non-site position;
* `hidden_final`, `digit_le`;
* **`crtEntry_finalCoincide : Flags.CrtFinalCoincide`**.
-/

import Proof.Privacy.CRT.Paths.LabelCoincide
import Proof.Privacy.CRT.Core.DigestSplit
import Proof.Privacy.CRT.Laws.Invisible
import Proof.Correctness.CRT.TreeSteps
import Proof.Correctness.CRT.EntryCorrect
import Proof.Privacy.Phase3.Glue.Uniform
import Proof.Privacy.CRT.Hidden.StageOneTable
import Proof.Privacy.CRT.Hidden.AlignEntry


set_option autoImplicit false

namespace Kriterion.CRT.Privacy.FinalCoincide

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.PlanB (digitCount)
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.Laws (Ignores Indep IndepS indep_swapped_pos)
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure)
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
      have hj' : j < 3 := hj
      exact ne (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ fam

/-- **The table key of an input**: the XOR of the table's first blocks at the input's digest-label positions. -/
def keyT (T : TagTable) (v : AffineInput) : Block :=
  xorFold fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount => (T (lpos c p (coordBit v c p.val))).1

/-- **On the table oracle a digest label is answered by its position.** -/
theorem h128_label (T : TagTable) (label : Block) (c : Fin 2) (p : Fin coordinateBitCount) {b : ℕ} (hb : b < 2) :
    h128 (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) label (digestLabelTag c.val p.val b) =
      (T (lpos c p b)).1 := by
  unfold h128
  rw [Asks.schemeHash_small T _ (Asks.hashInput_small label _ (labelTag_lt c p hb))]
  show (Conv.tagRead T (hashInput label (digestLabelTag c.val p.val b) / 2 ^ 128)).1 = _
  rw [hashInput_tag]
  rfl

/-- **The reach's digest key on the table oracle is the table key**, whatever the labels. -/
theorem digestKey_table (T : TagTable) (labels : Fin 2 → Fin coordinateBitCount → Block) (v : AffineInput) :
    digestKey (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) coordinateBitCount labels v = keyT T v := by
  unfold digestKey keyT
  refine congrArg xorFold (funext fun c => congrArg xorFold (funext fun p => ?_))
  exact h128_label T _ c p (Paths.coordBit_lt v c p.val)

/-- **The garbler's key of a point on the table oracle is the table key.** -/
theorem garblerKey_table (T : TagTable) (zero : Fin 2 → Fin coordinateBitCount → Block) (delta : Fin 2 → Block)
    (w : AffineInput) :
    garblerKey (digestTable (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) coordinateBitCount zero delta) w =
      keyT T w := by
  unfold garblerKey keyT
  refine congrArg xorFold (funext fun c => congrArg xorFold (funext fun p => ?_))
  dsimp only [digestTable]
  by_cases one : coordBit w c p.val = 1
  · rw [if_pos one, one, h128_label T _ c p (by norm_num)]
  · have zero' : coordBit w c p.val = 0 := by have := Paths.coordBit_lt w c p.val; omega
    rw [if_neg one, zero', h128_label T _ c p (by norm_num)]

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

/-! ### 4. The published value ignores the digest labels -/

/-- A tagged program whose keys avoid family 8 has the same value on two tables that agree off family 8. -/
theorem eval_off8 {α : Type} {S : Set Paths.TagKey} {program : CM α} (tagged : Paths.Tagged S program)
    (away : ∀ k ∈ S, k.fam ≠ 8) (T T' : TagTable) (agree : ∀ q : Fin (2 ^ 40), tagFamily q.val ≠ 8 → T q = T' q) :
    program.eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) =
      program.eval (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) := by
  refine ((Paths.SameVisible.asked_congr _ _ program fun n hn => ?_).2).symm
  obtain ⟨k, member, range, label, rfl⟩ := Align.asked_of_tagged tagged _ n hn
  show T (tagOfInput _) = T' (tagOfInput _)
  apply agree
  rw [Paths.tagOfInput_hashInput range, Align.tagFamily_key range]
  exact away k member

/-- **The published value reads the table only off family 8** (StageOneTable's `pubT_congr`). -/
theorem view_congr [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (c : crtEntry.Coins) (T T' : TagTable) (agree : ∀ q : Fin (2 ^ 40), tagFamily q.val ≠ 8 → T q = T' q) :
    stageOneView crtEntry parameter scalar (c, T) = stageOneView crtEntry parameter scalar (c, T') := by
  rw [StageOneProof.stageOneView_pubT, StageOneProof.stageOneView_pubT]
  exact StageOneProof.pubT_congr scalar c T T' fun q h8 _ => agree q h8

theorem view_ignores [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (c : crtEntry.Coins) (weight : crtEntry.Public → ℝ≥0∞) (pos : Fin (2 ^ 40)) (fam : tagFamily pos.val = 8) :
    Ignores {pos} (fun T => weight (stageOneView crtEntry parameter scalar (c, T))) := by
  intro T T' agree
  exact congrArg weight (view_congr parameter scalar c T T' fun q hq =>
    agree q fun h => hq (by rw [Set.mem_singleton_iff.mp h]; exact fam))

/-! ### 5. A hidden reached final forces a key coincidence -/

theorem hashInput_label_inj {A B : Block} {t t' : ℕ} (h : hashInput A t = hashInput B t') : A = B := by
  apply BitVec.eq_of_toNat_eq
  rw [← Paths.hashInput_label A t, ← Paths.hashInput_label B t', h]

/-- **The garbler's family-9 inputs on the table oracle**: digit `o`'s final at `exc_o`'s table key. -/
theorem garbler_final (scalar : NonZeroScalar) (c : Kriterion.CRT.Entry.Coins) (T : TagTable) (n : ℕ)
    (inG : n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) (Kriterion.CRT.Entry.garbleCM scalar c))
    (fam9 : tagFamily (n / 2 ^ 128) = 9) :
    ∃ o : Fin (2 * digitCount), ∃ w, Kriterion.CRT.Entry.exceptional scalar c o.val = some w ∧
      n = hashInput (keyT T w) (digestFinalTag o.val) := by
  have notIn : ∀ {α : Type} {S : Set Paths.TagKey} {program : CM α}, Paths.Tagged S program →
      (∀ k ∈ S, k.fam ≠ 9) → n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) program → False := by
    intro α S program tagged away inside
    obtain ⟨k, member, range, label, same⟩ := Align.asked_of_tagged tagged _ n inside
    have fam : tagFamily (n / 2 ^ 128) = k.fam := by rw [same, Align.hashInput_div, Align.tagFamily_key range]
    exact away k member (fam ▸ fam9)
  unfold Kriterion.CRT.Entry.garbleCM digestGarbleM at inG
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inG
  rcases inG with inX | inY | inKey | inMask | inTable | inFinals
  · exact (notIn (Paths.coordGarbleM_tagged Kriterion.CRT.Entry.table Kriterion.CRT.Entry.xCount 0
      (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _)
      (fun k member => by simp only [Paths.coordKeys, Set.mem_ofPred_eq] at member; omega) inX).elim
  · exact (notIn (Paths.coordGarbleM_tagged Kriterion.CRT.Entry.table Kriterion.CRT.Entry.yCount 1
      (Paths.bn254_ranges _ (by decide)) (by norm_num) _ _)
      (fun k member => by simp only [Paths.coordKeys, Set.mem_ofPred_eq] at member; omega) inY).elim
  · exact (notIn (Paths.keyM_tagged _) (fun k member => by rw [Set.mem_singleton_iff.mp member]; decide)
      inKey).elim
  · exact (notIn (Paths.maskAnswersM_tagged _ digitCount (by decide) (by decide))
      (fun k member => by have := Paths.maskKeys_fam k member; omega) inMask).elim
  · exfalso
    rw [Align.asked_digestTableM] at inTable
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false] at inTable
    obtain ⟨c', p, same | same⟩ := inTable
    · subst same
      have fam8 := (Align.digestLabelTag_fields (b := 0) c'.isLt (lt_of_lt_of_le p.isLt (by decide))
        (by norm_num)).1
      rw [Align.hashInput_div, fam8] at fam9
      omega
    · subst same
      have fam8 := (Align.digestLabelTag_fields (b := 1) c'.isLt (lt_of_lt_of_le p.isLt (by decide))
        (by norm_num)).1
      rw [Align.hashInput_div, fam8] at fam9
      omega
  · rw [Align.asked_tableM] at inFinals
    simp only [List.mem_flatMap, List.mem_finRange, true_and] at inFinals
    obtain ⟨o, inEntry⟩ := inFinals
    rw [Align.asked_garbleEntryM] at inEntry
    split at inEntry
    · exact absurd inEntry List.not_mem_nil
    · rename_i phi hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inEntry
      rcases inEntry with inEntry | inEntry
      · exact ⟨⟨2 * o.val, by have := o.isLt; omega⟩, _, Align.exceptional_some scalar c o phi hd,
          by rw [inEntry, eval_digestTableM, garblerKey_table]⟩
      · exact ⟨⟨2 * o.val + 1, by have := o.isLt; omega⟩, _, Align.triple_some scalar c o phi hd,
          by rw [inEntry, eval_digestTableM, garblerKey_table]⟩

theorem fullReplayKeys_fam9 : ∀ k ∈ Paths.fullReplayKeys, k.fam ≠ 9 := by
  rintro k (inC | inK | inM)
  · have := Paths.replayConvKeys_fam k inC
    omega
  · rw [Set.mem_singleton_iff.mp inK]
    decide
  · have := Paths.maskKeys_fam k inM
    omega

/-- **The reach's family-9 inputs**: its finals, at its digest key. -/
theorem reach_final [FieldCertificate] [GroupCertificate] (H : HashN) (pub : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : LamportSignature) (n : ℕ)
    (inside : n ∈ asked H (Paths.reachDecodedCM pub u labels)) (fam9 : tagFamily (n / 2 ^ 128) = 9) :
    ∃ o : Fin (2 * digitCount),
      n = hashInput (digestKey H coordinateBitCount (Kriterion.CRT.Entry.labelsOf labels) u) (digestFinalTag o.val) := by
  have notIn : ∀ {α : Type} {S : Set Paths.TagKey} {program : CM α}, Paths.Tagged S program →
      (∀ k ∈ S, k.fam ≠ 9) → n ∈ asked H program → False := by
    intro α S program tagged away inAsked
    obtain ⟨k, member, range, label, same⟩ := Align.asked_of_tagged tagged H n inAsked
    have fam : tagFamily (n / 2 ^ 128) = k.fam := by rw [same, Align.hashInput_div, Align.tagFamily_key range]
    exact away k member (fam ▸ fam9)
  have fromDigest : n ∈ asked H (digestEvalM coordinateBitCount digitCount (Kriterion.CRT.Entry.labelsOf labels) u
      (fun o => pub.exception.get o)) →
      ∃ o : Fin (2 * digitCount),
        n = hashInput (digestKey H coordinateBitCount (Kriterion.CRT.Entry.labelsOf labels) u)
          (digestFinalTag o.val) := by
    intro inDigest
    rw [Align.asked_digestEvalM, List.mem_append] at inDigest
    rcases inDigest with inLabels | inFinals
    · exfalso
      rw [Align.asked_digestKeyM] at inLabels
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at inLabels
      obtain ⟨c, p, rfl⟩ := inLabels
      have bit := Paths.coordBit_lt u c p.val
      have fam8 := (Align.digestLabelTag_fields (b := coordBit u c p.val) c.isLt
        (lt_of_lt_of_le p.isLt (by decide)) (by omega)).1
      rw [Align.hashInput_div, fam8] at fam9
      omega
    · obtain ⟨s, hs, rfl⟩ := Align.mem_finals inFinals
      exact ⟨⟨s, hs⟩, rfl⟩
  unfold Paths.reachDecodedCM at inside
  simp only [asked_bind, asked_pure, List.append_nil] at inside
  by_cases valid : validate u = true
  · rw [if_pos valid] at inside
    unfold Kriterion.CRT.Entry.reachCM at inside
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
    rcases inside with inReplay | inDigest
    · exact (notIn (Paths.replay_tagged pub u labels) fullReplayKeys_fam9 inReplay).elim
    · exact fromDigest inDigest
  · rw [if_neg valid] at inside
    unfold EntryReading.reachOffCM at inside
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
    rcases inside with inConv | inDigest
    · exact (notIn (Paths.replayConv_tagged pub u labels) (fun k member => by
        have := Paths.replayConvKeys_fam k member
        omega) inConv).elim
    · exact fromDigest inDigest

/-- Final site `o`'s final coincides at `u`: its exceptional input differs from `u` and has `u`'s table key. -/
def Bad (scalar : NonZeroScalar) (u : AffineInput) (o : Fin (2 * digitCount)) (c : Kriterion.CRT.Entry.Coins)
    (T : TagTable) : Prop :=
  ∃ w, Kriterion.CRT.Entry.exceptional scalar c o.val = some w ∧ w ≠ u ∧ keyT T w = keyT T u

/-- **A hidden reached final is a key coincidence of some digit.** -/
theorem hidden_final (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ)
    (scalar : NonZeroScalar) (u : AffineInput) (c : crtEntry.Coins) (T : TagTable) (e : Entry Empty Empty) :
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    Flags.HiddenReached crtEntry Kriterion.CRT.Entry.table parameter scalar (c, T) u e → Flags.entryFamily e = 9 →
      ∃ o : Fin (2 * digitCount), Bad scalar u o c T := by
  intro hidden fam
  obtain ⟨inG, inR, hiddenRule⟩ := hidden
  rw [StageTwo.garblerEntries_eq] at inG
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp inG
  unfold StageTwo.gAsked at hn
  have labelled := Paths.SameVisible.labelled_of_tagged (Paths.garbleCM_tagged scalar c)
    (schemeHash (tableOracle (FI := Empty) (EI := Empty) T)) n hn
  have fam9 : tagFamily (n / 2 ^ 128) = 9 := by
    have shown : tagFamily ((n : BaseField).val / 2 ^ 128) = 9 := fam
    rwa [labelled.val] at shown
  obtain ⟨o, w, hexc, hnw⟩ := garbler_final scalar c T n hn fam9
  unfold reachedEntries at inR
  dsimp only [Instance.crtEntry] at inR
  obtain ⟨n', hn', same⟩ := Paths.LabelCoincide.reachDecoded_queries _ _ _ _ _ _ inR
  have labelled' := Paths.SameVisible.labelled_of_tagged (Paths.reachDecodedCM_tagged _ u _) _ n' hn'
  have equal : n = n' := by
    have values := congrArg ZMod.val (PublicQuery.hash.inj same)
    rwa [labelled.val, labelled'.val] at values
  subst equal
  obtain ⟨o', hno'⟩ := reach_final _ _ u _ n hn' fam9
  have keys : keyT T w = keyT T u :=
    (hashInput_label_inj (hnw.symm.trans hno')).trans (digestKey_table T _ u)
  have slot : tagSlot (n / 2 ^ 128) = o.val := by
    rw [hnw, Align.hashInput_div]
    exact (Align.digestFinalTag_fields (lt_trans o.isLt (by decide))).2
  rw [Align.crtDesigned_hash, labelled.val, Align.designTag_final _ _ _ fam9, slot] at hiddenRule
  dsimp only [Instance.crtEntry] at hiddenRule
  refine ⟨o, w, hexc, fun wu => ?_, keys⟩
  rw [hexc, wu] at hiddenRule
  simp at hiddenRule

/-! ### 6. The mass of a coincidence -/

theorem val_lt (x : BaseField) : x.val < 2 ^ 254 :=
  lt_trans (ZMod.val_lt x) (by unfold baseFieldModulus; norm_num)

theorem testBit_diff {a b : ℕ} (ha : a < 2 ^ 254) (hb : b < 2 ^ 254) (ne : a ≠ b) :
    ∃ p : Fin coordinateBitCount, a.testBit p.val ≠ b.testBit p.val := by
  by_contra none
  push Not at none
  apply ne
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 254
  · exact none ⟨i, hi⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **Two distinct inputs differ in some bit.** -/
theorem bits_differ {w u : AffineInput} (ne : w ≠ u) :
    ∃ c0 : Fin 2, ∃ p0 : Fin coordinateBitCount, coordBit w c0 p0.val ≠ coordBit u c0 p0.val := by
  have hc : ∃ c0 : Fin 2, coordNat w c0 ≠ coordNat u c0 := by
    by_contra none
    push Not at none
    apply ne
    have hx := none 0
    have hy := none 1
    unfold coordNat at hx hy
    rw [if_pos rfl, if_pos rfl] at hx
    rw [if_neg (show (1 : Fin 2) ≠ 0 by decide), if_neg (show (1 : Fin 2) ≠ 0 by decide)] at hy
    obtain ⟨wx, wy⟩ := w
    obtain ⟨ux, uy⟩ := u
    simp only at hx hy
    rw [ZMod.val_injective _ hx, ZMod.val_injective _ hy]
  obtain ⟨c0, hc0⟩ := hc
  have lt : ∀ (v : AffineInput) (c : Fin 2), coordNat v c < 2 ^ 254 := by
    intro v c
    unfold coordNat
    split
    · exact val_lt _
    · exact val_lt _
  obtain ⟨p0, hp0⟩ := testBit_diff (lt w c0) (lt u c0) hc0
  refine ⟨c0, p0, ?_⟩
  unfold coordBit
  revert hp0
  cases (coordNat w c0).testBit p0.val <;> cases (coordNat u c0).testBit p0.val <;> simp

/-- **One final site's coincidence** has mass `2^-128` against every weight on the published value, per coins. -/
theorem digit_le [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (weight : crtEntry.Public → ℝ≥0∞) (o : Fin (2 * digitCount)) (c : crtEntry.Coins) :
    ∑' T, swappedTableLaw crtLayout T *
        (weight (stageOneView crtEntry parameter scalar (c, T)) * Flags.ind (Bad scalar u o c T)) ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' T, swappedTableLaw crtLayout T * weight (stageOneView crtEntry parameter scalar (c, T)) := by
  have never : (∀ T, ¬ Bad scalar u o c T) →
      ∑' T, swappedTableLaw crtLayout T *
          (weight (stageOneView crtEntry parameter scalar (c, T)) * Flags.ind (Bad scalar u o c T)) ≤
        (2 ^ 128 : ℝ≥0∞)⁻¹ *
          ∑' T, swappedTableLaw crtLayout T * weight (stageOneView crtEntry parameter scalar (c, T)) := by
    intro none
    have zero : ∀ T, Flags.ind (Bad scalar u o c T) = 0 := fun T => if_neg (none T)
    simp only [zero, mul_zero, tsum_zero]
    exact zero_le
  cases hexc : Kriterion.CRT.Entry.exceptional scalar c o.val with
  | none =>
      refine never ?_
      rintro T ⟨w, hw, -⟩
      rw [hexc] at hw
      cases hw
  | some w =>
      by_cases same : w = u
      · refine never ?_
        rintro T ⟨w', hw', ne, -⟩
        rw [hexc] at hw'
        cases hw'
        exact ne same
      · obtain ⟨c0, p0, hbit⟩ := bits_differ same
        have iff : ∀ T, Bad scalar u o c T = (keyT T w = keyT T u) := fun T => propext
          ⟨fun ⟨w', hw', _, key⟩ => by rw [hexc] at hw'; cases hw'; exact key, fun key => ⟨w, hexc, same, key⟩⟩
        simp only [iff]
        have reads : ∀ c' p, lpos c' p (coordBit u c' p.val) ≠ lpos c0 p0 (coordBit w c0 p0.val) := by
          intro c' p hsame
          obtain ⟨hc, hp, hb⟩ := lpos_inj (Paths.coordBit_lt u c' p.val) (Paths.coordBit_lt w c0 p0.val) hsame
          subst hc
          subst hp
          exact hbit hb.symm
        exact fresh_le (lpos c0 p0 (coordBit w c0 p0.val)) (lpos_away c0 p0 (Paths.coordBit_lt w c0 p0.val))
          (fun T => weight (stageOneView crtEntry parameter scalar (c, T)))
          (view_ignores parameter scalar c weight _ (lpos_family c0 p0 (Paths.coordBit_lt w c0 p0.val)))
          (fun T => keyT T w) (fun T => keyT T u) (keyT_ignores u _ reads) (fun T a => keyT_update T w c0 p0 a)

/-- The swapped tape, per coins. -/
theorem tape_le (F G : TableTape crtEntry → ℝ≥0∞) (ε : ℝ≥0∞)
    (each : ∀ c : crtEntry.Coins,
      ∑' T, swappedTableLaw crtLayout T * F (c, T) ≤ ε * ∑' T, swappedTableLaw crtLayout T * G (c, T)) :
    ∑' tape, swappedTableTape crtEntry tape * F tape ≤ ε * ∑' tape, swappedTableTape crtEntry tape * G tape := by
  unfold swappedTableTape
  rw [show crtEntry.layout = crtLayout from rfl]
  rw [PublicFirst.tsum_bind_mul, PublicFirst.tsum_bind_mul, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  rw [PublicFirst.tsum_map_mul, PublicFirst.tsum_map_mul, mul_left_comm]
  exact mul_le_mul' le_rfl (each c)

theorem ofReal_182 : ENNReal.ofReal (182 / 2 ^ 128) = 182 * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- **P8's family-9 row for the concrete entry**: a hidden digest final asked by the reach has mass at most
`182/2^128` (two final sites per digit) under the swapped tape, against every weight on the published value. -/
theorem crtEntry_finalCoincide : Flags.CrtFinalCoincide := by
  intro field group parameter scalar u
  letI := field
  letI := group
  letI := @Fintype.ofFinite Empty inferInstance
  letI := Classical.decEq Empty
  intro weight
  have split : ∀ tape : TableTape crtEntry,
      Flags.ind (∃ e, Flags.HiddenReached crtEntry Kriterion.CRT.Entry.table parameter scalar tape u e ∧
          Flags.entryFamily e = 9) ≤
        ∑ o : Fin (2 * digitCount), Flags.ind (Bad scalar u o tape.1 tape.2) := by
    rintro ⟨c, T⟩
    by_cases any : ∃ e, Flags.HiddenReached crtEntry Kriterion.CRT.Entry.table parameter scalar (c, T) u e ∧
        Flags.entryFamily e = 9
    · rw [Flags.ind_of any]
      obtain ⟨e, hidden, fam⟩ := any
      obtain ⟨o, bad⟩ := hidden_final field group parameter scalar u c T e hidden fam
      calc (1 : ℝ≥0∞) = Flags.ind (Bad scalar u o c T) := (Flags.ind_of bad).symm
        _ ≤ ∑ o' : Fin (2 * digitCount), Flags.ind (Bad scalar u o' c T) :=
          Finset.single_le_sum (f := fun o' => Flags.ind (Bad scalar u o' c T)) (fun _ _ => zero_le)
            (Finset.mem_univ o)
    · unfold Flags.ind
      rw [if_neg any]
      exact zero_le
  have perDigit : ∀ o : Fin (2 * digitCount),
      ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) * Flags.ind (Bad scalar u o tape.1 tape.2)) ≤
        (2 ^ 128 : ℝ≥0∞)⁻¹ *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) :=
    fun o => tape_le _ _ _ fun c => digit_le parameter scalar u weight o c
  have h182 : ((2 * digitCount : ℕ) : ℝ≥0∞) = 182 := by
    rw [show 2 * digitCount = 182 from rfl]
    norm_num
  calc ∑' tape, swappedTableTape crtEntry tape *
        (weight (stageOneView crtEntry parameter scalar tape) *
          Flags.ind (∃ e, Flags.HiddenReached crtEntry Kriterion.CRT.Entry.table parameter scalar tape u e ∧
            Flags.entryFamily e = 9))
      ≤ ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) *
            ∑ o : Fin (2 * digitCount), Flags.ind (Bad scalar u o tape.1 tape.2)) :=
        ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl (mul_le_mul' le_rfl (split tape))
    _ = ∑ o : Fin (2 * digitCount), ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) * Flags.ind (Bad scalar u o tape.1 tape.2)) := by
        simp_rw [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _o : Fin (2 * digitCount), (2 ^ 128 : ℝ≥0∞)⁻¹ *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) :=
        Finset.sum_le_sum fun o _ => perDigit o
    _ = ENNReal.ofReal (182 / 2 ^ 128) *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h182, ofReal_182, mul_assoc]

end

end Kriterion.CRT.Privacy.FinalCoincide
