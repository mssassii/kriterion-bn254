/-
**the real site layout and its swap facts** (row H3 with `Swap/Hop.lean`).

`crtLayout`:
* sites: the pad sites `.pad κ i ρ` for `κ < 2`, `i < 84`, `ρ < m_i` (the modulus 256 included), then the mask sites
  `.mask 0 k` for `k < 273` and `.mask 1 k` for `k < 182`;
* answers: `bn254Table.padAnswers S_κ i` for a pad site (`S_x = 367`, `S_y = 275`, D5), 2 for `.mask 0 k`, 3 for
  `.mask 1 k` (D8; the 364 non-collector masks fill 182 pair sites, no single site);
* law of a pad site: the fibre law of D6's fraction reading (`padVector m S q` of `Swap/Reading.lean`: the digit vector
  `Fin S → ZMod m`, drawn uniformly, then answers uniform on its fibre); law of a mask site: the fibre law of the
  `sampleFp` reading (`readSingle` for two answers, `readPair` for three; `Construction/CRT/Mask.lean`).

`crtLayout_facts : SwapLayoutFacts crtLayout`: each site's tags are distinct table positions; each site's law is
within its bias of uniform answers (a fibre law is as close to uniform answers as its reading of uniform answers is to
uniform: `Layout.fibreSiteLaw_close`); the biases are `m ^ S / 2 ^ (256 q)` for an odd pad site, 0 for the modulus 256,
`δ₃` per mask; and they sum exactly to `padSwapError`. So H3 for the entry is
`crt_swap_of_layout E (E.layout ▸ crtLayout_facts)` once `E.layout = crtLayout`.

Every closed fact about the table (moduli positive, `m ^ S ≤ 2 ^ (256 q)`, `q ≤ 17`, the numerator sum) is decided by
the kernel (`decide +kernel`); the rest is symbolic.
-/

import Proof.Privacy.CRT.Swap.Hop
import Proof.Privacy.CRT.Swap.Reading
import Construction.CRT.Mask

namespace Kriterion.CRT.Privacy

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3 (fibreLaw uniform_eq_bind_fibreLaw etvDist_map_le' productPMF
  uniformOfFintype_productPMF productPMF_map etvDist_productPMF_le sampleFp_etvDist_le delta3 reductionResidue)
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv uniformOfFintype_map_fst)
open Kriterion.ArgoMAC.PlanB (sampleFp sampleFp_surjective)
open scoped ENNReal

noncomputable section

namespace Layout

/-! ### Fibre laws -/

/-- The fibre law of a reading of `n` answers: a uniform target, then answers uniform on its fibre. -/
def fibreSiteLaw {n : ℕ} {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (read : (Fin n → Block × Block) → X) (onto : Function.Surjective read) : PMF (List (Block × Block)) :=
  ((PMF.uniformOfFintype X).bind (fibreLaw read onto)).map List.ofFn

/-- **A fibre law is as close to uniform answers as the reading of uniform answers is to uniform.** -/
theorem fibreSiteLaw_close {n : ℕ} {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (read : (Fin n → Block × Block) → X) (onto : Function.Surjective read) :
    (fibreSiteLaw read onto).etvDist (uniformAnswers n)
      ≤ ((PMF.uniformOfFintype (Fin n → Block × Block)).map read).etvDist (PMF.uniformOfFintype X) := by
  unfold fibreSiteLaw uniformAnswers
  calc (((PMF.uniformOfFintype X).bind (fibreLaw read onto)).map List.ofFn).etvDist
        ((PMF.uniformOfFintype (Fin n → Block × Block)).map List.ofFn)
      = (((PMF.uniformOfFintype X).bind (fibreLaw read onto)).map List.ofFn).etvDist
          ((((PMF.uniformOfFintype (Fin n → Block × Block)).map read).bind (fibreLaw read onto)).map
            List.ofFn) := by rw [← uniform_eq_bind_fibreLaw read onto]
    _ ≤ ((PMF.uniformOfFintype X).bind (fibreLaw read onto)).etvDist
          (((PMF.uniformOfFintype (Fin n → Block × Block)).map read).bind (fibreLaw read onto)) :=
        etvDist_map_le' _ _ _
    _ ≤ (PMF.uniformOfFintype X).etvDist ((PMF.uniformOfFintype (Fin n → Block × Block)).map read) :=
        PMF.etvDist_bind_right_le _ _ _
    _ = _ := PMF.etvDist_comm _ _

/-! ### Pad sites -/

/-- The fraction reading is onto when the pad has at least `m ^ S` values. -/
theorem padVector_surjective (m S q : ℕ) [NeZero m] (fits : m ^ S ≤ 2 ^ (256 * q)) :
    Function.Surjective (padVector m S q) := by
  intro target
  set X := (digitsEquiv m S).symm target
  have pos : 0 < m ^ S := pow_pos (NeZero.pos m) S
  have many : 0 < Fintype.card {u : Fin (2 ^ (256 * q)) // fractionMap m S q u = X} :=
    lt_of_lt_of_le (Nat.div_pos fits pos) (fraction_fibre m S q X)
  obtain ⟨⟨u, hu⟩⟩ := Fintype.card_pos_iff.mp many
  refine ⟨(packEquiv q).symm u, ?_⟩
  rw [padVector_factor, Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply, hu,
    Equiv.apply_symm_apply]

/-- The law of a pad site with `S` encodings, modulus `m` and `q` answers (uniform answers if the reading could not
be onto, which never happens on the real table: `tableFacts`). -/
def padSiteLaw (S m q : ℕ) : PMF (List (Block × Block)) :=
  if h : 0 < m ∧ m ^ S ≤ 2 ^ (256 * q) then
    haveI : NeZero m := ⟨h.1.ne'⟩
    fibreSiteLaw (padVector m S q) (padVector_surjective m S q h.2)
  else uniformAnswers q

theorem padSiteLaw_close (S m q : ℕ) (pos : 0 < m) (fits : m ^ S ≤ 2 ^ (256 * q)) :
    (padSiteLaw S m q).etvDist (uniformAnswers q)
      ≤ ((2 ^ (256 * q) % m ^ S : ℕ) : ℝ≥0∞) / (2 ^ (256 * q) : ℕ) := by
  have : NeZero m := ⟨pos.ne'⟩
  unfold padSiteLaw
  rw [dif_pos ⟨pos, fits⟩]
  exact le_trans (fibreSiteLaw_close _ _) (padVector_etvDist_le_mod m S q)

/-! ### Mask sites -/

/-- Two answers as three used blocks and the unused one. -/
def twoAnswers : (Fin 2 → Block × Block) ≃ (Block × Block × Block) × Block where
  toFun a := (((a 0).1, (a 0).2, (a 1).1), (a 1).2)
  invFun t := ![(t.1.1, t.1.2.1), (t.1.2.2, t.2)]
  left_inv a := by funext j; fin_cases j <;> rfl
  right_inv t := rfl

/-- Three answers as two triples of blocks. -/
def threeAnswers : (Fin 3 → Block × Block) ≃ (Block × Block × Block) × (Block × Block × Block) where
  toFun a := (((a 0).1, (a 0).2, (a 1).1), ((a 1).2, (a 2).1, (a 2).2))
  invFun t := ![(t.1.1, t.1.2.1), (t.1.2.2, t.2.1), (t.2.2.1, t.2.2.2)]
  left_inv a := by funext j; fin_cases j <;> rfl
  right_inv t := rfl

/-- `sampleFp` of a triple. -/
def sampleTriple (blocks : Block × Block × Block) : BaseField := sampleFp blocks.1 blocks.2.1 blocks.2.2

theorem readSingle_eq : readSingle = sampleTriple ∘ Prod.fst ∘ twoAnswers := rfl

theorem readPair_eq : readPair = Prod.map (fun b : Block × Block × Block => sampleFp b.1 b.2.1 b.2.2)
    (fun b : Block × Block × Block => sampleFp b.1 b.2.1 b.2.2) ∘ threeAnswers := rfl

theorem readSingle_surjective : Function.Surjective readSingle := by
  intro value
  obtain ⟨blocks, hit⟩ := sampleFp_surjective value
  exact ⟨twoAnswers.symm (blocks, 0), by rw [readSingle_eq]; simpa [sampleTriple] using hit⟩

theorem readPair_surjective : Function.Surjective readPair := by
  intro value
  obtain ⟨first, hitFirst⟩ := sampleFp_surjective value.1
  obtain ⟨second, hitSecond⟩ := sampleFp_surjective value.2
  refine ⟨threeAnswers.symm (first, second), ?_⟩
  rw [readPair_eq]
  simp only [Function.comp_apply, Equiv.apply_symm_apply, Prod.map_apply]
  exact Prod.ext hitFirst hitSecond

theorem readSingle_etvDist_le :
    ((PMF.uniformOfFintype (Fin 2 → Block × Block)).map readSingle).etvDist (PMF.uniformOfFintype BaseField)
      ≤ delta3 := by
  rw [readSingle_eq, ← PMF.map_comp, ← PMF.map_comp, uniformOfFintype_map_equiv, uniformOfFintype_map_fst]
  exact sampleFp_etvDist_le

theorem readPair_etvDist_le :
    ((PMF.uniformOfFintype (Fin 3 → Block × Block)).map readPair).etvDist
        (PMF.uniformOfFintype (BaseField × BaseField)) ≤ delta3 + delta3 := by
  have law : (PMF.uniformOfFintype (Fin 3 → Block × Block)).map readPair
      = productPMF ((PMF.uniformOfFintype (Block × Block × Block)).map
          (fun b : Block × Block × Block => sampleFp b.1 b.2.1 b.2.2))
        ((PMF.uniformOfFintype (Block × Block × Block)).map
          (fun b : Block × Block × Block => sampleFp b.1 b.2.1 b.2.2)) := by
    rw [readPair_eq, ← PMF.map_comp, uniformOfFintype_map_equiv, uniformOfFintype_productPMF, productPMF_map]
  have target : PMF.uniformOfFintype (BaseField × BaseField)
      = productPMF (PMF.uniformOfFintype BaseField) (PMF.uniformOfFintype BaseField) :=
    uniformOfFintype_productPMF
  rw [law, target]
  exact le_trans (etvDist_productPMF_le _ _ _ _) (add_le_add sampleFp_etvDist_le sampleFp_etvDist_le)

/-- The law of a two-answer mask site. -/
def singleSiteLaw : PMF (List (Block × Block)) := fibreSiteLaw readSingle readSingle_surjective

/-- The law of a three-answer mask site. -/
def pairSiteLaw : PMF (List (Block × Block)) := fibreSiteLaw readPair readPair_surjective

/-! ### The real table's pad rows -/

/-- The encodings of coordinate `κ`: 367 for `x`, 275 for `y`. -/
def padS (κ : ℕ) : ℕ := if κ = 0 then 367 else 275

/-- Modulus `i` of the real table (1 off range). -/
def padModulus (i : ℕ) : ℕ := if h : i < bn254Table.count then bn254Table.modulus ⟨i, h⟩ else 1

/-- The pad answers of coordinate `κ` and modulus `i` (D5; 0 off range). -/
def padCount (κ i : ℕ) : ℕ := if h : i < bn254Table.count then bn254Table.padAnswers (padS κ) ⟨i, h⟩ else 0

/-- The closed facts of the 168 rows, decided by the kernel. -/
theorem tableFacts : ∀ κ, κ < 2 → ∀ i, i < 84 →
    0 < padModulus i ∧ padModulus i ^ padS κ ≤ 2 ^ (256 * padCount κ i) ∧ 256 * padCount κ i ≤ 4352 ∧
      (padModulus i = 256 → 8 * padS κ ≤ 256 * padCount κ i) ∧ padModulus i < 65536 ∧ padCount κ i < 64 := by
  decide +kernel

/-- A pad row's numerator over `2 ^ 4352` (0 for the modulus 256). -/
def padNum (κ i : ℕ) : ℕ :=
  if padModulus i = 256 then 0 else padModulus i ^ padS κ * 2 ^ (4352 - 256 * padCount κ i)

/-- **The pad rows' numerators sum to `padSwapNum`** (each row counted `m` times, once per slot). -/
theorem padNum_sum :
    ((List.range 2).map fun κ => ((List.range 84).map fun i => padModulus i * padNum κ i).sum).sum
      = BudgetData.padSwapNum := by
  decide +kernel

theorem padSwapNumer_eq : BudgetData.padSwapNumer = BudgetData.padSwapNum + 637 * (2 ^ 384 % BudgetData.p) * 2 ^ 3968 := by
  decide +kernel

theorem padSwapDenom_eq' : BudgetData.padSwapDenom = 2 ^ 4352 := by
  decide +kernel

/-! ### The layout -/

/-- The pad sites. -/
def padSites : List SiteId :=
  (List.range 2).flatMap fun κ => (List.range 84).flatMap fun i =>
    (List.range (padModulus i)).map fun ρ => SiteId.pad κ i ρ

/-- The mask sites. -/
def maskSites : List SiteId :=
  (List.range 273).map (SiteId.mask 0) ++ (List.range 182).map (SiteId.mask 1)

/-- The answers of a site. -/
def layoutAnswers : SiteId → ℕ
  | .pad κ i _ => padCount κ i
  | .mask 0 _ => 2
  | .mask 1 _ => 3
  | .mask _ _ => 0

/-- The law of a site. -/
def layoutLaw : SiteId → PMF (List (Block × Block))
  | .pad κ i _ => padSiteLaw (padS κ) (padModulus i) (padCount κ i)
  | .mask 0 _ => singleSiteLaw
  | .mask 1 _ => pairSiteLaw
  | .mask _ _ => PMF.pure []

/-- The bias of a site. -/
def layoutBias : SiteId → ℝ≥0∞
  | .pad κ i _ => (padNum κ i : ℝ≥0∞) / 2 ^ 4352
  | .mask 0 _ => delta3
  | .mask 1 _ => delta3 + delta3
  | .mask _ _ => 0

end Layout

open Layout in
/-- **The real site layout**. -/
def crtLayout : SiteLayout where
  sites := padSites ++ maskSites
  answers := layoutAnswers
  law := layoutLaw

namespace Layout

/-! ### The facts -/

theorem mem_padSites {site : SiteId} (mem : site ∈ padSites) :
    ∃ κ i ρ, site = .pad κ i ρ ∧ κ < 2 ∧ i < 84 ∧ ρ < padModulus i := by
  simp only [padSites, List.mem_flatMap, List.mem_map, List.mem_range] at mem
  obtain ⟨κ, hκ, i, hi, ρ, hρ, rfl⟩ := mem
  exact ⟨κ, i, ρ, rfl, hκ, hi, hρ⟩

theorem mem_maskSites {site : SiteId} (mem : site ∈ maskSites) :
    (∃ k, site = .mask 0 k ∧ k < 273) ∨ (∃ k, site = .mask 1 k ∧ k < 182) := by
  simp only [maskSites, List.mem_append, List.mem_map, List.mem_range] at mem
  rcases mem with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact Or.inl ⟨k, rfl, hk⟩
  · exact Or.inr ⟨k, rfl, hk⟩

/-- The tags of a site with small fields are distinct table positions. -/
theorem nodup_tags (fam coord idx stage slot n : ℕ) (_hcoord : coord < 2) (_hidx : idx < 128)
    (_hstage : stage < 4) (_hslot : slot < 65536) (hn : n ≤ 64) (_hfam : fam < 16) :
    (((List.range n).map fun j => tagCode fam coord idx stage 0 slot j).map tagPos).Nodup := by
  rw [List.map_map]
  refine (List.nodup_range).map_on fun j hj j' hj' same => ?_
  rw [List.mem_range] at hj hj'
  have := congrArg Fin.val same
  simp only [Function.comp, tagPos, tagCode] at this
  omega

theorem crtLayout_nodup : ∀ site ∈ crtLayout.sites, ((siteTags crtLayout site).map tagPos).Nodup := by
  intro site mem
  rcases List.mem_append.mp mem with pad | mask
  · obtain ⟨κ, i, ρ, rfl, hκ, hi, hρ⟩ := mem_padSites pad
    obtain ⟨-, -, -, -, hm, hq⟩ := tableFacts κ hκ i hi
    exact nodup_tags Family.body κ i 0 ρ (padCount κ i) hκ (by omega) (by omega) (by omega) (by omega)
      (by decide)
  · rcases mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · exact nodup_tags Family.mask 0 0 0 k 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by decide)
    · exact nodup_tags Family.mask 0 0 1 k 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by decide)

theorem pad_close (κ i ρ : ℕ) (hκ : κ < 2) (hi : i < 84) :
    (layoutLaw (.pad κ i ρ)).etvDist (uniformAnswers (layoutAnswers (.pad κ i ρ))) ≤ layoutBias (.pad κ i ρ) := by
  obtain ⟨pos, fits, small, pow2, -, -⟩ := tableFacts κ hκ i hi
  simp only [layoutLaw, layoutAnswers, layoutBias, padNum]
  refine le_trans (padSiteLaw_close _ _ _ pos fits) ?_
  by_cases h256 : padModulus i = 256
  · have zero : 2 ^ (256 * padCount κ i) % padModulus i ^ padS κ = 0 := by
      rw [h256, show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]
      exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (pow2 h256))
    rw [zero]
    simp
  · rw [if_neg h256]
    have split : (2 : ℝ≥0∞) ^ 4352 = 2 ^ (256 * padCount κ i) * 2 ^ (4352 - 256 * padCount κ i) := by
      rw [← pow_add, Nat.add_sub_cancel' small]
    generalize hx : 2 ^ (256 * padCount κ i) % padModulus i ^ padS κ = x
    have xle : x ≤ padModulus i ^ padS κ := by
      rw [← hx]
      exact (Nat.mod_lt _ (pow_pos pos _)).le
    rw [Nat.cast_mul, Nat.cast_pow (padModulus i), Nat.cast_pow 2 (4352 - 256 * padCount κ i),
      Nat.cast_pow 2 (256 * padCount κ i), Nat.cast_two, split,
      ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
    refine ENNReal.div_le_div_right ?_ _
    rw [← Nat.cast_pow]
    exact Nat.cast_le.mpr xle

theorem crtLayout_close :
    ∀ site ∈ crtLayout.sites, (crtLayout.law site).etvDist (uniformAnswers (crtLayout.answers site))
      ≤ layoutBias site := by
  intro site mem
  rcases List.mem_append.mp mem with pad | mask
  · obtain ⟨κ, i, ρ, rfl, hκ, hi, -⟩ := mem_padSites pad
    exact pad_close κ i ρ hκ hi
  · rcases mem_maskSites mask with ⟨k, rfl, -⟩ | ⟨k, rfl, -⟩
    · exact le_trans (fibreSiteLaw_close _ _) readSingle_etvDist_le
    · show (layoutLaw (.mask 1 k)).etvDist (uniformAnswers (layoutAnswers (.mask 1 k))) ≤ layoutBias (.mask 1 k)
      simp only [layoutLaw, layoutAnswers, layoutBias]
      exact le_trans (fibreSiteLaw_close _ _) readPair_etvDist_le

/-! ### The sum of the biases -/

theorem sum_map_div {α : Type} (l : List α) (f : α → ℕ) (D : ℝ≥0∞) :
    (l.map fun a => (f a : ℝ≥0∞) / D).sum = (((l.map f).sum : ℕ) : ℝ≥0∞) / D := by
  induction l with
  | nil => simp
  | cons a rest ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, Nat.cast_add,
      ENNReal.add_div]

theorem sum_map_const {α : Type} (l : List α) (c : ℝ≥0∞) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a rest ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

theorem sum_flatMap' {α β : Type} (l : List α) (f : α → List β) (g : β → ℝ≥0∞) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a rest ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem padSites_sum : (padSites.map layoutBias).sum = (BudgetData.padSwapNum : ℝ≥0∞) / 2 ^ 4352 := by
  have inner : ∀ κ i, (((List.range (padModulus i)).map fun ρ => SiteId.pad κ i ρ).map layoutBias).sum
      = ((padModulus i * padNum κ i : ℕ) : ℝ≥0∞) / 2 ^ 4352 := by
    intro κ i
    rw [List.map_map]
    simp only [Function.comp_def, layoutBias]
    rw [sum_map_const, List.length_range, Nat.cast_mul, mul_div_assoc]
  unfold padSites
  rw [sum_flatMap']
  simp only [sum_flatMap', inner]
  rw [← padNum_sum]
  have outer : ∀ κ, ((List.range 84).map fun i => ((padModulus i * padNum κ i : ℕ) : ℝ≥0∞) / 2 ^ 4352).sum
      = ((((List.range 84).map fun i => padModulus i * padNum κ i).sum : ℕ) : ℝ≥0∞) / 2 ^ 4352 :=
    fun κ => sum_map_div _ (fun i => padModulus i * padNum κ i) _
  simp only [outer]
  exact sum_map_div _ _ _

theorem maskSites_sum : (maskSites.map layoutBias).sum = 637 * delta3 := by
  have ones : ((List.range 273).map (SiteId.mask 0)).map layoutBias = (List.range 273).map fun _ => delta3 := by
    rw [List.map_map]; rfl
  have pairs : ((List.range 182).map (SiteId.mask 1)).map layoutBias
      = (List.range 182).map fun _ => delta3 + delta3 := by
    rw [List.map_map]; rfl
  simp only [maskSites, List.map_append, List.sum_append, ones, pairs, sum_map_const, List.length_range]
  push_cast
  ring

/-- **The biases sum exactly to `padSwapError`.** -/
theorem crtLayout_total : (crtLayout.sites.map layoutBias).sum = ENNReal.ofReal padSwapError := by
  have denomPos : (0 : ℝ) < (BudgetData.padSwapDenom : ℝ) := by exact_mod_cast BudgetData.padSwapDenom_pos
  have value : ENNReal.ofReal padSwapError
      = ((BudgetData.padSwapNumer : ℕ) : ℝ≥0∞) / ((BudgetData.padSwapDenom : ℕ) : ℝ≥0∞) := by
    unfold padSwapError frac
    rw [ENNReal.ofReal_div_of_pos denomPos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have split : (2 : ℝ≥0∞) ^ 4352 = 2 ^ 384 * 2 ^ 3968 := pow_add (2 : ℝ≥0∞) 384 3968
  rw [value, padSwapNumer_eq, padSwapDenom_eq']
  generalize hr : 2 ^ 384 % BudgetData.p = r
  have deltaEq : delta3 = (r : ℝ≥0∞) / 2 ^ 384 := by
    unfold delta3 reductionResidue
    rw [baseFieldModulus_eq, hr]
  have cne : (2 : ℝ≥0∞) ^ 3968 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ctop : (2 : ℝ≥0∞) ^ 3968 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have maskPart : (637 : ℝ≥0∞) * delta3 = ((637 * r * 2 ^ 3968 : ℕ) : ℝ≥0∞) / 2 ^ 4352 := by
    rw [deltaEq, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow 2 3968, Nat.cast_two, Nat.cast_ofNat]
    generalize hc : (2 : ℝ≥0∞) ^ 3968 = c at split cne ctop
    rw [split, ENNReal.mul_div_mul_right _ _ cne ctop, mul_div_assoc]
  simp only [crtLayout, List.map_append, List.sum_append, padSites_sum, maskSites_sum]
  rw [Nat.cast_add, ENNReal.add_div, Nat.cast_pow 2 4352, Nat.cast_two, maskPart]

end Layout

/-- **The swap facts of the real layout.** -/
def crtLayout_facts : SwapLayoutFacts crtLayout where
  nodup := Layout.crtLayout_nodup
  bias := Layout.layoutBias
  close := Layout.crtLayout_close
  total := le_of_eq Layout.crtLayout_total

/-- **Ledger row H3 for an entry whose layout is `crtLayout`.** -/
theorem crt_swap {FI EI : Type} [Finite FI] [Finite EI] (E : CrtEntry FI EI) (layout : E.layout = crtLayout) :
    HopBound (crtChain E).tablePlanted (crtChain E).padSwapped fun _ _ => padSwapError :=
  crt_swap_of_layout E (layout ▸ crtLayout_facts)

end

end Kriterion.CRT.Privacy
