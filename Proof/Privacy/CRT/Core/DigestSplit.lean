/-
**CRT privacy core: the digest row of H8** (`H8.CrtDigestSplit`).

Off the doubling event the exception entries of the real garbling are distributed as the uniform source's and are
independent of every `g` that reads the table off the hidden digest tags (every final, the other bit's label) and the
coins up to the exception pads.

* On the table oracle a final is answered by its tag alone (`finalMask_table`: the input is a labelled input
  below `2^168`, so the key does not matter). So entry `o` is `entryOf`: the pad for a zero digit, the pad with the
  nibbles at the two exceptional kinds' slots replaced by `lowNibble (A (final (2 o + k))).1 ⊕ digitCode` otherwise
  (`realGarbled_exception`).
* `entryOf` pushes a uniform pad and a uniform answer to a uniform entry (`lowNibble_uniform`, `update_uniform`,
  `entryOf_uniform`), digit by digit (`pi_map_uniform`).
* The swapped tape is its own refill at the pads (`coins_refill`) and at the finals (`swappedTableLaw_fill`; the finals are family 9, away from the sites). Refilling changes neither `g` nor the doubling
  event (both read the coins off the pads and the table off the finals), so the entries are uniform and independent
  (`digest_core`, `ConvSplit.split_apply`); the doubling flag is carried inside the view (`digestSplit`).
* The ideal side: a uniform source's exception is uniform (`source_exception_law`).
-/

import Proof.Privacy.CRT.Core.ConvSplit

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.DigestSplit

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.Conv (tag40 tagRead)
open Kriterion.CRT.Privacy.Split (pi_map_uniform prod_map_uniform)
open scoped ENNReal

noncomputable section

/-- The entries as a finite type (`Entry.entryFinite`). -/
@[instance_reducible] def entryFintype : Fintype Exception.Entry := Fintype.ofFinite _

attribute [local instance] entryFintype

/-! ### Uniform nibbles and entries -/

theorem lowNibble_eq (b : Block) : Exception.lowNibble b = b.setWidth 4 := BitVec.ofNat_toNat 4 b

theorem lowNibble_shift (b : Block) (z : BitVec 4) : Exception.lowNibble (b ^^^ z.setWidth 128) = Exception.lowNibble b ^^^ z := by
  rw [lowNibble_eq, lowNibble_eq, BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- **The low nibble of a uniform block is uniform.** -/
theorem lowNibble_uniform : (PMF.uniformOfFintype Block).map Exception.lowNibble = PMF.uniformOfFintype (BitVec 4) := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun x y => ?_
  exact {
    toFun := fun b => ⟨b.1 ^^^ (x ^^^ y).setWidth 128, by
      rw [lowNibble_shift, b.2, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]⟩
    invFun := fun b => ⟨b.1 ^^^ (x ^^^ y).setWidth 128, by
      rw [lowNibble_shift, b.2, BitVec.xor_comm x y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]⟩
    left_inv := fun b => Subtype.ext (by
      show b.1 ^^^ (x ^^^ y).setWidth 128 ^^^ (x ^^^ y).setWidth 128 = b.1
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero])
    right_inv := fun b => Subtype.ext (by
      show b.1 ^^^ (x ^^^ y).setWidth 128 ^^^ (x ^^^ y).setWidth 128 = b.1
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]) }

/-- An entry as a function of its two slots. -/
abbrev EntryF : Type := Fin 2 → BitVec 4

def entryEquiv : Exception.Entry ≃ EntryF where
  toFun v := fun i => v[i]
  invFun f := Vector.ofFn f
  left_inv v := by
    apply Vector.ext
    intro i hi
    simp
  right_inv f := by
    funext i
    simp

/-- **Overwriting one slot with a uniform nibble keeps a uniform entry uniform.** -/
theorem update_uniform (idx : Fin 2) :
    (PMF.uniformOfFintype (EntryF × BitVec 4)).map (fun p => Function.update p.1 idx p.2) =
      PMF.uniformOfFintype EntryF := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun e e' => ?_
  exact {
    toFun := fun p => ⟨(Function.update e' idx (p.1.1 idx), e' idx), by simp⟩
    invFun := fun p => ⟨(Function.update e idx (p.1.1 idx), e idx), by simp⟩
    left_inv := fun p => by
      obtain ⟨⟨f, y⟩, h⟩ := p
      apply Subtype.ext
      simp only at h ⊢
      subst h
      simp
    right_inv := fun p => by
      obtain ⟨⟨f, y⟩, h⟩ := p
      apply Subtype.ext
      simp only at h ⊢
      subst h
      simp }

theorem writeEntry_eq (pad : Exception.Entry) (idx : Fin 2) (v : BitVec 4) :
    Exception.writeEntry pad idx v = entryEquiv.symm (Function.update (entryEquiv pad) idx v) := by
  apply Vector.ext
  intro j hj
  simp only [Exception.writeEntry, entryEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Vector.getElem_ofFn,
    Vector.getElem_set, Function.update_apply]
  by_cases h : (⟨j, hj⟩ : Fin 2) = idx
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (Fin.ext e.symm))]
    rfl

/-- **A digit's entry from its pad and its two finals' answers**: the pad for a zero digit; otherwise the pad with the
masked code at both exceptional inputs' slots. -/
def entryOf (digit : Digit) (offset : AffineInput) :
    Exception.Entry × ((Block × Block) × (Block × Block)) → Exception.Entry :=
  match digitEndomorphismBase digit with
  | none => fun p => p.1
  | some phi => fun p => Exception.writeEntry
      (Exception.writeEntry p.1 (Exception.slotOf false (Exception.exceptionalInput phi offset))
        (Exception.lowNibble p.2.1.1 ^^^ Exception.digitCode digit))
      (Exception.slotOf true (Exception.tripleInput phi offset))
      (Exception.lowNibble p.2.2.1 ^^^ Exception.digitCode digit)

theorem masked_uniform (code : BitVec 4) :
    (PMF.uniformOfFintype (Block × Block)).map (fun a => Exception.lowNibble a.1 ^^^ code) =
      PMF.uniformOfFintype (BitVec 4) := by
  have factor : (fun a : Block × Block => Exception.lowNibble a.1 ^^^ code) =
      (fun z => z ^^^ code) ∘ Exception.lowNibble ∘ Prod.fst := rfl
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, Conv.fst_uniform, lowNibble_uniform]
  refine map_uniform_of_bijective ⟨fun a b h => ?_, fun z => ⟨z ^^^ code, ?_⟩⟩
  · have := congrArg (· ^^^ code) h
    simpa [BitVec.xor_assoc] using this
  · simp [BitVec.xor_assoc]

/-- **One slot written with a masked uniform nibble keeps a uniform entry uniform.** -/
theorem writeEntry_uniform (i : Fin 2) (code : BitVec 4) :
    (PMF.uniformOfFintype (Exception.Entry × (Block × Block))).map
      (fun p => Exception.writeEntry p.1 i (Exception.lowNibble p.2.1 ^^^ code)) =
      PMF.uniformOfFintype Exception.Entry := by
  classical
  have factor : (fun p : Exception.Entry × (Block × Block) => Exception.writeEntry p.1 i
      (Exception.lowNibble p.2.1 ^^^ code)) =
      entryEquiv.symm ∘ (fun q : EntryF × BitVec 4 => Function.update q.1 i q.2) ∘
        (fun p : Exception.Entry × (Block × Block) => (entryEquiv p.1, Exception.lowNibble p.2.1 ^^^ code)) := by
    funext p
    exact writeEntry_eq _ _ _
  rw [factor, ← PMF.map_comp, ← PMF.map_comp,
    prod_map_uniform entryEquiv _ (Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv entryEquiv)
      (masked_uniform _), update_uniform, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]

/-- **Two slots written with masked uniform nibbles keep a uniform entry uniform.** -/
theorem writeEntry2_uniform (i0 i1 : Fin 2) (code : BitVec 4) :
    (PMF.uniformOfFintype (Exception.Entry × ((Block × Block) × (Block × Block)))).map
      (fun p => Exception.writeEntry (Exception.writeEntry p.1 i0 (Exception.lowNibble p.2.1.1 ^^^ code)) i1
        (Exception.lowNibble p.2.2.1 ^^^ code)) = PMF.uniformOfFintype Exception.Entry := by
  classical
  let first : Exception.Entry × (Block × Block) → Exception.Entry := fun q =>
    Exception.writeEntry q.1 i0 (Exception.lowNibble q.2.1 ^^^ code)
  let second : Exception.Entry × (Block × Block) → Exception.Entry := fun q =>
    Exception.writeEntry q.1 i1 (Exception.lowNibble q.2.1 ^^^ code)
  have inner : (PMF.uniformOfFintype ((Exception.Entry × (Block × Block)) × (Block × Block))).map
      (fun q => (first q.1, id q.2)) = PMF.uniformOfFintype (Exception.Entry × (Block × Block)) :=
    prod_map_uniform first id (writeEntry_uniform i0 code) (PMF.map_id _)
  have factor : (fun p : Exception.Entry × ((Block × Block) × (Block × Block)) =>
      Exception.writeEntry (Exception.writeEntry p.1 i0 (Exception.lowNibble p.2.1.1 ^^^ code)) i1
        (Exception.lowNibble p.2.2.1 ^^^ code)) =
      second ∘ (fun q : (Exception.Entry × (Block × Block)) × (Block × Block) => (first q.1, id q.2)) ∘
        (Equiv.prodAssoc _ _ _).symm := by
    funext p
    rfl
  rw [factor, ← PMF.map_comp, ← PMF.map_comp,
    Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv (Equiv.prodAssoc _ _ _).symm, inner]
  exact writeEntry_uniform i1 code

/-- **A digit's entry is uniform** under a uniform pad and two uniform answers. -/
theorem entryOf_uniform (digit : Digit) (offset : AffineInput) :
    (PMF.uniformOfFintype (Exception.Entry × ((Block × Block) × (Block × Block)))).map (entryOf digit offset) =
      PMF.uniformOfFintype Exception.Entry := by
  classical
  unfold entryOf
  split
  · exact Laws.uniform_map_fst
  · exact writeEntry2_uniform _ _ _

/-! ### The finals on the table oracle -/

/-- The position of final site `o` (`2 d + k` for digit `d`, kind `k`). -/
def finalPos (o : ℕ) : Fin (2 ^ 40) := tag40 (digestFinalTag o)

theorem digestFinalTag_lt (o : ℕ) (ho : o < 65536) : digestFinalTag o < 2 ^ 40 :=
  Asks.tagCode_lt (by decide) ⟨by decide, by decide, by decide, by decide, ho, by decide⟩

theorem finalPos_val (o : ℕ) (ho : o < 65536) : (finalPos o).val = digestFinalTag o :=
  Nat.mod_eq_of_lt (digestFinalTag_lt o ho)

/-- **On the table oracle a final is answered by its tag alone.** -/
theorem finalMask_table (A : TagTable) (key : Block) (o : ℕ) (ho : o < 65536) :
    finalMask (schemeHash (tableOracle (FI := Empty) (EI := Empty) A)) key o =
      Exception.lowNibble (A (finalPos o)).1 := by
  unfold finalMask h128
  rw [Asks.schemeHash_small A _ (Asks.hashInput_small key _ (digestFinalTag_lt o ho))]
  show Exception.lowNibble (tagRead A (hashInput key (digestFinalTag o) / 2 ^ 128)).1 = _
  rw [hashInput_tag]
  rfl

theorem digitCount_lt : digitCount < 65536 := by decide

/-- The final sites: two per digit. -/
abbrev FinalSite := Fin (2 * digitCount)

theorem finalSite_lt (o : FinalSite) : o.val < 65536 := lt_trans o.isLt (by decide)

theorem finalPos_injective : Function.Injective fun o : FinalSite => finalPos o.val := by
  intro o o' h
  have e := congrArg Fin.val h
  simp only at e
  rw [finalPos_val _ (finalSite_lt o), finalPos_val _ (finalSite_lt o')] at e
  have hs := congrArg tagSlot e
  unfold digestFinalTag at hs
  rw [tagSlot_tagCode ⟨by decide, by decide, by decide, by decide, finalSite_lt o, by decide⟩,
    tagSlot_tagCode ⟨by decide, by decide, by decide, by decide, finalSite_lt o', by decide⟩] at hs
  exact Fin.ext hs

/-- A digit's two final sites. -/
def siteOf (o : Fin digitCount) (k : Fin 2) : FinalSite := ⟨2 * o.val + k.val, by have := o.isLt; omega⟩

/-- A function on the final sites is a pair of functions on the digits. -/
def sitesEquiv (X : Type) : (FinalSite → X) ≃ (Fin digitCount → X × X) where
  toFun F := fun o => (F (siteOf o 0), F (siteOf o 1))
  invFun G := fun s => if s.val % 2 = 0 then (G ⟨s.val / 2, by have := s.isLt; omega⟩).1
    else (G ⟨s.val / 2, by have := s.isLt; omega⟩).2
  left_inv F := by
    funext s
    show (if s.val % 2 = 0 then F (siteOf _ 0) else F (siteOf _ 1)) = F s
    split_ifs with h
    · exact congrArg F (Fin.ext (by show 2 * (s.val / 2) + 0 = s.val; omega))
    · exact congrArg F (Fin.ext (by show 2 * (s.val / 2) + 1 = s.val; omega))
  right_inv G := by
    funext o
    have e0 : (⟨(siteOf o 0).val / 2, by have := (siteOf o 0).isLt; omega⟩ : Fin digitCount) = o :=
      Fin.ext (by show (2 * o.val + 0) / 2 = o.val; omega)
    have e1 : (⟨(siteOf o 1).val / 2, by have := (siteOf o 1).isLt; omega⟩ : Fin digitCount) = o :=
      Fin.ext (by show (2 * o.val + 1) / 2 = o.val; omega)
    have k0 : (siteOf o 0).val % 2 = 0 := by show (2 * o.val + 0) % 2 = 0; omega
    have k1 : ¬ (siteOf o 1).val % 2 = 0 := by show ¬ (2 * o.val + 1) % 2 = 0; omega
    simp only [if_pos k0, if_neg k1, e0, e1]

theorem family_final (o : ℕ) (ho : o < 65536) : tagFamily (finalPos o).val = 9 := by
  rw [finalPos_val o ho]
  exact tagFamily_tagCode ⟨by decide, by decide, by decide, by decide, ho, by decide⟩

/-- **The finals lie away from every pad and mask site.** -/
theorem final_away : ∀ site ∈ crtLayout.sites, ∀ o : FinalSite,
    finalPos o.val ∉ (siteTags crtLayout site).map tagPos := by
  intro site mem o hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  have ho := finalSite_lt o
  have fam := family_final o.val ho
  rw [← heq] at fam
  have ne : ∀ {fam' coord idx stage level slot part : ℕ}, 5 < fam' → fam' < 9 →
      TagInRange coord idx stage level slot part →
      tagFamily (tagPos (tagCode fam' coord idx stage level slot part)).val ≠ 9 := by
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

/-! ### The real entries -/

/-- **The real exception entries on a table tape.** -/
theorem realGarbled_exception [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape crtEntry) :
    (H8.realGarbled crtEntry parameter scalar tape).1.exception =
      Vector.ofFn fun o : Fin digitCount => entryOf ((outputKeysOf scalar tape.1).get o).digit
        ((outputKeysOf scalar tape.1).get o).offset.coordinates
        (tape.1.exceptionPad.get o, (tape.2 (finalPos (2 * o.val)), tape.2 (finalPos (2 * o.val + 1)))) := by
  rw [ConvSplit.realGarbled_eq]
  simp only [garbleCM, FreeQuery.eval_bind, FreeQuery.eval_pure, assemble]
  rw [eval_digestGarbleM]
  refine congrArg Vector.ofFn (funext fun o => ?_)
  unfold digestEntries garbleEntry entryOf
  cases digitEndomorphismBase ((outputKeysOf scalar tape.1).get o).digit with
  | none => rfl
  | some phi =>
      simp only
      rw [finalMask_table _ _ _ (by have := o.isLt; simp only [digitCount] at this; omega),
        finalMask_table _ _ _ (by have := o.isLt; simp only [digitCount] at this; omega)]


/-! ### Refilling the pads -/

theorem get_ofFn {α : Type} {n : ℕ} (P : Fin n → α) (o : Fin n) : (Vector.ofFn P).get o = P o := by
  simp [Vector.get]
  rfl

theorem ofFn_get {α : Type} {n : ℕ} (v : Vector α n) : Vector.ofFn v.get = v := by
  apply Vector.ext
  intro i hi
  simp [Vector.get]

/-- The coins with their exception pads replaced. Never let the unifier compare `withPad c P` with `c`: the structure
eta then unfolds `Vector.ofFn` over the 91 digits. The facts below are proved by `simp only [withPad]` or in term
mode. The coins stay typed `crtEntry.Coins`, because `rw` needs the tape's type at reducible transparency. -/
def withPad (c : crtEntry.Coins) (P : Fin digitCount → Exception.Entry) : crtEntry.Coins :=
  { c with exceptionPad := Vector.ofFn P }

theorem withPad_withPad (c : crtEntry.Coins) (P Q : Fin digitCount → Exception.Entry) :
    withPad (withPad c P) Q = withPad c Q := by
  simp only [withPad]
  rfl

theorem withPad_eq_self (c : crtEntry.Coins) (P : Fin digitCount → Exception.Entry)
    (h : Vector.ofFn P = c.exceptionPad) : withPad c P = c :=
  (congrArg (fun v => ({ c with exceptionPad := v } : Scheme.Coins)) h).trans rfl

theorem withPad_self (c : crtEntry.Coins) : withPad c (fun o => c.exceptionPad.get o) = c := by
  refine withPad_eq_self c _ ?_
  show Vector.ofFn (n := FieldMacToECMac.outputMacCount) (fun o => c.exceptionPad.get o) = c.exceptionPad
  exact ofFn_get _

theorem withPad_pad (c : crtEntry.Coins) (P : Fin digitCount → Exception.Entry) (o : Fin digitCount) :
    (withPad c P).exceptionPad.get o = P o := by
  simp only [withPad]
  exact get_ofFn P o

theorem withPad_same (c : crtEntry.Coins) (P : Fin digitCount → Exception.Entry) :
    H8.SameOffExceptionPad (withPad c P) c := by
  simp only [H8.SameOffExceptionPad, withPad, and_self]

theorem outputKeysOf_withPad (scalar : NonZeroScalar) (c : crtEntry.Coins) (P : Fin digitCount → Exception.Entry) :
    outputKeysOf scalar (withPad c P) = outputKeysOf scalar c := by
  simp only [outputKeysOf, withPad]

/-- **The uniform coins are their own refill at the pads.** -/
theorem coins_refill :
    letI : Fintype crtEntry.Coins := @Fintype.ofFinite _ crtEntry.coinsFinite
    haveI : Nonempty crtEntry.Coins := ⟨crtEntry.coinWitness⟩
    (PMF.uniformOfFintype crtEntry.Coins).bind (fun c =>
      (PMF.uniformOfFintype (Fin digitCount → Exception.Entry)).map (withPad c)) =
      PMF.uniformOfFintype crtEntry.Coins := by
  letI : Fintype crtEntry.Coins := @Fintype.ofFinite _ crtEntry.coinsFinite
  haveI : Nonempty crtEntry.Coins := ⟨crtEntry.coinWitness⟩
  classical
  have prod : ((PMF.uniformOfFintype crtEntry.Coins).bind fun c =>
      (PMF.uniformOfFintype (Fin digitCount → Exception.Entry)).map (withPad c)) =
      (PMF.uniformOfFintype (crtEntry.Coins × (Fin digitCount → Exception.Entry))).map
        (fun p => withPad p.1 p.2) := by
    rw [← Kriterion.ArgoMAC.Phase3.Glue.uniform_product, PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun c => ?_)
    rw [PMF.map_comp]
    rfl
  rw [prod]
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun c1 c2 => ?_
  exact {
    toFun := fun p => ⟨(withPad c2 fun o => p.1.1.exceptionPad.get o, fun o => c2.exceptionPad.get o),
      (withPad_withPad c2 _ _).trans (withPad_self c2)⟩
    invFun := fun p => ⟨(withPad c1 fun o => p.1.1.exceptionPad.get o, fun o => c1.exceptionPad.get o),
      (withPad_withPad c1 _ _).trans (withPad_self c1)⟩
    left_inv := fun p => by
      obtain ⟨⟨c, P⟩, h⟩ := p
      apply Subtype.ext
      simp only at h
      subst h
      have e1 : (fun o => (withPad c2 fun o => c.exceptionPad.get o).exceptionPad.get o) =
          fun o => c.exceptionPad.get o := funext fun o => withPad_pad _ _ o
      exact Prod.ext ((withPad_withPad c P _).trans ((congrArg (withPad c) e1).trans (withPad_self c)))
        (funext fun o => withPad_pad c P o)
    right_inv := fun p => by
      obtain ⟨⟨c, P⟩, h⟩ := p
      apply Subtype.ext
      simp only at h
      subst h
      have e1 : (fun o => (withPad c1 fun o => c.exceptionPad.get o).exceptionPad.get o) =
          fun o => c.exceptionPad.get o := funext fun o => withPad_pad _ _ o
      exact Prod.ext ((withPad_withPad c P _).trans ((congrArg (withPad c) e1).trans (withPad_self c)))
        (funext fun o => withPad_pad c P o) }

/-! ### The law -/

/-- The digits' entries from their pads and finals' answers, at the coins' output keys. -/
def entriesOf (scalar : NonZeroScalar) (c : crtEntry.Coins)
    (q : Fin digitCount → Exception.Entry × ((Block × Block) × (Block × Block))) : Fin digitCount → Exception.Entry :=
  fun o => entryOf ((outputKeysOf scalar c).get o).digit ((outputKeysOf scalar c).get o).offset.coordinates (q o)

theorem entriesOf_uniform (scalar : NonZeroScalar) (c : crtEntry.Coins) :
    (PMF.uniformOfFintype (Fin digitCount → Exception.Entry × ((Block × Block) × (Block × Block)))).map
      (entriesOf scalar c) = PMF.uniformOfFintype (Fin digitCount → Exception.Entry) := by
  classical
  exact pi_map_uniform (fun o => entryOf ((outputKeysOf scalar c).get o).digit
    ((outputKeysOf scalar c).get o).offset.coordinates) fun o => entryOf_uniform _ _

/-- **The core of the digest split**: for any `G` that reads the coins off the pads and the table off the hidden digest
tags, the real exception entries are uniform and independent of `G`. -/
theorem digest_core {α : Type} [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (G : TableTape crtEntry → α) (hG : H8.ReadsOff H8.SameOffExceptionPad (H8.hiddenDigestTag u) G)
    (b : Vector Exception.Entry digitCount) (a : α) :
    ((swappedTableTape crtEntry).map fun tape =>
        some ((H8.realGarbled crtEntry parameter scalar tape).1.exception, G tape)) (some (b, a)) =
      ((PMF.uniformOfFintype (Fin digitCount → Exception.Entry)).map Vector.ofFn) b *
        ((swappedTableTape crtEntry).map fun tape => some (G tape)) (some a) := by
  classical
  let pos : FinalSite → Fin (2 ^ 40) := fun o => finalPos o.val
  have inj : Function.Injective pos := finalPos_injective
  let μ := swappedTableTape crtEntry
  letI : Fintype crtEntry.Coins := @Fintype.ofFinite _ crtEntry.coinsFinite
  haveI : Nonempty crtEntry.Coins := ⟨crtEntry.coinWitness⟩
  let uF := PMF.uniformOfFintype (FinalSite → Block × Block)
  let uP := PMF.uniformOfFintype (Fin digitCount → Exception.Entry)
  -- the finals are refilled
  have hfillT : μ = μ.bind fun ρ => uF.map fun F => ((ρ.1, HiddenGuess.fillAt pos F ρ.2) : TableTape crtEntry) := by
    have law := HiddenGuess.swappedTableLaw_fill crtLayout pos inj final_away
    show (PMF.uniformOfFintype crtEntry.Coins).bind (fun coins => (swappedTableLaw crtLayout).map
        fun table => (coins, table)) = ((PMF.uniformOfFintype crtEntry.Coins).bind fun coins =>
          (swappedTableLaw crtLayout).map fun table => (coins, table)).bind _
    rw [PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun coins => ?_)
    rw [PMF.bind_map]
    conv_lhs => rw [← law]
    rw [PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun A => ?_)
    rw [PMF.map_comp]
    rfl
  -- the pads are refilled
  have hfillC : μ = μ.bind fun ρ => uP.map fun P => ((withPad ρ.1 P, ρ.2) : TableTape crtEntry) := by
    show (PMF.uniformOfFintype crtEntry.Coins).bind (fun coins => (swappedTableLaw crtLayout).map
        fun table => (coins, table)) = ((PMF.uniformOfFintype crtEntry.Coins).bind fun coins =>
          (swappedTableLaw crtLayout).map fun table => (coins, table)).bind _
    conv_lhs => rw [← coins_refill]
    rw [PMF.bind_bind, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun c => ?_)
    rw [PMF.bind_map, PMF.bind_map]
    show uP.bind (fun P => (swappedTableLaw crtLayout).map fun A => (withPad c P, A)) =
      (swappedTableLaw crtLayout).bind fun A => uP.map fun P => (withPad c P, A)
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  -- both refills
  have hfill : μ = μ.bind fun ρ => uF.bind fun F => uP.map fun P =>
      ((withPad ρ.1 P, HiddenGuess.fillAt pos F ρ.2) : TableTape crtEntry) := by
    conv_lhs => rw [hfillC]
    conv_lhs => rw [hfillT]
    rw [PMF.bind_bind]
    refine congrArg (PMF.bind μ) (funext fun ρ => ?_)
    rw [PMF.bind_map]
    rfl
  -- the view after both refills
  have gfill : ∀ ρ : TableTape crtEntry, ∀ F P, G (withPad ρ.1 P, HiddenGuess.fillAt pos F ρ.2) = G ρ := by
    intro ρ F P
    refine hG (withPad ρ.1 P, HiddenGuess.fillAt pos F ρ.2) ρ (withPad_same ρ.1 P) fun tag htag => ?_
    dsimp only
    rw [HiddenGuess.fillAt_apply_of_not_mem pos F ρ.2 tag ?_]
    rintro ⟨o, rfl⟩
    exact htag (Or.inl (family_final o.val (finalSite_lt o)))
  have partFill : ∀ ρ : TableTape crtEntry, ∀ F P,
      (H8.realGarbled crtEntry parameter scalar (withPad ρ.1 P, HiddenGuess.fillAt pos F ρ.2)).1.exception =
        Vector.ofFn (entriesOf scalar ρ.1 fun o => (P o, sitesEquiv _ F o)) := by
    intro ρ F P
    rw [realGarbled_exception]
    refine congrArg Vector.ofFn (funext fun o => ?_)
    unfold entriesOf
    dsimp only
    rw [withPad_pad, outputKeysOf_withPad,
      show HiddenGuess.fillAt pos F ρ.2 (finalPos (2 * o.val)) = F (siteOf o 0) from
        congrFun (HiddenGuess.fillAt_comp pos inj F ρ.2) (siteOf o 0),
      show HiddenGuess.fillAt pos F ρ.2 (finalPos (2 * o.val + 1)) = F (siteOf o 1) from
        congrFun (HiddenGuess.fillAt_comp pos inj F ρ.2) (siteOf o 1)]
    rfl
  have joint : (μ.map fun tape => some ((H8.realGarbled crtEntry parameter scalar tape).1.exception, G tape)) =
      μ.bind fun ρ => ((PMF.uniformOfFintype (Fin digitCount → Exception.Entry)).map Vector.ofFn).map
        fun e => some (e, G ρ) := by
    conv_lhs => rw [hfill]
    rw [PMF.map_bind]
    refine congrArg (PMF.bind μ) (funext fun ρ => ?_)
    rw [PMF.map_bind]
    have inner : ∀ F, (uP.map fun P => ((withPad ρ.1 P, HiddenGuess.fillAt pos F ρ.2) : TableTape crtEntry)).map
        (fun tape => some ((H8.realGarbled crtEntry parameter scalar tape).1.exception, G tape)) =
        uP.map fun P => some (Vector.ofFn (entriesOf scalar ρ.1 fun o => (P o, sitesEquiv _ F o)), G ρ) := by
      intro F
      rw [PMF.map_comp]
      refine congrArg (fun h => PMF.map h uP) (funext fun P => ?_)
      simp only [Function.comp]
      rw [partFill ρ F P, gfill ρ F P]
    simp_rw [inner]
    have prodLaw : (uF.bind fun F => uP.map fun P => some (Vector.ofFn (entriesOf scalar ρ.1 fun o =>
        (P o, sitesEquiv _ F o)), G ρ)) =
        (PMF.uniformOfFintype ((FinalSite → Block × Block) × (Fin digitCount → Exception.Entry))).map
          (fun q => some (Vector.ofFn (entriesOf scalar ρ.1 fun o => (q.2 o, sitesEquiv _ q.1 o)), G ρ)) := by
      rw [← Kriterion.ArgoMAC.Phase3.Glue.uniform_product, PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun F => ?_)
      rw [PMF.map_comp]
      rfl
    rw [prodLaw]
    let zip : ((FinalSite → Block × Block) × (Fin digitCount → Exception.Entry)) ≃
        (Fin digitCount → Exception.Entry × ((Block × Block) × (Block × Block))) :=
      ((sitesEquiv (Block × Block)).prodCongr (Equiv.refl _)).trans
        ((Equiv.prodComm _ _).trans (Equiv.arrowProdEquivProdArrow _ _ _).symm)
    have hzip : ∀ q, zip q = fun o => (q.2 o, sitesEquiv _ q.1 o) := fun q => rfl
    have factor : (fun q : (FinalSite → Block × Block) × (Fin digitCount → Exception.Entry) =>
        some (Vector.ofFn (entriesOf scalar ρ.1 fun o => (q.2 o, sitesEquiv _ q.1 o)), G ρ)) =
        (fun e => some (e, G ρ)) ∘ Vector.ofFn ∘ entriesOf scalar ρ.1 ∘ zip := by
      funext q
      simp only [Function.comp_apply, hzip]
    rw [factor, ← PMF.map_comp, ← PMF.map_comp, ← PMF.map_comp,
      Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv zip, entriesOf_uniform]
  rw [joint]
  exact ConvSplit.split_apply μ _ G b a

/-! ### The ideal side -/

/-- **A uniform source's exception entries are uniform.** -/
theorem source_exception_law [Fintype Source] :
    (PMF.uniformOfFintype Source).map (fun s => (publish s).exception) =
      (PMF.uniformOfFintype (Fin digitCount → Exception.Entry)).map Vector.ofFn := by
  classical
  have marginal : (PMF.uniformOfFintype Source).map (fun s => s.exception) =
      PMF.uniformOfFintype (Fin digitCount → Exception.Entry) := by
    refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun e e' => ?_
    exact {
      toFun := fun s => ⟨{ s.1 with exception := e' }, rfl⟩
      invFun := fun s => ⟨{ s.1 with exception := e }, rfl⟩
      left_inv := fun s => by
        obtain ⟨s, hs⟩ := s
        apply Subtype.ext
        cases s
        simp only at hs ⊢
        rw [hs]
      right_inv := fun s => by
        obtain ⟨s, hs⟩ := s
        apply Subtype.ext
        cases s
        simp only at hs ⊢
        rw [hs] }
  rw [← marginal, PMF.map_comp]
  rfl

/-! ### The row -/

/-- Doubling reads the coins only through the offsets. -/
theorem doubling_congr [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput)
    (tape tape' : TableTape crtEntry) (h : H8.SameOffExceptionPad tape.1 tape'.1) :
    H8.Doubling crtEntry scalar tape u ↔ H8.Doubling crtEntry scalar tape' u := by
  unfold H8.Doubling
  have e : ∀ o, crtEntry.exceptional scalar tape.1 o = crtEntry.exceptional scalar tape'.1 o := by
    intro o
    show Entry.exceptional scalar tape.1 o = Entry.exceptional scalar tape'.1 o
    unfold Entry.exceptional outputKeysOf
    rw [h.1]
  simp only [e]

open Classical in
/-- **P5a: the digest row of H8.** -/
theorem digestSplit : H8.CrtDigestSplit := by
  intro _ _ parameter scalar u α g hg b a
  let D : TableTape crtEntry → Prop := fun tape => H8.Doubling crtEntry scalar tape u
  let G : TableTape crtEntry → Option α := fun tape => if D tape then none else some (g tape)
  have hG : H8.ReadsOff H8.SameOffExceptionPad (H8.hiddenDigestTag u) G := by
    intro tape tape' hc ht
    simp only [G, D]
    rw [hg tape tape' hc ht]
    by_cases h1 : H8.Doubling crtEntry scalar tape u
    · have h2 := (doubling_congr scalar u tape tape' hc).mp h1
      simp [h1, h2]
    · have h2 : ¬ H8.Doubling crtEntry scalar tape' u := fun h => h1 ((doubling_congr scalar u tape tape' hc).mpr h)
      simp [h1, h2]
  have lhs : ((swappedTableTape crtEntry).map fun tape => if H8.Doubling crtEntry scalar tape u then none
        else some ((H8.realGarbled crtEntry parameter scalar tape).1.exception, g tape)) (some (b, a)) =
      ((swappedTableTape crtEntry).map fun tape =>
        some ((H8.realGarbled crtEntry parameter scalar tape).1.exception, G tape)) (some (b, some a)) := by
    rw [PMF.map_apply, PMF.map_apply]
    refine tsum_congr fun tape => ?_
    by_cases hd : H8.Doubling crtEntry scalar tape u
    · simp [G, D, hd]
    · simp [G, D, hd]
  have rhs : ((swappedTableTape crtEntry).map fun tape => if H8.Doubling crtEntry scalar tape u then none
        else some (g tape)) (some a) =
      ((swappedTableTape crtEntry).map fun tape => some (G tape)) (some (some a)) := by
    rw [PMF.map_apply, PMF.map_apply]
    refine tsum_congr fun tape => ?_
    by_cases hd : H8.Doubling crtEntry scalar tape u
    · simp [G, D, hd]
    · simp [G, D, hd]
  have ideal : ((@PMF.uniformOfFintype _ (Instance.view).sourceFintype (Instance.view).sourceNonempty).map
      fun source => ((Instance.view).publish source).exception) =
      (PMF.uniformOfFintype (Fin digitCount → Exception.Entry)).map Vector.ofFn :=
    @source_exception_law (Instance.view).sourceFintype
  rw [lhs, rhs, ideal]
  exact digest_core parameter scalar u G hG b (some a)

end

end Kriterion.CRT.Privacy.DigestSplit
