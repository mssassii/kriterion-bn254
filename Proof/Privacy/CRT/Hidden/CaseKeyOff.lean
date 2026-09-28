/-
**H7's case `keyOff`: the bridge key off the curve**.

`StageTwo.keyOff_case : GuessCase keyOff notNearEdge BmrOff.keyError` and
`StageTwo.keyOff_error_le : BmrOff.keyError ≤ ofReal crtHiddenCharge`, from `KeyOffEntry.keyLabel_entry`:

* **the input** (`key_of_fam10`): the only garbler input of family 10 is the key input `maskKeyInput t`, whose low 128
  bits are those of the bridge key `t` (`maskKeyInput_mod`);
* **the view reads P45 only through its output** (`stageTwoView_fd`): off the curve, two tapes with the same rest of
  the coins, the same P45 cells and hints and tables that agree off the hidden positions (`KeyOffEntry.HidPos`: hot
  body positions and every mask position) have the same stage-2 view. The curve, rows and records are P45's
  (`BmrEntry.curve_eq`, `rows_eq`, `recX_eq`, `recY_eq`); the conversion material reads only families 0 to 5
  (`Asks.readPub_congr`); the digest reads families 8 and 9; the labels read only the input keys and, through the
  absorbed chunk joins, the in-range conversion reading, families 0 to 5 (`keyOf_low`); the designed entries
  are the designed garbler inputs (`StageTwo.designedEntries_eq`), where the coordinate garblers ask the same inputs
  on both tables (their family-6 answers feed only the residues, `asked_coordGarbleM`), the key and mask inputs are
  not designed off the curve, and a designed input is never at a hidden position.
-/

import Proof.Privacy.CRT.Core.BmrKeyOffEntry
import Proof.Privacy.CRT.Hidden.StageTwoTable
import Proof.Privacy.CRT.Core.KeyZeroCongr

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.CaseKeyOff

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Privacy.StageTwo
open Kriterion.CRT.Privacy.KeyOffEntry
open scoped ENNReal

noncomputable section

attribute [local instance 2000] H8.tableModulusNeZero

/-! ### 1. The garbler's family-10 input is the key input -/

/-- **A garbler input of family 10 is the key input.** -/
theorem key_of_fam10 (scalar : NonZeroScalar) (coins : Entry.Coins) (T : TagTable) (N : ℕ)
    (inside : N ∈ gAsked scalar (coins, T)) (fam : tagFamily (N / 2 ^ 128) = 10) :
    N = maskKeyInput coins.bridgeKey := by
  rw [gAsked_eq] at inside
  simp only [List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (coordX_tagged coins) _ _ inX
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_ofPred_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (coordY_tagged coins) _ _ inY
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.coordKeys, Set.mem_ofPred_eq] at member
    omega
  · rw [asked_keyM, List.mem_singleton] at inKey
    exact inKey
  · rw [mask_fam _ _ N inMask] at fam
    exact absurd fam (by decide)
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (digest_tagged scalar coins _) _ _ inDigest
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union, Set.mem_ofPred_eq] at member
    omega

/-- The key input's low 128 bits are the bridge key's. -/
theorem maskKeyInput_mod (t : BaseField) : maskKeyInput t % 2 ^ 128 = t.val % 2 ^ 128 := by
  unfold maskKeyInput
  rw [hashInput_mod, BitVec.toNat_ofNat]

/-! ### 2. Hashes that agree off the hidden positions -/

/-- The hidden positions, on naturals (`KeyOffEntry.HidPos` at `⟨τ, _⟩`). -/
def Hid (u : AffineInput) (τ : ℕ) : Prop :=
  (tagFamily τ = 6 ∧ hotTag Entry.table u τ = true) ∨ tagFamily τ = 7

/-- Two hashes agree at every labelled input whose tag is in range and satisfies `P`. -/
def AgreeOn (P : ℕ → Prop) (H H' : HashN) : Prop :=
  ∀ (label : Block) (τ : ℕ), τ < 2 ^ 40 → P τ → H (hashInput label τ) = H' (hashInput label τ)

theorem AgreeOn.mono {P Q : ℕ → Prop} {H H' : HashN} (agree : AgreeOn P H H') (imp : ∀ τ, Q τ → P τ) :
    AgreeOn Q H H' :=
  fun label τ hτ q => agree label τ hτ (imp τ q)

theorem agreeOn_scheme (u : AffineInput) (T T' : TagTable) (agree : ∀ q, ¬ HidPos u q → T q = T' q) :
    AgreeOn (fun τ => ¬ Hid u τ) (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
      (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) := by
  intro label τ hτ notHid
  rw [tableHash_hashInput T label hτ, tableHash_hashInput T' label hτ]
  exact agree ⟨τ, hτ⟩ notHid

theorem agreeOn_tagHash (u : AffineInput) (T T' : TagTable) (agree : ∀ q, ¬ HidPos u q → T q = T' q) :
    AgreeOn (fun τ => ¬ Hid u τ) (H8.tagHash T) (H8.tagHash T') := by
  intro label τ hτ notHid
  rw [BmrEntry.tagHash_hashInput, BmrEntry.tagHash_hashInput]
  have eq : (⟨τ % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ : Fin (2 ^ 40)) = ⟨τ, hτ⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hτ)
  rw [eq]
  exact agree ⟨τ, hτ⟩ notHid

theorem not_hid_of_fam {u : AffineInput} {τ : ℕ} (six : tagFamily τ ≠ 6) (seven : tagFamily τ ≠ 7) :
    ¬ Hid u τ := by
  rintro (⟨h, -⟩ | h)
  · exact six h
  · exact seven h

theorem not_hid_of_low {u : AffineInput} {τ : ℕ} (low : tagFamily τ ≤ 5) : ¬ Hid u τ :=
  not_hid_of_fam (by omega) (by omega)

/-- **A tagged run whose keys satisfy `P` asks and computes the same on two hashes that agree on `P`.** -/
theorem tagged_congr {α : Type} {S : Set Paths.TagKey} {program : CM α} (tagged : Paths.Tagged S program)
    {P : ℕ → Prop} (keys : ∀ k ∈ S, k.InRange → P k.code) {H H' : HashN} (agree : AgreeOn P H H') :
    asked H program = asked H' program ∧ program.eval H = program.eval H' := by
  refine asked_eval_congr H H' program fun n inside => ?_
  obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged tagged H n inside
  exact agree label k.code (Paths.TagKey.code_lt range) (keys k member range)

theorem digest_keys (u : AffineInput) :
    ∀ k ∈ Paths.digestLabelKeys coordinateBitCount ∪ Paths.digestFinalKeys digitCount, k.InRange →
      ¬ Hid u k.code := by
  intro k member range
  simp only [Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union, Set.mem_ofPred_eq] at member
  refine not_hid_of_fam ?_ ?_ <;> rw [tagFamily_key range] <;> omega

/-! ### 3. The coordinate garbler reads the family-6 answers only for its residues -/

/-- A body asks the same inputs on every hash. -/
theorem asked_bodyGarbleM (H H' : HashN) (m S q coord i : ℕ) (final : Fin m → Label) :
    asked H (bodyGarbleM m S q coord i final) = asked H' (bodyGarbleM m S q coord i final) := by
  simp only [bodyGarbleM, asked_bind, asked_tableM, asked_padVectorM, asked_pure]

theorem chunk_keys (coord c : ℕ) :
    ∀ k ∈ Paths.pairKeys 0 1 coord c 0, k.InRange → tagFamily k.code ≤ 5 := by
  intro k member range
  simp only [Paths.pairKeys, Set.mem_ofPred_eq] at member
  rw [tagFamily_key range]
  omega

theorem conv_keys (coord idx : ℕ) : ∀ k ∈ Paths.convKeys coord idx, k.InRange → tagFamily k.code ≤ 5 := by
  intro k member range
  simp only [Paths.convKeys, Set.mem_ofPred_eq] at member
  rw [tagFamily_key range]
  omega

/-- **A modulus asks the same inputs on two hashes that agree at families 0 to 5.** -/
theorem asked_modGarbleM (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label)
    (chunks : ℕ → ChunkGarbled Entry.table.castWidth) (i : Fin Entry.table.count) {H H' : HashN}
    (agree : AgreeOn (fun τ => tagFamily τ ≤ 5) H H') :
    asked H (modGarbleM Entry.table S coord Δ chunks i) = asked H' (modGarbleM Entry.table S coord Δ chunks i) := by
  have ranges := Paths.bn254_ranges S hS
  cases hk : Entry.table.kind i with
  | chunkZero =>
    simp only [modGarbleM, hk, asked_bind, asked_pure, List.append_nil]
    exact asked_bodyGarbleM H H' _ _ _ _ _ _
  | odd row =>
    have conv := fun W => tagged_congr (Paths.conversionGarbleM_tagged coord i.val row (Entry.table.modulus i) hc
      (lt_of_lt_of_le i.isLt ranges.count) (ranges.rows i row hk) (ranges.modulus i) Δ W) (conv_keys coord i.val)
      agree
    simp only [modGarbleM, hk, asked_bind, asked_pure, asked_materializeM, eval_materializeM, List.nil_append,
      List.append_nil]
    rw [(conv _).1, (conv _).2, asked_bodyGarbleM H H']

/-- **A coordinate's garbler asks the same inputs on two hashes that agree at families 0 to 5.** -/
theorem asked_coordGarbleM (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label)
    {H H' : HashN} (agree : AgreeOn (fun τ => tagFamily τ ≤ 5) H H') :
    asked H (coordGarbleM Entry.table S coord Δ Z) = asked H' (coordGarbleM Entry.table S coord Δ Z) := by
  have ranges := Paths.bn254_ranges S hS
  have chunk : ∀ c : Fin Entry.table.chunkCount,
      asked H (chunkGarbleM Entry.table coord Δ Z c.val) = asked H' (chunkGarbleM Entry.table coord Δ Z c.val) ∧
        (chunkGarbleM Entry.table coord Δ Z c.val).eval H = (chunkGarbleM Entry.table coord Δ Z c.val).eval H' :=
    fun c => tagged_congr (Paths.chunkGarbleM_tagged Entry.table coord Δ Z c.val hc
      (lt_of_lt_of_le c.isLt ranges.chunkCount) (ranges.chunkWidth c.val c.isLt) ranges.castAnswers)
      (chunk_keys coord c.val) agree
  have chunkAsk : ∀ c : Fin Entry.table.chunkCount,
      asked H (chunkGarbleM Entry.table coord Δ Z c.val) = asked H' (chunkGarbleM Entry.table coord Δ Z c.val) :=
    fun c => (chunk c).1
  have chunkEval : ∀ c : Fin Entry.table.chunkCount,
      (chunkGarbleM Entry.table coord Δ Z c.val).eval H = (chunkGarbleM Entry.table coord Δ Z c.val).eval H' :=
    fun c => (chunk c).2
  have modAsk : ∀ (chunks : ℕ → ChunkGarbled Entry.table.castWidth) (i : Fin Entry.table.count),
      asked H (modGarbleM Entry.table S coord Δ chunks i) = asked H' (modGarbleM Entry.table S coord Δ chunks i) :=
    fun chunks i => asked_modGarbleM S coord hS hc Δ chunks i agree
  simp only [coordGarbleM, asked_bind, asked_tableM, asked_pure, List.append_nil, eval_tableM, chunkAsk, chunkEval,
    modAsk]

/-- **A coordinate's in-range conversion reading** (with its chunk joins) is the same on two hashes that agree at
families 0 to 5. -/
theorem readPub_coord (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label)
    {H H' : HashN} (agree : AgreeOn (fun τ => tagFamily τ ≤ 5) H H') :
    Conv.readPub Entry.table ((coordGarbleM Entry.table S coord Δ Z).eval H).pub =
      Conv.readPub Entry.table ((coordGarbleM Entry.table S coord Δ Z).eval H').pub := by
  have ranges := Paths.bn254_ranges S hS
  refine Asks.readPub_congr Entry.table S coord Δ Z H H' ?_ ?_
  · intro c hcc
    exact (tagged_congr (Paths.chunkGarbleM_tagged Entry.table coord Δ Z c hc (lt_of_lt_of_le hcc ranges.chunkCount)
      (ranges.chunkWidth c hcc) ranges.castAnswers) (chunk_keys coord c) agree).2
  · intro i row hk W
    exact (tagged_congr (Paths.conversionGarbleM_tagged coord i.val row (Entry.table.modulus i) hc
      (lt_of_lt_of_le i.isLt ranges.count) (ranges.rows i row hk) (ranges.modulus i) Δ W) (conv_keys coord i.val)
      agree).2

/-- **A coordinate's published conversion material** is the same on two hashes that agree at families 0 to 5. -/
theorem convVector_coord (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label)
    {H H' : HashN} (agree : AgreeOn (fun τ => tagFamily τ ≤ 5) H H') :
    Entry.convVector ((coordGarbleM Entry.table S coord Δ Z).eval H).pub =
      Entry.convVector ((coordGarbleM Entry.table S coord Δ Z).eval H').pub := by
  rw [Flat.convVector_eq_flatOf, Flat.convVector_eq_flatOf, readPub_coord S coord hS hc Δ Z agree]

/-- **A coordinate's in-range chunk joins** are the same on two hashes that agree at families 0 to 5. -/
theorem joins_coord (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label)
    {H H' : HashN} (agree : AgreeOn (fun τ => tagFamily τ ≤ 5) H H') :
    KeyZero.JoinsAgree ((coordGarbleM Entry.table S coord Δ Z).eval H).pub
      ((coordGarbleM Entry.table S coord Δ Z).eval H').pub := by
  intro c hcc n _ _
  have ranges := Paths.bn254_ranges S hS
  have chunk := (tagged_congr (Paths.chunkGarbleM_tagged Entry.table coord Δ Z c hc
    (lt_of_lt_of_le hcc ranges.chunkCount) (ranges.chunkWidth c hcc) ranges.castAnswers) (chunk_keys coord c) agree).2
  obtain ⟨fJ, -⟩ := SliceC.coordGarbleM_fields H Entry.table S coord Δ Z
  obtain ⟨fJ', -⟩ := SliceC.coordGarbleM_fields H' Entry.table S coord Δ Z
  rw [fJ c, fJ' c, SliceC.atNat_of_lt _ _ hcc, SliceC.atNat_of_lt _ _ hcc]
  exact congrArg (fun g : ChunkGarbled Entry.table.castWidth => g.joins n) chunk

/-- **No chunk joins: the actual key** is the same for coins that agree on the label keys, on two hashes that agree
at families 0 to 5 (its absorbed chunk joins are in-range chunk joins, `KeyZero.keyOf_congr`). -/
theorem keyZero_low {c1 c2 : Entry.Coins} (hZero : c1.inputZero = c2.inputZero)
    (hDelta : c1.inputDelta = c2.inputDelta) {H H' : HashN} (low : AgreeOn (fun τ => tagFamily τ ≤ 5) H H') :
    EntryCorrect.keyZero H c1 = EntryCorrect.keyZero H' c2 := by
  refine KeyZero.keyZero_congr hZero ?_ ?_
  · unfold EntryCorrect.gxOf
    rw [hDelta, hZero]
    exact joins_coord _ _ (by decide) (by norm_num) _ _ low
  · unfold EntryCorrect.gyOf
    rw [hDelta, hZero]
    exact joins_coord _ _ (by decide) (by norm_num) _ _ low

theorem keyOf_low {c1 c2 : Entry.Coins} (hZero : c1.inputZero = c2.inputZero)
    (hDelta : c1.inputDelta = c2.inputDelta) {H H' : HashN} (low : AgreeOn (fun τ => tagFamily τ ≤ 5) H H') :
    EntryCorrect.keyOf H c1 = EntryCorrect.keyOf H' c2 := by
  unfold EntryCorrect.keyOf Entry.deltaOf
  rw [keyZero_low hZero hDelta low, hDelta]

/-! ### 4. The coins -/

section Coins

variable {c1 c2 : Entry.Coins}

theorem outputKeysOf_congr (scalar : NonZeroScalar) (h : c1.offsets = c2.offsets) :
    Entry.outputKeysOf scalar c1 = Entry.outputKeysOf scalar c2 := by
  unfold Entry.outputKeysOf
  rw [h]

theorem exceptional_congr (scalar : NonZeroScalar) (h : c1.offsets = c2.offsets) :
    Entry.exceptional scalar c1 = Entry.exceptional scalar c2 := by
  funext o
  unfold Entry.exceptional Entry.outputKeysOf
  rw [h]

theorem zeroOf_congr (h : c1.inputZero = c2.inputZero) : Entry.zeroOf c1 = Entry.zeroOf c2 := by
  unfold Entry.zeroOf
  rw [h]

theorem deltaOf_congr (h : c1.inputDelta = c2.inputDelta) : Entry.deltaOf c1 = Entry.deltaOf c2 := by
  unfold Entry.deltaOf
  rw [h]

theorem inputMacKey_congr (hz : c1.inputZero = c2.inputZero) (hd : c1.inputDelta = c2.inputDelta) :
    c1.inputMacKey = c2.inputMacKey := by
  unfold Kriterion.ArgoMAC.Scheme.Coins.inputMacKey
  rw [hz, hd]

end Coins

/-! ### 5. The published value and the stage-2 view -/

theorem vector_ext_get {β : Type} {n : ℕ} (v w : Vector β n) (h : ∀ i : Fin n, v.get i = w.get i) : v = w := by
  ext i hi
  exact h ⟨i, hi⟩

theorem public_ext (p q : Entry.Public) (h1 : p.curve = q.curve) (h2 : p.rows = q.rows)
    (h3 : p.exception = q.exception) (h4 : p.crtX = q.crtX) (h5 : p.crtY = q.crtY) (h6 : p.recX = q.recX)
    (h7 : p.recY = q.recY) : p = q := by
  cases p
  cases q
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- P45's published cells and hints. -/
theorem realOutOff_fst (ctx : BMR.Context) (u : AffineInput) (c : BMR.Coins Entry.table) :
    (BMR.realOutOff ctx u c).1 = ((BMR.join ctx c, BMR.gamma ctx c, BMR.curveTable c), BMR.hint c) := rfl

section View

variable [FieldCertificate] [GroupCertificate]

omit [FieldCertificate] [GroupCertificate] in
/-- **The published value reads P45 only through its output**, off the hidden positions. -/
theorem pubOf_fd (scalar : NonZeroScalar) (u : AffineInput) (c1 c2 : Entry.Coins) (T T' : TagTable)
    (hOff : c1.offsets = c2.offsets) (hPad : c1.exceptionPad = c2.exceptionPad)
    (hZero : c1.inputZero = c2.inputZero) (hDelta : c1.inputDelta = c2.inputDelta) (ctx : BMR.Context)
    (hctx1 : BmrEntry.bmrContextOf scalar c1 = ctx) (hctx2 : BmrEntry.bmrContextOf scalar c2 = ctx)
    (p45 : (BMR.realOutOff ctx u (BmrEntry.bmrCoinsOf c1 T)).1 = (BMR.realOutOff ctx u (BmrEntry.bmrCoinsOf c2 T')).1)
    (agree : ∀ q, ¬ HidPos u q → T q = T' q) :
    EntryCorrect.pubOf (H8.tagHash T) scalar c1 = EntryCorrect.pubOf (H8.tagHash T') scalar c2 := by
  rw [realOutOff_fst, realOutOff_fst] at p45
  simp only [Prod.mk.injEq] at p45
  obtain ⟨⟨hjoin, hgamma, hcurve⟩, hhint⟩ := p45
  have tables := agreeOn_tagHash u T T' agree
  have low : AgreeOn (fun τ => tagFamily τ ≤ 5) (H8.tagHash T) (H8.tagHash T') :=
    tables.mono fun τ h => not_hid_of_low h
  refine public_ext _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [BmrEntry.curve_eq, BmrEntry.curve_eq]
    exact hcurve
  · refine vector_ext_get _ _ fun d => ?_
    have r1 := BmrEntry.rows_eq scalar c1 T d
    have r2 := BmrEntry.rows_eq scalar c2 T' d
    rw [r1, r2, hctx1, hctx2, hgamma]
  · rw [EntryCorrect.pubOf_exception, EntryCorrect.pubOf_exception]
    refine congrArg Vector.ofFn ?_
    unfold EntryCorrect.entriesOf
    rw [← eval_digestGarbleM, ← eval_digestGarbleM, keyZero_low hZero hDelta low, deltaOf_congr hDelta,
      outputKeysOf_congr scalar hOff, hPad]
    exact (tagged_congr (digest_tagged scalar c2 _) (digest_keys u) tables).2
  · rw [EntryCorrect.pubOf_crtX, EntryCorrect.pubOf_crtX, EntryCorrect.gxOf, EntryCorrect.gxOf, hDelta, hZero]
    exact convVector_coord _ _ (by decide) (by norm_num) _ _ low
  · rw [EntryCorrect.pubOf_crtY, EntryCorrect.pubOf_crtY, EntryCorrect.gyOf, EntryCorrect.gyOf, hDelta, hZero]
    exact convVector_coord _ _ (by decide) (by norm_num) _ _ low
  · refine vector_ext_get _ _ fun e => Fin.ext ?_
    have flat : BMR.xFlat (BMR.xEncEquiv.symm e) = e := BMR.xEncEquiv.apply_symm_apply e
    rw [← flat, BmrEntry.recX_eq, BmrEntry.recX_eq, hctx1, hctx2, hjoin, hhint]
  · refine vector_ext_get _ _ fun e => Fin.ext ?_
    have flat : BMR.yFlat (BMR.yEncEquiv.symm e) = e := BMR.yEncEquiv.apply_symm_apply e
    rw [← flat, BmrEntry.recY_eq, BmrEntry.recY_eq, hctx1, hctx2, hjoin, hhint]

/-- **The stage-2 view off the curve reads P45 only through its output**, off the hidden positions. -/
theorem view_fd_core (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (off : validate u = false)
    (c1 c2 : Entry.Coins) (T T' : TagTable)
    (hOff : c1.offsets = c2.offsets) (hPad : c1.exceptionPad = c2.exceptionPad)
    (hZero : c1.inputZero = c2.inputZero) (hDelta : c1.inputDelta = c2.inputDelta) (ctx : BMR.Context)
    (hctx1 : BmrEntry.bmrContextOf scalar c1 = ctx) (hctx2 : BmrEntry.bmrContextOf scalar c2 = ctx)
    (p45 : (BMR.realOutOff ctx u (BmrEntry.bmrCoinsOf c1 T)).1 = (BMR.realOutOff ctx u (BmrEntry.bmrCoinsOf c2 T')).1)
    (agree : ∀ q, ¬ HidPos u q → T q = T' q) :
    stageTwoView Instance.crtEntry Entry.table parameter scalar u (c1, T) =
      stageTwoView Instance.crtEntry Entry.table parameter scalar u (c2, T') := by
  have hpub := pubOf_fd scalar u c1 c2 T T' hOff hPad hZero hDelta ctx hctx1 hctx2 p45 agree
  have hmac : EntryCorrect.keyOf (H8.tagHash T) c1 = EntryCorrect.keyOf (H8.tagHash T') c2 :=
    keyOf_low hZero hDelta ((agreeOn_tagHash u T T' agree).mono fun τ h => not_hid_of_low h)
  have hexc := exceptional_congr scalar hOff
  have hg : (Instance.crtEntry.scheme inferInstance inferInstance).garble parameter scalar
        (c1, tapeOracle Instance.crtEntry (c1, T)) =
      (Instance.crtEntry.scheme inferInstance inferInstance).garble parameter scalar
        (c2, tapeOracle Instance.crtEntry (c2, T')) := by
    unfold tapeOracle
    dsimp only [Instance.crtEntry]
    rw [scheme_garble, scheme_garble, EntryCorrect.garbleCM_eval, EntryCorrect.garbleCM_eval,
      BmrReal.pubOf_table, BmrReal.pubOf_table, BmrReal.keyOf_table scalar, BmrReal.keyOf_table scalar, hpub, hmac]
  unfold stageTwoView
  dsimp only
  rw [hg, designedEntries_eq, designedEntries_eq]
  have tables := agreeOn_scheme u T T' agree
  have low : AgreeOn (fun τ => tagFamily τ ≤ 5) (schemeHash (tableOracle (FI := Empty) (EI := Empty) T))
      (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) :=
    tables.mono fun τ h => not_hid_of_low h
  have hl : List.map (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) T).2.2
        (n : BaseField)⟩ : Entry Empty Empty))
        (List.filter (fun n => designTag Entry.table (Entry.exceptional scalar c1) u (n / 2 ^ 128))
          (gAsked scalar (c1, T))) =
      List.map (fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) T').2.2
        (n : BaseField)⟩ : Entry Empty Empty))
        (List.filter (fun n => designTag Entry.table (Entry.exceptional scalar c2) u (n / 2 ^ 128))
          (gAsked scalar (c2, T'))) := by
    have hzero : zeroOn c1 T = zeroOn c2 T' := by
      rw [zeroOn_eq, zeroOn_eq]
      exact keyZero_low hZero hDelta low
    rw [hexc, gAsked_eq, gAsked_eq, hzero, hDelta, hZero, deltaOf_congr hDelta,
      outputKeysOf_congr scalar hOff, hPad,
      asked_coordGarbleM _ _ (by decide) (by norm_num) _ _ low,
      asked_coordGarbleM _ _ (by decide) (by norm_num) _ _ low,
      (tagged_congr (digest_tagged scalar c2 _) (digest_keys u) tables).1]
    have maskGone : ∀ H K, (asked H (maskAnswersM K digitCount)).filter
        (fun n => designTag Entry.table (Entry.exceptional scalar c2) u (n / 2 ^ 128)) = [] := by
      intro H K
      refine List.filter_eq_nil_iff.mpr fun n inside => ?_
      rw [designTag_of_family _ _ _ (Or.inl (mask_fam H K n inside)), off]
      simp
    have keyGone : ∀ H t, (asked H (keyM t)).filter
        (fun n => designTag Entry.table (Entry.exceptional scalar c2) u (n / 2 ^ 128)) = [] := by
      intro H t
      refine List.filter_eq_nil_iff.mpr fun n inside => ?_
      rw [asked_keyM] at inside
      rw [List.mem_singleton.mp inside, designTag_of_family _ _ _ (Or.inr (keyInput_fam _)), off]
      simp
    rw [List.filter_append, List.filter_append, List.filter_append, List.filter_append,
      List.filter_append, List.filter_append, List.filter_append, List.filter_append, maskGone, maskGone,
      keyGone, keyGone, List.nil_append, List.nil_append]
    refine List.map_congr_left fun n inside => ?_
    simp only [List.mem_append, List.mem_filter] at inside
    -- a designed input is never at a hidden position
    have answer : ∀ {S : Set Paths.TagKey} {α : Type} {program : CM α}, Paths.Tagged S program →
        (∀ k ∈ S, k.InRange → designTag Entry.table (Entry.exceptional scalar c2) u k.code = true →
          ¬ Hid u k.code) →
        n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) T')) program →
        designTag Entry.table (Entry.exceptional scalar c2) u (n / 2 ^ 128) = true →
        (tableOracle (FI := Empty) (EI := Empty) T).2.2 (n : BaseField) =
          (tableOracle (FI := Empty) (EI := Empty) T').2.2 (n : BaseField) := by
      intro S α program tagged keys member designed
      obtain ⟨k, kmem, range, label, rfl⟩ := asked_of_tagged tagged _ n member
      rw [hashInput_div] at designed
      show schemeHash (tableOracle (FI := Empty) (EI := Empty) T) (hashInput label k.code) =
        schemeHash (tableOracle (FI := Empty) (EI := Empty) T') (hashInput label k.code)
      exact tables label k.code (Paths.TagKey.code_lt range) (keys k kmem range designed)
    have coordKeys : ∀ κ : ℕ, ∀ k ∈ Paths.coordKeys κ, k.InRange →
        designTag Entry.table (Entry.exceptional scalar c2) u k.code = true → ¬ Hid u k.code := by
      intro κ k member range designed
      simp only [Paths.coordKeys, Set.mem_ofPred_eq] at member
      have fam : tagFamily k.code ≤ 6 := by rw [tagFamily_key range]; exact member.1
      rw [designTag_conv _ _ _ fam] at designed
      rintro (⟨_, hot⟩ | seven)
      · rw [hot] at designed
        exact absurd designed (by decide)
      · omega
    have same : (tableOracle (FI := Empty) (EI := Empty) T).2.2 (n : BaseField) =
        (tableOracle (FI := Empty) (EI := Empty) T').2.2 (n : BaseField) := by
      rcases inside with ⟨a, d⟩ | ⟨a, d⟩ | ⟨a, d⟩
      · exact answer (coordX_tagged c2) (coordKeys 0) a d
      · exact answer (coordY_tagged c2) (coordKeys 1) a d
      · exact answer (digest_tagged scalar c2 _) (fun k member range _ => digest_keys u k member range) a d
    rw [same]
  dsimp only
  rw [hl]

/-- **`ViewFD` for the stage-2 view off the curve.** -/
theorem stageTwoView_fd (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (off : validate u = false) :
    ViewFD scalar u fun coins T => stageTwoView Instance.crtEntry Entry.table parameter scalar u (coins, T) := by
  intro r l l' T T' p45 agree
  exact view_fd_core parameter scalar u off _ _ T T' rfl rfl rfl rfl (ctxOf scalar r) (ctxOf_eq scalar r l)
    (ctxOf_eq scalar r l') p45 fun q hq => congrFun agree ⟨q, hq⟩

end View

end

end Kriterion.CRT.Privacy.CaseKeyOff

namespace Kriterion.CRT.Privacy.StageTwo

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

/-- **H7's case `keyOff`**: off the curve and off `curveNearEdge`, the garbler's key input has conditional mass at
most `keyError = 2/2^128 + 1/(p − 1)` given the stage-2 view. -/
theorem keyOff_case : GuessCase keyOff notNearEdge BmrOff.keyError := by
  intro field group parameter scalar u view N hc
  obtain ⟨fam, off⟩ := hc
  have notOn : ¬ OnCurve u := fun on => by
    rw [(validate_eq_true_iff u).mpr on] at off
    exact absurd off (by decide)
  have sub : {tape : TableTape Instance.crtEntry |
        stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧ N ∈ gAsked scalar tape ∧
          notNearEdge scalar u N tape} ⊆
      {tape : TableTape Instance.crtEntry |
        (fun coins T => stageTwoView Instance.crtEntry Entry.table parameter scalar u (coins, T)) tape.1 tape.2 =
            view ∧ tape.1.bridgeKey.val % 2 ^ 128 = N % 2 ^ 128 ∧ ¬ curveNearEdge tape} := by
    rintro ⟨coins, T⟩ ⟨hv, inside, far⟩
    refine ⟨hv, ?_, far⟩
    rw [CaseKeyOff.key_of_fam10 scalar coins T N inside fam, CaseKeyOff.maskKeyInput_mod]
  refine le_trans (MeasureTheory.measure_mono sub) ?_
  exact KeyOffEntry.keyLabel_entry scalar u notOn _ (CaseKeyOff.stageTwoView_fd parameter scalar u off) view
    (N % 2 ^ 128)

/-- The key case's error is within the hidden charge: `2/2^128 + 1/(p − 1) ≤ 4/2^104 + 1/(p − 1)`. -/
theorem keyOff_error_le : BmrOff.keyError ≤ ENNReal.ofReal crtHiddenCharge := by
  unfold BmrOff.keyError
  refine ENNReal.ofReal_le_ofReal ?_
  rw [crtHiddenCharge_eq]
  have two : (2 : ℝ) / 2 ^ 128 ≤ 4 / 2 ^ labelBits := by norm_num [labelBits]
  linarith

end Kriterion.CRT.Privacy.StageTwo
