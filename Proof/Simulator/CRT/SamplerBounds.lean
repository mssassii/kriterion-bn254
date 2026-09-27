/-
**The sampler cutoff of the CRT machine**: the four per-sampler bounds of `Cutoff.samplerCutoff_of` at `crtEntry` and the bounded samplers `CrtBounded.samplers`, and the closed
`samplerCutoff_crt : LawShape.SamplerCutoff crtEntry CrtBounded.samplers`.

| sampler | bound | where |
|---|---|---|
| source | `2^-130` | `source_close` here: 276 field cells and 54,570 record digits by bounded rejection |
| rows | `2^-129` | `Cutoff.boundedRows_close`, `Cutoff.rowsMass_le` (`CrtBounded.rows` is `Cutoff.boundedRows`) |
| preimage | `2^-399` each, `273 · 2^-399 ≤ 2^-130` | xinshu's `preimage_close`, `preimageAbort_le`; `Cutoff.preimagesMass_le` |
| fourth | `0` | the machine's fourth block is the view's own uniform block |

The source bound (`source_close`): the machine's stage-1 draws (`CrtDraws.drawLaw`) differ from the exact draws
(`idealDrawLaw`: uniform field cells and uniform digits) by at most the extra abort mass of the cut-off samplers
(`draws_close`); the exact draws are the uniform law on `Exact` (`idealDrawLaw_eq`), and `sourceOf` read on exact
draws is a bijection `Exact ≃ Entry.Source` (`readEquiv`: re-indexings, and the mixed radix of each record).
-/

import Proof.Simulator.CRT.Bounded
import Proof.Simulator.CRT.Cutoff
import Proof.Simulator.CRT.SourceCells

namespace Kriterion.CRT.SimMachine.SamplerBounds

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.Phase3.Glue (optionProduct)
open Kriterion.CRT.SimMachine.CrtStage1 (fieldCount modulusAt digitWidth moduliCount recordCount pinOf pinCoord
  pinWidthAt)
open Kriterion.CRT.SimMachine.CrtDraws (Draw drawLaw optBind digitLaw fieldsLaw bytesLaw joinsLaw pinsLaw digitsLaw
  zerosLaw deltasLaw)
open scoped ENNReal

noncomputable section

/-! ### The moduli -/

theorem moduli_pos_fin : ∀ i : Fin 85, 0 < modulusAt i := by decide +kernel

theorem moduli_size : bn254Moduli.size = 85 := by decide

theorem modulusAt_pos (i : Nat) : 0 < modulusAt i := by
  by_cases inside : i < 85
  · exact moduli_pos_fin ⟨i, inside⟩
  · have outside : ¬ i < bn254Moduli.size := by rw [moduli_size]; exact inside
    unfold modulusAt Array.getD
    rw [dif_neg outside]
    decide

instance modulusAtNeZero (i : Nat) : NeZero (modulusAt i) := ⟨(modulusAt_pos i).ne'⟩

/-- Every modulus fits its digit width, and more than half the draws at that width are accepted. -/
theorem digitFacts_fin : ∀ i : Fin 85,
    modulusAt i ≤ 2 ^ digitWidth (modulusAt i) ∧ 2 ^ digitWidth (modulusAt i) ≤ 2 * modulusAt i := by
  decide +kernel

theorem digitFacts (n : Nat) :
    modulusAt (n % moduliCount) ≤ 2 ^ digitWidth (modulusAt (n % moduliCount)) ∧
      2 ^ digitWidth (modulusAt (n % moduliCount)) ≤ 2 * modulusAt (n % moduliCount) :=
  digitFacts_fin ⟨n % moduliCount, Nat.mod_lt _ (by decide)⟩

section Laws

-- The release-r1 lemmas used here carry the certificates as section instances.
variable [FieldCertificate] [GroupCertificate]

/-! ### Independent uniform draws of different types -/

/-- **Independent uniform draws of varying types are uniform on the dependent product**, read through `g`. -/
theorem optionProduct_uniform_dep {γ : Type} :
    ∀ (count : Nat) (β : Fin count → Type) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] (g : ∀ i, β i → γ),
      optionProduct count (fun i => (PMF.uniformOfFintype (β i)).map fun b => some (g i b)) =
        (PMF.uniformOfFintype ((i : Fin count) → β i)).map fun f => some fun i => g i (f i)
  | 0, β, _, _, g => by
      simp only [optionProduct]
      have single : PMF.uniformOfFintype ((i : Fin 0) → β i) = PMF.pure (fun i => i.elim0) := by
        apply PMF.ext
        intro f
        have : f = fun i => i.elim0 := funext fun i => i.elim0
        subst this
        simp [PMF.uniformOfFintype_apply]
      rw [single, PMF.pure_map]
      congr 2
      funext i
      exact i.elim0
  | count + 1, β, _, _, g => by
      have rest := optionProduct_uniform_dep count (fun i => β i.succ) (fun i => g i.succ)
      have left : optionProduct (count + 1) (fun i => (PMF.uniformOfFintype (β i)).map fun b => some (g i b)) =
          (PMF.uniformOfFintype (β 0)).bind fun b =>
            (PMF.uniformOfFintype ((i : Fin count) → β i.succ)).map fun f =>
              some (Fin.cons (α := fun _ => γ) (g 0 b) fun i => g i.succ (f i)) := by
        simp only [optionProduct]
        rw [PMF.bind_map]
        congr 1
        funext b
        simp only [Function.comp_apply]
        rw [rest, PMF.map_comp]
        rfl
      rw [left, ← uniform_equiv (Fin.consEquiv β), ← uniform_product, PMF.map_comp, PMF.map_bind]
      congr 1
      funext b
      rw [PMF.map_comp]
      congr 1
      funext f
      simp only [Function.comp_apply, Option.some.injEq]
      funext i
      cases i using Fin.cases with
      | zero => simp [Fin.consEquiv]
      | succ i => simp [Fin.consEquiv]

/-! ### Bounded rejection keeps only accepted draws -/

/-- A map that fixes `none` and every accepted draw leaves the rejection law unchanged. -/
theorem rejectLaw_map_fix (width : Nat) (accept : Nat → Bool) (f : Option Nat → Option Nat)
    (fnone : f none = none) (fsome : ∀ value, accept value = true → f (some value) = some value) :
    ∀ count, (rejectLaw width accept count).map f = rejectLaw width accept count
  | 0 => by simp [rejectLaw, PMF.pure_map, fnone]
  | count + 1 => by
      rw [rejectLaw, PMF.map_bind]
      congr 1
      funext value
      split
      · rename_i accepted
        rw [PMF.pure_map, fsome _ accepted]
      · exact rejectLaw_map_fix width accept f fnone fsome count

/-! ### The digit sampler -/

/-- The exact law of a digit below `m`. -/
def idealDigit (m : Nat) [NeZero m] : PMF (Option Nat) := (PMF.uniformOfFintype (Fin m)).map fun v => some v.val

/-- **A digit sampler is abort-close to the uniform digit.** -/
theorem digitLaw_close (m : Nat) [NeZero m] (fits : m ≤ 2 ^ digitWidth m) :
    AbortClose (rejectLaw (digitWidth m) (fun value => decide (value < m)) attempts none) (digitLaw m)
      (idealDigit m) := by
  have close := rejectLaw_close (β := Fin m) (digitWidth m) (fun value => decide (value < m)) attempts
    (fun value => if inside : value < m then some ⟨value, inside⟩ else none) Fin.val
    (fun b => ⟨by simp [b.isLt], lt_of_lt_of_le b.isLt fits, by simp [b.isLt]⟩)
    (fun value b accepted _ hit => by
      simp only [decide_eq_true_eq] at accepted
      simp only [accepted, dif_pos, Option.some.injEq] at hit
      rw [← hit])
    (fun value accepted _ => by
      simp only [decide_eq_true_eq] at accepted
      simp [accepted])
  have mapped := close.map_opt (Option.map Fin.val) rfl
  rw [PMF.map_comp, PMF.map_comp] at mapped
  have fix := rejectLaw_map_fix (digitWidth m) (fun value => decide (value < m))
    (Option.map Fin.val ∘ fun drawn => drawn.bind fun value =>
      if inside : value < m then some (⟨value, inside⟩ : Fin m) else none) rfl
    (fun value accepted => by
      simp only [decide_eq_true_eq] at accepted
      simp [accepted]) attempts
  rw [fix] at mapped
  exact mapped

/-- **A digit sampler aborts with probability below `2^-256`.** -/
theorem digitAbort_le (m : Nat) (fits : m ≤ 2 ^ digitWidth m) (half : 2 ^ digitWidth m ≤ 2 * m) :
    rejectLaw (digitWidth m) (fun value => decide (value < m)) attempts none ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have accepted : m ≤ (acceptedSet (digitWidth m) fun value => decide (value < m)).card := by
    have le := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin m)))
      (t := acceptedSet (digitWidth m) fun value => decide (value < m))
      (fun b => (⟨b.val, lt_of_lt_of_le b.isLt fits⟩ : Fin (2 ^ digitWidth m)))
      (fun b _ => by simp [acceptedSet, b.isLt])
      (fun first _ second _ same => Fin.ext (by simpa using congrArg Fin.val same))
    simpa using le
  have split := acceptedSet_add_rejectedCount (digitWidth m) fun value => decide (value < m)
  have fewer : rejectedCount (digitWidth m) (fun value => decide (value < m)) ≤ 2 ^ digitWidth m - m := by
    omega
  refine (rejectLaw_none_le _ _ attempts _ fewer).trans ?_
  rw [show attempts = 256 from rfl]
  refine ratio_pow_le (2 ^ digitWidth m - m) (digitWidth m) 256 256 ?_
  rw [← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by omega) 256

/-! ### The exact draws and their law -/

/-- A lane word of pin `pinOf n`. -/
abbrev PinWord (n : Fin (2 * (Entry.pinCount * 128))) : Type := Fin (2 ^ pinWidthAt (pinOf n.val))

/-- A digit below its modulus. -/
abbrev DigitVal (n : Fin (recordCount * moduliCount)) : Type := Fin (modulusAt (n.val % moduliCount))

instance pinWordNonempty (n : Fin (2 * (Entry.pinCount * 128))) : Nonempty (PinWord n) :=
  ⟨⟨0, Nat.two_pow_pos _⟩⟩

instance digitValNonempty (n : Fin (recordCount * moduliCount)) : Nonempty (DigitVal n) :=
  ⟨⟨0, modulusAt_pos _⟩⟩

/-- The pin lanes of exact draws. -/
abbrev Pins : Type := (n : Fin (2 * (Entry.pinCount * 128))) → PinWord n

/-- The record digits of exact draws. -/
abbrev Digits : Type := (n : Fin (recordCount * moduliCount)) → DigitVal n

instance pinsFintype : Fintype Pins := inferInstance
instance digitsFintype : Fintype Digits := inferInstance
instance pinsNonempty : Nonempty Pins := inferInstance
instance digitsNonempty : Nonempty Digits := inferInstance

/-- **The exact draws**: field cells, bytes, joins, pin lanes, record digits, zero labels, offsets. -/
abbrev Exact : Type := (Fin fieldCount → BaseField) × (Fin exceptionByteCount → Fin (2 ^ 8)) ×
  (Fin (2 * Entry.joinCount) → Fin (2 ^ 128)) × Pins × Digits × (Fin labelCount → Fin (2 ^ 128)) ×
  (Fin 2 → Fin (2 ^ 128))

/-- Exact draws as the machine's draws. -/
def embed (D : Exact) : Draw :=
  ⟨D.1, fun n => (D.2.1 n).val, fun n => (D.2.2.1 n).val, fun n => (D.2.2.2.1 n).val,
    fun n => (D.2.2.2.2.1 n).val, fun n => (D.2.2.2.2.2.1 n).val, fun n => (D.2.2.2.2.2.2 n).val⟩

/-- Exact field cells. -/
def idealFields : PMF (Option (Fin fieldCount → BaseField)) :=
  optionProduct fieldCount fun _ => (PMF.uniformOfFintype BaseField).map some

/-- Exact digits. -/
def idealDigits : PMF (Option (Fin (recordCount * moduliCount) → Nat)) :=
  optionProduct (recordCount * moduliCount) fun n => idealDigit (modulusAt (n.val % moduliCount))

/-- **The exact draws' law**: the machine's draws with exact field cells and exact digits. -/
def idealDrawLaw : PMF (Option Draw) :=
  optBind idealFields fun f => optBind bytesLaw fun b => optBind joinsLaw fun j => optBind pinsLaw fun p =>
    optBind idealDigits fun d => optBind zerosLaw fun z => optBind deltasLaw fun dl =>
      PMF.pure (some ⟨f, b, j, p, d, z, dl⟩)

/-- Abort-or-value binds are abort-close when their parts are. -/
theorem optBind_close {α β : Type} {ε ε' : ℝ≥0∞} {law law' : PMF (Option α)} {next next' : α → PMF (Option β)}
    (close : AbortClose ε law law') (step : ∀ a, AbortClose ε' (next a) (next' a)) :
    AbortClose (ε + ε') (optBind law next) (optBind law' next') := by
  unfold optBind
  exact AbortClose.bind_opt close _ _ rfl rfl step

/-- The extra abort mass of the stage-1 draws: the field cells' and the digits'. -/
def drawsMass : ℝ≥0∞ :=
  (fieldCount : ℝ≥0∞) * rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none +
    (0 + (0 + (0 + (((recordCount * moduliCount : Nat) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ + (0 + (0 + 0))))))

/-- **The machine's draws are abort-close to the exact draws.** -/
theorem draws_close : AbortClose drawsMass drawLaw idealDrawLaw := by
  have fields := AbortClose.optionProduct fieldCount (fun _ => fieldCellLaw)
    (fun _ => (PMF.uniformOfFintype BaseField).map some) (fun _ => fieldCell_close)
  have digits := AbortClose.optionProduct (recordCount * moduliCount)
    (fun n => digitLaw (modulusAt (n.val % moduliCount))) (fun n => idealDigit (modulusAt (n.val % moduliCount)))
    (fun n => (digitLaw_close _ (digitFacts n.val).1).mono
      (digitAbort_le _ (digitFacts n.val).1 (digitFacts n.val).2))
  unfold drawLaw idealDrawLaw drawsMass
  exact optBind_close fields fun f => optBind_close (AbortClose.refl _) fun b =>
    optBind_close (AbortClose.refl _) fun j => optBind_close (AbortClose.refl _) fun p =>
      optBind_close digits fun d => optBind_close (AbortClose.refl _) fun z =>
        optBind_close (AbortClose.refl _) fun dl => AbortClose.refl _

/-- **The draws' extra abort mass is below `2^-130`.** -/
theorem drawsMass_le : drawsMass ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
  have cells : (fieldCount : ℝ≥0∞) * rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none ≤
      ((2 : ℝ≥0∞) ^ 131)⁻¹ :=
    (mul_le_mul' le_rfl fieldAbort_le).trans
      (mul_inv_pow_le _ 500 131 (count_le _ 9 131 500 (by decide) (by decide)))
  have digits : ((recordCount * moduliCount : Nat) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 131)⁻¹ :=
    mul_inv_pow_le _ 256 131 (count_le _ 16 131 256 (by decide) (by decide))
  unfold drawsMass
  simp only [add_zero, zero_add]
  rw [← inv_pow_add_self 130 131 rfl]
  exact add_le_add cells digits

/-! ### The exact draws are uniform -/

theorem optBind_map_some {α β γ : Type} (law : PMF α) (g : α → γ) (next : γ → PMF (Option β)) :
    optBind (law.map fun a => some (g a)) next = law.bind fun a => next (g a) := by
  unfold optBind
  rw [PMF.bind_map]
  rfl

theorem optBind_map_some_id {α β : Type} (law : PMF α) (next : α → PMF (Option β)) :
    optBind (law.map fun a => some a) next = law.bind next := by
  unfold optBind
  rw [PMF.bind_map]
  rfl

theorem idealFields_eq :
    idealFields = (PMF.uniformOfFintype (Fin fieldCount → BaseField)).map fun f => some f :=
  optionProduct_uniform fieldCount

theorem pinsLaw_eq : pinsLaw = (PMF.uniformOfFintype Pins).map fun P => some fun n => (P n).val := by
  have each : ∀ n : Fin (2 * (Entry.pinCount * 128)), (wordLaw (pinWidthAt (pinOf n.val))).map some =
      (PMF.uniformOfFintype (PinWord n)).map fun v => some v.val := fun n => by
    unfold wordLaw
    rw [PMF.map_comp]
    rfl
  unfold pinsLaw
  simp only [each]
  exact optionProduct_uniform_dep _ PinWord (fun _ v => v.val)

theorem idealDigits_eq : idealDigits = (PMF.uniformOfFintype Digits).map fun D => some fun n => (D n).val :=
  optionProduct_uniform_dep _ DigitVal (fun _ v => v.val)

/-- **The exact draws' law is the uniform law on `Exact`.** -/
theorem idealDrawLaw_eq : idealDrawLaw = (PMF.uniformOfFintype Exact).map fun D => some (embed D) := by
  unfold idealDrawLaw
  rw [idealFields_eq, show bytesLaw = _ from wordProduct_eq exceptionByteCount 8,
    show joinsLaw = _ from wordProduct_eq (2 * Entry.joinCount) 128, pinsLaw_eq, idealDigits_eq,
    show zerosLaw = _ from wordProduct_eq labelCount 128, show deltasLaw = _ from wordProduct_eq 2 128]
  simp only [optBind_map_some, optBind_map_some_id]
  rw [← uniform_product (A := Fin fieldCount → BaseField), ← uniform_product (A := Fin exceptionByteCount → Fin (2 ^ 8)),
    ← uniform_product (A := Fin (2 * Entry.joinCount) → Fin (2 ^ 128)), ← uniform_product (A := Pins),
    ← uniform_product (A := Digits), ← uniform_product (A := Fin labelCount → Fin (2 ^ 128))]
  simp only [PMF.map_bind, PMF.map_comp]
  rfl

/-! ### Reading exact draws as a source is a bijection -/

/-- **The source of exact draws.** -/
def readSource (D : Exact) : Entry.Source := CrtSource.sourceOf (embed D)

theorem flat_div_mod {J κ i : Nat} (hi : i < J) : (κ * J + i) / J = κ ∧ (κ * J + i) % J = i := by
  have hJ : 0 < J := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem toFin_ofNat_val {w : Nat} (v : Fin (2 ^ w)) : (BitVec.ofNat w v.val).toFin = v :=
  Fin.ext (by simp [Nat.mod_eq_of_lt v.isLt])

theorem fieldCount_eq : fieldCount = 276 := rfl

/-- The field cells of a source: the curve constants, then the row constants. -/
def exFields (s : Entry.Source) (n : Fin fieldCount) : BaseField :=
  if n.val = 0 then s.curve.1 else if n.val = 1 then s.curve.2.1 else if n.val = 2 then s.curve.2.2
  else rowField (s.rows ⟨(n.val - 3) / 3, by
    have small : n.val < 276 := n.isLt
    show (n.val - 3) / 3 < 91
    omega⟩) ((n.val - 3) % 3)

/-- The exception bytes of a source. -/
def exBytes (s : Entry.Source) (n : Fin exceptionByteCount) : Fin (2 ^ 8) :=
  ((s.exception ⟨n.val / 12, by
    have := n.isLt
    unfold exceptionByteCount at this
    show n.val / 12 < 91
    omega⟩)[n.val % 12]'(Nat.mod_lt _ (by decide))).toFin

theorem joinCoord_lt (n : Fin (2 * Entry.joinCount)) : n.val / Entry.joinCount < 2 :=
  Nat.div_lt_of_lt_mul (lt_of_lt_of_eq n.isLt (Nat.mul_comm 2 Entry.joinCount))

theorem joinIndex_lt (n : Fin (2 * Entry.joinCount)) : n.val % Entry.joinCount < Entry.joinCount :=
  Nat.mod_lt _ (by have := n.isLt; omega)

/-- The joins of a source. -/
def exJoins (s : Entry.Source) (n : Fin (2 * Entry.joinCount)) : Fin (2 ^ 128) :=
  (s.joins ⟨n.val / Entry.joinCount, joinCoord_lt n⟩ ⟨n.val % Entry.joinCount, joinIndex_lt n⟩).toFin

theorem pinCoord_lt (n : Fin (2 * (Entry.pinCount * 128))) : pinCoord n.val < 2 := by
  show n.val / (Entry.pinCount * 128) < 2
  exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq n.isLt (Nat.mul_comm 2 (Entry.pinCount * 128)))

theorem pinOf_lt (n : Fin (2 * (Entry.pinCount * 128))) : pinOf n.val < Entry.pinCount := by
  show n.val / 128 % Entry.pinCount < Entry.pinCount
  have small : n.val < 2 * (Entry.pinCount * 128) := n.isLt
  exact Nat.mod_lt _ (by omega)

instance twoPowNeZero (w : Nat) : NeZero (2 ^ w) := ⟨pow_ne_zero _ two_ne_zero⟩

/-- The pin lanes of a source. -/
def exPins (s : Entry.Source) : Pins := fun n =>
  ⟨(s.pins ⟨pinCoord n.val, pinCoord_lt n⟩ ⟨pinOf n.val, pinOf_lt n⟩
      ⟨n.val % 128, Nat.mod_lt _ (by decide)⟩).val, by
    rw [CrtConv.pinWidthAt_eq _ (pinOf_lt n)]
    exact ZMod.val_lt _⟩

/-- Record `r` of a source (`x` then `y`), as a natural. -/
def recAt (s : Entry.Source) (r : Nat) : Nat :=
  if hx : r < Entry.xCount then (s.recX ⟨r, hx⟩).val
  else if hy : r - Entry.xCount < Entry.yCount then (s.recY ⟨r - Entry.xCount, hy⟩).val else 0

/-- The record digits of a source: the mixed-radix digits of each record. -/
def exDigits (s : Entry.Source) : Digits := fun n =>
  ⟨recAt s (n.val / moduliCount) / CrtConv.radixAt (n.val % moduliCount) % modulusAt (n.val % moduliCount),
    Nat.mod_lt _ (modulusAt_pos _)⟩

/-- The zero labels of a source. -/
def exZeros (s : Entry.Source) (n : Fin labelCount) : Fin (2 ^ 128) :=
  (s.zeros ⟨n.val / 254, by have := n.isLt; unfold labelCount at this; omega⟩
    ⟨n.val % 254, Nat.mod_lt _ (by decide)⟩).toFin

/-- The offsets of a source. -/
def exDeltas (s : Entry.Source) (n : Fin 2) : Fin (2 ^ 128) := (s.deltas n).toFin

/-- **The exact draws of a source.** -/
def exOf (s : Entry.Source) : Exact := (exFields s, exBytes s, exJoins s, exPins s, exDigits s, exZeros s, exDeltas s)

/-! #### The mixed radix -/

/-- A record below `M` is the mixed-radix value of its digits. -/
theorem mixed_sum (x : Fin Entry.table.product) :
    ∑ i ∈ Finset.range moduliCount, x.val / CrtConv.radixAt i % modulusAt i * CrtConv.radixAt i = x.val := by
  have back := congrArg Fin.val (Entry.table.mixedRadixEquiv.apply_symm_apply x)
  rw [CrtTable.mixedRadixEquiv_val] at back
  unfold CrtTable.mixedRadix at back
  simp only [CrtTable.mixedRadixEquiv_symm_val, SourceCells.radix_eq, SourceCells.modulus_eq] at back
  rw [← Fin.sum_univ_eq_sum_range (fun i => x.val / CrtConv.radixAt i % modulusAt i * CrtConv.radixAt i)
    moduliCount]
  exact back

/-- The digits of record `r` of a draw, as a residue vector. -/
def resOf (digits : Nat → Nat) (small : ∀ n, digits n < modulusAt (n % moduliCount)) (r : Nat) :
    Entry.table.Residues := fun i => ⟨digits (r * moduliCount + i.val), by
  rw [SourceCells.modulus_eq]
  have := small (r * moduliCount + i.val)
  rwa [(flat_div_mod (J := moduliCount) (κ := r) (lt_of_lt_of_eq i.isLt TableFacts.count)).2] at this⟩

/-- Sums over the moduli, by `Fin` or by range. -/
theorem sum_count (f : Nat → Nat) : ∑ i : Fin Entry.table.count, f i.val = ∑ i ∈ Finset.range moduliCount, f i :=
  Fin.sum_univ_eq_sum_range f _

/-- A record of a draw is the mixed-radix value of its digits. -/
theorem recordNat_eq (D : Exact) (r : Nat) (small : ∀ n, total 0 (fun n => (D.2.2.2.2.1 n).val) n <
      modulusAt (n % moduliCount)) :
    CrtSource.recordNat (embed D) r = Entry.table.mixedRadix (resOf _ small r) := by
  unfold CrtSource.recordNat CrtTable.mixedRadix resOf
  simp only [SourceCells.radix_eq]
  exact (sum_count fun i => total 0 (fun n => (D.2.2.2.2.1 n).val) (r * moduliCount + i) *
    CrtConv.radixAt i).symm

theorem digits_small (D : Exact) (n : Nat) :
    total 0 (fun n => (D.2.2.2.2.1 n).val) n < modulusAt (n % moduliCount) := by
  unfold total
  split
  · exact (D.2.2.2.2.1 _).isLt
  · exact modulusAt_pos _

/-! #### Reading back a source -/

theorem exFields_at (s : Entry.Source) (g : Fin digitCount) (k n : Nat) (hk : k < 3) (hn : n = 3 + 3 * g.val + k) :
    total 0 (exFields s) n = rowField (s.rows g) k := by
  have gs : g.val < 91 := g.isLt
  subst hn
  rw [total_apply _ _ _ (show 3 + 3 * g.val + k < fieldCount from show _ < 276 by omega)]
  unfold exFields
  rw [if_neg (show ¬ (3 + 3 * g.val + k = 0) by omega), if_neg (show ¬ (3 + 3 * g.val + k = 1) by omega),
    if_neg (show ¬ (3 + 3 * g.val + k = 2) by omega)]
  congr 1
  · exact congrArg s.rows (Fin.ext (show (3 + 3 * g.val + k - 3) / 3 = g.val by omega))
  · show (3 + 3 * g.val + k - 3) % 3 = k
    omega

theorem read_curve (s : Entry.Source) : (readSource (exOf s)).curve = s.curve := by
  show (total 0 (exFields s) 0, total 0 (exFields s) 1, total 0 (exFields s) 2) = s.curve
  rw [total_apply _ _ 0 (by decide), total_apply _ _ 1 (by decide), total_apply _ _ 2 (by decide)]
  simp [exFields]

theorem read_rows (s : Entry.Source) : (readSource (exOf s)).rows = s.rows := by
  funext g
  show (⟨total 0 (exFields s) (3 + 3 * g.val), total 0 (exFields s) (3 + 3 * g.val + 1),
    total 0 (exFields s) (3 + 3 * g.val + 2)⟩ : RowGamma) = s.rows g
  rw [exFields_at s g 0 (3 + 3 * g.val) (by decide) (by omega), exFields_at s g 1 _ (by decide) rfl,
    exFields_at s g 2 _ (by decide) rfl]
  exact rowGamma_eq _

theorem exception_get (s : Entry.Source) (a c : Nat) (ha : a < digitCount) (hc : c < 12) (g : Fin digitCount)
    (b : Nat) (hb : b < 12) (h1 : a = g.val) (h2 : c = b) : (s.exception ⟨a, ha⟩)[c]'hc = (s.exception g)[b]'hb := by
  subst h1 h2
  rfl

theorem read_exception (s : Entry.Source) : (readSource (exOf s)).exception = s.exception := by
  funext g
  apply Vector.ext
  intro b hb
  have gs : g.val < 91 := g.isLt
  show (Vector.ofFn fun b : Fin 12 =>
    BitVec.ofNat 8 (total 0 (fun n => (exBytes s n).val) (12 * g.val + b.val)))[b] = (s.exception g)[b]
  rw [Vector.getElem_ofFn]
  simp only
  rw [total_apply _ _ _ (show 12 * g.val + b < exceptionByteCount from show _ < 1092 by omega)]
  unfold exBytes
  simp only [BitVec.val_toFin]
  rw [bitVec_ofNat_toNat]
  exact exception_get s _ _ _ _ g b hb (show (12 * g.val + b) / 12 = g.val by omega)
    (show (12 * g.val + b) % 12 = b by omega)

theorem read_joins (s : Entry.Source) : (readSource (exOf s)).joins = s.joins := by
  funext κ i
  show BitVec.ofNat 128 (total 0 (fun n => (exJoins s n).val) (κ.val * Entry.joinCount + i.val)) = s.joins κ i
  have fd := flat_div_mod (J := Entry.joinCount) (κ := κ.val) i.isLt
  have le : κ.val * Entry.joinCount ≤ 1 * Entry.joinCount := Nat.mul_le_mul_right _ (by omega)
  have is := i.isLt
  rw [total_apply _ _ _ (by omega)]
  unfold exJoins
  simp only [BitVec.val_toFin]
  rw [bitVec_ofNat_toNat]
  exact congrArg₂ s.joins (Fin.ext fd.1) (Fin.ext fd.2)

theorem pins_val (s : Entry.Source) (a b c : Nat) (ha : a < 2) (hb : b < Entry.pinCount) (hc : c < 128) (κ : Fin 2)
    (k : Fin Entry.pinCount) (lane : Fin 128) (h1 : a = κ.val) (h2 : b = k.val) (h3 : c = lane.val) :
    (s.pins ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩).val = (s.pins κ k lane).val := by
  subst h1 h2 h3
  rfl

theorem read_pins (s : Entry.Source) : (readSource (exOf s)).pins = s.pins := by
  funext κ k lane
  show (((total 0 (fun n => (exPins s n).val) ((κ.val * Entry.pinCount + k.val) * 128 + lane.val) : Nat)) :
    ZMod (2 ^ Entry.pinWidth k)) = s.pins κ k lane
  have fd1 := flat_div_mod (J := 128) (κ := κ.val * Entry.pinCount + k.val) lane.isLt
  have fd2 := flat_div_mod (J := Entry.pinCount) (κ := κ.val) k.isLt
  have le : κ.val * Entry.pinCount ≤ 1 * Entry.pinCount := Nat.mul_le_mul_right _ (by omega)
  have ks := k.isLt
  have ls : lane.val < 128 := lane.isLt
  rw [total_apply _ _ _ (by omega)]
  unfold exPins
  simp only
  have c1 : pinCoord ((κ.val * Entry.pinCount + k.val) * 128 + lane.val) = κ.val := by
    show ((κ.val * Entry.pinCount + k.val) * 128 + lane.val) / (Entry.pinCount * 128) = κ.val
    rw [Nat.mul_comm Entry.pinCount 128, ← Nat.div_div_eq_div_mul, fd1.1, fd2.1]
  have c2 : pinOf ((κ.val * Entry.pinCount + k.val) * 128 + lane.val) = k.val := by
    show ((κ.val * Entry.pinCount + k.val) * 128 + lane.val) / 128 % Entry.pinCount = k.val
    rw [fd1.1, fd2.2]
  rw [pins_val s _ _ _ _ _ _ κ k lane c1 c2 fd1.2, ZMod.natCast_zmod_val]

theorem recX_val (s : Entry.Source) (a : Nat) (ha : a < Entry.xCount) (e : Fin Entry.xCount) (h : a = e.val) :
    (s.recX ⟨a, ha⟩).val = (s.recX e).val := by
  subst h
  rfl

theorem recY_val (s : Entry.Source) (a : Nat) (ha : a < Entry.yCount) (e : Fin Entry.yCount) (h : a = e.val) :
    (s.recY ⟨a, ha⟩).val = (s.recY e).val := by
  subst h
  rfl

theorem read_record (s : Entry.Source) (r : Nat) (value : Nat) (inside : r < recordCount)
    (at_r : recAt s r = value) :
    CrtSource.recordNat (embed (exOf s)) r = ∑ i ∈ Finset.range moduliCount,
      value / CrtConv.radixAt i % modulusAt i * CrtConv.radixAt i := by
  unfold CrtSource.recordNat
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have fd := flat_div_mod (J := moduliCount) (κ := r) hi
  have bound : r * moduliCount + i < recordCount * moduliCount := by
    have le : r * moduliCount + moduliCount ≤ recordCount * moduliCount := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ inside
    omega
  rw [total_apply _ _ _ bound]
  show (exDigits s ⟨r * moduliCount + i, bound⟩).val * CrtConv.radixAt i = _
  unfold exDigits
  simp only [fd.1, fd.2, at_r]

theorem read_recX (s : Entry.Source) : (readSource (exOf s)).recX = s.recX := by
  funext e
  apply Fin.ext
  show CrtSource.recordNat (embed (exOf s)) e.val % Entry.table.product = (s.recX e).val
  have es : e.val < Entry.xCount := e.isLt
  have es' : e.val < 367 := e.isLt
  have at_e : recAt s e.val = (s.recX e).val := by
    unfold recAt
    rw [dif_pos es]
  rw [read_record s e.val _ (by show e.val < 367 + 275; omega) at_e, mixed_sum, Nat.mod_eq_of_lt (s.recX e).isLt]

theorem read_recY (s : Entry.Source) : (readSource (exOf s)).recY = s.recY := by
  funext e
  apply Fin.ext
  show CrtSource.recordNat (embed (exOf s)) (Entry.xCount + e.val) % Entry.table.product = (s.recY e).val
  have es : e.val < Entry.yCount := e.isLt
  have es' : e.val < 275 := e.isLt
  have at_e : recAt s (Entry.xCount + e.val) = (s.recY e).val := by
    unfold recAt
    rw [dif_neg (show ¬ (Entry.xCount + e.val < Entry.xCount) by omega),
      dif_pos (show Entry.xCount + e.val - Entry.xCount < Entry.yCount by omega)]
    exact recY_val s _ _ e (by omega)
  rw [read_record s _ _ (by show Entry.xCount + e.val < 367 + 275; show 367 + e.val < 367 + 275; omega) at_e,
    mixed_sum, Nat.mod_eq_of_lt (s.recY e).isLt]

theorem read_zeros (s : Entry.Source) : (readSource (exOf s)).zeros = s.zeros := by
  funext κ i
  show BitVec.ofNat 128 (total 0 (fun n => (exZeros s n).val) (254 * κ.val + i.val)) = s.zeros κ i
  have κs : κ.val < 2 := κ.isLt
  have is : i.val < 254 := i.isLt
  rw [total_apply _ _ _ (show 254 * κ.val + i.val < labelCount from show _ < 508 by omega)]
  unfold exZeros
  simp only [BitVec.val_toFin]
  rw [bitVec_ofNat_toNat]
  exact congrArg₂ s.zeros (Fin.ext (show (254 * κ.val + i.val) / 254 = κ.val by omega))
    (Fin.ext (show (254 * κ.val + i.val) % 254 = i.val by omega))

theorem read_deltas (s : Entry.Source) : (readSource (exOf s)).deltas = s.deltas := by
  funext κ
  show BitVec.ofNat 128 (total 0 (fun n => (exDeltas s n).val) κ.val) = s.deltas κ
  rw [total_apply _ _ _ κ.isLt]
  unfold exDeltas
  simp only [BitVec.val_toFin]
  exact bitVec_ofNat_toNat _

/-- **Every source is the reading of its exact draws.** -/
theorem readSource_exOf (s : Entry.Source) : readSource (exOf s) = s := by
  apply Entry.Source.data_injective
  unfold Entry.Source.data
  rw [read_curve, read_rows, read_exception, read_joins, read_pins, read_recX, read_recY, read_zeros,
    read_deltas]

/-! #### Reading back exact draws -/

theorem rowField_mk (f : Nat → BaseField) (b k : Nat) (hk : k < 3) :
    rowField ⟨f b, f (b + 1), f (b + 2)⟩ k = f (b + k) := by
  interval_cases k <;> rfl

theorem exFields_read (D : Exact) : exFields (readSource D) = D.1 := by
  funext n
  have ns : n.val < 276 := n.isLt
  unfold exFields
  by_cases h0 : n.val = 0
  · rw [if_pos h0]
    show total 0 D.1 0 = D.1 n
    rw [total_apply _ _ 0 (by decide)]
    exact congrArg D.1 (Fin.ext h0.symm)
  by_cases h1 : n.val = 1
  · rw [if_neg h0, if_pos h1]
    show total 0 D.1 1 = D.1 n
    rw [total_apply _ _ 1 (by decide)]
    exact congrArg D.1 (Fin.ext h1.symm)
  by_cases h2 : n.val = 2
  · rw [if_neg h0, if_neg h1, if_pos h2]
    show total 0 D.1 2 = D.1 n
    rw [total_apply _ _ 2 (by decide)]
    exact congrArg D.1 (Fin.ext h2.symm)
  rw [if_neg h0, if_neg h1, if_neg h2]
  show rowField ⟨total 0 D.1 (3 + 3 * ((n.val - 3) / 3)), total 0 D.1 (3 + 3 * ((n.val - 3) / 3) + 1),
    total 0 D.1 (3 + 3 * ((n.val - 3) / 3) + 2)⟩ ((n.val - 3) % 3) = D.1 n
  rw [rowField_mk (fun m => total 0 D.1 m) _ _ (Nat.mod_lt _ (by decide)),
    show 3 + 3 * ((n.val - 3) / 3) + (n.val - 3) % 3 = n.val by omega, total_apply _ _ _ n.isLt]

theorem exBytes_read (D : Exact) : exBytes (readSource D) = D.2.1 := by
  funext n
  apply Fin.ext
  have ns : n.val < 1092 := n.isLt
  unfold exBytes
  simp only [BitVec.val_toFin]
  show (Vector.ofFn fun b : Fin 12 =>
      BitVec.ofNat 8 (total 0 (fun m => (D.2.1 m).val) (12 * (n.val / 12) + b.val)))[n.val % 12].toNat =
        (D.2.1 n).val
  rw [Vector.getElem_ofFn]
  simp only [BitVec.toNat_ofNat]
  rw [show 12 * (n.val / 12) + n.val % 12 = n.val by omega, total_apply _ _ _ n.isLt,
    Nat.mod_eq_of_lt (D.2.1 n).isLt]

theorem exJoins_read (D : Exact) : exJoins (readSource D) = D.2.2.1 := by
  funext n
  apply Fin.ext
  unfold exJoins
  simp only [BitVec.val_toFin]
  show (BitVec.ofNat 128 (total 0 (fun m => (D.2.2.1 m).val)
    (n.val / Entry.joinCount * Entry.joinCount + n.val % Entry.joinCount))).toNat = (D.2.2.1 n).val
  rw [Nat.div_add_mod', total_apply _ _ _ n.isLt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (D.2.2.1 n).isLt]

theorem pin_index (P m : Nat) : (m / (P * 128) * P + m / 128 % P) * 128 + m % 128 = m := by
  rw [Nat.mul_comm P 128, ← Nat.div_div_eq_div_mul, Nat.div_add_mod', Nat.div_add_mod']

theorem exPins_read (D : Exact) : exPins (readSource D) = D.2.2.2.1 := by
  funext n
  apply Fin.ext
  unfold exPins
  show ((((total 0 (fun m => (D.2.2.2.1 m).val)
      ((pinCoord n.val * Entry.pinCount + pinOf n.val) * 128 + n.val % 128) : Nat)) :
      ZMod (2 ^ Entry.pinWidth ⟨pinOf n.val, pinOf_lt n⟩))).val = (D.2.2.2.1 n).val
  have idx : (pinCoord n.val * Entry.pinCount + pinOf n.val) * 128 + n.val % 128 = n.val :=
    pin_index Entry.pinCount n.val
  rw [ZMod.val_natCast, idx, total_apply _ _ _ n.isLt]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq (D.2.2.2.1 n).isLt (by rw [CrtConv.pinWidthAt_eq _ (pinOf_lt n)]))

theorem recAt_read (D : Exact) (r : Nat) (inside : r < recordCount) :
    recAt (readSource D) r = CrtSource.recordNat (embed D) r % Entry.table.product := by
  have small : r < 367 + 275 := inside
  unfold recAt
  split
  · rfl
  · split
    · show CrtSource.recordNat (embed D) (Entry.xCount + (r - Entry.xCount)) % Entry.table.product = _
      rw [show Entry.xCount + (r - Entry.xCount) = r by omega]
    · rename_i hx hy
      exfalso
      exact hy (show r - 367 < 275 by omega)

theorem exDigits_read (D : Exact) : exDigits (readSource D) = D.2.2.2.2.1 := by
  funext n
  apply Fin.ext
  unfold exDigits
  simp only
  have rs : n.val / moduliCount < recordCount := Nat.div_lt_of_lt_mul n.isLt
  have is : n.val % moduliCount < Entry.table.count := Nat.mod_lt _ (by decide)
  rw [recAt_read D _ rs, recordNat_eq D _ (digits_small D), Nat.mod_eq_of_lt (Entry.table.mixedRadix_lt _)]
  have r1 : Entry.table.radix ⟨n.val % moduliCount, is⟩ = CrtConv.radixAt (n.val % moduliCount) :=
    SourceCells.radix_eq _
  have m1 : Entry.table.modulus ⟨n.val % moduliCount, is⟩ = modulusAt (n.val % moduliCount) :=
    SourceCells.modulus_eq _
  have digit : Entry.table.mixedRadix (resOf _ (digits_small D) (n.val / moduliCount)) /
      CrtConv.radixAt (n.val % moduliCount) % modulusAt (n.val % moduliCount) =
        (resOf _ (digits_small D) (n.val / moduliCount) ⟨n.val % moduliCount, is⟩).val := by
    rw [← Entry.table.digit_mixedRadix (resOf _ (digits_small D) (n.val / moduliCount)) ⟨n.val % moduliCount, is⟩,
      r1, m1]
  rw [digit]
  show total 0 (fun m => (D.2.2.2.2.1 m).val) (n.val / moduliCount * moduliCount + n.val % moduliCount) = _
  rw [Nat.div_add_mod', total_apply _ _ _ n.isLt]

theorem exZeros_read (D : Exact) : exZeros (readSource D) = D.2.2.2.2.2.1 := by
  funext n
  apply Fin.ext
  have ns : n.val < 508 := n.isLt
  unfold exZeros
  simp only [BitVec.val_toFin]
  show (BitVec.ofNat 128 (total 0 (fun m => (D.2.2.2.2.2.1 m).val) (254 * (n.val / 254) + n.val % 254))).toNat =
    (D.2.2.2.2.2.1 n).val
  rw [show 254 * (n.val / 254) + n.val % 254 = n.val by omega, total_apply _ _ _ n.isLt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (D.2.2.2.2.2.1 n).isLt]

theorem exDeltas_read (D : Exact) : exDeltas (readSource D) = D.2.2.2.2.2.2 := by
  funext n
  apply Fin.ext
  unfold exDeltas
  simp only [BitVec.val_toFin]
  show (BitVec.ofNat 128 (total 0 (fun m => (D.2.2.2.2.2.2 m).val) n.val)).toNat = (D.2.2.2.2.2.2 n).val
  rw [total_apply _ _ _ n.isLt, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

/-- **Every exact draw is the draw of its reading.** -/
theorem exOf_readSource (D : Exact) : exOf (readSource D) = D :=
  Prod.ext (exFields_read D) (Prod.ext (exBytes_read D) (Prod.ext (exJoins_read D) (Prod.ext (exPins_read D)
    (Prod.ext (exDigits_read D) (Prod.ext (exZeros_read D) (exDeltas_read D))))))

/-- **Reading exact draws is a bijection onto the sources.** -/
def readEquiv : Exact ≃ Entry.Source where
  toFun := readSource
  invFun := exOf
  left_inv := exOf_readSource
  right_inv := readSource_exOf

/-! ### The source bound -/

/-- **The machine's source law is abort-close to the uniform source.** -/
theorem source_close :
    AbortClose drawsMass (CrtDraws.drawLaw.map (Option.map CrtSource.sourceOf))
      ((@PMF.uniformOfFintype Entry.Source (Fintype.ofFinite _) _).map some) := by
  have mapped := draws_close.map_opt (Option.map CrtSource.sourceOf) rfl
  rw [idealDrawLaw_eq, PMF.map_comp] at mapped
  have reading : (Option.map CrtSource.sourceOf ∘ fun D : Exact => some (embed D)) =
      (fun s : Entry.Source => some s) ∘ readEquiv := rfl
  letI : Fintype Entry.Source := Fintype.ofFinite _
  rw [reading, ← PMF.map_comp, uniform_equiv readEquiv] at mapped
  exact mapped

/-- **`δs`: the machine's source law is within `2^-130` of the uniform source.** -/
theorem source_etvDist_le :
    ((@PMF.uniformOfFintype Entry.Source (Fintype.ofFinite _) _).map some).etvDist
      (CrtDraws.drawLaw.map (Option.map CrtSource.sourceOf)) ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ :=
  (Cutoff.abortClose_etvDist_le source_close).trans drawsMass_le

end Laws

/-! ### The sampler cutoff of the CRT machine -/

/-- `273` preimages' extra abort mass is below `2^-130` (`Cutoff.preimagesMass_le`, without the certificates). -/
theorem preimages_le : (273 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 399)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
  have := mul_inv_pow_le 273 399 130 (count_le _ 9 130 399 (by decide) (by decide))
  simpa using this

/-- **The sampler cutoff of the CRT machine**: route M with the machine's bounded samplers is within
`machineCutoffError = 2^-128` of route M with the exact samplers, since
`2^-130 + (2^-129 + 273 · (2^-399 + 0)) ≤ 2^-128` (`samplerCutoff_of`). -/
theorem samplerCutoff_crt :
    LawShape.SamplerCutoff Kriterion.CRT.Privacy.Instance.crtEntry CrtBounded.samplers := by
  refine Cutoff.samplerCutoff_of Kriterion.CRT.Privacy.Instance.crtEntry CrtBounded.samplers
    ((2 : ℝ≥0∞) ^ 130)⁻¹ ((2 : ℝ≥0∞) ^ 129)⁻¹ ((2 : ℝ≥0∞) ^ 399)⁻¹ 0 ?_ ?_ ?_ ?_ ?_
  · intro field group
    letI := field
    letI := group
    exact source_etvDist_le
  · intro field group scalar u target _
    letI := field
    letI := group
    exact (Cutoff.abortClose_etvDist_le (Cutoff.boundedRows_close u target)).trans Cutoff.rowsMass_le
  · intro field group x
    letI := field
    exact Cutoff.abortClose_etvDist_le ((preimage_close x).mono (preimageAbort_le x.val))
  · intro field group
    exact le_of_eq (PMF.etvDist_self _)
  · rw [add_zero]
    calc ((2 : ℝ≥0∞) ^ 130)⁻¹ + (((2 : ℝ≥0∞) ^ 129)⁻¹ + 273 * ((2 : ℝ≥0∞) ^ 399)⁻¹)
        ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ + (((2 : ℝ≥0∞) ^ 129)⁻¹ + ((2 : ℝ≥0∞) ^ 130)⁻¹) :=
          add_le_add le_rfl (add_le_add le_rfl preimages_le)
      _ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
          rw [add_comm ((2 : ℝ≥0∞) ^ 129)⁻¹, ← add_assoc, inv_pow_add_self 129 130 rfl,
            inv_pow_add_self 128 129 rfl]
      _ = ENNReal.ofReal Kriterion.CRT.Privacy.machineCutoffError := by
          rw [Kriterion.CRT.Privacy.machineCutoffError_eq, one_div,
            ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

end

end Kriterion.CRT.SimMachine.SamplerBounds
