/-
**The per-encoding records (D7, D14).**

A record is `h * M + Σ_i J_i * Π_{i' < i} m_{i'}` with the wrap hint `h ∈ {0, 1}` and the residue joins `J_i < m_i`
(`CoordGarbled.records`, `Construction/CRT/Coord.lean`); the evaluator reads the hint as `M ≤ record` and the joins
by `recordJoin` (`record % M / Π_{i' < i} m_{i'} % m_i`). This file proves, for any modulus table:

1. the mixed radix is a bijection `(∀ i, Fin m_i) ≃ Fin M` (`mixedRadixEquiv`, Mathlib's `finPiFinEquiv`, whose
   prefix products are the table's `radix`), with the digit read-back `digit_mixedRadix`;
2. **L19** (`record_roundtrip`): every record is below `2 M`, and its hint and joins read back exactly;
   `records_roundtrip` states it for `CoordGarbled.records` and `recordJoin`;
3. the byte facts for the real table: `2 M < 2 ^ 620 ≤ 256 ^ 78`, so every record is a value of
   `Encoding.natural 78` (`bn254RecordFin`), which encodes to 78 bytes and decodes back;
4. the stage-1 law: a uniform record below `M` (hint 0) reads as a uniform residue vector
   (`uniform_recordJoin`).
-/

import Construction.CRT.Coord
import Encoding
import Mathlib.Probability.Distributions.Uniform

namespace Kriterion.CRT

open scoped ENNReal

namespace CrtTable

variable (T : CrtTable)

/-! ### The mixed radix -/

/-- The residue vectors of a table: one residue below each modulus. -/
abbrev Residues := ∀ i : Fin T.count, Fin (T.modulus i)

/-- The mixed-radix natural of a residue vector: `Σ_i J_i * radix_i`. -/
def mixedRadix (J : T.Residues) : Nat := ∑ i : Fin T.count, (J i).val * T.radix i

/-- **The mixed-radix bijection** `(∀ i, Fin m_i) ≃ Fin M`. -/
def mixedRadixEquiv : T.Residues ≃ Fin T.product := finPiFinEquiv

theorem mixedRadixEquiv_val (J : T.Residues) : (T.mixedRadixEquiv J).val = T.mixedRadix J := rfl

theorem mixedRadixEquiv_symm_val (x : Fin T.product) (i : Fin T.count) :
    ((T.mixedRadixEquiv.symm x) i).val = x.val / T.radix i % T.modulus i := rfl

theorem mixedRadix_lt (J : T.Residues) : T.mixedRadix J < T.product := by
  rw [← mixedRadixEquiv_val]
  exact (T.mixedRadixEquiv J).isLt

/-- The digits of a mixed-radix natural read back. -/
theorem digit_mixedRadix (J : T.Residues) (i : Fin T.count) :
    T.mixedRadix J / T.radix i % T.modulus i = (J i).val := by
  have back := congrArg (fun family : T.Residues => (family i).val) (T.mixedRadixEquiv.symm_apply_apply J)
  simp only [mixedRadixEquiv_symm_val, mixedRadixEquiv_val] at back
  exact back

/-! ### L19: records -/

/-- The record of a hint and a residue vector: `h * M + mixedRadix J`. -/
def record (hint : Bool) (J : T.Residues) : Nat := (if hint then T.product else 0) + T.mixedRadix J

theorem record_lt (hint : Bool) (J : T.Residues) : T.record hint J < 2 * T.product := by
  have small := T.mixedRadix_lt J
  unfold record
  cases hint
  · simp only [Bool.false_eq_true, if_false, Nat.zero_add]
    omega
  · simp only [if_true]
    omega

theorem record_mod (hint : Bool) (J : T.Residues) : T.record hint J % T.product = T.mixedRadix J := by
  have small := T.mixedRadix_lt J
  unfold record
  cases hint
  · simp [Nat.mod_eq_of_lt small]
  · simp [Nat.add_mod_left, Nat.mod_eq_of_lt small]

/-- **L19, record round trip**: the hint reads back as `M ≤ record` (and as `record / M`), and every residue join
as `record % M / radix_i % m_i`. -/
theorem record_roundtrip (hint : Bool) (J : T.Residues) :
    decide (T.product ≤ T.record hint J) = hint
      ∧ T.record hint J / T.product = (if hint then 1 else 0)
      ∧ ∀ i : Fin T.count, T.record hint J % T.product / T.radix i % T.modulus i = (J i).val := by
  have small := T.mixedRadix_lt J
  have pos : 0 < T.product := lt_of_le_of_lt (Nat.zero_le _) small
  refine ⟨?_, ?_, fun i => by rw [record_mod, digit_mixedRadix]⟩
  · unfold record
    cases hint
    · simp only [Bool.false_eq_true, if_false, Nat.zero_add, decide_eq_false_iff_not, not_le]
      exact small
    · simp only [if_true, decide_eq_true_eq]
      omega
  · unfold record
    cases hint
    · simp [Nat.div_eq_of_lt small]
    · simp only [if_true]
      rw [Nat.add_comm, Nat.add_div_right _ pos, Nat.div_eq_of_lt small]

/-- The residue joins of a garbling as a residue vector. -/
def joinVector {S : Nat} (garbled : CoordGarbled T S) (slopes : Fin S → Nat) (e : Fin S)
    (pos : ∀ i, 0 < T.modulus i) : T.Residues :=
  fun i => ⟨garbled.join slopes i e, Nat.mod_lt _ (pos i)⟩

theorem records_eq {S : Nat} (garbled : CoordGarbled T S) (slopes : Fin S → Nat) (e : Fin S)
    (pos : ∀ i, 0 < T.modulus i) :
    garbled.records slopes e = T.record (garbled.hint e) (T.joinVector garbled slopes e pos) := by
  simp [CoordGarbled.records, record, mixedRadix, joinVector]

/-- **L19 for the construction's records**: the evaluator's hint `M ≤ record_e` is the garbler's hint, and
`recordJoin` returns the garbler's residue join `J_{e,i}`. -/
theorem records_roundtrip {S : Nat} (garbled : CoordGarbled T S) (slopes : Fin S → Nat) (e : Fin S)
    (pos : ∀ i, 0 < T.modulus i) :
    garbled.records slopes e < 2 * T.product
      ∧ decide (T.product ≤ garbled.records slopes e) = garbled.hint e
      ∧ ∀ i, recordJoin T T.product (stored T.radix) (garbled.records slopes e) i = garbled.join slopes i e := by
  rw [records_eq T garbled slopes e pos]
  obtain ⟨hint, -, joins⟩ := T.record_roundtrip (garbled.hint e) (T.joinVector garbled slopes e pos)
  refine ⟨T.record_lt _ _, hint, fun i => ?_⟩
  simp only [recordJoin, stored_eq]
  exact joins i

/-! ### The stage-1 law -/

/-- With positive moduli the record space is nonempty. -/
theorem nonempty_product (pos : ∀ i, 0 < T.modulus i) : Nonempty (Fin T.product) :=
  ⟨⟨0, Finset.prod_pos fun i _ => pos i⟩⟩

/-- With positive moduli there are residue vectors. -/
theorem nonempty_residues (pos : ∀ i, 0 < T.modulus i) : Nonempty T.Residues := ⟨fun i => ⟨0, pos i⟩⟩

theorem uniform_map_equiv' {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (e : A ≃ B) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  classical
  refine PMF.ext fun b => ?_
  rw [PMF.map_apply, tsum_eq_single (e.symm b) (fun a hne => ?_)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · have notHit : b ≠ e a := fun hit => hne (by rw [hit, Equiv.symm_apply_apply])
    simp [notHit]

/-- **A uniform record below `M` (hint 0) is a uniform residue vector**: the joins the evaluator reads with
`recordJoin` from a uniform natural below `M` have the law of a uniform residue vector. -/
theorem uniform_recordJoin [Nonempty (Fin T.product)] [Nonempty T.Residues] :
    (PMF.uniformOfFintype (Fin T.product)).map
        (fun record : Fin T.product => fun i => recordJoin T T.product (stored T.radix) record.val i)
      = (PMF.uniformOfFintype T.Residues).map (fun J : T.Residues => fun i => (J i).val) := by
  have factor : (fun record : Fin T.product => fun i => recordJoin T T.product (stored T.radix) record.val i)
      = (fun J : T.Residues => fun i => (J i).val) ∘ T.mixedRadixEquiv.symm := by
    funext record i
    simp only [Function.comp, recordJoin, stored_eq, mixedRadixEquiv_symm_val, Nat.mod_eq_of_lt record.isLt]
  rw [factor, ← PMF.map_comp, uniform_map_equiv']

end CrtTable

/-! ### Byte facts for the real table -/

/-- The product of the real table, as a literal (619 bits). -/
theorem bn254Table_product :
    bn254Table.product = 1226489348707553756519335942975404354288386879012005821186927534631901567509458030177894725488781446327566652219420625218609205291914242482673623847674331957077662193154441207182389536000 := by
  decide +kernel

/-- `2 M < 2 ^ 620 ≤ 2 ^ 624 = 256 ^ 78`: a record fits 78 bytes. -/
theorem bn254Table_record_fits : 2 * bn254Table.product ≤ 256 ^ 78 := by
  rw [bn254Table_product]
  decide +kernel

theorem bn254Table_modulus_pos : ∀ i, 0 < bn254Table.modulus i := by
  decide +kernel

/-- A record of the real table as a value of `Encoding.natural 78`. -/
def bn254RecordFin (hint : Bool) (J : bn254Table.Residues) : Fin (256 ^ 78) :=
  ⟨bn254Table.record hint J, lt_of_lt_of_le (bn254Table.record_lt hint J) bn254Table_record_fits⟩

/-- Every record encodes to exactly 78 bytes. -/
theorem bn254Record_length (hint : Bool) (J : bn254Table.Residues) :
    ((Encoding.natural 78).encode (bn254RecordFin hint J)).length = 78 :=
  Encoding.natural_length 78 _

/-- **The byte round trip**: decoding a record's 78 bytes gives the record back, whose hint and joins read back by
`record_roundtrip`. -/
theorem bn254Record_decode (hint : Bool) (J : bn254Table.Residues) (tail : List (Fin 256)) :
    (Encoding.natural 78).decode ((Encoding.natural 78).encode (bn254RecordFin hint J) ++ tail)
      = some (bn254RecordFin hint J, tail) :=
  (Encoding.natural 78).decode_encode _ _

end Kriterion.CRT
