/-
**OffDecomp for the CRT entry** (input (ii) of `crtMiddleFactor_of`, the statement
`Laws.OffSplit` in `Laws/MiddleOff.lean`).

Off the curve the shadow runs the reach `reachOffCM`: the conversion blocks `C`, the digest labels at `u`'s bits `D`,
then the 91 finals `F`, each at `hashInput key (digestFinalTag o)` with `key` the XOR of the answers at `D`. On the
table (`offAnswer t`) the private run stores exactly `C ++ D ++ F` with the table's answers (`tableRunOff_empty`).

* `P` is the 91 final positions (`DigestSplit.finalPos`): outside every site (`final_away`), invisible (family 9).
* `xs t` is `F`: it reads the table only at `D` (family 8), so it ignores `P`; its tags are the final positions,
  pairwise distinct.
* The reveal reads only the conversion blocks (families at most 6, `Flags.replayWraps_congr`), so it ignores `P`.
* The view's entries are the reach's transcript on the view's table, at the visible tags. `C` is cold at `u` for
  **any** source (`EvalCold.replayConv_cold_labelled`) and `D` is at `u`'s bits, so both are visible: on them the view's
  table is the table, the reach asks the same inputs as on the table, and the visible filter keeps `C ++ D` and drops
  `F`. With the table's answers at `F` (`tableEntries`), the installation holds the same lookups as the private run.
-/

import Proof.Privacy.CRT.Laws.MiddleOff
import Proof.Privacy.CRT.Flags.WrapBridge
import Proof.Privacy.CRT.Core.EvalCold
import Proof.Privacy.CRT.Core.DigestSplit
import Proof.Privacy.CRT.Hidden.Reached
import Proof.Privacy.CRT.Paths.ReachTranscript

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.OffDecomp

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance Kriterion.CRT.Privacy.Laws
open Kriterion.CRT.Privacy.PublicFirst (viewHere)
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure)

noncomputable section

/-! ### Asked inputs -/

theorem asked_congr {α : Type} (H H' : HashN) :
    ∀ p : CM α, (∀ n ∈ asked H p, H n = H' n) → asked H' p = asked H p ∧ p.eval H' = p.eval H := by
  intro p
  induction p with
  | pure v => exact fun _ => ⟨rfl, rfl⟩
  | query n next ih =>
      intro agree
      have first : H n = H' n := agree n (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨askedSame, evalSame⟩ := ih (H n) fun m inside => agree m (List.mem_cons.mpr (Or.inr inside))
      refine ⟨?_, ?_⟩
      · show n :: asked H' (next (H' n)) = n :: asked H (next (H n))
        rw [← first, askedSame]
      · show (next (H' n)).eval H' = (next (H n)).eval H
        rw [← first, evalSame]

/-- The inputs an off-curve run reads are its `asked` inputs on the table's answers. -/
theorem offPoints_eq (t : TagTable) {α : Type} : ∀ P : CM α, offPoints t P = (asked (offAnswer t) P).map Nat.cast
  | .pure _ => rfl
  | .query n next => by
      show (n : BaseField) :: offPoints t (next (offAnswer t n)) =
        ((n :: asked (offAnswer t) (next (offAnswer t n))).map Nat.cast)
      rw [offPoints_eq t (next _)]
      rfl

/-- The finals the reach asks at the digest key `key`. -/
def finalsAt (key : Block) : List ℕ :=
  (List.finRange digitCount).flatMap fun o => [hashInput key (digestFinalTag o.val)]

theorem asked_reachOff (X : HashN) (pub : Entry.Public) (u : AffineInput) (L : LamportSignature) :
    asked X (EntryReading.reachOffCM pub u L) =
      asked X (Entry.replayConv pub u L) ++ (asked X (digestKeyM coordinateBitCount (Entry.labelsOf L) u) ++
        finalsAt (digestKey X coordinateBitCount (Entry.labelsOf L) u)) := by
  unfold EntryReading.reachOffCM
  simp only [asked_bind, asked_pure, List.append_nil, Align.asked_digestEvalM]
  rfl

/-! ### Labelled and visible inputs -/

/-- A labelled input below `p`, at a tag below `2 ^ 40`. -/
def Small (n : ℕ) : Prop := ((n : BaseField)).val = n ∧ n / 2 ^ 128 < 2 ^ 40

theorem small_hashInput (label : Block) (tag : ℕ) (h : tag < 2 ^ 40) : Small (hashInput label tag) := by
  refine ⟨?_, by rw [Align.hashInput_div]; exact h⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans (Asks.hashInput_small label tag h) Asks.modulus_gt)]

theorem tagOfInput_small {n : ℕ} (h : Small n) : tagOfInput (n : BaseField) = ⟨n / 2 ^ 128, h.2⟩ := by
  apply Fin.ext
  show ((n : BaseField)).val / 2 ^ 128 % 2 ^ 40 = n / 2 ^ 128
  rw [h.1, Nat.mod_eq_of_lt h.2]

theorem visTag_cold (T : CrtTable) (u : AffineInput) {tag : ℕ} (fam : tagFamily tag ≤ 6)
    (cold : hotTag T u tag = false) : visTag T u tag = true := by
  unfold H8.visTag
  generalize hf : tagFamily tag = f at fam
  interval_cases f <;> simp [cold]

theorem visTag_final (T : CrtTable) (u : AffineInput) {tag : ℕ} (fam : tagFamily tag = 9) : visTag T u tag = false := by
  unfold H8.visTag
  rw [fam]
  rfl

/-- The conversion inputs are small and visible, for any published value and labels. -/
theorem conv_visible (X : HashN) (pub : Entry.Public) (u : AffineInput) (L : LamportSignature) :
    ∀ n ∈ asked X (Entry.replayConv pub u L), Small n ∧ visTag Entry.table u (n / 2 ^ 128) = true := by
  intro n hn
  obtain ⟨label, tag, rfl, hlt, hfam, hcold⟩ := EvalCold.replayConv_cold_labelled X pub u L n hn
  refine ⟨small_hashInput label tag hlt, ?_⟩
  rw [Align.hashInput_div]
  exact visTag_cold _ u hfam hcold

/-- The digest labels are small and visible (at `u`'s bits). -/
theorem label_visible (X : HashN) (u : AffineInput) (labels : Fin 2 → Fin coordinateBitCount → Block) :
    ∀ n ∈ asked X (digestKeyM coordinateBitCount labels u), Small n ∧ visTag Entry.table u (n / 2 ^ 128) = true := by
  intro n hn
  rw [Align.asked_digestKeyM] at hn
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at hn
  obtain ⟨c, p, rfl⟩ := hn
  have bit := Paths.coordBit_lt u c p.val
  have pSmall : p.val < 65536 := lt_of_lt_of_le p.isLt (by decide)
  have range : TagInRange c.val 0 0 0 p.val (coordBit u c p.val) :=
    ⟨c.isLt, by norm_num, by norm_num, by norm_num, pSmall, by omega⟩
  refine ⟨small_hashInput _ _ (Asks.tagCode_lt (by decide) range), ?_⟩
  obtain ⟨hf, hcoord, hslot, hpart⟩ := Align.digestLabelTag_fields (b := coordBit u c p.val) c.isLt pSmall (by omega)
  rw [Align.hashInput_div]
  unfold H8.visTag
  rw [hf, hcoord, hslot, hpart, Align.inputBit_eq_coordBit]
  exact beq_self_eq_true _

theorem final_small (key : Block) : ∀ n ∈ finalsAt key, Small n ∧ tagFamily (n / 2 ^ 128) = 9 := by
  intro n hn
  simp only [finalsAt, List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at hn
  obtain ⟨o, rfl⟩ := hn
  have ho := lt_trans o.isLt DigestSplit.digitCount_lt
  refine ⟨small_hashInput _ _ (DigestSplit.digestFinalTag_lt _ ho), ?_⟩
  rw [Align.hashInput_div]
  exact (Align.digestFinalTag_fields ho).1

/-! ### The final positions -/

/-- **`P`**: the 91 final positions. -/
def finalSet : Finset (Fin (2 ^ 40)) :=
  Finset.univ.image fun o : Fin digitCount => DigestSplit.finalPos o.val

theorem mem_finalSet {p : Fin (2 ^ 40)} (hp : p ∈ finalSet) : tagFamily p.val = 9 := by
  obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hp
  exact DigestSplit.family_final o.val (lt_trans o.isLt DigestSplit.digitCount_lt)

theorem not_mem_finalSet {p : Fin (2 ^ 40)} (hp : tagFamily p.val ≠ 9) : p ∉ finalSet :=
  fun mem => hp (mem_finalSet mem)

/-! ### The installation of table-consistent hash entries -/

theorem install_table_lookup (t : TagTable) :
    ∀ (l : List (Entry Empty Empty)), (∀ e ∈ l, ∃ x, e = ⟨.hash x, t (tagOfInput x)⟩) →
      ∀ (σ : LazyOracle.State Empty Empty), TableConsistent t σ → ∀ y,
        (Privacy.installEntries l σ).hash.lookup y =
          if y ∈ l.map entryInput then some (Fintype.equivFin (Block × Block) (t (tagOfInput y)))
          else σ.hash.lookup y
  | [], _, σ, _, y => by simp [Privacy.installEntries]
  | e :: rest, form, σ, cons, y => by
      obtain ⟨x, rfl⟩ := form e List.mem_cons_self
      have restForm : ∀ e ∈ rest, ∃ x, e = ⟨.hash x, t (tagOfInput x)⟩ := fun e he =>
        form e (List.mem_cons_of_mem _ he)
      have cons' : TableConsistent t (installOne σ ⟨.hash x, t (tagOfInput x)⟩) := by
        rw [installOne_hash]
        split
        · exact plant_consistent t cons x _ rfl
        · exact cons
      rw [installEntries_cons, install_table_lookup t rest restForm _ cons' y]
      have input : entryInput (⟨.hash x, t (tagOfInput x)⟩ : Entry Empty Empty) = x := rfl
      rw [List.map_cons, input]
      by_cases inRest : y ∈ rest.map entryInput
      · rw [if_pos inRest, if_pos (List.mem_cons_of_mem _ inRest)]
      · rw [if_neg inRest]
        rw [installOne_hash]
        by_cases yx : y = x
        · subst yx
          rw [if_pos List.mem_cons_self]
          split
          · rw [plantHash_lookup, if_pos rfl]
          · rename_i stored
            obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp stored
            rw [hv, cons y v hv]
        · have notHead : y ∉ x :: rest.map entryInput := by
            rw [List.mem_cons]
            rintro (h | h)
            · exact yx h
            · exact inRest h
          rw [if_neg notHead]
          split
          · rw [plantHash_lookup, if_neg yx]
          · rfl

/-! ### The decomposition -/

section Decomp

variable [FieldCertificate] [GroupCertificate]

/-- A source's published value, at the entry's type (so that the reach's programs are well typed at reducible
transparency, which `rw` needs). -/
def pubS (source : (viewHere crtEntry).Source) : Entry.Public := (viewHere crtEntry).publish source

/-- A source's labels at `u`. -/
def labS (source : (viewHere crtEntry).Source) (u : AffineInput) : LamportSignature := (viewHere crtEntry).labels source u

/-- The digest key of the reach on the table's answers. -/
def keyOf (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable) : Block :=
  digestKey (offAnswer t) coordinateBitCount (Entry.labelsOf (labS source u)) u

/-- **`xs t`**: the finals' inputs. -/
def xsOf (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable) : List BaseField :=
  (finalsAt (keyOf source u t)).map Nat.cast

/-- The view's table at a visible small input is the table. -/
theorem viewTable_visible (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable) {n : ℕ}
    (small : Small n) (vis : visTag Entry.table u (n / 2 ^ 128) = true) :
    viewTable crtEntry Entry.table u (offView crtEntry Entry.table source u t) (tagOfInput (n : BaseField)) =
      t (tagOfInput (n : BaseField)) := by
  rw [tagOfInput_small small]
  unfold H8.viewTable
  rw [dif_pos vis]

/-- The reach asks the same inputs on the view's table as on the table. -/
theorem asked_view (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable) :
    asked (schemeHash (tableOracle (FI := Empty) (EI := Empty)
        (viewTable crtEntry Entry.table u (offView crtEntry Entry.table source u t))))
      (EntryReading.reachOffCM (pubS source) u (labS source u)) =
      asked (offAnswer t) (EntryReading.reachOffCM (pubS source) u (labS source u)) := by
  set V := viewTable crtEntry Entry.table u (offView crtEntry Entry.table source u t)
  have agree : ∀ n, Small n → visTag Entry.table u (n / 2 ^ 128) = true →
      offAnswer t n = schemeHash (tableOracle (FI := Empty) (EI := Empty) V) n := by
    intro n small vis
    show t (tagOfInput (n : BaseField)) = V (tagOfInput (n : BaseField))
    exact (viewTable_visible source u t small vis).symm
  rw [asked_reachOff, asked_reachOff]
  have convSame := asked_congr (offAnswer t) (schemeHash (tableOracle (FI := Empty) (EI := Empty) V))
    (Entry.replayConv (pubS source) u (labS source u)) fun n hn =>
      agree n (conv_visible _ _ u _ n hn).1 (conv_visible _ _ u _ n hn).2
  have keySame := asked_congr (offAnswer t) (schemeHash (tableOracle (FI := Empty) (EI := Empty) V))
    (digestKeyM coordinateBitCount (Entry.labelsOf (labS source u)) u) fun n hn =>
      agree n (label_visible _ u _ n hn).1 (label_visible _ u _ n hn).2
  have keyEq : digestKey (schemeHash (tableOracle (FI := Empty) (EI := Empty) V)) coordinateBitCount
      (Entry.labelsOf (labS source u)) u =
      digestKey (offAnswer t) coordinateBitCount (Entry.labelsOf (labS source u)) u :=
    (eval_digestKeyM _ _ _ _).symm.trans (keySame.2.trans (eval_digestKeyM _ _ _ _))
  rw [convSame.1, keySame.1, keyEq]

/-- The reach program of the entry at a source's view is `EntryReading.reachProgram`. -/
theorem reachProgram_offView (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable) :
    crtEntry.reachProgram inferInstance inferInstance (offView crtEntry Entry.table source u t).1 u
      (offView crtEntry Entry.table source u t).2.1 = EntryReading.reachProgram (pubS source) u (labS source u) := by
  have h0 : crtEntry.reachProgram = fun field group => @EntryReading.reachProgram field group := rfl
  rw [h0]
  rfl

/-- The view's transcript is `EntryReading.reachProgram`'s. -/
theorem transcript_offView (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable)
    (A : ∀ query : PublicQuery Empty Empty, query.Answer) :
    programTranscript A (crtEntry.reachProgram inferInstance inferInstance (offView crtEntry Entry.table source u t).1 u
      (offView crtEntry Entry.table source u t).2.1) =
      programTranscript A (EntryReading.reachProgram (pubS source) u (labS source u)) := by
  have h0 : crtEntry.reachProgram = fun field group => @EntryReading.reachProgram field group := rfl
  rw [h0]
  rfl

/-- The transcript of the off-curve reach on a table oracle. -/
theorem transcript_off (pub : Entry.Public) (u : AffineInput) (L : LamportSignature) (V : TagTable)
    (off : validate u = false) :
    programTranscript (publicAnswer (tableOracle (FI := Empty) (EI := Empty) V)) (EntryReading.reachProgram pub u L) =
      (asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) V)) (EntryReading.reachOffCM pub u L)).map
        fun n : ℕ => (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) V).2.2 (n : BaseField)⟩ :
          Entry Empty Empty) := by
  unfold EntryReading.reachProgram
  rw [Align.transcript_toProgram, Paths.reachDecodedM_eq, Align.ftranscript_liftHash]
  unfold Paths.reachDecodedCM
  rw [asked_bind, if_neg (by rw [off]; decide)]
  simp only [asked_pure, List.append_nil]

/-- **The view's entries**: the reach's inputs on the table with the view's answers, at the visible tags. -/
theorem mem_viewEntries (source : (viewHere crtEntry).Source) (u : AffineInput) (off : validate u = false)
    (t : TagTable) (e : Entry Empty Empty) :
    e ∈ viewEntries crtEntry Entry.table u (offView crtEntry Entry.table source u t) ↔
      ∃ n ∈ asked (offAnswer t) (EntryReading.reachOffCM (pubS source) u (labS source u)),
        e = ⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty)
          (viewTable crtEntry Entry.table u (offView crtEntry Entry.table source u t))).2.2 (n : BaseField)⟩ ∧
        visTag Entry.table u (((n : BaseField)).val / 2 ^ 128) = true := by
  unfold H8.viewEntries
  rw [List.mem_filter, transcript_offView source u t, transcript_off (pubS source) u (labS source u)
    (viewTable crtEntry Entry.table u (offView crtEntry Entry.table source u t)) off]
  rw [asked_view source u t, List.mem_map]
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, hvis⟩
    exact ⟨n, hn, rfl, hvis⟩
  · rintro ⟨n, hn, rfl, hvis⟩
    exact ⟨⟨n, hn, rfl⟩, hvis⟩

/-- **The reach's inputs on the table**: the conversion and label inputs (small and visible), then the finals. -/
theorem decomp (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable) :
    ∃ C D : List ℕ,
      asked (offAnswer t) (EntryReading.reachOffCM (pubS source) u (labS source u)) =
        C ++ (D ++ finalsAt (keyOf source u t)) ∧
      ∀ n ∈ C ++ D, Small n ∧ visTag Entry.table u (n / 2 ^ 128) = true := by
  refine ⟨_, _, asked_reachOff _ _ _ _, fun n hn => ?_⟩
  rcases List.mem_append.mp hn with hc | hd
  · exact conv_visible _ _ u _ n hc
  · exact label_visible _ u _ n hd

/-- The off-curve shadow's program asks the reach's inputs. -/
theorem asked_shadow (source : (viewHere crtEntry).Source) (u : AffineInput) (X : HashN) :
    asked X (crtShadowOffCurve source u) =
      asked X (EntryReading.reachOffCM (pubS source) u (labS source u)) := by
  unfold crtShadowOffCurve
  rw [asked_bind]
  simp only [asked_pure, List.append_nil]
  rfl

/-- An entry of the view holds the table's answer at its input, which is one of the reach's small inputs. -/
theorem viewEntry_form (source : (viewHere crtEntry).Source) (u : AffineInput) (off : validate u = false)
    (t : TagTable) (e : Entry Empty Empty)
    (he : e ∈ viewEntries crtEntry Entry.table u (offView crtEntry Entry.table source u t)) :
    ∃ n ∈ asked (offAnswer t) (EntryReading.reachOffCM (pubS source) u (labS source u)),
      Small n ∧ e = ⟨.hash (n : BaseField), t (tagOfInput (n : BaseField))⟩ := by
  obtain ⟨n, hn, rfl, hvis⟩ := (mem_viewEntries source u off t e).mp he
  obtain ⟨C, D, hR, hCD⟩ := decomp source u t
  have hn' := hn
  rw [hR] at hn'
  have small : Small n ∧ visTag Entry.table u (n / 2 ^ 128) = true := by
    rcases List.mem_append.mp hn' with hc | hrest
    · exact hCD n (List.mem_append_left _ hc)
    · rcases List.mem_append.mp hrest with hd | hf
      · exact hCD n (List.mem_append_right _ hd)
      · obtain ⟨smallF, fam⟩ := final_small _ n hf
        rw [smallF.1, visTag_final _ u fam] at hvis
        exact absurd hvis Bool.false_ne_true
  refine ⟨n, hn, small.1, ?_⟩
  have answer : (tableOracle (FI := Empty) (EI := Empty)
      (viewTable crtEntry Entry.table u (offView crtEntry Entry.table source u t))).2.2 (n : BaseField) =
      t (tagOfInput (n : BaseField)) := viewTable_visible source u t small.1 small.2
  rw [answer]

/-- **OffDecomp for the CRT entry at every source**, off the curve. -/
theorem crtOffDecomp (source : (viewHere crtEntry).Source) (u : AffineInput) (off : validate u = false) :
    OffDecomp crtEntry Entry.table crtShadow crtRevealOff source u () finalSet (xsOf source u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- P lies outside every site
  · intro p hp site mem
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hp
    exact DigestSplit.final_away site mem o
  -- P is invisible
  · intro p hp
    exact visTag_final _ u (mem_finalSet hp)
  -- the reveal ignores P
  · intro t t' agree
    refine Flags.replayWraps_congr source u t t' fun n hn => ?_
    obtain ⟨key, member, range, label, rfl⟩ :=
      Flags.keyRun_queries (Paths.replayConv_tagged ((view).publish source) u ((view).labels source u)) _ n hn
    rw [ReplayDelivered.tagHash_hashInput, ReplayDelivered.tagHash_hashInput]
    refine agree _ (not_mem_finalSet ?_)
    show tagFamily (key.code % 2 ^ 40) ≠ 9
    rw [Nat.mod_eq_of_lt (Paths.TagKey.code_lt range), Align.tagFamily_key range]
    have := Paths.replayConvKeys_fam key member
    omega
  -- xs ignores P
  · intro t t' agree
    unfold xsOf keyOf
    rw [← eval_digestKeyM, ← eval_digestKeyM]
    rw [(asked_congr (offAnswer t) (offAnswer t') _ fun n hn => ?_).2]
    obtain ⟨small, vis⟩ := label_visible (offAnswer t) u _ n hn
    show t (tagOfInput (n : BaseField)) = t' (tagOfInput (n : BaseField))
    refine agree _ (not_mem_finalSet ?_)
    rw [tagOfInput_small small]
    intro fam
    rw [visTag_final _ u fam] at vis
    exact Bool.false_ne_true vis
  -- the tags of xs are pairwise distinct
  · intro t
    unfold xsOf finalsAt
    rw [List.map_map]
    have form : (tagOfInput ∘ Nat.cast : ℕ → Fin (2 ^ 40)) ∘ (fun o : Fin digitCount =>
        hashInput (keyOf source u t) (digestFinalTag o.val)) = fun o => DigestSplit.finalPos o.val := by
      funext o
      simp only [Function.comp]
      have ho := lt_trans o.isLt DigestSplit.digitCount_lt
      rw [tagOfInput_small (small_hashInput _ _ (DigestSplit.digestFinalTag_lt _ ho))]
      apply Fin.ext
      show hashInput _ _ / 2 ^ 128 = (DigestSplit.finalPos o.val).val
      rw [Align.hashInput_div, DigestSplit.finalPos_val _ ho]
    rw [Align.flatMap_singleton_eq_map, List.map_map, form]
    exact (List.nodup_finRange _).map DigestSplit.finalPos_injective
  -- the tags of xs lie in P
  · intro t x hx
    unfold xsOf finalsAt at hx
    simp only [List.mem_map, List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at hx
    obtain ⟨n, ⟨o, rfl⟩, rfl⟩ := hx
    have ho := lt_trans o.isLt DigestSplit.digitCount_lt
    rw [tagOfInput_small (small_hashInput _ _ (DigestSplit.digestFinalTag_lt _ ho))]
    refine Finset.mem_image.mpr ⟨o, Finset.mem_univ _, Fin.ext ?_⟩
    show (DigestSplit.finalPos o.val).val = hashInput _ _ / 2 ^ 128
    rw [Align.hashInput_div, DigestSplit.finalPos_val _ ho]
  -- the view's entries are hash entries
  · intro t e he
    obtain ⟨n, -, -, rfl⟩ := viewEntry_form source u off t e he
    exact ⟨_, rfl⟩
  -- xs are not inputs of the view's entries
  · intro t x hx hin
    obtain ⟨e, he, hex⟩ := List.mem_map.mp hin
    obtain ⟨n, -, rfl, hvisN⟩ := (mem_viewEntries source u off t e).mp he
    unfold xsOf at hx
    obtain ⟨m, hm, same⟩ := List.mem_map.mp hx
    obtain ⟨smallM, famM⟩ := final_small _ m hm
    have input : entryInput (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty)
        (viewTable crtEntry Entry.table u (offView crtEntry Entry.table source u t))).2.2 (n : BaseField)⟩ :
          Entry Empty Empty) = (n : BaseField) := rfl
    rw [input] at hex
    rw [hex, ← same, smallM.1, visTag_final _ u famM] at hvisN
    exact Bool.false_ne_true hvisN
  -- the lookups
  · intro t y
    obtain ⟨C, D, hR, hCD⟩ := decomp source u t
    have run := (tableRunOff_empty (FI := Empty) (EI := Empty) t (crtShadowOffCurve source u)).2.2.2 y
    have form : ∀ e ∈ viewEntries crtEntry Entry.table u (offView crtEntry Entry.table source u t) ++
        tableEntries t (xsOf source u t), ∃ x, e = ⟨.hash x, t (tagOfInput x)⟩ := by
      intro e he
      rcases List.mem_append.mp he with hv | ht
      · obtain ⟨n, -, -, rfl⟩ := viewEntry_form source u off t e hv
        exact ⟨_, rfl⟩
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht
        exact ⟨x, rfl⟩
    have hmem : y ∈ offPoints t (crtShadowOffCurve source u) ↔
        y ∈ (viewEntries crtEntry Entry.table u (offView crtEntry Entry.table source u t) ++
          tableEntries t (xsOf source u t)).map entryInput := by
      rw [List.map_append (f := entryInput), tableEntries_inputs, List.mem_append, offPoints_eq, asked_shadow, hR]
      constructor
      · intro hy
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
        rcases List.mem_append.mp hn with hc | hrest
        · have vis := hCD n (List.mem_append_left _ hc)
          refine Or.inl (List.mem_map.mpr ⟨_, (mem_viewEntries source u off t _).mpr ⟨n, ?_, rfl, ?_⟩, rfl⟩)
          · rw [hR]; exact List.mem_append_left _ hc
          · rw [vis.1.1]; exact vis.2
        · rcases List.mem_append.mp hrest with hd | hf
          · have vis := hCD n (List.mem_append_right _ hd)
            refine Or.inl (List.mem_map.mpr ⟨_, (mem_viewEntries source u off t _).mpr ⟨n, ?_, rfl, ?_⟩, rfl⟩)
            · rw [hR]; exact List.mem_append_right _ (List.mem_append_left _ hd)
            · rw [vis.1.1]; exact vis.2
          · exact Or.inr (List.mem_map.mpr ⟨n, hf, rfl⟩)
      · rintro (hv | hx)
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
          obtain ⟨n, hn, -, rfl⟩ := viewEntry_form source u off t e he
          rw [hR] at hn
          exact List.mem_map.mpr ⟨n, hn, rfl⟩
        · unfold xsOf at hx
          obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
          exact List.mem_map.mpr ⟨m, List.mem_append_right _ (List.mem_append_right _ hm), rfl⟩
    show (offFinal t (crtShadowOffCurve source u) LazyOracle.empty).hash.lookup y = _
    rw [run, install_table_lookup t _ form LazyOracle.empty (Flags.tableConsistent_empty t) y]
    by_cases h : y ∈ offPoints t (crtShadowOffCurve source u)
    · rw [if_pos h, if_pos (hmem.mp h)]
    · rw [if_neg h, if_neg fun h' => h (hmem.mpr h')]

/-- **`OffSplit` for the CRT entry**, at every source, off the curve. -/
theorem crtOffSplit (scalar : NonZeroScalar) (u : AffineInput)
    (offCurve : (crtEntry.scheme inferInstance inferInstance).function scalar u = none)
    (source : (viewHere crtEntry).Source) :
    OffSplit crtEntry Entry.table crtShadow crtRevealOff source u := by
  have off : validate u = false := by
    have decoded : decodePoint u = none := Option.map_eq_none_iff.mp offCurve
    cases valid : validate u
    · rfl
    · exfalso
      simp [decodePoint, valid] at decoded
  intro coin
  exact ⟨finalSet, xsOf source u, crtOffDecomp source u off⟩

end Decomp

end

end Kriterion.CRT.Privacy.OffDecomp
