/-
**The finals are fresh on the curve** (the named input
`Flags.CrtOnFinalFresh` of `Flags/TouchSplit.lean`).

After the collector programs the private state stores exactly the full replay's inputs (`Contain.containment`), which
are never digest labels (family 8) nor finals (family 9). The shadow's digest on the curve then asks `u`'s 508 digest
labels, all fresh, and the 182 finals (two per digit) at their key, the XOR of the first blocks of the answers at the digest labels. A
family-9 point is stored at the end only if it is one of these finals, which fixes the key to the point's label part.

The bound is a generic fact about the lazy reader (`fresh_xor`): if a program asks every point of a nonempty list `S`
of fresh distinct points on every path, and `F` is a function of the answers at `S` that is the answer's first block
XOR the rest at each point of `S`, then `F` of the final answers hits any given block with mass at most `2^-128`. The
proof is by induction on the program: at the first query of a point of `S` the answer is uniform, and the rest of `F`
is either constant (the last point of `S`) or handled by the induction hypothesis at the shifted target.

* `fresh_xor`: the generic bound;
* **`crtOnFinalFresh : Flags.CrtOnFinalFresh`**.
-/

import Proof.Privacy.CRT.Flags.TouchSplit
import Proof.Privacy.CRT.Glue.OnDecomp
import Proof.Correctness.CRT.TreeSteps

namespace Kriterion.CRT.Privacy.Flags.OnFresh

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.Align (asked)
open Kriterion.CRT.Privacy.PublicFirst (storedPoints)
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-! ### 1. The lazy reader -/

section Lazy

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- The answer a state stores at a point (`(0, 0)` if none). -/
def ansAt (s : LazyOracle.State FI EI) (x : BaseField) : Block × Block :=
  ((s.hash.lookup x).map Laws.hashValue).getD (0, 0)

/-- The same, read at a natural input. -/
def ansN (s : LazyOracle.State FI EI) : HashN := fun n => ansAt s (n : BaseField)

theorem ansAt_of_lookup {s : LazyOracle.State FI EI} {x : BaseField} {v : Fin (Fintype.card (Block × Block))}
    (h : s.hash.lookup x = some v) : ansAt s x = Laws.hashValue v := by
  unfold ansAt
  rw [h]
  rfl

theorem hashValue_equiv (b : Block × Block) : Laws.hashValue (Fintype.equivFin (Block × Block) b) = b :=
  (Fintype.equivFin (Block × Block)).symm_apply_apply b

/-- **One lazy read**: the answer is stored at the point, old lookups are kept, and only the point is new. -/
theorem lazyReader_support (n : ℕ) (σ : LazyOracle.State FI EI) (a : (Block × Block) × LazyOracle.State FI EI)
    (member : a ∈ (lazyReader n σ).support) :
    a.2.hash.lookup (n : BaseField) = some (Fintype.equivFin (Block × Block) a.1) ∧
      (∀ y v, σ.hash.lookup y = some v → a.2.hash.lookup y = some v) ∧
      ∀ y, (a.2.hash.lookup y).isSome → (σ.hash.lookup y).isSome ∨ y = (n : BaseField) := by
  cases found : σ.hash.lookup (n : BaseField) with
  | some v =>
    rw [Laws.lazyReader_stored n σ v found, PMF.mem_support_pure_iff] at member
    subst member
    refine ⟨?_, fun y w h => h, fun y h => Or.inl h⟩
    show σ.hash.lookup (n : BaseField) = some (Fintype.equivFin (Block × Block) (Laws.hashValue v))
    rw [found]
    simp [Laws.hashValue]
  | none =>
    rw [Laws.lazyReader_fresh n σ found, PMF.mem_support_map_iff] at member
    obtain ⟨b, _, rfl⟩ := member
    refine ⟨?_, fun y w h => ?_, fun y h => ?_⟩
    · show (Laws.plantHash (n : BaseField) b σ).hash.lookup (n : BaseField) = _
      rw [Laws.plantHash_lookup, if_pos rfl]
    · show (Laws.plantHash (n : BaseField) b σ).hash.lookup y = _
      rw [Laws.plantHash_lookup]
      split_ifs with hy
      · subst hy
        rw [found] at h
        cases h
      · exact h
    · change ((Laws.plantHash (n : BaseField) b σ).hash.lookup y).isSome at h
      rw [Laws.plantHash_lookup] at h
      split_ifs at h with hy
      · exact Or.inr hy
      · exact Or.inl h

/-- A lazy run keeps every old lookup. -/
theorem run_keeps {α : Type} (P : CM α) : ∀ (σ : LazyOracle.State FI EI),
    ∀ p ∈ (runReader lazyReader P σ).support, ∀ y v, σ.hash.lookup y = some v → p.2.hash.lookup y = some v := by
  induction P with
  | pure value =>
    intro σ p member
    have same : p = (value, σ) := (PMF.mem_support_pure_iff _ _).mp member
    subst same
    exact fun _ _ h => h
  | query n next ih =>
    intro σ p member y v hv
    obtain ⟨a, inA, inRest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    exact ih a.1 a.2 p inRest y v ((lazyReader_support n σ a inA).2.1 y v hv)

/-- After a read, the final state answers the read point with the read answer. -/
theorem ansN_read {α : Type} (n : ℕ) (next : Block × Block → CM α) (σ : LazyOracle.State FI EI)
    (a : (Block × Block) × LazyOracle.State FI EI) (inA : a ∈ (lazyReader n σ).support)
    (p : α × LazyOracle.State FI EI) (inP : p ∈ (runReader lazyReader (next a.1) a.2).support) :
    ansN p.2 n = a.1 := by
  unfold ansN
  rw [ansAt_of_lookup (run_keeps (next a.1) a.2 p inP _ _ (lazyReader_support n σ a inA).1), hashValue_equiv]

theorem asked_read {α : Type} (n : ℕ) (next : Block × Block → CM α) (H : HashN) (a : Block × Block)
    (ans : H n = a) : asked H (FreeQuery.query n next) = n :: asked H (next a) := by
  show n :: asked H (next (H n)) = _
  rw [ans]

/-- **A lazy run stores only the old points and the inputs its path asks**, on the final state's answers. -/
theorem run_new {α : Type} (P : CM α) : ∀ (σ : LazyOracle.State FI EI),
    ∀ p ∈ (runReader lazyReader P σ).support, ∀ y, (p.2.hash.lookup y).isSome →
      (σ.hash.lookup y).isSome ∨ ∃ n ∈ asked (ansN p.2) P, y = (n : BaseField) := by
  induction P with
  | pure value =>
    intro σ p member y hy
    have same : p = (value, σ) := (PMF.mem_support_pure_iff _ _).mp member
    subst same
    exact Or.inl hy
  | query n next ih =>
    intro σ p member y hy
    obtain ⟨a, inA, inRest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    have facts := lazyReader_support n σ a inA
    rw [asked_read n next _ a.1 (ansN_read n next σ a inA p inRest)]
    rcases ih a.1 a.2 p inRest y hy with old | ⟨m, hm, same⟩
    · rcases facts.2.2 y old with older | same
      · exact Or.inl older
      · exact Or.inr ⟨n, List.mem_cons_self, same⟩
    · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, same⟩

end Lazy

/-! ### 2. The generic freshness bound -/

section Fresh

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

theorem card_block : Fintype.card Block = 2 ^ 128 :=
  (Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ : Block ≃ Fin (2 ^ 128))).trans
    (Fintype.card_fin _)

open Classical in
/-- A uniform answer's first block hits a given block with mass `2^-128`. -/
theorem uniform_fst (t : Block) :
    ∑' a : Block × Block, PMF.uniformOfFintype (Block × Block) a * (if a.1 = t then 1 else 0) =
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  calc ∑' a : Block × Block, PMF.uniformOfFintype (Block × Block) a * (if a.1 = t then 1 else 0)
      = ((PMF.uniformOfFintype (Block × Block)).map Prod.fst) t := by
        rw [PMF.map_apply]
        refine tsum_congr fun a => ?_
        by_cases h : a.1 = t
        · rw [if_pos h, if_pos h.symm, mul_one]
        · rw [if_neg h, if_neg (fun h' => h h'.symm), mul_zero]
    _ = PMF.uniformOfFintype Block t := by rw [Laws.uniform_map_fst]
    _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
        rw [PMF.uniformOfFintype_apply, card_block]
        norm_num

theorem tsum_le_const {β : Type} (μ : PMF β) (f : β → ℝ≥0∞) (c : ℝ≥0∞) (each : ∀ b, f b ≤ c) :
    ∑' b, μ b * f b ≤ c :=
  calc ∑' b, μ b * f b ≤ ∑' b, μ b * c := ENNReal.tsum_le_tsum fun b => mul_le_mul' le_rfl (each b)
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem outer_le_one {β : Type} (μ : PMF β) (s : Set β) : μ.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply]
  calc ∑' x, s.indicator μ x ≤ ∑' x, μ x := ENNReal.tsum_le_tsum fun x => Set.indicator_le_self s μ x
    _ = 1 := PMF.tsum_coe μ

theorem xor_solve (c a k : Block) (h : c ^^^ a = k) : a = c ^^^ k := by
  rw [← h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xor_shift (a b k : Block) : (a ^^^ b = k) ↔ (a = k ^^^ b) := by
  constructor
  · intro h
    rw [← h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro h
    rw [h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **The generic freshness bound** (see the module docstring). -/
theorem fresh_xor {α : Type} (P : CM α) : ∀ (σ : LazyOracle.State FI EI) (S : List BaseField)
    (F : (BaseField → Block × Block) → Block) (k0 : Block), S ≠ [] → S.Nodup →
    (∀ x ∈ S, σ.hash.lookup x = none) →
    (∀ G G' : BaseField → Block × Block, (∀ x ∈ S, G x = G' x) → F G = F G') →
    (∀ (G : BaseField → Block × Block), ∀ x ∈ S, F G = F (Function.update G x (0, 0)) ^^^ (G x).1) →
    (∀ p ∈ (runReader lazyReader P σ).support, ∀ x ∈ S, ∃ n ∈ asked (ansN p.2) P, (n : BaseField) = x) →
    (runReader lazyReader P σ).toOuterMeasure {p | F (ansAt p.2) = k0} ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  induction P with
  | pure value =>
    intro σ S F k0 nonempty _ _ _ _ covered
    exfalso
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil S nonempty
    obtain ⟨n, hn, _⟩ := covered (value, σ) ((PMF.mem_support_pure_iff _ _).mpr rfl) x hx
    exact List.not_mem_nil hn
  | query n next ih =>
    intro σ S F k0 nonempty nodup fresh ignores xorAt covered
    -- coverage of the continuation, off the read point
    have coveredNext : ∀ a ∈ (lazyReader n σ).support, ∀ p ∈ (runReader lazyReader (next a.1) a.2).support,
        ∀ x ∈ S, x ≠ (n : BaseField) → ∃ m ∈ asked (ansN p.2) (next a.1), (m : BaseField) = x := by
      intro a inA p inP x hx ne
      have whole : p ∈ (runReader lazyReader (FreeQuery.query n next) σ).support :=
        (PMF.mem_support_bind_iff _ _ _).mpr ⟨a, inA, inP⟩
      obtain ⟨m, hm, same⟩ := covered p whole x hx
      rw [asked_read n next _ a.1 (ansN_read n next σ a inA p inP)] at hm
      rcases List.mem_cons.mp hm with rfl | later
      · exact absurd same.symm ne
      · exact ⟨m, later, same⟩
    show ((lazyReader n σ).bind fun a => runReader lazyReader (next a.1) a.2).toOuterMeasure _ ≤ _
    cases found : σ.hash.lookup (n : BaseField) with
    | some v =>
      have notS : ∀ x ∈ S, x ≠ (n : BaseField) := fun x hx same => by
        have := fresh x hx
        rw [same, found] at this
        cases this
      have inA : (Laws.hashValue v, σ) ∈ (lazyReader n σ).support := by
        rw [Laws.lazyReader_stored n σ v found]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      rw [Laws.lazyReader_stored n σ v found, PMF.pure_bind]
      exact ih (Laws.hashValue v) σ S F k0 nonempty nodup fresh ignores xorAt fun p inP x hx =>
        coveredNext _ inA p inP x hx (notS x hx)
    | none =>
      have inA : ∀ b : Block × Block, (b, Laws.plantHash (n : BaseField) b σ) ∈ (lazyReader n σ).support := by
        intro b
        rw [Laws.lazyReader_fresh n σ found]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨b, PMF.mem_support_uniformOfFintype b, rfl⟩
      have plantLookup : ∀ (b : Block × Block) (x : BaseField), x ≠ (n : BaseField) →
          (Laws.plantHash (n : BaseField) b σ).hash.lookup x = σ.hash.lookup x := by
        intro b x ne
        rw [Laws.plantHash_lookup, if_neg ne]
      have answered : ∀ (b : Block × Block),
          ∀ p ∈ (runReader lazyReader (next b) (Laws.plantHash (n : BaseField) b σ)).support,
            ansAt p.2 (n : BaseField) = b := by
        intro b p inP
        have := ansN_read n next σ _ (inA b) p inP
        exact this
      rw [Laws.lazyReader_fresh n σ found, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
      by_cases inS : (n : BaseField) ∈ S
      · -- the read point is in `S`: the answer's first block shifts the target
        set x0 : BaseField := (n : BaseField) with hx0
        have memErase : ∀ x, x ∈ S.erase x0 ↔ x ≠ x0 ∧ x ∈ S := fun x => nodup.mem_erase_iff
        by_cases empty : S.erase x0 = []
        · -- `x0` is the last point: the rest of `F` is constant
          have onlyX0 : ∀ x ∈ S, x = x0 := fun x hx => by
            by_contra ne
            have : x ∈ S.erase x0 := (memErase x).mpr ⟨ne, hx⟩
            rw [empty] at this
            exact List.not_mem_nil this
          set c : Block := F (Function.update (fun _ => ((0 : Block), (0 : Block))) x0 (0, 0)) with hc
          have rest : ∀ G : BaseField → Block × Block, F (Function.update G x0 (0, 0)) = c := by
            intro G
            refine ignores _ _ fun x hx => ?_
            rw [onlyX0 x hx, Function.update_self, Function.update_self]
          have each : ∀ b : Block × Block,
              (runReader lazyReader (next b) (Laws.plantHash x0 b σ)).toOuterMeasure
                  {p | F (ansAt p.2) = k0} ≤ if b.1 = c ^^^ k0 then 1 else 0 := by
            intro b
            by_cases hb : b.1 = c ^^^ k0
            · rw [if_pos hb]
              exact outer_le_one _ _
            · rw [if_neg hb]
              refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_)
              rw [Set.disjoint_left]
              intro p inP hit
              have value : F (ansAt p.2) = c ^^^ b.1 := by
                rw [xorAt (ansAt p.2) x0 inS, rest, show ansAt p.2 x0 = b from answered b p inP]
              exact hb (xor_solve c b.1 k0 (value.symm.trans hit))
          refine le_trans (ENNReal.tsum_le_tsum fun b => mul_le_mul' le_rfl ?_) (le_of_eq (uniform_fst (c ^^^ k0)))
          exact each b
        · -- more points of `S` remain: the induction hypothesis at the shifted target
          refine tsum_le_const _ _ _ fun b => ?_
          show (runReader lazyReader (next b) (Laws.plantHash (n : BaseField) b σ)).toOuterMeasure
            {p | F (ansAt p.2) = k0} ≤ _
          have bound := ih b (Laws.plantHash (n : BaseField) b σ) (S.erase x0)
            (fun G => F (Function.update G x0 (0, 0))) (k0 ^^^ b.1) empty (nodup.erase x0)
            (fun x hx => by
              obtain ⟨ne, hxS⟩ := (memErase x).mp hx
              rw [plantLookup b x ne]
              exact fresh x hxS)
            (fun G G' agree => ignores _ _ fun x hx => by
              by_cases hx' : x = x0
              · rw [hx', Function.update_self, Function.update_self]
              · rw [Function.update_of_ne hx', Function.update_of_ne hx']
                exact agree x ((memErase x).mpr ⟨hx', hx⟩))
            (fun G x hx => by
              obtain ⟨ne, hxS⟩ := (memErase x).mp hx
              show F (Function.update G x0 (0, 0)) = F (Function.update (Function.update G x (0, 0)) x0 (0, 0)) ^^^ (G x).1
              rw [xorAt (Function.update G x0 (0, 0)) x hxS, Function.update_of_ne ne,
                Function.update_comm (Ne.symm ne)])
            (fun p inP x hx => coveredNext _ (inA b) p inP x ((memErase x).mp hx).2 ((memErase x).mp hx).1)
          refine le_trans (PMF.toOuterMeasure_mono _ ?_) bound
          intro p ⟨hit, inP⟩
          show F (Function.update (ansAt p.2) x0 (0, 0)) = k0 ^^^ b.1
          have value := xorAt (ansAt p.2) x0 inS
          rw [show ansAt p.2 x0 = b from answered b p inP] at value
          exact (xor_shift _ _ _).mp (value.symm.trans hit)
      · -- the read point is off `S`
        refine tsum_le_const _ _ _ fun b => ?_
        show (runReader lazyReader (next b) (Laws.plantHash (n : BaseField) b σ)).toOuterMeasure
          {p | F (ansAt p.2) = k0} ≤ _
        exact ih b (Laws.plantHash (n : BaseField) b σ) S F k0 nonempty nodup
          (fun x hx => by
            rw [plantLookup b x fun same => inS (same ▸ hx)]
            exact fresh x hx)
          ignores xorAt
          (fun p inP x hx => coveredNext _ (inA b) p inP x hx fun same => inS (same ▸ hx))

end Fresh

/-! ### 3. The shadow's digest on the curve -/

section Digest

open Kriterion.CRT.Privacy.Contain
open Kriterion.ArgoMAC.PlanB (digitCount)

theorem lookup_isSome_of_mem {V : Type} :
    ∀ (l : List (BaseField × V)) (x : BaseField), x ∈ l.map Prod.fst → (l.lookup x).isSome
  | [], x, h => by simp at h
  | (k, v) :: rest, x, h => by
    by_cases hx : x = k
    · subst hx
      simp [List.lookup]
    · have later : x ∈ rest.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        exact h.resolve_left hx
      have := lookup_isSome_of_mem rest x later
      have hb : (x == k) = false := by simpa using hx
      simp only [List.lookup, hb]
      exact this

theorem xorFold_off {n : ℕ} (j : Fin n) (F G : Fin n → Block) (agree : ∀ i, i ≠ j → F i = G i) :
    xorFold F = xorFold G ^^^ G j ^^^ F j := by
  have e := SliceC.xorFoldExcept_congr j F G agree
  rw [SliceC.xorFoldExcept_eq, SliceC.xorFoldExcept_eq] at e
  rw [← e, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_zero' (a : Block) : a ^^^ 0 = a := BitVec.xor_zero

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

variable [FieldCertificate] [GroupCertificate] (source : Kriterion.CRT.Entry.Source) (u : AffineInput)

/-- The digest-label point of coordinate `c`, position `p`. -/
def labelPoint (c : Fin 2) (p : Fin coordinateBitCount) : BaseField :=
  ((hashInput (Kriterion.CRT.Entry.labelsOf (Kriterion.CRT.Entry.labels source u) c p)
    (digestLabelTag c.val p.val (coordBit u c p.val)) : ℕ) : BaseField)

/-- The digest key of the answers at the digest-label points. -/
def keyF (G : BaseField → Block × Block) : Block :=
  digestKey (fun m => G (m : BaseField)) coordinateBitCount
    (Kriterion.CRT.Entry.labelsOf (Kriterion.CRT.Entry.labels source u)) u

theorem keyF_eq (G : BaseField → Block × Block) :
    keyF source u G = xorFold fun c : Fin 2 => xorFold fun p : Fin coordinateBitCount =>
      (G (labelPoint source u c p)).1 := rfl

theorem mem_dsOf {x : BaseField} (hx : x ∈ dsOf source u) : ∃ c p, x = labelPoint source u c p := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c, p, rfl⟩ := mem_digestList hn
  exact ⟨c, p, rfl⟩

theorem labelPoint_mem (c : Fin 2) (p : Fin coordinateBitCount) : labelPoint source u c p ∈ dsOf source u := by
  refine List.mem_map.mpr ⟨_, ?_, rfl⟩
  unfold digestList
  exact List.mem_flatMap.mpr ⟨c, List.mem_finRange _,
    List.mem_flatMap.mpr ⟨p, List.mem_finRange _, List.mem_singleton_self _⟩⟩

theorem labelPoint_inj {c c' : Fin 2} {p p' : Fin coordinateBitCount}
    (same : labelPoint source u c p = labelPoint source u c' p') : c = c' ∧ p = p' :=
  OnDecompCrt.digest_tag_inj _ u (congrArg tagOfInput same)

theorem keyF_ignores :
    ∀ G G' : BaseField → Block × Block, (∀ x ∈ dsOf source u, G x = G' x) → keyF source u G = keyF source u G' := by
  intro G G' agree
  rw [keyF_eq, keyF_eq]
  exact congrArg xorFold (funext fun c => congrArg xorFold (funext fun p => by
    rw [agree _ (labelPoint_mem source u c p)]))

theorem keyF_xor : ∀ (G : BaseField → Block × Block), ∀ x ∈ dsOf source u,
    keyF source u G = keyF source u (Function.update G x (0, 0)) ^^^ (G x).1 := by
  intro G x hx
  obtain ⟨c0, p0, rfl⟩ := mem_dsOf source u hx
  rw [keyF_eq, keyF_eq, fold2_off (fun c p => (G (labelPoint source u c p)).1)
    (fun c p => (Function.update G (labelPoint source u c0 p0) (0, 0) (labelPoint source u c p)).1) c0 p0
    fun c p ne => by
      rw [Function.update_of_ne fun same => ne (by
        obtain ⟨h1, h2⟩ := labelPoint_inj source u same
        rw [h1, h2])]]
  simp only [Function.update_self]
  rw [xor_zero']

theorem dsOf_ne_nil : dsOf source u ≠ [] := List.ne_nil_of_mem (labelPoint_mem source u 0 0)

theorem dsOf_family {x : BaseField} (hx : x ∈ dsOf source u) : tagFamily (x.val / 2 ^ 128) = 8 := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  obtain ⟨labelled, fam, _⟩ := digestList_labelled hn
  rw [labelled.val]
  exact fam

/-- The inputs the shadow's digest asks: `u`'s digest labels, then the finals at the digest key. -/
theorem asked_shadow (H : HashN) :
    asked H (H8.crtShadowOnCurve source u) = digestList (Kriterion.CRT.Entry.labels source u) u ++
      OffDecomp.finalsAt (digestKey H coordinateBitCount
        (Kriterion.CRT.Entry.labelsOf (Kriterion.CRT.Entry.labels source u)) u) := by
  show asked H (digestEvalM coordinateBitCount digitCount
      (Kriterion.CRT.Entry.labelsOf (Kriterion.CRT.Entry.labels source u)) u
      (fun o => (Kriterion.CRT.Entry.publish source).exception.get o) >>= fun _ => pure ()) = _
  rw [Align.asked_bind, Align.asked_pure, List.append_nil, Align.asked_digestEvalM, digestList_eq]
  rfl

theorem inv_eq_ofReal : ((2 : ℝ≥0∞) ^ 128)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- **The on-curve freshness at one source, with the global instances.** -/
theorem onFinalFresh_at (scalar : NonZeroScalar) (Q : Point)
    (defined : (Instance.crtEntry.scheme inferInstance inferInstance).function scalar u = some Q)
    (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (installed : LazyOracle.State Empty Empty) (complete : drawn.map Prod.fst = collectorList)
    (done : programHashAll (programRequests (Laws.outOf Instance.crtEntry table source u).key drawn)
      (Laws.finOf Instance.crtEntry table source u) = some installed)
    (x : BaseField) (fam : tagFamily (x.val / 2 ^ 128) = 9) :
    (runReader lazyReader (H8.crtShadowOnCurve source u) installed).toOuterMeasure {p | x ∈ storedPoints p.2}
      ≤ ENNReal.ofReal (1 / 2 ^ 128) := by
  have valid := OnDecompCrt.valid_of_function defined
  have none_of : ∀ y : BaseField, (tagFamily (y.val / 2 ^ 128) = 8 ∨ tagFamily (y.val / 2 ^ 128) = 9) →
      installed.hash.lookup y = none := by
    intro y fy
    rw [containment source u valid table drawn installed complete done y, replayEntries_eq, install_empty_lookup,
      if_neg]
    intro member
    obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨labelled, visible, fam8⟩ := entryReplay_facts _ u _ valid _ n inside
    rw [labelled.val] at fy
    rcases fy with f8 | f9
    · exact fam8 f8
    · rw [Paths.SameVisible.visTag_final f9] at visible
      cases visible
  have bound := fresh_xor (H8.crtShadowOnCurve source u) installed (dsOf source u) (keyF source u)
    (BitVec.ofNat 128 (x.val % 2 ^ 128)) (dsOf_ne_nil source u) (OnDecompCrt.ds_nodup source u).of_map
    (fun y hy => none_of y (Or.inl (dsOf_family source u hy)))
    (keyF_ignores source u) (keyF_xor source u)
    (fun p _ y hy => by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
      exact ⟨n, by rw [asked_shadow]; exact List.mem_append_left _ hn, rfl⟩)
  rw [← inv_eq_ofReal]
  refine le_trans (PMF.toOuterMeasure_mono _ ?_) bound
  intro p ⟨stored, inP⟩
  have isSome : (p.2.hash.lookup x).isSome := lookup_isSome_of_mem _ x stored
  rcases run_new _ installed p inP x isSome with old | ⟨m, hm, same⟩
  · rw [none_of x (Or.inr fam)] at old
    cases old
  · rw [asked_shadow, List.mem_append] at hm
    rcases hm with lab | final
    · obtain ⟨labelled, f8, _⟩ := digestList_labelled lab
      rw [same, labelled.val] at fam
      omega
    · obtain ⟨small, _⟩ := OffDecomp.final_small _ m final
      unfold OffDecomp.finalsAt at final
      obtain ⟨o, -, rfl⟩ := Align.mem_finals final
      show digestKey (ansN p.2) coordinateBitCount
        (Kriterion.CRT.Entry.labelsOf (Kriterion.CRT.Entry.labels source u)) u = BitVec.ofNat 128 (x.val % 2 ^ 128)
      generalize digestKey (ansN p.2) coordinateBitCount
        (Kriterion.CRT.Entry.labelsOf (Kriterion.CRT.Entry.labels source u)) u = key at same small
      have hv : x.val = hashInput key (digestFinalTag o) := by rw [same]; exact small.1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, hv]
      unfold hashInput
      have lt := key.isLt
      omega

end Digest

/-! ### 4. The named input -/

/-- The same, with any instances for `Empty` (the named input's are `Fintype.ofFinite` and `Classical.decEq`). -/
theorem onFinalFresh_gen [FieldCertificate] [GroupCertificate] [fe : Fintype Empty] [de : DecidableEq Empty]
    (scalar : NonZeroScalar) (u : AffineInput) :
    ∀ Q : Point, (Instance.crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
    ∀ (source : (PublicFirst.viewHere Instance.crtEntry).Source) (table : TagTable)
      (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State Empty Empty),
      drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (Laws.outOf Instance.crtEntry table source u).key drawn)
          (Laws.finOf Instance.crtEntry table source u) = some installed →
      ∀ x : BaseField, tagFamily (x.val / 2 ^ 128) = 9 →
        (runReader lazyReader (H8.crtShadowOnCurve source u) installed).toOuterMeasure {p | x ∈ storedPoints p.2}
          ≤ ENNReal.ofReal (1 / 2 ^ 128) := by
  have one : de = instDecidableEqEmpty := Subsingleton.elim _ _
  have two : fe = Fintype.instEmpty := Subsingleton.elim _ _
  subst one two
  intro Q defined source table drawn installed complete done x fam
  exact onFinalFresh_at source u scalar Q defined table drawn installed complete done x fam

end

end Kriterion.CRT.Privacy.Flags.OnFresh

namespace Kriterion.CRT.Privacy.Flags

/-- **The finals are fresh on the curve.** -/
theorem crtOnFinalFresh : CrtOnFinalFresh := by
  intro field group scalar u
  exact @OnFresh.onFinalFresh_gen field group (Fintype.ofFinite Empty) (Classical.decEq Empty) scalar u

end Kriterion.CRT.Privacy.Flags
