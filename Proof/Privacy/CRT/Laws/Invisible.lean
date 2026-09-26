/-
**Tools for (B) off the curve: table answers at invisible positions are invisible**.

Off the curve `M'` stores the table's answers at every input its shadow reads, the invisible ones included. This file
gives the two tools that remove them:

* `IndepS.tsum`: an independent read in expectation form (`∑ μ · f(read, ·) = ∑ ν · ∑ μ · f(v, ·)` for `f` ignoring
  the read's positions);
* `queryAll`, `transcript_queryAll`, `avoidPath_queryAll`: the program asking a list of inputs, its transcript on a
  table and its avoidance of a state;
* **`plant_table_invisible`**: planting a uniform table's answers at inputs with distinct tags that a state does not
  store is invisible to a later lazy run (`install_table_invisible`).
-/

import Proof.Privacy.CRT.Laws.TableIndep
import Proof.Privacy.CRT.Laws.Rest
import Proof.Privacy.CRT.Laws.ReplayOff
import Proof.Privacy.CRT.Laws.Middle

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.CRT.Privacy.PublicFirst (tsum_bind_mul tsum_map_mul storedPoints mem_keys_of_lookup
  lookup_isSome_of_mem)
open scoped ENNReal

noncomputable section

variable {FI EI : Type}

/-! ### 1. Independence in expectation form -/

theorem tsum_prodLaw {A B : Type} (ν₁ : PMF A) (ν₂ : PMF B) (F : A × B → ℝ≥0∞) :
    ∑' z, prodLaw ν₁ ν₂ z * F z = ∑' a, ν₁ a * ∑' b, ν₂ b * F (a, b) := by
  unfold prodLaw
  rw [tsum_bind_mul]
  refine tsum_congr fun a => ?_
  rw [tsum_map_mul]

/-- **An independent read in expectation form.** -/
theorem IndepS.tsum {V : Type} {μ : PMF TagTable} {P : Set (Fin (2 ^ 40))} {ν : PMF V} {read : TagTable → V}
    (indep : IndepS μ P ν read) (f : V → TagTable → ℝ≥0∞) (ignores : ∀ v, Ignores P (f v)) :
    ∑' T, μ T * f (read T) T = ∑' v, ν v * ∑' T, μ T * f v T := by
  classical
  let rest : TagTable → TagTable := fun T p => if p ∈ P then (0, 0) else T p
  have restIgnores : Ignores P rest := fun T T' agree => funext fun p => by
    by_cases hp : p ∈ P
    · simp only [rest, if_pos hp]
    · simp only [rest, if_neg hp]
      exact agree p hp
  have throughRest : ∀ v T, f v T = f v (rest T) := fun v T =>
    ignores v T (rest T) fun p hp => by simp only [rest, if_neg hp]
  have joint := indep.joint rest restIgnores
  calc ∑' T, μ T * f (read T) T = ∑' T, μ T * (fun z : V × TagTable => f z.1 z.2) (read T, rest T) :=
        tsum_congr fun T => by rw [throughRest (read T) T]
    _ = ∑' z, (μ.map fun T => (read T, rest T)) z * (fun z : V × TagTable => f z.1 z.2) z :=
        (tsum_map_mul μ (fun T => (read T, rest T)) (fun z : V × TagTable => f z.1 z.2)).symm
    _ = ∑' v, ν v * ∑' r, (μ.map rest) r * f v r := by
        rw [joint, tsum_prodLaw]
    _ = ∑' v, ν v * ∑' T, μ T * f v T := by
        refine tsum_congr fun v => congrArg _ ?_
        rw [tsum_map_mul]
        exact tsum_congr fun T => by rw [← throughRest v T]

/-! ### 2. The program asking a list of inputs -/

/-- The program asking each input of a list, in order. -/
def queryAll : (xs : List BaseField) → QueryProgram (publicOracleSpec FI EI) Unit xs.length
  | [] => .pure ()
  | x :: rest => .query (PublicQuery.hash x) fun _ => queryAll rest

theorem transcript_queryAll {C : Type} (c : BaseField → C) (F : C → Block × Block) :
    ∀ xs : List BaseField, programTranscript (publicAnswer (coordOracle (FI := FI) (EI := EI) c F)) (queryAll xs) =
      xs.map fun x => (⟨.hash x, F (c x)⟩ : Entry FI EI)
  | [] => rfl
  | x :: rest => by
      show ⟨.hash x, _⟩ :: programTranscript _ (queryAll rest) = _
      rw [transcript_queryAll c F rest]
      rfl

theorem avoidPath_queryAll {C : Type} (c : BaseField → C) (σ₁ : LazyOracle.State FI EI) :
    ∀ (xs seen : List BaseField), (∀ x ∈ xs, σ₁.hash.lookup x = none) → (xs.map c).Nodup →
      (∀ x ∈ xs, ∀ y ∈ seen, c x ≠ c y) → AvoidPath c σ₁ seen (queryAll (FI := FI) (EI := EI) xs)
  | [], seen, _, _, _ => AvoidPath.pure seen ()
  | x :: rest, seen, absent, nodup, apart => by
      have restNodup : (rest.map c).Nodup := (List.nodup_cons.mp nodup).2
      have headNew : c x ∉ rest.map c := (List.nodup_cons.mp nodup).1
      refine AvoidPath.hash seen x _ (absent x List.mem_cons_self)
        (fun y hy same => absurd same (apart x List.mem_cons_self y hy)) fun _ => ?_
      refine avoidPath_queryAll c σ₁ rest (x :: seen) (fun z hz => absent z (List.mem_cons_of_mem _ hz)) restNodup ?_
      intro z hz y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun same => headNew (same ▸ List.mem_map_of_mem hz)
      · exact apart z (List.mem_cons_of_mem _ hz) y hy

/-! ### 3. Planting a uniform table is invisible -/

/-- The entries holding a table's answers at a list of inputs. -/
def tableEntries (table : TagTable) (xs : List BaseField) : List (Entry FI EI) :=
  xs.map fun x => ⟨.hash x, table (tagOfInput x)⟩

/-- **Planting a uniform table's answers at inputs with distinct tags that a state does not store is invisible.** -/
theorem plant_table_invisible [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] {Result : Type}
    {budget : ℕ} (A : OracleProgram (publicOracleSpec FI EI) Result budget) (σ₁ : LazyOracle.State FI EI)
    (xs : List BaseField) (absent : ∀ x ∈ xs, σ₁.hash.lookup x = none) (distinct : (xs.map tagOfInput).Nodup)
    (r : Result) :
    ∑' table, PMF.uniformOfFintype TagTable table *
        ((LazyOracle.run A (Privacy.installEntries (tableEntries table xs) σ₁)).map Prod.fst) r =
      ((LazyOracle.run A σ₁).map Prod.fst) r := by
  have law := install_table_invisible tagOfInput σ₁
    (avoidPath_queryAll tagOfInput σ₁ xs [] absent distinct fun _ _ _ hy => absurd hy List.not_mem_nil) A
  rw [← law, PMF.bind_apply]
  refine tsum_congr fun table => ?_
  rw [transcript_queryAll]
  rfl

/-! ### 4. Stored inputs of installations -/

section Stored

variable [DecidableEq FI] [DecidableEq EI]

theorem installEntries_isSome : ∀ (l : List (Entry FI EI)), HashEntries l → ∀ (σ : LazyOracle.State FI EI) x,
    ((Privacy.installEntries l σ).hash.lookup x).isSome ↔ ((σ.hash.lookup x).isSome ∨ x ∈ l.map entryInput)
  | [], _, σ, x => by
      rw [List.map_nil]
      simp only [List.not_mem_nil, or_false]
      exact Iff.rfl
  | e :: rest, hashes, σ, x => by
      obtain ⟨y, hy⟩ := hashes e List.mem_cons_self
      obtain ⟨q, a⟩ := e
      simp only at hy
      subst hy
      rw [installEntries_cons, installEntries_isSome rest (fun e' m => hashes e' (List.mem_cons_of_mem _ m)),
        installOne_hash σ y a]
      have input : entryInput (⟨.hash y, a⟩ : Entry FI EI) = y := rfl
      rw [List.map_cons, List.mem_cons, input]
      split
      · rw [plant_isSome σ y x a]
        tauto
      · rename_i stored
        have yStored : (σ.hash.lookup y).isSome := Option.ne_none_iff_isSome.mp stored
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl h
          · subst h
            exact Or.inl yStored
          · exact Or.inr h

theorem installEntries_append (l₁ l₂ : List (Entry FI EI)) (σ : LazyOracle.State FI EI) :
    Privacy.installEntries (l₁ ++ l₂) σ = Privacy.installEntries l₂ (Privacy.installEntries l₁ σ) := by
  unfold Privacy.installEntries
  exact List.foldl_append

omit [DecidableEq FI] [DecidableEq EI] in
theorem tableEntries_inputs (table : TagTable) (xs : List BaseField) :
    (tableEntries (FI := FI) (EI := EI) table xs).map entryInput = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      show entryInput (⟨.hash x, table (tagOfInput x)⟩ : Entry FI EI) :: (tableEntries table rest).map entryInput = _
      rw [ih]
      rfl

omit [DecidableEq FI] [DecidableEq EI] in
theorem tableEntries_hash (table : TagTable) (xs : List BaseField) :
    HashEntries (tableEntries (FI := FI) (EI := EI) table xs) := fun e he => by
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
  exact ⟨x, rfl⟩

omit [DecidableEq FI] [DecidableEq EI] in
theorem mem_storedPoints_iff (state : LazyOracle.State FI EI) (x : BaseField) :
    x ∈ storedPoints state ↔ (state.hash.lookup x).isSome := by
  constructor
  · exact lookup_isSome_of_mem state.hash x
  · intro stored
    obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp stored
    exact mem_keys_of_lookup state.hash x v found

end Stored

/-! ### 5. The swapped table at positions outside the sites -/

/-- The table at the positions `P`, `(0, 0)` elsewhere. -/
def resP (P : Finset (Fin (2 ^ 40))) (table : TagTable) : TagTable := fun p => if p ∈ P then table p else (0, 0)

/-- **At positions outside every site the swapped table has the uniform table's law.** -/
theorem swapped_map_resP (layout : SiteLayout) (P : Finset (Fin (2 ^ 40)))
    (away : ∀ p ∈ P, ∀ site ∈ layout.sites, p ∉ (siteTags layout site).map tagPos) :
    (swappedTableLaw layout).map (resP P) = (PMF.uniformOfFintype TagTable).map (resP P) := by
  classical
  let noSites : SiteLayout := ⟨[], layout.answers, layout.law⟩
  have h₁ := (indep_swapped_positions layout P.toList (Finset.nodup_toList P)
    fun p hp => away p (Finset.mem_toList.mp hp)).map_read
  have h₂ := (indep_swapped_positions noSites P.toList (Finset.nodup_toList P)
    fun _ _ _ member => absurd member List.not_mem_nil).map_read
  have uniformEq : swappedTableLaw noSites = PMF.uniformOfFintype TagTable := rfl
  rw [uniformEq] at h₂
  let rebuild : List (Block × Block) → TagTable := fun l p =>
    if p ∈ P then l.getD (P.toList.idxOf p) (0, 0) else (0, 0)
  have factor : resP P = rebuild ∘ fun T => P.toList.map T := funext fun T => funext fun p => by
    by_cases hp : p ∈ P
    · have lt := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr hp)
      simp only [resP, rebuild, Function.comp_apply, if_pos hp, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem lt, List.getElem_idxOf lt, Option.map_some, Option.getD_some]
    · simp only [resP, rebuild, Function.comp_apply, if_neg hp]
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, h₁, h₂]

/-- **The table's answers at inputs with distinct tags in `P`, fresh in a state, are invisible**, under the swapped
table's law at `P`. -/
theorem uniform_part_invisible [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] (layout : SiteLayout)
    (P : Finset (Fin (2 ^ 40))) (away : ∀ p ∈ P, ∀ site ∈ layout.sites, p ∉ (siteTags layout site).map tagPos)
    {Result : Type} {budget : ℕ} (A : OracleProgram (publicOracleSpec FI EI) Result budget)
    (σ₁ : LazyOracle.State FI EI) (xs : List BaseField) (absent : ∀ x ∈ xs, σ₁.hash.lookup x = none)
    (distinct : (xs.map tagOfInput).Nodup) (inP : ∀ x ∈ xs, tagOfInput x ∈ P) (r : Result) :
    ∑' w, ((swappedTableLaw layout).map (resP P)) w *
        ((LazyOracle.run A (Privacy.installEntries (tableEntries w xs) σ₁)).map Prod.fst) r =
      ((LazyOracle.run A σ₁).map Prod.fst) r := by
  rw [swapped_map_resP layout P away, tsum_map_mul]
  have same : ∀ T, tableEntries (FI := FI) (EI := EI) (resP P T) xs = tableEntries T xs := fun T =>
    List.map_congr_left fun x hx => by simp only [resP, if_pos (inP x hx)]
  simp only [same]
  exact plant_table_invisible A σ₁ xs absent distinct r

/-- **Planting at inputs a state may already store**: the stored ones are skipped, so only the fresh ones count. -/
theorem installEntries_tableEntries_filter [DecidableEq FI] [DecidableEq EI] (w : TagTable) :
    ∀ (xs : List BaseField), xs.Nodup → ∀ σ : LazyOracle.State FI EI,
      Privacy.installEntries (tableEntries w xs) σ =
        Privacy.installEntries (tableEntries w (xs.filter fun x => σ.hash.lookup x = none)) σ
  | [], _, σ => rfl
  | x :: rest, nodup, σ => by
      have restNodup := (List.nodup_cons.mp nodup).2
      have notMem := (List.nodup_cons.mp nodup).1
      show Privacy.installEntries (tableEntries w rest) (installOne σ ⟨.hash x, w (tagOfInput x)⟩) = _
      rw [installOne_hash σ x (w (tagOfInput x))]
      by_cases fresh : σ.hash.lookup x = none
      · rw [if_pos fresh, List.filter_cons_of_pos (by simpa using fresh)]
        show _ = Privacy.installEntries (tableEntries w (rest.filter _))
          (installOne σ ⟨.hash x, w (tagOfInput x)⟩)
        rw [installOne_hash σ x (w (tagOfInput x)), if_pos fresh,
          installEntries_tableEntries_filter w rest restNodup]
        congr 2
        refine List.filter_congr fun y hy => ?_
        have ne : y ≠ x := fun same => notMem (same ▸ hy)
        rw [plantHash_lookup, if_neg ne]
      · rw [if_neg fresh, List.filter_cons_of_neg (by simpa using fresh)]
        exact installEntries_tableEntries_filter w rest restNodup σ

/-- **The swapped table's answers at inputs with distinct tags in `P` are invisible**, whether or not the state
already stores them. -/
theorem uniform_part_invisible' [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] (layout : SiteLayout)
    (P : Finset (Fin (2 ^ 40))) (away : ∀ p ∈ P, ∀ site ∈ layout.sites, p ∉ (siteTags layout site).map tagPos)
    {Result : Type} {budget : ℕ} (A : OracleProgram (publicOracleSpec FI EI) Result budget)
    (σ₁ : LazyOracle.State FI EI) (xs : List BaseField) (distinct : (xs.map tagOfInput).Nodup)
    (inP : ∀ x ∈ xs, tagOfInput x ∈ P) (r : Result) :
    ∑' w, ((swappedTableLaw layout).map (resP P)) w *
        ((LazyOracle.run A (Privacy.installEntries (tableEntries w xs) σ₁)).map Prod.fst) r =
      ((LazyOracle.run A σ₁).map Prod.fst) r := by
  have nodup : xs.Nodup := distinct.of_map _
  simp only [installEntries_tableEntries_filter _ xs nodup σ₁]
  refine uniform_part_invisible layout P away A σ₁ _ (fun x hx => ?_) ?_ (fun x hx => inP x (List.mem_of_mem_filter hx)) r
  · simpa using (List.mem_filter.mp hx).2
  · exact distinct.sublist (List.Sublist.map _ List.filter_sublist)

end

end Kriterion.CRT.Privacy.Laws
