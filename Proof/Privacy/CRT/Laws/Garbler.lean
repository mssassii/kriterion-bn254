/-
**P6a2: `G1U`'s stage 2 on the table**.

`G1U` installs, at the input choice, the garbler entries its reach meets (`hiddenDeletedHybrid`): the garbler's
transcript on `tableOracle T`, filtered by membership in the reach's transcript, in the garbler's order. This file
shows that the adversary's stage 2 then depends on the table only through what the reach reads:

* `run_lookup_congr`: a lazy run's output law depends on its state only through the permutation parts and the hash
  table's lookup function;
* `installEntries_perm`: hash entries at pairwise distinct inputs install to the same lookups in any order (by
  `installOne_swap` and `List.Perm` induction);
* `transcript_congr`: a query program's transcript and result depend on the answer function only along its own path;
  `tableTranscript_congr`: on the table oracle, only through the table at the tags of that path (`pathTags`);
* `visible_perm`: if every reach query is a garbler query (containment, off the coincidence flag) and both ask each
  query once, the garbler entries the reach meets are the reach's transcript up to order;
* **`stage2_visible_eq_reach`**: so `G1U`'s stage 2 after installing the visible entries has the output law of the
  stage 2 after installing the reach's own transcript, which is a function of the published value, `u`'s labels and
  the table on the reach's tags.
-/

import Proof.Privacy.CRT.Laws.Plant

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.OperationalOracle

noncomputable section

variable {FI EI : Type}

/-! ### 1. A lazy run reads its state through lookups -/

/-- Two lazy states with the same permutation parts and the same hash lookup function. -/
def SameLookup (σ σ' : LazyOracle.State FI EI) : Prop :=
  σ.fixed = σ'.fixed ∧ σ.enc = σ'.enc ∧ ∀ x, σ.hash.lookup x = σ'.hash.lookup x

theorem SameLookup.plant {σ σ' : LazyOracle.State FI EI} (same : SameLookup σ σ') (x : BaseField)
    (a : Block × Block) : SameLookup (plantHash x a σ) (plantHash x a σ') := by
  refine ⟨same.1, same.2.1, fun y => ?_⟩
  show ((x, _) :: σ.hash).lookup y = ((x, _) :: σ'.hash).lookup y
  rw [lookup_cons, lookup_cons, same.2.2 y]

/-- **A lazy run's output law depends on its state only through the lookups.** -/
theorem run_lookup_congr [DecidableEq FI] [DecidableEq EI] {Result : Type} {budget : ℕ}
    (A : OracleProgram (publicOracleSpec FI EI) Result budget) :
    ∀ (σ σ' : LazyOracle.State FI EI), SameLookup σ σ' →
      (LazyOracle.run A σ).map Prod.fst = (LazyOracle.run A σ').map Prod.fst := by
  induction A with
  | pure result =>
      intro σ σ' _
      show ((result.map fun value => (value, σ)).map Prod.fst) = (result.map fun value => (value, σ')).map Prod.fst
      rw [PMF.map_comp, PMF.map_comp]
      rfl
  | sample distribution next ih =>
      intro σ σ' same
      show (distribution.bind fun value => LazyOracle.run (next value) σ).map Prod.fst =
        (distribution.bind fun value => LazyOracle.run (next value) σ').map Prod.fst
      rw [PMF.map_bind, PMF.map_bind]
      exact congrArg _ (funext fun value => ih value σ σ' same)
  | query request next ih =>
      intro σ σ' same
      show ((LazyOracle.query request σ).bind fun a => LazyOracle.run (next a.1) a.2).map Prod.fst =
        ((LazyOracle.query request σ').bind fun a => LazyOracle.run (next a.1) a.2).map Prod.fst
      rw [PMF.map_bind, PMF.map_bind]
      obtain ⟨fixedEq, encEq, hashEq⟩ := same
      cases request with
      | hash x =>
          cases found : σ.hash.lookup x with
          | some v =>
              have found' : σ'.hash.lookup x = some v := (hashEq x).symm.trans found
              rw [query_hash_stored σ x v found, query_hash_stored σ' x v found']
              exact (PMF.pure_bind _ _).trans ((ih (hashValue v) σ σ' ⟨fixedEq, encEq, hashEq⟩).trans
                (PMF.pure_bind (hashValue v, σ') fun a => PMF.map Prod.fst (LazyOracle.run (next a.1) a.2)).symm)
          | none =>
              have found' : σ'.hash.lookup x = none := (hashEq x).symm.trans found
              rw [query_hash_fresh σ x found, query_hash_fresh σ' x found']
              refine (PMF.bind_map _ _ _).trans (Eq.trans ?_ (PMF.bind_map _ _ _).symm)
              exact congrArg _ (funext fun b => ih b _ _ (SameLookup.plant ⟨fixedEq, encEq, hashEq⟩ x b))
      | fixedForward index input =>
          simp only [LazyOracle.query, fixedEq, PMF.bind_map]
          refine congrArg _ (funext fun answer => ih _ _ _ ⟨rfl, encEq, hashEq⟩)
      | fixedInverse index output =>
          simp only [LazyOracle.query, fixedEq, PMF.bind_map]
          refine congrArg _ (funext fun answer => ih _ _ _ ⟨rfl, encEq, hashEq⟩)
      | encForward index input =>
          simp only [LazyOracle.query, encEq, PMF.bind_map]
          refine congrArg _ (funext fun answer => ih _ _ _ ⟨fixedEq, rfl, hashEq⟩)
      | encInverse index output =>
          simp only [LazyOracle.query, encEq, PMF.bind_map]
          refine congrArg _ (funext fun answer => ih _ _ _ ⟨fixedEq, rfl, hashEq⟩)

/-! ### 2. Installing hash entries, in any order -/

/-- A list of hash entries: every query of the list is a hash query. -/
def HashEntries (entries : List (Entry FI EI)) : Prop :=
  ∀ entry ∈ entries, ∃ x, entry.1 = .hash x

/-- Install one entry (a failed program is skipped). -/
def installOne [DecidableEq FI] [DecidableEq EI] (σ : LazyOracle.State FI EI) (entry : Entry FI EI) :
    LazyOracle.State FI EI :=
  (LazyOracle.program entry.1 entry.2 σ).getD σ

theorem installEntries_cons [DecidableEq FI] [DecidableEq EI] (entry : Entry FI EI) (rest : List (Entry FI EI))
    (σ : LazyOracle.State FI EI) :
    installEntries (entry :: rest) σ = installEntries rest (installOne σ entry) := rfl

theorem installOne_hash [DecidableEq FI] [DecidableEq EI] (σ : LazyOracle.State FI EI) (x : BaseField)
    (a : Block × Block) :
    installOne σ ⟨.hash x, a⟩ = if σ.hash.lookup x = none then plantHash x a σ else σ := by
  unfold installOne
  rw [program_hash]
  split <;> rfl

/-- Installing a hash entry into two states with the same lookups. -/
theorem SameLookup.installOne [DecidableEq FI] [DecidableEq EI] {σ σ' : LazyOracle.State FI EI}
    (same : SameLookup σ σ') (x : BaseField) (a : Block × Block) :
    SameLookup (Laws.installOne σ ⟨.hash x, a⟩) (Laws.installOne σ' ⟨.hash x, a⟩) := by
  rw [installOne_hash, installOne_hash, same.2.2 x]
  split
  · exact same.plant x a
  · exact same

theorem SameLookup.installEntries [DecidableEq FI] [DecidableEq EI] :
    ∀ (entries : List (Entry FI EI)) {σ σ' : LazyOracle.State FI EI}, HashEntries entries → SameLookup σ σ' →
      SameLookup (Privacy.installEntries entries σ) (Privacy.installEntries entries σ')
  | [], _, _, _, same => same
  | entry :: rest, σ, σ', hashes, same => by
      obtain ⟨x, hx⟩ := hashes entry List.mem_cons_self
      obtain ⟨query, a⟩ := entry
      simp only at hx
      subst hx
      rw [installEntries_cons, installEntries_cons]
      exact SameLookup.installEntries rest (fun e member => hashes e (List.mem_cons_of_mem _ member))
        (same.installOne x a)

theorem SameLookup.refl (σ : LazyOracle.State FI EI) : SameLookup σ σ := ⟨rfl, rfl, fun _ => rfl⟩

theorem SameLookup.symm {σ σ' : LazyOracle.State FI EI} (same : SameLookup σ σ') : SameLookup σ' σ :=
  ⟨same.1.symm, same.2.1.symm, fun x => (same.2.2 x).symm⟩

theorem SameLookup.trans {σ σ' σ'' : LazyOracle.State FI EI} (first : SameLookup σ σ')
    (second : SameLookup σ' σ'') : SameLookup σ σ'' :=
  ⟨first.1.trans second.1, first.2.1.trans second.2.1, fun x => (first.2.2 x).trans (second.2.2 x)⟩

/-- Two hash entries at distinct inputs install in either order. -/
theorem installOne_swap [DecidableEq FI] [DecidableEq EI] (σ : LazyOracle.State FI EI) (x y : BaseField)
    (a b : Block × Block) (apart : x ≠ y) :
    SameLookup (installOne (installOne σ ⟨.hash x, a⟩) ⟨.hash y, b⟩)
      (installOne (installOne σ ⟨.hash y, b⟩) ⟨.hash x, a⟩) := by
  have yx : y ≠ x := fun same => apart same.symm
  have keepX : ∀ c, (plantHash y c σ).hash.lookup x = σ.hash.lookup x := fun c => lookup_plantHash σ y x c apart
  have keepY : ∀ c, (plantHash x c σ).hash.lookup y = σ.hash.lookup y := fun c => lookup_plantHash σ x y c yx
  by_cases hx : σ.hash.lookup x = none <;> by_cases hy : σ.hash.lookup y = none
  · have i1 : installOne σ ⟨.hash x, a⟩ = plantHash x a σ := by rw [installOne_hash, if_pos hx]
    have i2 : installOne σ ⟨.hash y, b⟩ = plantHash y b σ := by rw [installOne_hash, if_pos hy]
    have o1 : installOne (plantHash x a σ) ⟨.hash y, b⟩ = plantHash y b (plantHash x a σ) := by
      rw [installOne_hash, keepY, if_pos hy]
    have o2 : installOne (plantHash y b σ) ⟨.hash x, a⟩ = plantHash x a (plantHash y b σ) := by
      rw [installOne_hash, keepX, if_pos hx]
    rw [i1, i2, o1, o2]
    refine ⟨rfl, rfl, fun z => ?_⟩
    show ((y, _) :: (x, _) :: σ.hash).lookup z = ((x, _) :: (y, _) :: σ.hash).lookup z
    rw [lookup_cons, lookup_cons, lookup_cons, lookup_cons]
    by_cases zy : z = y
    · subst zy
      rw [if_pos rfl, if_neg yx, if_pos rfl]
    · rw [if_neg zy]
      by_cases zx : z = x
      · rw [if_pos zx, if_pos zx]
      · rw [if_neg zx, if_neg zx, if_neg zy]
  · have i1 : installOne σ ⟨.hash x, a⟩ = plantHash x a σ := by rw [installOne_hash, if_pos hx]
    have i2 : installOne σ ⟨.hash y, b⟩ = σ := by rw [installOne_hash, if_neg hy]
    have o1 : installOne (plantHash x a σ) ⟨.hash y, b⟩ = plantHash x a σ := by
      rw [installOne_hash, keepY, if_neg hy]
    rw [i1, o1, i2, i1]
    exact SameLookup.refl _
  · have i1 : installOne σ ⟨.hash x, a⟩ = σ := by rw [installOne_hash, if_neg hx]
    have i2 : installOne σ ⟨.hash y, b⟩ = plantHash y b σ := by rw [installOne_hash, if_pos hy]
    have o2 : installOne (plantHash y b σ) ⟨.hash x, a⟩ = plantHash y b σ := by
      rw [installOne_hash, keepX, if_neg hx]
    rw [i1, i2, o2]
    exact SameLookup.refl _
  · have i1 : installOne σ ⟨.hash x, a⟩ = σ := by rw [installOne_hash, if_neg hx]
    have i2 : installOne σ ⟨.hash y, b⟩ = σ := by rw [installOne_hash, if_neg hy]
    rw [i1, i2, i1]
    exact SameLookup.refl _

/-- The input of a hash entry (`0` for any other entry). -/
def entryInput : Entry FI EI → BaseField
  | ⟨.hash x, _⟩ => x
  | _ => 0

/-- **Hash entries at pairwise distinct inputs install to the same lookups in any order.** -/
theorem installEntries_perm [DecidableEq FI] [DecidableEq EI] {l l' : List (Entry FI EI)} (perm : l.Perm l')
    (hashes : HashEntries l) (distinct : (l.map entryInput).Nodup) :
    ∀ σ : LazyOracle.State FI EI, SameLookup (Privacy.installEntries l σ) (Privacy.installEntries l' σ) := by
  induction perm with
  | nil => exact fun σ => SameLookup.refl σ
  | cons entry _ ih =>
      intro σ
      rw [installEntries_cons, installEntries_cons]
      exact ih (fun e member => hashes e (List.mem_cons_of_mem _ member)) (List.nodup_cons.mp distinct).2 _
  | swap first second rest =>
      intro σ
      obtain ⟨y, hy⟩ := hashes first (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨x, hx⟩ := hashes second List.mem_cons_self
      obtain ⟨fq, b⟩ := first
      obtain ⟨sq, a⟩ := second
      simp only at hx hy
      subst hx
      subst hy
      have apart : x ≠ y := by
        have := (List.nodup_cons.mp distinct).1
        intro same
        exact this (by rw [same]; exact List.mem_cons_self)
      rw [installEntries_cons, installEntries_cons, installEntries_cons, installEntries_cons]
      exact SameLookup.installEntries rest (fun e member => hashes e (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ member))) (installOne_swap σ x y a b apart)
  | trans first _ ih₁ ih₂ =>
      intro σ
      have hashes' : HashEntries _ := fun e member => hashes e (first.symm.subset member)
      have distinct' := (first.map entryInput).nodup_iff.mp distinct
      exact (ih₁ hashes distinct σ).trans (ih₂ hashes' distinct' σ)

/-! ### 3. Transcripts read the answer function along their path -/

/-- **A program's transcript and result depend on the answer function only along its own path.** -/
theorem transcript_congr {α : Type} (a a' : ∀ q : PublicQuery FI EI, q.Answer) :
    ∀ {budget : ℕ} (P : QueryProgram (publicOracleSpec FI EI) α budget),
      (∀ entry ∈ programTranscript a P, a' entry.1 = entry.2) →
      programTranscript a' P = programTranscript a P ∧ P.eval a' = P.eval a
  | _, .pure _, _ => ⟨rfl, rfl⟩
  | _, .query request next, agree => by
      have head : a' request = a request := agree ⟨request, a request⟩ List.mem_cons_self
      have rest := transcript_congr a a' (next (a request)) fun entry member =>
        agree entry (List.mem_cons_of_mem _ member)
      show ⟨request, a' request⟩ :: programTranscript a' (next (a' request)) =
          ⟨request, a request⟩ :: programTranscript a (next (a request)) ∧
        (next (a' request)).eval a' = (next (a request)).eval a
      rw [head, rest.1, rest.2]
      exact ⟨rfl, rfl⟩

/-- Every transcript entry carries the answer function's answer. -/
theorem transcript_answer {α : Type} (a : ∀ q : PublicQuery FI EI, q.Answer) :
    ∀ {budget : ℕ} (P : QueryProgram (publicOracleSpec FI EI) α budget),
      ∀ entry ∈ programTranscript a P, a entry.1 = entry.2
  | _, .pure _ => fun entry member => by cases member
  | _, .query request next => fun entry member => by
      rcases List.mem_cons.mp member with same | rest
      · subst same
        rfl
      · exact transcript_answer a (next (a request)) entry rest

/-- The tags a program reads along its path on the table oracle. -/
def pathTags {α : Type} (T : TagTable) {budget : ℕ} (P : QueryProgram (publicOracleSpec FI EI) α budget) :
    List (Fin (2 ^ 40)) :=
  (programTranscript (publicAnswer (tableOracle (FI := FI) (EI := EI) T)) P).filterMap fun entry =>
    match entry.1 with
    | .hash x => some (tagOfInput x)
    | _ => none

/-- **On the table oracle a hash-only program reads the table only at the tags of its path.** -/
theorem tableTranscript_congr {α : Type} (T T' : TagTable) {budget : ℕ}
    (P : QueryProgram (publicOracleSpec FI EI) α budget)
    (hashes : HashEntries (programTranscript (publicAnswer (tableOracle (FI := FI) (EI := EI) T)) P))
    (agree : ∀ k ∈ pathTags T P, T k = T' k) :
    programTranscript (publicAnswer (tableOracle (FI := FI) (EI := EI) T')) P =
        programTranscript (publicAnswer (tableOracle (FI := FI) (EI := EI) T)) P ∧
      P.eval (publicAnswer (tableOracle (FI := FI) (EI := EI) T')) =
        P.eval (publicAnswer (tableOracle (FI := FI) (EI := EI) T)) := by
  refine transcript_congr _ _ P fun entry member => ?_
  obtain ⟨x, hx⟩ := hashes entry member
  obtain ⟨query, answer⟩ := entry
  simp only at hx
  subst hx
  have value : answer = T (tagOfInput x) := by
    have := transcript_answer _ P ⟨.hash x, answer⟩ member
    exact this.symm.trans rfl
  have inPath : tagOfInput x ∈ pathTags T P := by
    unfold pathTags
    exact List.mem_filterMap.mpr ⟨⟨.hash x, answer⟩, member, rfl⟩
  show T' (tagOfInput x) = answer
  rw [value, agree _ inPath]

/-! ### 4. The visible entries are the reach's transcript -/

/-- A transcript entry is its query with the answer function's answer. -/
theorem entry_eq_of_mem {α : Type} (a : ∀ q : PublicQuery FI EI, q.Answer) {budget : ℕ}
    (P : QueryProgram (publicOracleSpec FI EI) α budget) {entry : Entry FI EI}
    (member : entry ∈ programTranscript a P) : entry = ⟨entry.1, a entry.1⟩ := by
  obtain ⟨q, answer⟩ := entry
  have := transcript_answer a P ⟨q, answer⟩ member
  simp only at this
  rw [this]

/-- **The garbler entries a reach meets are the reach's transcript, up to order**, when every reach query is a
garbler query (containment, off the coincidence flag) and both runs ask each query once. -/
theorem visible_perm {α β : Type} (a : ∀ q : PublicQuery FI EI, q.Answer) {budget budget' : ℕ}
    (G : QueryProgram (publicOracleSpec FI EI) α budget) (R : QueryProgram (publicOracleSpec FI EI) β budget')
    (p : Entry FI EI → Bool) (hp : ∀ entry, p entry = true ↔ entry.1 ∈ (programTranscript a R).map Sigma.fst)
    (garblerOnce : ((programTranscript a G).map Sigma.fst).Nodup)
    (reachOnce : ((programTranscript a R).map Sigma.fst).Nodup)
    (contained : ∀ q ∈ (programTranscript a R).map Sigma.fst, q ∈ (programTranscript a G).map Sigma.fst) :
    ((programTranscript a G).filter p).Perm (programTranscript a R) := by
  refine (List.perm_ext_iff_of_nodup ((garblerOnce.of_map _).filter _) (reachOnce.of_map _)).mpr fun entry => ?_
  rw [List.mem_filter]
  constructor
  · rintro ⟨inG, hit⟩
    obtain ⟨other, inR, same⟩ := List.mem_map.mp ((hp entry).mp hit)
    rw [entry_eq_of_mem a G inG, ← same, ← entry_eq_of_mem a R inR]
    exact inR
  · intro inR
    obtain ⟨other, inG, same⟩ := List.mem_map.mp (contained _ (List.mem_map_of_mem inR))
    refine ⟨?_, (hp entry).mpr (List.mem_map_of_mem inR)⟩
    rw [entry_eq_of_mem a R inR, ← same, ← entry_eq_of_mem a G inG]
    exact inG

theorem entryInput_nodup {l : List (Entry FI EI)} (hashes : HashEntries l) (once : (l.map Sigma.fst).Nodup) :
    (l.map entryInput).Nodup := by
  refine List.Nodup.map_on (fun e he e' he' same => ?_) (once.of_map _)
  obtain ⟨x, hx⟩ := hashes e he
  obtain ⟨x', hx'⟩ := hashes e' he'
  obtain ⟨q, a⟩ := e
  obtain ⟨q', a'⟩ := e'
  simp only at hx hx'
  subst hx
  subst hx'
  have xs : x = x' := same
  subst xs
  exact List.inj_on_of_nodup_map once he he' rfl

/-- **P6a2: `G1U`'s stage 2 runs as after installing the reach's own transcript.** Under containment (every reach
query is a garbler query) and single asking, installing the visible garbler entries (garbler order) and installing the
reach's transcript (reach order) give the adversary's stage 2 the same output law. The reach's transcript on the table
oracle is a function of the table at the reach's tags (`tableTranscript_congr`). -/
theorem stage2_visible_eq_reach [DecidableEq FI] [DecidableEq EI]
    {α β Result : Type} (a : ∀ q : PublicQuery FI EI, q.Answer) {budget budget' budgetA : ℕ}
    (G : QueryProgram (publicOracleSpec FI EI) α budget) (R : QueryProgram (publicOracleSpec FI EI) β budget')
    (A : OracleProgram (publicOracleSpec FI EI) Result budgetA) (σ : LazyOracle.State FI EI)
    (p : Entry FI EI → Bool) (hp : ∀ entry, p entry = true ↔ entry.1 ∈ (programTranscript a R).map Sigma.fst)
    (hashes : HashEntries (programTranscript a R))
    (garblerOnce : ((programTranscript a G).map Sigma.fst).Nodup)
    (reachOnce : ((programTranscript a R).map Sigma.fst).Nodup)
    (contained : ∀ q ∈ (programTranscript a R).map Sigma.fst, q ∈ (programTranscript a G).map Sigma.fst) :
    (LazyOracle.run A (installEntries ((programTranscript a G).filter p) σ)).map Prod.fst =
      (LazyOracle.run A (installEntries (programTranscript a R) σ)).map Prod.fst := by
  have perm := visible_perm a G R p hp garblerOnce reachOnce contained
  have hashesVisible : HashEntries ((programTranscript a G).filter p) := fun e member =>
    hashes e (perm.subset member)
  have distinct := entryInput_nodup hashesVisible
    (perm.map Sigma.fst |>.nodup_iff.mpr reachOnce)
  exact run_lookup_congr A _ _ (installEntries_perm perm hashesVisible distinct σ)

end

end Kriterion.CRT.Privacy.Laws
