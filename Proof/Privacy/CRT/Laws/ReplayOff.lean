/-
**P6b2: the off-curve law of `HW` against `G1U`, the tools**.

Off the curve `HW`'s stage 2 makes no oracle call: the adversary's second stage runs on the stage-1 state `σ₁`. `G1U`
installs the designed-visible garbler entries its reach meets (cold conversion and body positions and the digest labels
of `u`'s bits; the key and the masks are hidden off the curve, F3). Where those answers are, given everything the
adversary sees, fresh uniform answers along the reach's path, installing them is invisible:

* **`run_discard`**: a lazy run of any program `R` whose result is discarded does not change the output law of a later
  lazy run `A` (both are the eager run on the completion of `σ`: `public_run`, `public_run_result`);
* **`run_table_avoid`**: a coordinate-injective program run on a uniform table from a state that holds none of its
  inputs, with its transcript installed, has the law of its lazy run from that state (the adaptive answer-table law of
  `Table.lean` for a state that is not the program's own history);
* **`install_table_invisible`**: so installing the transcript of such a program read on a uniform table is invisible
  to a later lazy run. This is `G1U`'s off-curve installation once the core gives the reach's answers the uniform
  table law given the published value and the labels (the stage-1 flag gives that
  `σ₁` holds none of the reach's points).
-/

import Proof.Privacy.CRT.Laws.Garbler

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_run public_run_result)

noncomputable section

variable {FI EI : Type}

/-! ### 1. A discarded lazy run is invisible -/

/-- **A lazy run whose result is discarded does not change the output law of a later lazy run.** -/
theorem run_discard [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] {α Result : Type}
    {budget budgetA : ℕ} (R : OracleProgram (publicOracleSpec FI EI) α budget)
    (A : OracleProgram (publicOracleSpec FI EI) Result budgetA) (σ : LazyOracle.State FI EI) :
    (LazyOracle.run R σ).bind (fun r => (LazyOracle.run A r.2).map Prod.fst) = (LazyOracle.run A σ).map Prod.fst := by
  let g : PublicOracle FI EI → PMF Result := fun H => (A.run (publicHandler id) H).map Prod.fst
  have eachState : ∀ r : α × LazyOracle.State FI EI,
      (LazyOracle.run A r.2).map Prod.fst = ((publicCompletion r.2).map fun H => (r.1, H)).bind fun p => g p.2 := by
    intro r
    rw [← public_run_result A r.2, PMF.bind_map]
    rfl
  simp only [eachState]
  rw [← PMF.bind_bind, ← public_run R σ, PMF.bind_bind, ← public_run_result A σ]
  refine congrArg _ (funext fun H => ?_)
  rw [PMF.bind_congr _ _ _ fun p member => by rw [eagerRun_state R H p member]]
  exact PMF.bind_const _ _

/-! ### 2. The adaptive answer-table law from a foreign state -/

section Avoid

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The coordinates of a list of inputs. -/
def coordsOf (c : BaseField → C) (seen : List BaseField) : Set C := {k | ∃ y ∈ seen, c y = k}

open Classical in
/-- The table seen through the inputs read so far: at their coordinates the fixed value `T0`, elsewhere `T`. -/
def throughSeen (c : BaseField → C) (seen : List BaseField) (T0 T : C → Block × Block) : C → Block × Block :=
  fun k => if k ∈ coordsOf c seen then T0 k else T k

/-- **Coordinate injectivity and avoidance along every path**: every query is a hash query at an input that is not
stored in the initial state `σ₁` and whose coordinate is not that of an earlier input unless it is that input. -/
inductive AvoidPath (c : BaseField → C) (σ₁ : LazyOracle.State FI EI) {α : Type} :
    List BaseField → {budget : ℕ} → QueryProgram (publicOracleSpec FI EI) α budget → Prop
  | pure (seen : List BaseField) {budget : ℕ} (result : α) :
      AvoidPath c σ₁ seen (QueryProgram.pure (budget := budget) result)
  | hash (seen : List BaseField) {budget : ℕ} (x : BaseField)
      (next : Block × Block → QueryProgram (publicOracleSpec FI EI) α budget)
      (absent : σ₁.hash.lookup x = none)
      (fresh : ∀ y ∈ seen, c x = c y → x = y)
      (rest : ∀ answer, AvoidPath c σ₁ (x :: seen) (next answer)) :
      AvoidPath c σ₁ seen (QueryProgram.query (PublicQuery.hash x) next)

open Classical in
/-- The state after installing the inputs read so far on top of `σ₁`: a read input holds `T0` at its coordinate,
every other input what `σ₁` holds. -/
def SeenState (c : BaseField → C) (σ₁ : LazyOracle.State FI EI) (seen : List BaseField)
    (T0 : C → Block × Block) (s : LazyOracle.State FI EI) : Prop :=
  s.fixed = σ₁.fixed ∧ s.enc = σ₁.enc ∧ ∀ y, s.hash.lookup y =
    if y ∈ seen then some (Fintype.equivFin (Block × Block) (T0 (c y))) else σ₁.hash.lookup y

theorem coordsOf_cons (c : BaseField → C) (x : BaseField) (seen : List BaseField) (k : C) :
    k ∈ coordsOf c (x :: seen) ↔ k = c x ∨ k ∈ coordsOf c seen := by
  unfold coordsOf
  simp only [Set.mem_ofPred_eq, List.mem_cons]
  constructor
  · rintro ⟨y, (rfl | member), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨y, member, rfl⟩
  · rintro (rfl | ⟨y, member, rfl⟩)
    · exact ⟨x, Or.inl rfl, rfl⟩
    · exact ⟨y, Or.inr member, rfl⟩

theorem throughSeen_nil (c : BaseField → C) (T0 T : C → Block × Block) : throughSeen c [] T0 T = T := by
  funext k
  have none : k ∉ coordsOf c [] := by
    rintro ⟨y, member, _⟩
    cases member
  unfold throughSeen
  rw [if_neg none]

/-- **The adaptive answer-table law from a foreign state.** A program that avoids the inputs of `σ₁` and reads
pairwise distinct coordinates, run on a table whose read coordinates hold the read answers and whose other
coordinates are uniform, with its transcript installed, has the law of its lazy run. -/
theorem run_table_avoid [DecidableEq FI] [DecidableEq EI] (c : BaseField → C) (σ₁ : LazyOracle.State FI EI)
    {α : Type} {seen : List BaseField} {budget : ℕ} {P : QueryProgram (publicOracleSpec FI EI) α budget}
    (path : AvoidPath c σ₁ seen P) :
    ∀ (s : LazyOracle.State FI EI) (T0 : C → Block × Block), SeenState c σ₁ seen T0 s →
      (PMF.uniformOfFintype (C → Block × Block)).map (fun T =>
          (P.eval (publicAnswer (coordOracle (FI := FI) (EI := EI) c (throughSeen c seen T0 T))),
            installEntries (programTranscript (publicAnswer (coordOracle (FI := FI) (EI := EI) c
              (throughSeen c seen T0 T))) P) s)) =
        LazyOracle.run P.toOracleProgram s := by
  induction path with
  | pure seen result =>
      intro s T0 _
      show (PMF.uniformOfFintype _).map (fun _ => (result, s)) = (PMF.pure result).map (fun value => (value, s))
      rw [PMF.pure_map]
      exact PMF.map_const _ _
  | hash seen x next absent fresh rest ih =>
      intro s T0 state
      show _ = (LazyOracle.query (.hash x) s).bind fun answer =>
        LazyOracle.run (next answer.1).toOracleProgram answer.2
      by_cases wasSeen : x ∈ seen
      · -- a read input: its stored answer on both sides
        have atX : c x ∈ coordsOf c seen := ⟨x, wasSeen, rfl⟩
        have found : s.hash.lookup x = some (Fintype.equivFin (Block × Block) (T0 (c x))) := by
          rw [state.2.2 x, if_pos wasSeen]
        rw [query_hash_stored s x _ found]
        erw [PMF.pure_bind]
        have value : hashValue (Fintype.equivFin (Block × Block) (T0 (c x))) = T0 (c x) := by
          simp [hashValue]
        rw [value]
        have seenState : SeenState c σ₁ (x :: seen) T0 s := by
          refine ⟨state.1, state.2.1, fun y => ?_⟩
          rw [state.2.2 y]
          by_cases hy : y ∈ seen
          · rw [if_pos hy, if_pos (List.mem_cons_of_mem _ hy)]
          · by_cases yx : y = x
            · subst yx
              exact absurd wasSeen hy
            · rw [if_neg hy, if_neg (by simp [yx, hy])]
        have throughSame : ∀ T, throughSeen c (x :: seen) T0 T = throughSeen c seen T0 T := by
          intro T
          funext k
          unfold throughSeen
          by_cases inOld : k ∈ coordsOf c seen
          · rw [if_pos ((coordsOf_cons c x seen k).mpr (Or.inr inOld)), if_pos inOld]
          · have notX : k ≠ c x := fun same => inOld (same ▸ atX)
            rw [if_neg (fun inNew => ((coordsOf_cons c x seen k).mp inNew).elim notX inOld), if_neg inOld]
        rw [← ih (T0 (c x)) s T0 seenState]
        refine congrArg (fun f => PMF.map f _) (funext fun T => ?_)
        have answerEq : throughSeen c seen T0 T (c x) = T0 (c x) := by
          unfold throughSeen
          rw [if_pos atX]
        have skip : LazyOracle.program (PublicQuery.hash x) (T0 (c x)) s = none := by
          rw [program_hash, found]
          rfl
        show ((next (throughSeen c seen T0 T (c x))).eval _,
            installEntries (⟨PublicQuery.hash x, throughSeen c seen T0 T (c x)⟩ :: programTranscript _
              (next (throughSeen c seen T0 T (c x)))) s) = _
        rw [answerEq, throughSame]
        show (_, installEntries _ ((LazyOracle.program (PublicQuery.hash x) (T0 (c x)) s).getD s)) = _
        rw [skip]
        rfl
      · -- a new input: an unread coordinate
        have missing : s.hash.lookup x = none := by
          rw [state.2.2 x, if_neg wasSeen]
          exact absent
        have unread : c x ∉ coordsOf c seen := by
          rintro ⟨y, member, same⟩
          exact wasSeen (fresh y member same.symm ▸ member)
        let fixed : Block × Block → C → Block × Block := fun b => Function.update T0 (c x) b
        have seenAfter : ∀ b, SeenState c σ₁ (x :: seen) (fixed b) (plantHash x b s) := by
          intro b
          refine ⟨state.1, state.2.1, fun y => ?_⟩
          show ((x, _) :: s.hash).lookup y = _
          rw [lookup_cons]
          by_cases yx : y = x
          · subst yx
            rw [if_pos rfl, if_pos List.mem_cons_self]
            simp [fixed]
          · rw [if_neg yx, state.2.2 y]
            by_cases hy : y ∈ seen
            · have apart : c y ≠ c x := fun same => yx (fresh y hy same.symm).symm
              rw [if_pos hy, if_pos (List.mem_cons_of_mem _ hy)]
              simp only [fixed, Function.update_of_ne apart]
            · rw [if_neg hy, if_neg (by simp [yx, hy])]
        have throughEq : ∀ T, throughSeen c seen T0 T =
            throughSeen c (x :: seen) (fixed (T (c x))) T := by
          intro T
          funext k
          unfold throughSeen
          by_cases inOld : k ∈ coordsOf c seen
          · have apart : k ≠ c x := fun equal => unread (equal ▸ inOld)
            rw [if_pos inOld, if_pos ((coordsOf_cons c x seen k).mpr (Or.inr inOld))]
            simp only [fixed, Function.update_of_ne apart]
          · rw [if_neg inOld]
            by_cases atX : k = c x
            · subst atX
              rw [if_pos ((coordsOf_cons c x seen _).mpr (Or.inl rfl))]
              simp [fixed]
            · rw [if_neg fun inNew => ((coordsOf_cons c x seen k).mp inNew).elim atX inOld]
        have ignores : ∀ b T, throughSeen c (x :: seen) (fixed b) (Function.update T (c x) b) =
            throughSeen c (x :: seen) (fixed b) T := by
          intro b T
          funext k
          unfold throughSeen
          by_cases inNew : k ∈ coordsOf c (x :: seen)
          · rw [if_pos inNew, if_pos inNew]
          · have apart : k ≠ c x := fun equal => inNew ((coordsOf_cons c x seen k).mpr (Or.inl equal))
            rw [if_neg inNew, if_neg inNew, Function.update_of_ne apart]
        have installed : ∀ b : Block × Block, LazyOracle.program (PublicQuery.hash x) b s = some (plantHash x b s) :=
          fun b => program_hash_fresh s x b missing
        rw [query_hash_fresh s x missing]
        erw [PMF.bind_map]
        show _ = (PMF.uniformOfFintype (Block × Block)).bind fun b =>
          LazyOracle.run (next b).toOracleProgram (plantHash x b s)
        have step := fun b => ih b (plantHash x b s) (fixed b) (seenAfter b)
        simp_rw [← step]
        let G : Block × Block → (C → Block × Block) → _ := fun b T =>
          ((next b).eval (publicAnswer (coordOracle (FI := FI) (EI := EI) c (throughSeen c (x :: seen) (fixed b) T))),
            installEntries (programTranscript (publicAnswer (coordOracle (FI := FI) (EI := EI) c
              (throughSeen c (x :: seen) (fixed b) T))) (next b)) (plantHash x b s))
        have law := uniform_update_bind (c x) G fun b T => by
          simp only [G, ignores]
        refine Eq.trans ?_ law
        refine congrArg (fun f => PMF.map f _) (funext fun T => ?_)
        have answerEq : throughSeen c seen T0 T (c x) = T (c x) := by
          unfold throughSeen
          rw [if_neg unread]
        show ((next (throughSeen c seen T0 T (c x))).eval _,
            installEntries (⟨PublicQuery.hash x, throughSeen c seen T0 T (c x)⟩ :: programTranscript _
              (next (throughSeen c seen T0 T (c x)))) s) = _
        rw [answerEq]
        show (_, installEntries _
          ((LazyOracle.program (PublicQuery.hash x) (T (c x)) s).getD s)) = _
        rw [installed, Option.getD_some, throughEq T]

/-- **Installing the transcript of an avoiding program read on a uniform table is invisible** to a later lazy run. -/
theorem install_table_invisible [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (c : BaseField → C) (σ₁ : LazyOracle.State FI EI) {α Result : Type} {budget budgetA : ℕ}
    {P : QueryProgram (publicOracleSpec FI EI) α budget} (path : AvoidPath c σ₁ [] P)
    (A : OracleProgram (publicOracleSpec FI EI) Result budgetA) :
    (PMF.uniformOfFintype (C → Block × Block)).bind (fun T =>
        (LazyOracle.run A (installEntries (programTranscript
          (publicAnswer (coordOracle (FI := FI) (EI := EI) c T)) P) σ₁)).map Prod.fst) =
      (LazyOracle.run A σ₁).map Prod.fst := by
  have law := run_table_avoid c σ₁ path σ₁ (fun _ => (0, 0))
    ⟨rfl, rfl, fun y => by simp⟩
  simp only [throughSeen_nil] at law
  rw [← run_discard P.toOracleProgram A σ₁, ← law, PMF.bind_map]
  rfl

end Avoid

end

end Kriterion.CRT.Privacy.Laws
