/-
**P6b2, part 1: planting uniform answers at fresh inputs is invisible to a lazy run**.

The hybrids `G1U` and `HW` differ in which hash answers the adversary's stage-2 lazy oracle holds before it runs:
`G1U` installs every designed-visible garbler entry, `HW` installs only what its replay reads (none off the curve, and
not the digest labels on the curve, F6). Where the installed answers are uniform and independent of everything else
the adversary sees, installing them is the same as leaving the lazy oracle to draw them:

* `pairHash_fresh`, `publicCompletion_plant`: the eager completion of a lazy state is the completion of the state with
  one more uniform answer at a fresh input (xinshu's `HashTable.fresh_completion`);
* `plant_invisible`: for any oracle program `A` and a fresh input `x`, averaging `A`'s lazy run over a uniform answer
  planted at `x` gives `A`'s lazy run (through `public_run_result`, the lazy run is the eager run on the completion);
* `plantAll_invisible`: the same for a list of pairwise distinct fresh inputs, planted one after the other.
-/

import Proof.Privacy.CRT.Laws.Table

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion pairHashCompletion public_run_result uniform_equiv hashSize
  indexedKernel blockCompletion)

noncomputable section

variable {FI EI : Type}

/-- Plant one hash answer at an input: the lazy state with the pair `(x, a)` prepended. -/
def plantHash (x : BaseField) (a : Block × Block) (σ : LazyOracle.State FI EI) : LazyOracle.State FI EI :=
  { σ with hash := (x, Fintype.equivFin (Block × Block) a) :: σ.hash }

/-- At a fresh input, a hash program plants the pair. -/
theorem program_hash_fresh [DecidableEq FI] [DecidableEq EI] (σ : LazyOracle.State FI EI) (x : BaseField)
    (a : Block × Block) (fresh : σ.hash.lookup x = none) :
    LazyOracle.program (.hash x) a σ = some (plantHash x a σ) := by
  rw [program_hash, fresh]
  rfl

/-- **One fresh answer of the eager completion of a hash table is uniform and independent of the rest.** -/
theorem pairHash_fresh (table : HashTable BaseField hashSize) (x : BaseField) (fresh : table.lookup x = none) :
    pairHashCompletion table = (PMF.uniformOfFintype (Block × Block)).bind fun a =>
      pairHashCompletion ((x, Fintype.equivFin (Block × Block) a) :: table) := by
  haveI : Nonempty (Fin hashSize) := ⟨⟨0, Fintype.card_pos⟩⟩
  have split := Kriterion.ArgoMAC.Phase3.Glue.HashTable.fresh_completion Fintype.card_pos table x fresh
  unfold pairHashCompletion
  have viaVal : ∀ (t : HashTable BaseField hashSize),
      (PMF.uniformOfFintype t.Completion).map
          (fun complete key => (Fintype.equivFin (Block × Block)).symm (complete.val key)) =
        ((PMF.uniformOfFintype t.Completion).map Subtype.val).map
          (fun f key => (Fintype.equivFin (Block × Block)).symm (f key)) := by
    intro t
    rw [PMF.map_comp]
    rfl
  rw [viaVal, split, PMF.map_bind]
  simp only [← viaVal]
  rw [← uniform_equiv (Fintype.equivFin (Block × Block)), PMF.bind_map]
  rfl

/-- **The eager completion of a lazy state with one more fresh hash answer.** -/
theorem publicCompletion_plant [Fintype FI] [Fintype EI] (σ : LazyOracle.State FI EI) (x : BaseField)
    (fresh : σ.hash.lookup x = none) :
    publicCompletion σ = (PMF.uniformOfFintype (Block × Block)).bind fun a => publicCompletion (plantHash x a σ) := by
  unfold publicCompletion
  rw [pairHash_fresh σ.hash x fresh]
  simp only [PMF.map_bind]
  conv_lhs => arg 2; ext fixed; rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  rfl

/-- **Planting a uniform answer at a fresh input is invisible to a lazy run.** -/
theorem plant_invisible [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] {Result : Type} {budget : ℕ}
    (A : OracleProgram (publicOracleSpec FI EI) Result budget) (σ : LazyOracle.State FI EI) (x : BaseField)
    (fresh : σ.hash.lookup x = none) :
    (PMF.uniformOfFintype (Block × Block)).bind (fun a => (LazyOracle.run A (plantHash x a σ)).map Prod.fst) =
      (LazyOracle.run A σ).map Prod.fst := by
  rw [← public_run_result A σ, publicCompletion_plant σ x fresh, PMF.bind_bind]
  refine congrArg _ (funext fun a => ?_)
  exact (public_run_result A (plantHash x a σ)).symm

/-- Plant uniform answers at a list of inputs, one after the other. -/
def plantAll : List BaseField → LazyOracle.State FI EI → PMF (LazyOracle.State FI EI)
  | [], σ => PMF.pure σ
  | x :: xs, σ => (PMF.uniformOfFintype (Block × Block)).bind fun a => plantAll xs (plantHash x a σ)

theorem lookup_plantHash (σ : LazyOracle.State FI EI) (x y : BaseField) (a : Block × Block) (apart : y ≠ x) :
    (plantHash x a σ).hash.lookup y = σ.hash.lookup y := by
  show ((x, Fintype.equivFin (Block × Block) a) :: σ.hash).lookup y = _
  rw [lookup_cons, if_neg apart]

/-- **Planting uniform answers at pairwise distinct fresh inputs is invisible to a lazy run.** -/
theorem plantAll_invisible [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] {Result : Type}
    {budget : ℕ} (A : OracleProgram (publicOracleSpec FI EI) Result budget) :
    ∀ (xs : List BaseField) (σ : LazyOracle.State FI EI), xs.Nodup → (∀ x ∈ xs, σ.hash.lookup x = none) →
      (plantAll xs σ).bind (fun σ' => (LazyOracle.run A σ').map Prod.fst) = (LazyOracle.run A σ).map Prod.fst
  | [], σ, _, _ => by
      show (PMF.pure σ).bind _ = _
      rw [PMF.pure_bind]
  | x :: xs, σ, nodup, fresh => by
      obtain ⟨notMem, nodupRest⟩ := List.nodup_cons.mp nodup
      show ((PMF.uniformOfFintype (Block × Block)).bind fun a => plantAll xs (plantHash x a σ)).bind _ = _
      rw [PMF.bind_bind]
      have each : ∀ a, (plantAll xs (plantHash x a σ)).bind (fun σ' => (LazyOracle.run A σ').map Prod.fst) =
          (LazyOracle.run A (plantHash x a σ)).map Prod.fst := fun a =>
        plantAll_invisible A xs (plantHash x a σ) nodupRest fun y member => by
          rw [lookup_plantHash σ x y a (fun same => notMem (same ▸ member))]
          exact fresh y (List.mem_cons_of_mem _ member)
      simp only [each]
      exact plant_invisible A σ x (fresh x List.mem_cons_self)

end

end Kriterion.CRT.Privacy.Laws
