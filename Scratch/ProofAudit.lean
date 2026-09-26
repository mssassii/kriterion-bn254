/-
Whole-tree axiom audit: every declaration whose module lies under `Construction`, `Proof` or
`Submission` may use only `propext`, `Classical.choice` and `Quot.sound`; the count of audited
declarations is printed.

Run after `lake build`: `lake env lean Scratch/ProofAudit.lean`.
-/
import Construction
import Proof
import Submission
import Lean

open Lean

run_cmd do
  let env ← getEnv
  let mut audited : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut union : NameSet := {}
  for (name, _) in env.constants.toList do
    let origin := (env.getModuleIdxFor? name).bind fun index => env.header.moduleNames[index.toNat]?
    if origin.any (fun moduleName => #[`Construction, `Proof, `Submission].contains moduleName.getRoot) then
      audited := audited + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        union := union.insert ax
      let illegal := axioms.filter fun axiomName =>
        !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
      unless illegal.isEmpty do
        bad := bad.push (name, illegal)
  logInfo m!"audited {audited} declarations; union of their axioms: {union.toList}"
  unless bad.isEmpty do
    throwError m!"{bad.size} declarations use disallowed axioms, first ones: {bad.toList.take 10}"
  logInfo "proof audit passed"
