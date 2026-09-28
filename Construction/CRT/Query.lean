/-
The query language of the CRT layer. Every program of `Construction/CRT/` is a `FreeQuery` over
`CrtSpec`, whose only question is the hash at a natural input (`label + 2 ^ 128 * tag`, or the
bridge input `t'.val`). `liftHash` turns such a program into one over the contest's public oracle
(each question becomes exactly one `.hash (n : BaseField)` question), with its `eval` and
`Bounded` lemmas; so a position of the layer is a position of the scheme, and the privacy side's
answer tables are plain `HashN` values.

The definitions of the layer are these programs: the pure view of a program at a hash `H` is
`FreeQuery.eval H`, so the object that correctness, the answer-table laws and the machine replay
reason about is the object that `#eval` tests.
-/

import Construction.QueryMonad
import Construction.CRT.Lanes

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC

/-- The CRT layer's oracle interface: a question is a natural hash input. -/
abbrev CrtSpec : OracleSpec.{0, 0} := ⟨Nat, fun _ => Block × Block⟩

/-- A CRT query program. -/
abbrev CM := FreeQuery CrtSpec

/-- Ask the hash at a natural input. -/
def askN (input : Nat) : CM (Block × Block) := FreeQuery.ask (spec := CrtSpec) input

@[simp] theorem eval_askN (H : HashN) (input : Nat) : (askN input).eval H = H input := rfl

theorem bounded_askN (input : Nat) : (askN input).Bounded 1 := FreeQuery.Bounded.ask _

/-- The one-block hash as a program (one query). -/
def h128M (label : Block) (tag : Nat) : CM Block :=
  askN (hashInput label tag) >>= fun answer => pure answer.1

@[simp] theorem eval_h128M (H : HashN) (label : Block) (tag : Nat) :
    (h128M label tag).eval H = h128 H label tag := rfl

theorem bounded_h128M (label : Block) (tag : Nat) : (h128M label tag).Bounded 1 :=
  FreeQuery.Bounded.bind (bounded_askN _) fun _ => FreeQuery.Bounded.pure' _ 0

/-- The narrow conversion hash: one raw query at an embedded label. -/
def hLabelM (label : Label) (tag : Nat) : CM Label :=
  askN (hashInput (embed label) tag) >>= fun answer => pure (clip answer.1)

@[simp] theorem eval_hLabelM (H : HashN) (label : Label) (tag : Nat) :
    (hLabelM label tag).eval H = hLabel H label tag := rfl

theorem bounded_hLabelM (label : Label) (tag : Nat) : (hLabelM label tag).Bounded 1 :=
  FreeQuery.Bounded.bind (bounded_askN _) fun _ => FreeQuery.Bounded.pure' _ 0

/-- The long hash as a program (`count` queries, parts ascending). -/
def hlongM (label : Block) (tagOf : Nat → Nat) (count : Nat) : CM Nat :=
  FreeQuery.vector count (fun j => askN (hashInput label (tagOf j.val))) >>= fun answers =>
    pure (packAnswers count answers.get)

@[simp] theorem eval_hlongM (H : HashN) (label : Block) (tagOf : Nat → Nat) (count : Nat) :
    (hlongM label tagOf count).eval H = hlong H label tagOf count := by
  simp [hlongM, hlong]

theorem bounded_hlongM (label : Block) (tagOf : Nat → Nat) (count : Nat) :
    (hlongM label tagOf count).Bounded count :=
  (FreeQuery.Bounded.bind (FreeQuery.Bounded.vector_const fun _ => bounded_askN _) fun _ =>
    FreeQuery.Bounded.pure' _ 0).of_eq (by simp)

/-! ### Lifting into the contest's public oracle -/

/-- Each CRT question becomes one `.hash` question of the public oracle. -/
def liftHash {FixedIndex EncIndex : Type} {α : Type} :
    CM α → FreeQuery (publicOracleSpec FixedIndex EncIndex) α
  | .pure value => .pure value
  | .query input next => .query (.hash (input : BN254.BaseField)) fun answer => liftHash (next answer)

/-- The scheme's instance of the layer's hash. -/
def schemeHash {FixedIndex EncIndex : Type} (oracle : PublicOracle FixedIndex EncIndex) : HashN :=
  fun input => oracle.2.2 (input : BN254.BaseField)

theorem eval_liftHash {FixedIndex EncIndex : Type} {α : Type}
    (oracle : PublicOracle FixedIndex EncIndex) (program : CM α) :
    (liftHash program).eval (publicAnswer oracle) = program.eval (schemeHash oracle) := by
  induction program with
  | pure value => rfl
  | query input next ih => exact ih _

theorem bounded_liftHash {FixedIndex EncIndex : Type} {α : Type} {program : CM α} {budget : Nat}
    (bounded : program.Bounded budget) :
    (liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) program).Bounded budget := by
  induction bounded with
  | pure value budget => exact .pure value budget
  | query input next budget _ ih => exact .query _ _ budget fun answer => ih answer

/-! ### Loops -/

/-- A loop over `Fin count` whose results are stored in an array and read back as a function. -/
def tableM {α : Type} (count : Nat) (program : Fin count → CM α) : CM (Fin count → α) :=
  FreeQuery.vector count program >>= fun values => pure values.get

@[simp] theorem eval_tableM (H : HashN) {α : Type} (count : Nat) (program : Fin count → CM α) :
    (tableM count program).eval H = fun index => (program index).eval H := by
  funext index
  simp [tableM]

theorem bounded_tableM {α : Type} {count : Nat} {program : Fin count → CM α}
    {budget : Fin count → Nat} (bounded : ∀ index, (program index).Bounded (budget index)) :
    (tableM count program).Bounded (∑ index, budget index) :=
  (FreeQuery.Bounded.bind (FreeQuery.Bounded.vector bounded) fun _ =>
    FreeQuery.Bounded.pure' _ 0).of_eq (by simp)

/-- Store a finite family in an array, as a program step without queries: the array arrives as a
bind parameter, so the compiled closure reads it and never recomputes the family. -/
def storeM {α : Type} {count : Nat} (family : Fin count → α) : CM (Fin count → α) :=
  tableM count fun index => pure (family index)

@[simp] theorem eval_storeM (H : HashN) {α : Type} {count : Nat} (family : Fin count → α) :
    (storeM family).eval H = family := by
  funext index
  simp [storeM]

theorem bounded_storeM {α : Type} {count : Nat} (family : Fin count → α) :
    (storeM family).Bounded 0 :=
  (bounded_tableM (budget := fun _ => 0) fun _ => FreeQuery.Bounded.pure' _ 0).of_eq (by simp)

/-- Store the lanes of an arithmetic label (no query). -/
def materializeM {width : Nat} (lanes : Lanes width) : CM (Lanes width) := storeM lanes

@[simp] theorem eval_materializeM (H : HashN) {width : Nat} (lanes : Lanes width) :
    (materializeM lanes).eval H = lanes := eval_storeM H lanes

end Kriterion.CRT
