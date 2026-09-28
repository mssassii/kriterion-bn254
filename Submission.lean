/-
The CRT entry at the challenge's `Solution` record (CRT-residue projectivization, sign rows, 135,855 bytes).
Every field has a proof term; every odd CRT row uses first extraction width 8, and the
conversion casts carry their control label in the low plane so every pin is even and is published halved;
the chunk-tree joins are absorbed into the Lamport labels and not published.

* `FixedIndex` and `EncIndex` are `Empty` (the entry is hash-only);
* `Randomness` is the switch-system entry's `Scheme.Coins` (the CRT layer draws no coins of its own);
* `Public` is `Kriterion.CRT.Entry.Public`, 135,855 bytes (`Wire.encoding_length`);
* `garbleProgram` / `evaluateProgram` are `Entry.garbleProgram` / `Entry.evaluateProgram` at the
  term-by-term budgets `garbleBudget` (988,438) and `evaluateBudget` (981,506);
* `perfectCorrectness` is `Kriterion.CRT.EntryCorrect.perfectCorrectness`
  (`Proof/Correctness/CRT/EntryCorrect.lean`);
* `adaptivePrivacy` is `Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy`
  (`Proof/Privacy/CRT/Final.lean`), the closed CRT hybrid chain with the CRT simulator machine, whose
  statement `CrtPrivacy crtEntry` is the type of this field once `crtEntry`'s projections are reduced.

As in the switch-system entry's `Submission.lean`, each non-trivial field is a standalone theorem named
in the instance, and `scheme` is the constant `@Entry.scheme`.
-/

import Solution
import Construction
import Proof

set_option maxRecDepth 8000

namespace Submission

open Kriterion Kriterion.BN254 Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry

/-- `Solution.lamportCompatible`: `Encode` selects one label of each of the 508 pairs. -/
def lamportCompatible (field : FieldCertificate) (group : @GroupCertificate field) :
    GarbledCircuit.LamportCompatibility (@Entry.scheme field group) affineLamportBits where
  keyPairs key := Lamport.keyPairs key
  encodeSelectsLabels key input := Lamport.selectedLabels_eq key input

/-- `Solution.garbleProgramCorrect`: the program is the lifted `garbleCM`, and the scheme's garbler
is `garbleCM` evaluated at the scheme's hash. -/
theorem garbleProgramCorrect (field : FieldCertificate) (group : @GroupCertificate field)
    (parameter : Nat) (scalar : NonZeroScalar) (coins : Entry.Coins) (oracle : Entry.Oracle) :
    (Entry.garbleProgram scalar coins).eval (Cryptography.publicAnswer oracle) =
      (@Entry.scheme field group).garble parameter scalar (coins, oracle) := by
  rw [Entry.garbleProgram, FreeQuery.eval_toProgram, Entry.garbleM, eval_liftHash]
  simp only [Entry.scheme]

/-- `Solution.evaluateProgramCorrect`. -/
theorem evaluateProgramCorrect (field : FieldCertificate) (group : @GroupCertificate field)
    (pub : Entry.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature)
    (oracle : Entry.Oracle) :
    (@Entry.evaluateProgram field group pub input labels).eval (Cryptography.publicAnswer oracle) =
      (@Entry.scheme field group).evaluate oracle pub input labels := by
  rw [Entry.evaluateProgram, FreeQuery.eval_toProgram, Entry.evaluateM, eval_liftHash]
  simp only [Entry.scheme]

/-- `Solution.ciphertextSize`: every public value is 135,855 bytes. -/
theorem ciphertextSize (field : FieldCertificate) (group : @GroupCertificate field) (parameter : Nat)
    (scalar : NonZeroScalar) (tape : Entry.Coins × Entry.Oracle) :
    (Wire.encoding.encode ((@Entry.scheme field group).garble parameter scalar tape).1).length =
      ciphertextBytes :=
  Wire.encoding_length _

/-- `Solution.perfectCorrectness` (`Proof/Correctness/CRT/EntryCorrect.lean`): the replay delivers
through the published material (`coord_delivery` on the real table), the curve check
releases `t`, the rows are the switch-system entry's delivered values, the digest unlocks every exceptional digit
(both kinds, `Q = K` and `Q = 2K`), and the decode chain with the sign row gives the scalar multiple. -/
theorem perfectCorrectness (field : FieldCertificate) (group : @GroupCertificate field) :
    GarbledCircuit.PerfectCorrectness (@Entry.scheme field group) Prod.snd :=
  Kriterion.CRT.EntryCorrect.perfectCorrectness field group

/-- The configuration-E submission with sign rows, at 135,855 bytes. -/
def solution : Kriterion.Solution := {
  FixedIndex := Empty
  EncIndex := Empty
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Entry.Coins
  randomnessFinite := inferInstance
  randomness := Entry.witness
  Public := Entry.Public
  EncodingKey := Entry.Key
  encoding := Wire.encoding
  ciphertextBytes := ciphertextBytes
  garbleQueries := garbleBudget
  evaluateQueries := evaluateBudget
  scheme := @Entry.scheme
  garbleProgram := fun _ _ _ => Entry.garbleProgram
  evaluateProgram := @Entry.evaluateProgram
  garbleProgramCorrect := garbleProgramCorrect
  evaluateProgramCorrect := evaluateProgramCorrect
  ciphertextSize := by
    intro field group parameter scalar tape
    exact Wire.encoding_length _
  lamportCompatible := lamportCompatible
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := perfectCorrectness
  adaptivePrivacy := by
    intro field group
    have h := Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy field group
    simp only [Kriterion.CRT.Privacy.Instance.crtEntry] at h
    exact h
}

end Submission
