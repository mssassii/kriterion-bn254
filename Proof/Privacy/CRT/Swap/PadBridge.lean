/-
**The pad reading of the privacy side is the construction's** (`Swap/Reading.lean`'s `padVector` against
`padVectorM`, `Construction/CRT/Body.lean`): the program's digits, cast to `ZMod m`, are `padVector` of
the answers it reads.
-/

import Proof.Privacy.CRT.Swap.Reading
import Proof.Correctness.CRT.BodyStep

namespace Kriterion.CRT.Privacy

open Cryptography Kriterion.CRT

/-- **The bridge**: `padVectorM` at a label and a tag map reads `padVector` of its `q` answers. -/
theorem padVectorM_eq_padVector (H : HashN) (m S q : ℕ) (label : Label) (tagOf : ℕ → ℕ) :
    (fun e => (((padVectorM m S q label tagOf).eval H e : ℕ) : ZMod m))
      = padVector m S q (fun j => H (hashInput (embed label) (tagOf j.val))) := by
  funext e
  simp [Kriterion.CRT.SliceC.eval_padVectorM, padVector, hlong]

end Kriterion.CRT.Privacy
