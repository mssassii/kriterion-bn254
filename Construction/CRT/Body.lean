/-
The body.

For modulus `m` (index `i`), each slot `ρ < m` of the final one-hot `h_m` and the coordinate's `S`
encodings: the pad natural `N_ρ = hlong(h_m[ρ], body tags (i, ρ, part), q)`, its fraction reading
`X_ρ = ⌊N_ρ * m ^ S / 2 ^ (256 q)⌋` and the digits `V_ρ[e] = ⌊X_ρ / m ^ e⌋ mod m`.

Garbler (slope-free): the residue `R_{e,m} = Σ_ρ ρ * V_ρ[e] mod m` and the pad sum
`Σ_ρ V_ρ[e] mod m`; the published residue join is `J_{e,m} = (pad sum + a_e) mod m`, formed after
the slopes exist (`Coord.lean`). Evaluator: the `m - 1` cold pad vectors (slots ascending, parts
ascending) and
`L_{e,m} = Σ_{ρ ≠ hot} ρ V_ρ[e] + hot * (J_{e,m} - Σ_{ρ ≠ hot} V_ρ[e])` in `ZMod m`, which equals
`R_{e,m} + (v mod m) * (a_e mod m)` (L15, xinshu's `evalScale_garbleScale` over `ZMod m`).
-/

import Construction.CRT.Fold

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC

/-- The tag of part `part` of the pad of slot `residue` of modulus index `i`. -/
def bodyTag (coord i residue part : Nat) : Nat := tagCode Family.body coord i 0 0 residue part

/-- The pad digits of one slot: `q` answers, the fraction reading, `S` digits base `m`. -/
def padVectorM (m S q : Nat) (label : Block) (tagOf : Nat → Nat) : CM (Fin S → Nat) :=
  hlongM label tagOf q >>= fun value =>
    let fraction := fractionValue m S q value
    pure (stored fun e => digit m fraction e.val)

/-- The garbler's body of one modulus. -/
structure BodyGarbled (S : Nat) where
  /-- `R_{e,m}`. -/
  residue : Fin S → Nat
  /-- `Σ_ρ V_ρ[e] mod m`. -/
  padSum : Fin S → Nat

/-- The garbler's body of modulus `m` (index `i`) on its final one-hot. -/
def bodyGarbleM (m S q coord i : Nat) (final : Fin m → Block) : CM (BodyGarbled S) :=
  tableM m (fun residue => padVectorM m S q (final residue) (bodyTag coord i residue.val))
    >>= fun pads =>
      pure { residue := stored fun e =>
               (∑ residue : Fin m, (residue.val : ZMod m) * (pads residue e : ZMod m)).val
             padSum := stored fun e => (∑ residue : Fin m, (pads residue e : ZMod m)).val }

/-- The evaluator's body of modulus `m` (index `i`) on its final one-hot with hot index `hot` and
the residue joins `joins e`: the residues `L_{e,m}`. -/
def bodyEvalM (m S q coord i : Nat) (final : Fin m → Block) (hot : Nat) (joins : Fin S → Nat) :
    CM (Fin S → Nat) :=
  tableM m (fun residue =>
    if residue.val = hot then pure fun _ => 0
    else padVectorM m S q (final residue) (bodyTag coord i residue.val)) >>= fun pads =>
      pure (stored fun e =>
        let known : ZMod m := ∑ residue : Fin m, if residue.val = hot then 0 else (pads residue e : ZMod m)
        let weighted : ZMod m := ∑ residue : Fin m,
          if residue.val = hot then 0 else (residue.val : ZMod m) * (pads residue e : ZMod m)
        (weighted + (hot : ZMod m) * ((joins e : ZMod m) - known)).val)

end Kriterion.CRT
