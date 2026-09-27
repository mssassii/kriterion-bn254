/-
**The machine's bounded samplers for the CRT entry** (M7), in `LawShape.BoundedSamplers crtEntry` form.

| knob | the machine's sampler | the exact sampler it replaces (`Instance.view`) |
|---|---|---|
| `source` | `CrtDraws.drawLaw` mapped by `CrtSource.sourceOf` (stage 1: bounded field cells, bounded digits, coin words) | the uniform `Entry.Source` |
| `rows` | `rows`: release-r1's `tailLaw` and `liftLaw` (`91` randomiser pairs `(λ, t)`) through `targetRows` | `simRows` = `simulatedRows` (`idealSamplers.tail`, `.lift`) |
| `preimage` | release-r1's `preimageLaw` (bounded multiplier) | `idealPreimage` |
| `fourth` | the view's own (a 128-coin word is exactly uniform, `Preimages.fourth_eq`) | the same |
-/

import Proof.Simulator.CRT.LawShape
import Proof.Simulator.CRT.Stage1Source
import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.PlanB.SimMachine

namespace CrtBounded

noncomputable section

/-- **The machine's rows**: the tail points and the lifts by release-r1's bounded samplers, the rows by
`targetRows` (the shape of `simulatedRows`). -/
def rows [FieldCertificate] [GroupCertificate] :
    AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)) := fun _ target =>
  tailLaw.bind fun tail => match tail with
  | none => PMF.pure none
  | some tail => liftLaw.bind fun lift => match lift with
    | none => PMF.pure none
    | some lift => PMF.pure (some (Phase3.Glue.targetRows target tail lift))

/-- The machine's stage-1 source law. -/
def source [FieldCertificate] : PMF (Option Entry.Source) := CrtDraws.drawLaw.map (Option.map CrtSource.sourceOf)

/-- **The bounded samplers of the CRT machine.** -/
def samplers : LawShape.BoundedSamplers Privacy.Instance.crtEntry := fun field group =>
  letI := field
  letI := group
  { source := source
    rows := rows
    preimage := preimageLaw
    fourth := (@Privacy.Instance.view field group).fourth }

end

end CrtBounded

end Kriterion.CRT.SimMachine
