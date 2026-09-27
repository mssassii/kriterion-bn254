/-
**P45: the joint body-mask-row lemma, formulation 1 of F2**.

The layer's coins, after the swap `G0T → G0U`: every pad vector (every modulus, slot and encoding), the 637 Embryo
masks, the row randomizers and the curve coins. Formulation 1 takes the row offsets `b_e = (O_e : F_p) − π_e` as
coins, so the slopes are functions of coins, each hot pad vector is a translate of its residue join, the
per-digit bijection sends the row offsets to the published constants and the non-collector row values, and
the masks are derived. The row randomizers are all unused coins (the coefficient cut carries every coefficient in the
slopes, and the sign row's shift `t` is a function of an offset).

Encodings are indexed structurally: `Enc = (Fin 91 × XElement ⊕ CurveXElement) ⊕ (Fin 91 × YElement ⊕ CurveYElement)`
(`367 + 275 = 642`); the construction's flat order is a bijection onto `Fin 367` and `Fin 275` (row P45.0). The
table `T` is abstract (`CrtTable`); `TableFacts` lists what the statements need of it.

Statements (proved in `Core/BodyMaskRowJoint.lean`, `Core/BodyMaskRowOff.lean` and `Core/WrapMass.lean`):

* `bmrEquiv` (P45.a, `BodyMaskRowJoint.lean`): coins ≃ (hint-free published cells × visible cells) × residual, on
  the curve;
* `bmr_real_eq_ideal` (P45.b, `BodyMaskRowJoint.lean`): off the wrap event, the real outputs are the ideal outputs
  of the image;
* `bmr_wrap_mass` (P45.c, in `Core/WrapMass.lean`, proved): the wrap event has mass at most `642 (B − 1)/M`;
* `bmr_core` (`BodyMaskRowJoint.lean`): the exact core, `CoreUntilBad`'s `realCore = simCore` for this layer;
* the same three off the curve (`bmrEquivOff`, `bmr_real_eq_ideal_off`, `bmr_core_off`, `BodyMaskRowOff.lean`).
-/

import Construction.CRT.Params
import Construction.ArgoMAC.FieldMacToECMac
import Construction.ArgoMAC.CurveMembership
import Proof.Privacy.CRT.Sites
import Mathlib.Probability.Distributions.Uniform

namespace Kriterion.CRT.Privacy.BMR

open BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

/-! ### Encodings -/

/-- The 367 encodings of coordinate `x`: 91 digits × 4 point elements, and the 3 curve elements. -/
abbrev XEnc := (Fin 91 × XElement) ⊕ CurveXElement
/-- The 275 encodings of coordinate `y`: 91 digits × 3 point elements, and the 2 curve elements. -/
abbrev YEnc := (Fin 91 × YElement) ⊕ CurveYElement
/-- All 642 encodings. -/
abbrev Enc := XEnc ⊕ YEnc
/-- The 637 row encodings: one per digit and row element. -/
abbrev RowEnc := Fin 91 × Biquadratic.Element

/-- A row encoding as an encoding. -/
def rowEnc : RowEnc → Enc
  | (d, .inl x) => .inl (.inl (d, x))
  | (d, .inr y) => .inr (.inl (d, y))

/-- A curve encoding as an encoding. -/
def curveEnc : CurveMembership.Element → Enc
  | .inl x => .inl (.inr x)
  | .inr y => .inr (.inr y)

/-- The coordinate of an encoding (`0` for `x`). -/
def coordOf : Enc → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The collectors: the `x` slots `rowX_x9`, `rowY_cubic`, `rowZ_x9` of every digit (D3). -/
def IsCollector (element : Biquadratic.Element) : Prop :=
  element = .inl .rowX_x9 ∨ element = .inl .rowY_cubic ∨ element = .inl .rowZ_x9

instance (element : Biquadratic.Element) : Decidable (IsCollector element) := by
  unfold IsCollector; infer_instance

/-- The 273 collector encodings. -/
abbrev Collector := {r : RowEnc // IsCollector r.2}
/-- The 364 non-collector row encodings. -/
abbrev NonCollector := {r : RowEnc // ¬ IsCollector r.2}

/-! ### The table and the context -/

variable (T : CrtTable)

/-- What the statements need of the modulus table (for `bn254Table`: row C4.facts). -/
structure TableFacts : Prop where
  pos : ∀ i, 0 < T.modulus i
  coprime : ∀ i j, i ≠ j → Nat.Coprime (T.modulus i) (T.modulus j)
  wrapBound_eq : T.wrapBound = wrapBound baseFieldModulus
  wrap_room : 2 * T.wrapBound ≤ T.product

/-- The quantities outside this layer that it reads: the row coefficients and `ρ` of each digit (functions of the
scalar and of coins outside the layer; xinshu's `JointContext`). -/
structure Context where
  rows : Fin 91 → Coordinates.Rows
  rho : Fin 91 → NonZeroBase

variable [∀ i, NeZero (T.modulus i)]

/-! ### The coins -/

/-- Every pad vector: modulus index, slot, encoding (the per-coordinate pad vectors of D6, reindexed). -/
abbrev Pads := (i : Fin T.count) → ZMod (T.modulus i) → Enc → ZMod (T.modulus i)

/-- **The coins of the layer**: pads, the 637 masks, the eight unused row randomizers of each digit (`r4` and seven
more), and the curve coins `(t, mask ≠ 0, r1, r2)`. -/
abbrev Coins := Pads T × (RowEnc → BaseField) × (Fin 91 → BaseField) × (Fin 91 → Fin 7 → BaseField) ×
  (BaseField × {m : BaseField // m ≠ 0} × BaseField × BaseField)

/-! Named instances. -/

/-- `F_p` has a nonzero element. -/
theorem one_ne_zero_base : (1 : BaseField) ≠ 0 := by decide

/-- The curve mask's type, nonempty. -/
instance nonZeroBaseNonempty : Nonempty {m : BaseField // m ≠ 0} := ⟨⟨1, one_ne_zero_base⟩⟩

/-- `RowGamma` is three field elements. -/
def rowGammaEquiv : RowGamma ≃ BaseField × BaseField × BaseField where
  toFun g := (g.xC0, g.yC4, g.zC0)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance rowGammaFintype : Fintype RowGamma := Fintype.ofEquiv _ rowGammaEquiv.symm

instance padsFintype : Fintype (Pads T) :=
  @Pi.instFintype _ _ _ _ fun _ => @Pi.instFintype _ _ _ _ fun _ => @Pi.instFintype _ _ _ _ fun _ => inferInstance

instance padsNonempty : Nonempty (Pads T) := ⟨fun _ _ _ => 0⟩

instance coinsFintype : Fintype (Coins T) := instFintypeProd _ _

instance coinsNonempty : Nonempty (Coins T) := ⟨(fun _ _ _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0,
  (0, ⟨1, one_ne_zero_base⟩, 0, 0))⟩

variable {T}

def Coins.pads (c : Coins T) : Pads T := c.1
def Coins.mask (c : Coins T) : RowEnc → BaseField := c.2.1
def Coins.r4 (c : Coins T) : Fin 91 → BaseField := c.2.2.1
def Coins.unused (c : Coins T) : Fin 91 → Fin 7 → BaseField := c.2.2.2.1
def Coins.bridge (c : Coins T) : BaseField := c.2.2.2.2.1
def Coins.curveMask (c : Coins T) : BaseField := c.2.2.2.2.2.1.1
def Coins.r1 (c : Coins T) : BaseField := c.2.2.2.2.2.2.1
def Coins.r2 (c : Coins T) : BaseField := c.2.2.2.2.2.2.2

/-- The eight randomizers of a digit from `r4` and the seven others (none is read). -/
def rowRand (r4 : BaseField) (unused : Fin 7 → BaseField) :
    Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness :=
  (⟨unused 0, unused 1, unused 2⟩, ⟨unused 3, unused 4, r4, unused 5⟩, ⟨unused 6⟩)

/-! ### The real layer -/

/-- The garbler's readout of modulus `i` for encoding `e`: `Σ_ρ ρ · V_ρ[e]`. -/
def readout (c : Coins T) (e : Enc) (i : Fin T.count) : ZMod (T.modulus i) :=
  ∑ ρ : ZMod (T.modulus i), ρ * c.pads i ρ e

/-- The CRT offset `O_e ∈ [0, M)`. -/
def offset (c : Coins T) (e : Enc) : ℕ := T.crt fun i => (readout c e i).val

/-- The offset handed to the rows, `(O_e : F_p)`. -/
def offsetF (c : Coins T) (e : Enc) : BaseField := (offset c e : BaseField)

/-- **The row offset** `b_e = (O_e : F_p) − π_e` of a row encoding (formulation 1's coin). -/
def rowOffset (c : Coins T) (r : RowEnc) : BaseField := offsetF c (rowEnc r) - c.mask r

/-- The digit's seven slopes, from its row offsets (`Biquadratic.slopes`). -/
def digitSlopes (ctx : Context) (c : Coins T) (d : Fin 91) : Biquadratic.Values :=
  let rand := rowRand (c.r4 d) (c.unused d)
  Biquadratic.slopes (ctx.rows d) rand.1 rand.2.1 rand.2.2 fun element => rowOffset c (d, element)

/-- The curve encodings' offsets. -/
def curveK (c : Coins T) : CurveMembership.Values := fun element => offsetF c (curveEnc element)

/-- The slope of every encoding. -/
def slope (ctx : Context) (c : Coins T) : Enc → BaseField
  | .inl (.inl (d, x)) => digitSlopes ctx c d (.inl x)
  | .inr (.inl (d, y)) => digitSlopes ctx c d (.inr y)
  | .inl (.inr x) => CurveMembership.slopes c.r1 c.r2 (curveK c) (.inl x)
  | .inr (.inr y) => CurveMembership.slopes c.r1 c.r2 (curveK c) (.inr y)

/-- **The residue join** `J_{e,i} = Σ_ρ V_ρ[e] + a_e mod m_i`. -/
def join (ctx : Context) (c : Coins T) (e : Enc) (i : Fin T.count) : ZMod (T.modulus i) :=
  ∑ ρ : ZMod (T.modulus i), c.pads i ρ e + ((slope ctx c e).val : ZMod (T.modulus i))

/-- The wrap hint `[O_e > M − B]` (D7). -/
def hint (c : Coins T) (e : Enc) : Bool := wrapHint T.product T.wrapBound (offset c e)

/-- The digit's three published constants (`garbleRow` on the row offsets). -/
def gamma (ctx : Context) (c : Coins T) (d : Fin 91) : RowGamma :=
  FieldMacToECMac.garbleRow (ctx.rows d) fun element => rowOffset c (d, element)

/-- The curve check's three published constants. -/
def curveTable (c : Coins T) : BaseField × BaseField × BaseField :=
  CurveMembership.garble c.bridge c.curveMask c.r1 c.r2 (curveK c)

/-! ### The evaluator at `u` -/

variable (T)

/-- The hot residue of encoding `e` at modulus `i`: `v mod m_i` for its coordinate's value `v`. -/
def hotRes (u : AffineInput) (e : Enc) (i : Fin T.count) : ZMod (T.modulus i) :=
  (coordValue u (coordOf e) : ZMod (T.modulus i))

/-- The cold pad entries at `u`. -/
abbrev Cold (u : AffineInput) :=
  (i : Fin T.count) → (e : Enc) → {ρ : ZMod (T.modulus i) // ρ ≠ hotRes T u e i} → ZMod (T.modulus i)

/-- The published residue joins. -/
abbrev Joins := Enc → (i : Fin T.count) → ZMod (T.modulus i)

variable {T}

/-- The evaluator's residue `L = Σ_{ρ ≠ h} ρ V_ρ + h (J − Σ_{ρ ≠ h} V_ρ)`. -/
def evalResidue (u : AffineInput) (J : Joins T) (cold : Cold T u) (e : Enc) (i : Fin T.count) :
    ZMod (T.modulus i) :=
  let h := hotRes T u e i
  (∑ ρ : {ρ : ZMod (T.modulus i) // ρ ≠ h}, ρ.1 * cold i e ρ) +
    h * (J e i - ∑ ρ : {ρ : ZMod (T.modulus i) // ρ ≠ h}, cold i e ρ)

/-- The evaluator's CRT integer `w`. -/
def evalInt (u : AffineInput) (J : Joins T) (cold : Cold T u) (e : Enc) : ℕ :=
  T.crt fun i => (evalResidue u J cold e i).val

/-- The real delivered value (wrap-hint decoding, D7). -/
def delivered (u : AffineInput) (J : Joins T) (hints : Enc → Bool) (cold : Cold T u) (e : Enc) : BaseField :=
  (wrapDecode T.product T.wrapBound (hints e) (evalInt u J cold e) : BaseField)

/-- The ideal delivered value `v⁰` (hint 0). -/
def deliveredIdeal (u : AffineInput) (J : Joins T) (cold : Cold T u) (e : Enc) : BaseField :=
  (evalInt u J cold e : BaseField)

/-! ### The outputs -/

variable (T)

/-- The hint-free published cells of the layer: the residue joins, the row constants, the curve constants. -/
abbrev Source := Joins T × (Fin 91 → RowGamma) × (BaseField × BaseField × BaseField)

/-- The visible cells at `u` on the curve: every cold pad entry, every non-collector mask. -/
abbrev Visible (u : AffineInput) := Cold T u × (NonCollector → BaseField)

instance joinsFintype : Fintype (Joins T) := @Pi.instFintype _ _ _ _ fun _ => @Pi.instFintype _ _ _ _ fun _ => inferInstance

instance coldFintype (u : AffineInput) : Fintype (Cold T u) :=
  @Pi.instFintype _ _ _ _ fun _ => @Pi.instFintype _ _ _ _ fun _ => inferInstance

instance sourceFintype : Fintype (Source T) := instFintypeProd _ _

instance visibleFintype (u : AffineInput) : Fintype (Visible T u) := instFintypeProd _ _

instance sourceNonempty : Nonempty (Source T) :=
  ⟨(fun _ _ => 0, fun _ => ⟨0, 0, 0⟩, (0, 0, 0))⟩

instance coldNonempty (u : AffineInput) : Nonempty (Cold T u) := ⟨fun _ _ _ => 0⟩

instance visibleNonempty (u : AffineInput) : Nonempty (Visible T u) := ⟨(fun _ _ _ => 0, fun _ => 0)⟩

/-- The outputs: (published cells, hints), visible cells, the collector masks, the bridge key. -/
abbrev Out (u : AffineInput) := (Source T × (Enc → Bool)) × Visible T u × (Collector → BaseField) × BaseField

/-- The residual coordinates: the eight unused randomizers of each digit (`r4`, then the seven others) and the curve
mask. -/
abbrev Residual := (Fin 91 → BaseField) × (Fin 91 → Fin 7 → BaseField) × {m : BaseField // m ≠ 0}

instance residualNonempty : Nonempty Residual := ⟨(fun _ => 0, fun _ _ => 0, ⟨1, one_ne_zero_base⟩)⟩

instance cellsResidualNonempty (u : AffineInput) : Nonempty ((Source T × Visible T u) × Residual) :=
  ⟨((Classical.arbitrary _, Classical.arbitrary _), Classical.arbitrary _)⟩

instance cellsNonempty (u : AffineInput) : Nonempty (Source T × Visible T u) :=
  ⟨(Classical.arbitrary _, Classical.arbitrary _)⟩

instance residualFintype : Fintype Residual := instFintypeProd _ _

instance cellsFintype (u : AffineInput) : Fintype (Source T × Visible T u) := instFintypeProd _ _

instance cellsResidualFintype (u : AffineInput) : Fintype ((Source T × Visible T u) × Residual) :=
  instFintypeProd _ _

variable {T}

/-- The cold pad entries of the coins. -/
def coldOf (u : AffineInput) (c : Coins T) : Cold T u := fun i e ρ => c.pads i ρ.1 e

/-- **The real outputs** of the layer at `u`. -/
def realOut (ctx : Context) (u : AffineInput) (c : Coins T) : Out T u :=
  (((join ctx c, gamma ctx c, curveTable c), hint c), (coldOf u c, fun r => c.mask r.1),
    fun r => c.mask r.1, c.bridge)

/-- The true row values of a digit at `u` (xinshu's `rowTarget`; the sign row in the `y` slot). -/
def rowTarget (rows : Coordinates.Rows) (u : AffineInput) : FieldMacToECMac.HomogeneousValue :=
  ⟨rows.x.constant + rows.x.x * u.x + rows.x.y * u.y + rows.x.xSquared * u.x ^ 2,
   rows.y.constant + rows.y.y * u.y + rows.y.xSquared * u.x ^ 2 + rows.y.ySquared * u.y ^ 2,
   rows.z.constant + rows.z.x * u.x⟩

/-- **The route-M collector solve**: the row-level value of a collector that makes its row equal the target, given
the published constants and the other elements' row-level values (the `X` and `Z` collectors have multiplier 1,
the sign row's collector `x²`, divided out as the inverse `(x · x)⁻¹`). -/
def collectorSolve (target : FieldMacToECMac.HomogeneousValue) (g : RowGamma) (u : AffineInput)
    (values : Biquadratic.Values) : Biquadratic.Element → BaseField
  | .inl .rowX_x9 => target.x - (g.xC0 + values (.inl .rowX_x7) * u.x + values (.inr .rowX_y10))
  | .inl .rowY_cubic => (target.y - (g.yC4 * u.x ^ 2 + values (.inr .rowY_y8) * u.y +
      values (.inr .rowY_y10))) * (u.x * u.x)⁻¹
  | .inl .rowZ_x9 => target.z - g.zC0
  | _ => 0

/-- **The ideal outputs** at `u` from a source and visible cells: hints 0, the collector masks
`π_c = v⁰_c − τ_c` of the route-M solve at the true rows, the key as the evaluator's curve value. -/
def idealOut (ctx : Context) (u : AffineInput) (cells : Source T × Visible T u) : Out T u :=
  let src := cells.1
  let vis := cells.2
  let v0 := deliveredIdeal u src.1 vis.1
  let rowValue (d : Fin 91) : Biquadratic.Values := fun element =>
    if h : IsCollector element then 0 else v0 (rowEnc (d, element)) - vis.2 ⟨(d, element), h⟩
  ((src, fun _ => false), vis,
    fun r => v0 (rowEnc r.1) -
      collectorSolve (rowTarget (ctx.rows r.1.1) u) (src.2.1 r.1.1) u (rowValue r.1.1) r.1.2,
    CurveMembership.evaluate src.2.2 u fun element => v0 (curveEnc element))

/-! ### The statements -/

variable (T)

/-- The first coordinate of a uniform product law is uniform. -/
theorem uniform_map_fst {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.fst = PMF.uniformOfFintype A := by
  classical
  apply PMF.ext
  intro a
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod]
  rw [ENNReal.tsum_prod']
  push_cast
  rw [ENNReal.mul_inv] <;> try simp [Fintype.card_ne_zero]
  rw [mul_left_comm, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast Fintype.card_ne_zero
  · simp

/-- A bijection pushes the uniform law to the uniform law. -/
theorem uniform_map_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (e : A ≃ B) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  classical
  refine PMF.ext fun b => ?_
  rw [PMF.map_apply, tsum_eq_single (e.symm b) (fun a hne => ?_)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · have notHit : b ≠ e a := fun hit => hne (by rw [hit, Equiv.symm_apply_apply])
    simp [notHit]

/-! ### Off the curve -/

/-- The outputs off the curve: (published cells, hints) and the cold pad entries (masks and bridge hidden). -/
abbrev OutOff (u : AffineInput) := (Source T × (Enc → Bool)) × Cold T u

/-- The residual off the curve: per digit the row offsets of the four row encodings that no constant absorbs
(`rowX_x7`, `rowX_y10`, `rowY_y8`, `rowY_y10`; offsets, not masks, because the sign row's slopes of `rowY_y8` and
`rowY_y10` read each other's offset), then the on-curve residual (`r4`, the unused randomizers, the curve mask). -/
abbrev ResidualOff := (Fin 91 → Fin 4 → BaseField) × Residual

instance residualOffNonempty : Nonempty ResidualOff := ⟨(fun _ _ => 0, Classical.arbitrary _)⟩

instance residualOffFintype : Fintype ResidualOff := instFintypeProd _ _

instance cellsOffNonempty (u : AffineInput) : Nonempty (Source T × Cold T u) :=
  ⟨(Classical.arbitrary _, Classical.arbitrary _)⟩

instance cellsOffFintype (u : AffineInput) : Fintype (Source T × Cold T u) := instFintypeProd _ _

instance cellsResidualOffNonempty (u : AffineInput) : Nonempty ((Source T × Cold T u) × ResidualOff) :=
  ⟨((Classical.arbitrary _, Classical.arbitrary _), Classical.arbitrary _)⟩

instance cellsResidualOffFintype (u : AffineInput) : Fintype ((Source T × Cold T u) × ResidualOff) :=
  instFintypeProd _ _

variable {T}

def realOutOff (ctx : Context) (u : AffineInput) (c : Coins T) : OutOff T u :=
  (((join ctx c, gamma ctx c, curveTable c), hint c), coldOf u c)

def idealOutOff (u : AffineInput) (cells : Source T × Cold T u) : OutOff T u := ((cells.1, fun _ => false), cells.2)

variable (T)

end

end Kriterion.CRT.Privacy.BMR
