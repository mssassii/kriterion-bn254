/-
**Route M's preimages and fourth blocks, against the abstract simulator** (M6).

The machine's `Preimages.preimages` is `rep 91 (rep 3 preimageSite)`: for site `k = 3 d + c`, release-r1's verbatim
`preimageOne d c` (a multiplier `m < q + [π < ρ]` by bounded rejection, then the limbs of `π + p · m` at
`openLimb d c`), then a 128-coin word at `Layout.fourthCell k`.

* `siteLaw`, `siteMem`, `memSem_preimageSite`: one site draws `(m, coin)` and stores it;
* `memSem_preimages`, `sem_preimages`: the 273 sites are the product of their draws, folded by `siteStep`;
* `siteSample_eq`, `drawAll_sites`: the abstract simulator's draw (`drawAll` over `collectorList` of the bounded
  samplers `preimageLaw` and the exact fourth block) is the same product, decoded by `decodeSite`;
* `allHold_after`, `drawn_eq`, `frame_after`: after the stores, the program batch's cells hold exactly the decoded
  draws (`Programs.AllHold programCells`), the abstract list is `collectorList.map (c, draws c)`, and the frame.
-/

import Proof.Simulator.OpeningPreimages
import Proof.Simulator.Stage1Cells
import Proof.Simulator.OracleUse
import Proof.Simulator.CRT.Programs
import Construction.Simulator.CRT.Preimages

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue (optionProduct limbs preimageCount)

noncomputable section

namespace Preimages

/-! ### Folds of stores (generic) -/

/-- A reading every step keeps is kept by the fold. -/
theorem foldStore_keep {α β : Type} (read : Memory → β) :
    ∀ (step : Nat → Memory → α → Memory) (count : Nat) (memory : Memory) (values : Fin count → α),
      (∀ index, index < count → ∀ later value, read (step index later value) = read later) →
      read (foldStore step count memory values) = read memory
  | _, 0, _, _, _ => by rw [foldStore]
  | step, count + 1, memory, values, keeps => by
      rw [foldStore, foldStore_keep read (fun index => step (index + 1)) count _ _
        (fun index bound => keeps (index + 1) (by omega)), keeps 0 (by omega)]

/-- A cell set by step `index` and kept by every later step. -/
theorem foldStore_ram_set {α : Type} (target : Word) :
    ∀ (step : Nat → Memory → α → Memory) (count : Nat) (memory : Memory) (values : Fin count → α)
      (index : Fin count) (value : Word),
      (∀ later, (step index later (values index)).ram target = value) →
      (∀ later, index.val < later → later < count → ∀ other drawn,
        (step later other drawn).ram target = other.ram target) →
      (foldStore step count memory values).ram target = value
  | _, 0, _, _, index, _, _, _ => index.elim0
  | step, count + 1, memory, values, ⟨0, _⟩, value, sets, keeps => by
      rw [foldStore, foldStore_keep (fun later => later.ram target) (fun index => step (index + 1)) count _ _
        (fun index bound => keeps (index + 1) (by show 0 < index + 1; omega) (by omega))]
      exact sets memory
  | step, count + 1, memory, values, ⟨index + 1, bound⟩, value, sets, keeps => by
      rw [foldStore]
      exact foldStore_ram_set target (fun index => step (index + 1)) count _ (fun index => values index.succ)
        ⟨index, by omega⟩ value (fun later => sets later)
        (fun later after inside => keeps (later + 1) (by simp only at after ⊢; omega) (by omega))

/-! ### One site -/

variable [FieldCertificate]

/-- One site's draws: the multiplier by bounded rejection below `q + [π < ρ]`, then 128 coins. -/
def siteLaw (value : BaseField) : PMF (Option (Nat × Nat)) :=
  (rejectLaw multiplierWidth (fun candidate => decide (candidate < multBound value)) attempts).bind fun drawn =>
    match drawn with
    | none => PMF.pure none
    | some mult => (wordLaw 128).map fun coin => some (mult, coin)

/-- The memory one site leaves. -/
def siteMem (d c : Nat) (value : BaseField) (memory : Memory) (drawn : Nat × Nat) : Memory :=
  clearRegs (storeRam (preMem d c value memory drawn.1) (word (Layout.fourthCell (3 * d + c)))
    (BitVec.ofNat 256 drawn.2)) [rAcc, rBit, rAddr]

/-- **One site**: the multiplier draw, the limbs, the fourth block. -/
theorem memSem_preimageSite (d c : Nat) (dSmall : d < 91) (cSmall : c < 3) (memory : Memory)
    (value : BaseField) (targetCell : memory.ram (word (openTarget d c)) = fieldWord value) :
    (preimageSite d c).memSem memory = (siteLaw value).map (Option.map (siteMem d c value memory)) := by
  unfold preimageSite fourthCoin siteLaw
  rw [memSem_seq, memSem_preimageOne d c dSmall cSmall memory value targetCell, PMF.bind_map, PMF.map_bind]
  apply PMF.bind_congr
  intro drawn _
  cases drawn with
  | none => simp [kleisli, PMF.pure_map]
  | some mult =>
      simp only [Function.comp_apply, Option.map_some, kleisli]
      rw [memSem_wordCell 128 _ (by norm_num), PMF.map_comp]
      rfl

/-! ### The 273 sites -/

/-- Flat site `i` is collector `i % 3` of digit `i / 3`. -/
def collectorOf (index : Fin 273) : Privacy.BMR.Collector :=
  Programs.collectorAt ⟨index.val / 3, by omega⟩ ⟨index.val % 3, by omega⟩

/-- The mask of flat site `i`. -/
def maskAt (masks : Privacy.BMR.Collector → BaseField) (index : Nat) : BaseField :=
  if inside : index < 273 then masks (collectorOf ⟨index, inside⟩) else 0

/-- The store of flat site `i`. -/
def siteStep (masks : Privacy.BMR.Collector → BaseField) (index : Nat) (memory : Memory) (drawn : Nat × Nat) :
    Memory :=
  siteMem (index / 3) (index % 3) (maskAt masks index) memory drawn

theorem siteStep_ram_off (masks : Privacy.BMR.Collector → BaseField) (index : Nat) (memory : Memory)
    (drawn : Nat × Nat) (target : Word) (notM : target ≠ word tmpM)
    (notLimb : ∀ position, position < 3 → target ≠ word (openLimb (index / 3) (index % 3) 0 + position))
    (notFourth : target ≠ word (Layout.fourthCell index)) :
    (siteStep masks index memory drawn).ram target = memory.ram target := by
  unfold siteStep siteMem preMem
  rw [(clearRegs_other _ _).1, storeRam_ram, Nat.div_add_mod, Function.update_of_ne notFourth,
    (clearRegs_other _ _).1, withRam_ram, putPoint_off _ _ _ _ notLimb, Function.update_of_ne notM]

/-- **The preimages**: 273 independent site draws, one per collector, in `collectorList` order. -/
theorem memSem_preimages (memory : Memory) (masks : Privacy.BMR.Collector → BaseField)
    (cells : ∀ (d : Fin 91) (c : Fin 3),
      memory.ram (word (openTarget d c)) = fieldWord (masks (Programs.collectorAt d c))) :
    preimages.memSem memory =
      (optionProduct 273 fun index => siteLaw (masks (collectorOf index))).map
        (Option.map (foldStore (siteStep masks) 273 memory)) := by
  have holdsStart : ∀ index, index < 273 →
      memory.ram (word (openTarget (index / 3) (index % 3))) = fieldWord (maskAt masks index) := by
    intro index inside
    unfold maskAt
    rw [dif_pos inside]
    exact cells ⟨index / 3, by omega⟩ ⟨index % 3, by omega⟩
  unfold preimages
  rw [memSem_rep_nest 3 (fun d c => preimageSite d c) (by norm_num) 91 memory]
  change (Prog.rep 273 _).memSem memory = _
  have lawIs : (fun index : Fin 273 => siteLaw (masks (collectorOf index))) =
      fun index : Fin 273 => siteLaw (maskAt masks index.val) := by
    funext index
    unfold maskAt
    rw [dif_pos index.isLt]
  rw [lawIs]
  exact memSem_rep_law_idx (fun later => ∀ index, index < 273 →
      later.ram (word (openTarget (index / 3) (index % 3))) = fieldWord (maskAt masks index))
    273 (fun index => siteLaw (maskAt masks index)) _ (siteStep masks)
    (fun index bound later holds => memSem_preimageSite (index / 3) (index % 3) (by omega) (by omega)
      later (maskAt masks index) (holds index bound))
    (fun index bound later drawn holds other otherBound => by
      rw [siteStep_ram_off masks index later drawn _ (by addr_ne) (fun position inside => by addr_ne)
        (by apply word_ne <;> simp only [Layout.fourthCell, openTarget, openBase] <;> omega)]
      exact holds other otherBound)
    memory holdsStart

omit [FieldCertificate] in
/-- The preimages make no oracle call. -/
theorem preimages_noOracle : preimages.NoOracle :=
  noOracle_rep _ _ fun _ _ => noOracle_rep _ _ fun _ _ => by
    unfold preimageSite fourthCoin Stage1.wordCell Opening.preimageOne Opening.limbsOf Opening.shr128
    simp only [Prog.seqList]
    exact ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, noOracle_bounded _ _ _ _ rfl ⟨rfl, rfl⟩,
        noOracle_zeroRegs _,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, noOracle_zeroRegs _, trivial⟩,
        trivial⟩, noOracle_sampleWord _, ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩

/-- **The preimages on the machine's semantics**: the oracle is untouched. -/
theorem sem_preimages {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (memory : Memory) (masks : Privacy.BMR.Collector → BaseField)
    (cells : ∀ (d : Fin 91) (c : Fin 3),
      memory.ram (word (openTarget d c)) = fieldWord (masks (Programs.collectorAt d c)))
    (oracle : OState FI EI) :
    preimages.sem memory oracle =
      (optionProduct 273 fun index => siteLaw (masks (collectorOf index))).map
        (Option.map fun values => (foldStore (siteStep masks) 273 memory values, oracle)) := by
  rw [sem_noOracle _ preimages_noOracle, memSem_preimages memory masks cells, PMF.map_comp]
  congr 1
  funext drawn
  cases drawn <;> rfl

/-! ### The abstract simulator's draws -/

/-- The exact fourth block is the 128-coin word. -/
theorem fourth_eq : (PMF.uniformOfFintype Block).map some =
    (wordLaw 128).map fun coin => some (BitVec.ofNat 128 coin) := by
  haveI : Nonempty (Fin (2 ^ 128)) := uniform_nonempty_pow 128
  let equiv : Fin (2 ^ 128) ≃ Block := ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩
  rw [← uniform_equiv equiv, PMF.map_comp, wordLaw, PMF.map_comp]
  congr 1
  funext index
  simp only [Function.comp_apply, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [equiv, Nat.mod_eq_of_lt index.isLt]

/-- The abstract simulator's draw of one collector site at the machine's bounded preimage sampler and the exact
fourth block (the body of `routeMWith`'s `drawAll`). -/
def siteSample (value : BaseField) : PMF (Option ((Block × Block × Block) × Block)) :=
  (preimageLaw value).bind fun limbs => match limbs with
    | none => PMF.pure none
    | some limbs => ((PMF.uniformOfFintype Block).map some).map (Option.map fun fourth => (limbs, fourth))

/-- A site's draws decoded: the limbs of `π + p · m` and the coin word as a block. -/
def decodeSite (value : BaseField) (drawn : Nat × Nat) : (Block × Block × Block) × Block :=
  (limbs (value.val + baseFieldModulus * drawn.1), BitVec.ofNat 128 drawn.2)

theorem siteSample_eq (value : BaseField) :
    siteSample value = (siteLaw value).map (Option.map (decodeSite value)) := by
  unfold siteSample siteLaw preimageLaw multBound
  rw [PMF.bind_map, PMF.map_bind]
  congr 1
  funext drawn
  cases drawn with
  | none => simp [PMF.pure_map]
  | some mult =>
      simp only [Function.comp_apply, Option.map_some]
      rw [fourth_eq, PMF.map_comp, PMF.map_comp]
      rfl

omit [FieldCertificate] in
/-- `drawAll` over a list of functions is an `optionProduct`. -/
theorem drawAll_ofFn {α β : Type} (sample : α → PMF (Option β)) :
    ∀ (count : Nat) (f : Fin count → α), Privacy.drawAll sample (List.ofFn f) =
      (optionProduct count fun index => sample (f index)).map
        (Option.map fun values => List.ofFn fun index => (f index, values index))
  | 0, f => by simp [Privacy.drawAll, optionProduct, PMF.pure_map]
  | count + 1, f => by
      rw [List.ofFn_succ, Privacy.drawAll]
      simp only [optionProduct]
      rw [PMF.map_bind]
      congr 1
      funext drawn
      cases drawn with
      | none => simp [PMF.pure_map]
      | some head =>
          simp only
          rw [drawAll_ofFn sample count (fun index => f index.succ), PMF.map_comp, PMF.map_comp]
          congr 1
          funext values
          cases values with
          | none => rfl
          | some values => simp [List.ofFn_succ]

omit [FieldCertificate] in
theorem collectorList_ofFn : Privacy.collectorList = List.ofFn collectorOf := by
  decide +kernel

/-- **The abstract draw is the machine's product**, decoded. -/
theorem drawAll_sites (masks : Privacy.BMR.Collector → BaseField) :
    Privacy.drawAll (fun c => siteSample (masks c)) Privacy.collectorList =
      (optionProduct 273 fun index => siteLaw (masks (collectorOf index))).map
        (Option.map fun values => List.ofFn fun index =>
          (collectorOf index, decodeSite (masks (collectorOf index)) (values index))) := by
  rw [collectorList_ofFn, drawAll_ofFn]
  simp only [siteSample_eq]
  rw [optionProduct_map_idx 273 _ (fun index => decodeSite (masks (collectorOf index))), PMF.map_comp]
  congr 1
  funext drawn
  cases drawn <;> rfl

/-! ### The collectors by flat index -/

omit [FieldCertificate] in
theorem collectorIndex_lt (c : Privacy.BMR.Collector) : Privacy.collectorIndex c < 273 := by
  unfold Privacy.collectorIndex
  have := c.1.1.isLt
  split <;> omega

/-- The flat index of a collector. -/
def collectorFin (c : Privacy.BMR.Collector) : Fin 273 := ⟨Privacy.collectorIndex c, collectorIndex_lt c⟩

omit [FieldCertificate] in
theorem collectorFin_at (d : Fin 91) (c : Fin 3) :
    collectorFin (Programs.collectorAt d c) = ⟨3 * d.val + c.val, by omega⟩ :=
  Fin.ext (Programs.collectorIndex_at d c)

omit [FieldCertificate] in
theorem collectorOf_at (d : Fin 91) (c : Fin 3) :
    collectorOf ⟨3 * d.val + c.val, by omega⟩ = Programs.collectorAt d c := by
  show Programs.collectorAt ⟨(3 * d.val + c.val) / 3, _⟩ ⟨(3 * d.val + c.val) % 3, _⟩ = _
  congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

omit [FieldCertificate] in
theorem collectorFin_of (index : Fin 273) : collectorFin (collectorOf index) = index := by
  unfold collectorOf
  rw [collectorFin_at]
  apply Fin.ext
  show 3 * (index.val / 3) + index.val % 3 = index.val
  omega

/-- The decoded draw of each collector. -/
def drawsOf (masks : Privacy.BMR.Collector → BaseField) (values : Fin 273 → Nat × Nat)
    (c : Privacy.BMR.Collector) : (Block × Block × Block) × Block :=
  decodeSite (masks c) (values (collectorFin c))

/-- **The abstract list is `collectorList.map (c, draws c)`**, the program batch's shape. -/
theorem drawn_eq (masks : Privacy.BMR.Collector → BaseField) (values : Fin 273 → Nat × Nat) :
    (List.ofFn fun index => (collectorOf index, decodeSite (masks (collectorOf index)) (values index))) =
      Privacy.collectorList.map fun c => (c, drawsOf masks values c) := by
  rw [collectorList_ofFn, List.map_ofFn]
  congr 1
  funext index
  simp [drawsOf, collectorFin_of]

/-! ### The cells after the stores -/

omit [FieldCertificate] in
/-- A value of an `optionProduct` is a value of every factor. -/
theorem optionProduct_support {α : Type} :
    ∀ (count : Nat) (sample : Fin count → PMF (Option α)) (values : Fin count → α),
      some values ∈ (optionProduct count sample).support →
        ∀ index, some (values index) ∈ (sample index).support
  | 0, _, _, _, index => index.elim0
  | count + 1, sample, values, member, index => by
      simp only [optionProduct, PMF.mem_support_bind_iff] at member
      obtain ⟨head, headMember, rest⟩ := member
      cases head with
      | none => simp at rest
      | some head =>
          simp only [PMF.mem_support_map_iff] at rest
          obtain ⟨tail, tailMember, same⟩ := rest
          cases tail with
          | none => simp at same
          | some tail =>
              simp only [Option.map_some, Option.some.injEq] at same
              subst same
              refine Fin.cases ?_ (fun later => ?_) index
              · simpa using headMember
              · simpa using optionProduct_support count (fun index => sample index.succ) tail
                  tailMember later

theorem siteLaw_support (value : BaseField) (drawn : Nat × Nat) (member : some drawn ∈ (siteLaw value).support) :
    drawn.1 < multBound value ∧ drawn.2 < 2 ^ 128 := by
  unfold siteLaw at member
  rw [PMF.mem_support_bind_iff] at member
  obtain ⟨first, firstMember, rest⟩ := member
  cases first with
  | none => simp at rest
  | some mult =>
      simp only [PMF.mem_support_map_iff, Option.some.injEq] at rest
      obtain ⟨coin, coinMember, same⟩ := rest
      subst same
      have good := rejectLaw_support _ _ _ _ firstMember
      simp only [decide_eq_true_eq] at good
      refine ⟨good.1, ?_⟩
      simp only [wordLaw, PMF.mem_support_map_iff] at coinMember
      obtain ⟨index, _, same⟩ := coinMember
      subst same
      exact index.isLt

omit [FieldCertificate] in
theorem sum_lt (value : BaseField) (mult : Nat) (small : mult < multBound value) :
    value.val + baseFieldModulus * mult < 2 ^ 384 := by
  have count := preimageCount_succ value
  unfold multBound at small
  rw [← count] at small
  have le : baseFieldModulus * mult ≤ 2 ^ 384 - 1 - value.val :=
    calc baseFieldModulus * mult ≤ baseFieldModulus * preimageCount value := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 ^ 384 - 1 - value.val := by unfold preimageCount; exact Nat.mul_div_le _ _
  have below : value.val < 2 ^ 384 := by
    have := value.val_lt
    unfold baseFieldModulus at *
    omega
  omega

omit [FieldCertificate] in
theorem blockWord_limbs (n : Nat) (small : n < 2 ^ 384) :
    blockWord (limbs n).1 = (limbWords n).1 ∧ blockWord (limbs n).2.1 = (limbWords n).2.1 ∧
      blockWord (limbs n).2.2 = (limbWords n).2.2 := by
  have top : n / 2 ^ 256 < 2 ^ 128 := Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact small)
  unfold blockWord limbs limbWords
  refine ⟨?_, ?_, ?_⟩ <;> simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt top]

omit [FieldCertificate] in
theorem blockWord_coin (coin : Nat) (small : coin < 2 ^ 128) :
    blockWord (BitVec.ofNat 128 coin) = BitVec.ofNat 256 coin := by
  unfold blockWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem siteStep_limb (masks : Privacy.BMR.Collector → BaseField) (index : Nat) (memory : Memory)
    (drawn : Nat × Nat) (block : Nat) (inside : block < 3) (small : index < 273) :
    (siteStep masks index memory drawn).ram (word (Layout.limbCell index block)) =
      wordAt (limbWords ((maskAt masks index).val + pNat * drawn.1)) block := by
  unfold siteStep siteMem preMem
  rw [(clearRegs_other _ _).1, storeRam_ram, Nat.div_add_mod,
    Function.update_of_ne (by apply word_ne <;> simp only [Layout.limbCell, Layout.fourthCell, openBase] <;> omega),
    (clearRegs_other _ _).1, withRam_ram,
    show Layout.limbCell index block = openLimb (index / 3) (index % 3) 0 + block by
      unfold Layout.limbCell openLimb; omega,
    putPoint_at _ _ _ _ (by unfold openLimb openBase; omega) inside]

theorem siteStep_fourth (masks : Privacy.BMR.Collector → BaseField) (index : Nat) (memory : Memory)
    (drawn : Nat × Nat) :
    (siteStep masks index memory drawn).ram (word (Layout.fourthCell index)) = BitVec.ofNat 256 drawn.2 := by
  unfold siteStep siteMem
  rw [(clearRegs_other _ _).1, storeRam_ram, Nat.div_add_mod, Function.update_self]

/-- **After the stores, the program batch's cells hold the decoded draws.** -/
theorem allHold_after (masks : Privacy.BMR.Collector → BaseField) (memory : Memory)
    (values : Fin 273 → Nat × Nat)
    (support : some values ∈ (optionProduct 273 fun index => siteLaw (masks (collectorOf index))).support) :
    Programs.AllHold programCells (foldStore (siteStep masks) 273 memory values) (drawsOf masks values) := by
  intro d c
  let site : Fin 273 := ⟨3 * d.val + c.val, by omega⟩
  have atSite : collectorOf site = Programs.collectorAt d c := collectorOf_at d c
  have maskSite : maskAt masks site.val = masks (Programs.collectorAt d c) := by
    unfold maskAt
    rw [dif_pos site.isLt]
    exact congrArg masks atSite
  have member := optionProduct_support 273 _ values support site
  rw [atSite] at member
  obtain ⟨multSmall, coinSmall⟩ := siteLaw_support _ _ member
  have encoded := blockWord_limbs _ (sum_lt _ _ multSmall)
  have limb : ∀ block, block < 3 →
      (foldStore (siteStep masks) 273 memory values).ram (word (Layout.limbCell (3 * d.val + c.val) block)) =
        wordAt (limbWords ((masks (Programs.collectorAt d c)).val + pNat * (values site).1)) block := by
    intro block inside
    rw [← maskSite]
    exact foldStore_ram_set _ (siteStep masks) 273 memory values site _
      (fun later => siteStep_limb masks site.val later (values site) block inside site.isLt)
      (fun later after bound other drawn => siteStep_ram_off masks later other drawn _
        (by apply word_ne <;> simp only [Layout.limbCell, tmpM, tmpBase, openBase] <;> omega)
        (fun position below => by
          have after' : 3 * d.val + c.val < later := after
          apply word_ne <;> simp only [Layout.limbCell, openLimb, openBase] <;> omega)
        (by apply word_ne <;> simp only [Layout.limbCell, Layout.fourthCell, openBase] <;> omega))
  have fourth : (foldStore (siteStep masks) 273 memory values).ram
      (word (Layout.fourthCell (3 * d.val + c.val))) = BitVec.ofNat 256 (values site).2 :=
    foldStore_ram_set _ (siteStep masks) 273 memory values site _
      (fun later => siteStep_fourth masks site.val later (values site))
      (fun later after bound other drawn => siteStep_ram_off masks later other drawn _
        (by apply word_ne <;> simp only [Layout.fourthCell, tmpM, tmpBase] <;> omega)
        (fun position below => by
          apply word_ne <;> simp only [Layout.fourthCell, openLimb, openBase] <;> omega)
        (by
          have after' : 3 * d.val + c.val < later := after
          apply word_ne <;> simp only [Layout.fourthCell] <;> omega))
  unfold Programs.SiteHolds drawsOf
  rw [collectorFin_at]
  simp only [programCells, decodeSite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [if_pos (by norm_num), limb 0 (by norm_num)]
    exact encoded.1.symm
  · rw [if_pos (by norm_num), limb 1 (by norm_num)]
    exact encoded.2.1.symm
  · rw [if_pos (by norm_num), limb 2 (by norm_num)]
    exact encoded.2.2.symm
  · rw [if_neg (by norm_num), fourth, blockWord_coin _ coinSmall]

/-- The cells the preimages write: the multiplier scratch, the 819 limbs, the 273 fourth blocks. -/
def preimagesWrites : Writes := fun address => address = word tmpM ∨
  (∃ index, index < 273 ∧ ∃ block, block < 3 ∧ address = word (Layout.limbCell index block)) ∨
  (∃ index, index < 273 ∧ address = word (Layout.fourthCell index))

/-- The registers the preimages change. -/
def preimagesClobbers : Clobbers := Clobbers.ofList limbScratch

/-- **The frame of the preimages.** -/
theorem frame_after (masks : Privacy.BMR.Collector → BaseField) (memory : Memory) (values : Fin 273 → Nat × Nat) :
    Frame preimagesWrites preimagesClobbers memory (foldStore (siteStep masks) 273 memory values) where
  ram address outside := foldStore_keep (fun later => later.ram address) _ 273 memory values
    (fun index bound later drawn => siteStep_ram_off masks index later drawn address
      (fun same => outside (Or.inl same))
      (fun position inside same => outside (Or.inr (Or.inl ⟨index, bound, position, inside, by
        rw [same]
        congr 1
        unfold Layout.limbCell openLimb
        omega⟩)))
      (fun same => outside (Or.inr (Or.inr ⟨index, bound, same⟩))))
  bits := foldStore_keep (fun later => later.bits) _ 273 memory values (fun index bound later drawn => by
    unfold siteStep siteMem preMem
    rw [(clearRegs_other _ _).2, storeRam_bits, (clearRegs_other _ _).2, withRam_bits])
  registers register outside := foldStore_keep (fun later => later.registers register) _ 273 memory values
    (fun index bound later drawn => by
      have notList : register ∉ limbScratch := outside
      have notSampler : register ∉ [rAcc, rBit, rAddr] := fun mem => notList (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        simp only [limbScratch, List.mem_cons, List.not_mem_nil, or_false]
        rcases mem with same | same | same <;> simp [same])
      unfold siteStep siteMem preMem
      rw [clearRegs_registers, if_neg notSampler, storeRam_registers, clearRegs_registers, if_neg notList,
        withRam_registers])

omit [FieldCertificate] in
theorem keyCell_outside : ¬ preimagesWrites (word Layout.keyCell) := by
  rintro (same | ⟨index, bound, block, inside, same⟩ | ⟨index, bound, same⟩)
  · exact word_ne (by simp only [Layout.keyCell]; omega) (by simp only [tmpM, tmpBase]; omega)
      (by simp only [Layout.keyCell, tmpM, tmpBase]; omega) same
  · exact word_ne (by simp only [Layout.keyCell]; omega) (by simp only [Layout.limbCell, openBase]; omega)
      (by simp only [Layout.keyCell, Layout.limbCell, openBase]; omega) same
  · exact word_ne (by simp only [Layout.keyCell]; omega) (by simp only [Layout.fourthCell]; omega)
      (by simp only [Layout.keyCell, Layout.fourthCell]; omega) same

/-! ### The preimages, then the 546 programs -/

section Oracle

variable {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **Route M's collector sites on the machine**: the 273 site draws, then the 546 programs at the key `K`, with
the abstract simulator's request list `collectorList.map (c, draws c)` of the decoded draws. -/
theorem sem_preimagesPrograms (memory : Memory) (masks : Privacy.BMR.Collector → BaseField) (key : Block)
    (cells : ∀ (d : Fin 91) (c : Fin 3),
      memory.ram (word (openTarget d c)) = fieldWord (masks (Programs.collectorAt d c)))
    (keyCell : memory.ram (word Layout.keyCell) = blockWord key) :
    ∃ finalMem : (Fin 273 → Nat × Nat) → Memory,
      (∀ values, Frame (preimagesWrites.union Programs.programsWrites)
        (preimagesClobbers.union Programs.programsClobbers) memory (finalMem values)) ∧
      ∀ oracle : OState FI EI,
        (Prog.seq preimages (Programs.programs programCells)).sem memory oracle =
          (optionProduct 273 fun index => siteLaw (masks (collectorOf index))).map fun drawn =>
            drawn.bind fun values =>
              (Privacy.programHashAll (Privacy.programRequests key
                (Privacy.collectorList.map fun c => (c, drawsOf masks values c))) oracle).map
                  fun updated => (finalMem values, updated) := by
  classical
  have exists_after : ∀ values : Fin 273 → Nat × Nat, ∃ after,
      Frame (preimagesWrites.union Programs.programsWrites) (preimagesClobbers.union Programs.programsClobbers)
        memory after ∧
      (some values ∈ (optionProduct 273 fun index => siteLaw (masks (collectorOf index))).support →
        ∀ oracle : OState FI EI,
          (Programs.programs programCells).sem (foldStore (siteStep masks) 273 memory values) oracle =
            PMF.pure ((Privacy.programHashAll (Privacy.programRequests key
              (Privacy.collectorList.map fun c => (c, drawsOf masks values c))) oracle).map
                fun updated => (after, updated))) := by
    intro values
    by_cases member : some values ∈ (optionProduct 273 fun index => siteLaw (masks (collectorOf index))).support
    · obtain ⟨after, frame, run⟩ := Programs.sem_programs (FI := FI) (EI := EI) programCells
        (foldStore (siteStep masks) 273 memory values) key (drawsOf masks values)
        (by rw [show programCells.key = Layout.keyCell from rfl,
          (frame_after masks memory values).ram _ keyCell_outside, keyCell])
        (allHold_after masks memory values member)
      exact ⟨after, (frame_after masks memory values).trans frame, fun _ => run⟩
    · exact ⟨foldStore (siteStep masks) 273 memory values,
        (frame_after masks memory values).mono (fun _ inside => Or.inl inside) (fun _ inside => Or.inl inside),
        fun inside => absurd inside member⟩
  choose finalMem frames runs using exists_after
  refine ⟨finalMem, frames, fun oracle => ?_⟩
  show andThen preimages.sem (Programs.programs programCells).sem memory oracle = _
  unfold andThen
  rw [sem_preimages memory masks cells oracle, PMF.bind_map, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro drawn member
  cases drawn with
  | none => rfl
  | some values =>
      simp only [Function.comp_apply, Option.map_some]
      rw [runs values member oracle]
      rfl

end Oracle

end Preimages

end

end Kriterion.CRT.SimMachine
