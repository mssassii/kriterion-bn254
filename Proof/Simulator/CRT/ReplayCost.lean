/-
**The size and cost of route M's replay on the machine** (for `Design.totalCost_le`): `cost ≤ size` for every program (the padded `ite`), and upper bounds on the
size of every block of `Machine.replay`, composed to one bound.
-/

import Proof.Simulator.CRT.ReplayIndexFacts
import Construction.Simulator.CRT.ReplayMachine
import Construction.Simulator.CRT.ReplayConversionSize

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT Finset

namespace CostFacts

/-- **A program's cost is at most its size** (the `ite` pads its shorter arm). -/
theorem cost_le_size : ∀ program : Prog, program.cost ≤ program.size
  | .op _ => le_rfl
  | .popBit _ _ => by show 2 ≤ 4; norm_num
  | .skip _ => le_rfl
  | .abort _ => le_rfl
  | .seq first second => by
      rw [Prog.cost_seq, Prog.size_seq]
      exact Nat.add_le_add (cost_le_size first) (cost_le_size second)
  | .ite source whenSet whenClear => by
      have := cost_le_size whenSet
      have := cost_le_size whenClear
      rw [Prog.cost_ite, Prog.size_ite]
      omega

theorem size_rep_le (count : Nat) (body : Nat → Prog) (bound : Nat)
    (each : ∀ index, index < count → (body index).size ≤ bound) :
    (Prog.rep count body).size ≤ count * bound := by
  rw [size_rep_sum]
  calc ∑ index ∈ range count, (body index).size ≤ ∑ _index ∈ range count, bound :=
        sum_le_sum fun index mem => each index (mem_range.mp mem)
    _ = count * bound := by rw [sum_const, card_range, smul_eq_mul]

theorem size_ite_le (source : Register) (whenSet whenClear : Prog) :
    (Prog.ite source whenSet whenClear).size ≤ 3 + 2 * (whenSet.size + whenClear.size) := by
  have := cost_le_size whenSet
  have := cost_le_size whenClear
  rw [Prog.size_ite]
  omega

/-! ### The chunk loop -/

theorem size_treeStep (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) :
    (treeStep cells tagOf n).size = 16 + 38 * 2 ^ n := by
  simp only [treeStep, treeLevel, Prog.size_seq]
  rw [Prog.size_rep _ _ 29 (fun s _ => size_treeEntry cells tagOf n s),
    Prog.size_rep _ _ 9 (fun s _ => rfl), show (treeRecover cells n).size = 15 from rfl,
    show (cst rD 0).size = 1 from rfl]
  ring

theorem size_treeEval_le (cells : TreeCells) (tagOf : Nat → Nat → Nat) (levels : Nat) (small : levels ≤ 8) :
    (treeEval cells tagOf levels).size ≤ 2 ^ 17 := by
  simp only [treeEval, Prog.size_seq]
  have steps := size_rep_le (levels - 1) (fun k => treeStep cells (tagOf (k + 1)) (k + 1))
    (16 + 38 * 2 ^ 8) fun k kb => by
      rw [size_treeStep]
      have : 2 ^ (k + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have : (levels - 1) * (16 + 38 * 2 ^ 8) ≤ 8 * (16 + 38 * 2 ^ 8) := Nat.mul_le_mul_right _ (by omega)
  rw [show (treePrefix cells).size = 8 from rfl]
  omega

theorem size_castBlock (cells : CastCells) (l : Nat) (tagOf : Nat → Nat) :
    (castBlock cells l tagOf).size = 9 * castAnswers l + 8 * laneCount := by
  simp only [castBlock, castQueries, castLanesProg, Prog.size_seq]
  rw [Prog.size_rep _ _ 9 (fun j _ => rfl), Prog.size_rep _ _ 8 (fun i _ => rfl)]
  rw [show laneCount = 104 from rfl]
  ring

theorem size_chunkCastPhase_le (cc : ChunkCastCells) (width l : Nat) (tagOf : Nat → Nat → Nat)
    (widthLe : width ≤ 8) (answersLe : castAnswers l ≤ 64) :
    (chunkCastPhase cc width l tagOf).size ≤ 2 ^ 21 := by
  have lc : laneCount = 104 := rfl
  have pw : 2 ^ width ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) widthLe
  simp only [chunkCastPhase, castLoop, pinSolve, Prog.size_seq]
  have casts := size_rep_le (2 ^ width) (castEntry cc width l tagOf) (9 + 2 * (9 * 64 + 1024))
    fun leaf _ => by
      simp only [castEntry, Prog.size_seq]
      have := size_ite_le rA (castBlock (leafCells cc leaf) l (tagOf leaf)) (.skip 0)
      rw [size_castBlock, show (Prog.skip 0).size = 0 from rfl] at this
      rw [show (entryTest (alphaCells cc) width leaf).size = 6 from rfl]
      omega
  have lanes := size_rep_le laneCount (solveLane cc width l) (9 + 23 * 2 ^ 8) fun i _ => by
    simp only [solveLane, Prog.size_seq]
    have terms := size_rep_le (2 ^ width) (solveTerm cc width l i) 23 fun leaf _ => by
      simp only [solveTerm, Prog.size_seq]
      have := size_ite_le rA
        (.seq (loadAt rB (cc.castBase + 128 * leaf + i)) (.seq (cst rC (2 ^ l)) (.seq (ar .add rD rD rC)
          (.seq (ar .sub rD rD rB) (.seq (cst rC (2 ^ l - 1)) (ar .and rD rD rC)))))) (.skip 0)
      rw [show (entryTest (alphaCells cc) width leaf).size = 6 from rfl]
      rw [show (Prog.seq (loadAt rB (cc.castBase + 128 * leaf + i)) (.seq (cst rC (2 ^ l))
          (.seq (ar .add rD rD rC) (.seq (ar .sub rD rD rB) (.seq (cst rC (2 ^ l - 1))
          (ar .and rD rD rC)))))).size = 7 from rfl, show (Prog.skip 0).size = 0 from rfl] at this
      omega
    have : 2 ^ width * 23 ≤ 2 ^ 8 * 23 := Nat.mul_le_mul_right _ pw
    simp only [Prog.size, size_loadAt, cst, ar]
    omega
  have : 2 ^ width * (9 + 2 * (9 * 64 + 1024)) ≤ 2 ^ 8 * (9 + 2 * (9 * 64 + 1024)) :=
    Nat.mul_le_mul_right _ pw
  rw [lc] at lanes ⊢
  omega

theorem size_chunkLoop_le (cc : CoordCells) (offset width : Nat → Nat)
    (tagTree tagCast : Nat → Nat → Nat → Nat) (l count : Nat) (countLe : count ≤ 32)
    (widthLe : ∀ c, c < count → width c ≤ 8) (answersLe : castAnswers l ≤ 64) :
    (chunkLoop cc offset width tagTree tagCast l count).size ≤ 2 ^ 27 := by
  have each := size_rep_le count (chunkStep cc offset width tagTree tagCast l) (2 ^ 22) fun c cb => by
    simp only [chunkStep, chunkReplay, Prog.size_seq]
    have tree := size_treeEval_le (cc.tree (offset c) c) (tagTree c) (width c) (widthLe c cb)
    have phase := size_chunkCastPhase_le (cc.cast c) (width c) l (tagCast c) (widthLe c cb) answersLe
    have save : (saveLeaves cc.levelBase cc.leafBase (width c) c).size ≤ 4 * 2 ^ 8 := by
      unfold saveLeaves
      rw [Prog.size_rep _ _ 4 (fun _ _ => rfl)]
      have : 2 ^ width c ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (widthLe c cb)
      omega
    rw [show (chunkPrefix cc.coordCell cc.alpha (offset c) (width c)).size = 8 from rfl]
    omega
  unfold chunkLoop
  have : count * 2 ^ 22 ≤ 32 * 2 ^ 22 := Nat.mul_le_mul_right _ countLe
  omega

/-! ### The body, the words, the word value -/

theorem size_bodyBlock_le (bc : BodyCells) (m S q : Nat) (tagOf : Nat → Nat → Nat) (mLe : m ≤ 2 ^ 10)
    (sLe : S ≤ 512) (qLt : q < 64) : (bodyBlock bc m S q tagOf).size ≤ 2 ^ 32 := by
  simp only [bodyBlock, bodyZero, Prog.size_seq]
  have zero : (Prog.rep S fun e => Prog.seq (storeAt (bc.accA + e) rA) (storeAt (bc.accB + e) rA)).size =
      S * 4 := Prog.size_rep _ _ 4 fun _ _ => rfl
  have finals : (Prog.rep S (bodyFinal bc m)).size = S * 27 := Prog.size_rep _ _ 27 fun _ _ => rfl
  have entries := size_rep_le m (bodyEntry bc m S q tagOf) (2 ^ 21) fun ρ _ => by
    simp only [bodyEntry, Prog.size_seq]
    have ite := size_ite_le rA (bodyPad bc m S q (tagOf ρ) ρ) (.skip 0)
    rw [show (Prog.skip 0).size = 0 from rfl] at ite
    have pad : (bodyPad bc m S q (tagOf ρ) ρ).size ≤ 2 ^ 19 := by
      simp only [bodyPad, castQueries, Prog.size_seq]
      rw [Prog.size_rep _ _ 9 (fun _ _ => rfl), size_setupConsts, size_fracDigits,
        Prog.size_rep _ _ 14 (fun _ _ => rfl)]
      have : S * (3 + 7 * (2 * q)) ≤ 512 * (3 + 7 * (2 * 63)) :=
        Nat.mul_le_mul sLe (by omega)
      omega
    rw [show (bodyTest bc ρ).size = 4 from rfl]
    omega
  have : m * 2 ^ 21 ≤ 2 ^ 10 * 2 ^ 21 := Nat.mul_le_mul_right _ mLe
  rw [show (cst rA 0).size = 1 from rfl]
  omega

theorem size_truthWordBlock_le (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (count ell : Nat) (countLe : count ≤ 32) (widthLe : ∀ c, c < count → width c ≤ 8) :
    (truthWordBlock castBase wordBase truthOf width count ell).size ≤ 2 ^ 23 := by
  have lc : laneCount = 104 := rfl
  unfold truthWordBlock
  have each := size_rep_le laneCount (wordLane castBase wordBase truthOf width count ell) (5 + 32 * (5 * 2 ^ 8))
    fun i _ => by
      simp only [wordLane, Prog.size_seq]
      have chunks := size_rep_le count (wordChunk castBase truthOf width i) (5 * 2 ^ 8) fun c cb => by
        unfold wordChunk
        rw [Prog.size_rep _ _ 5 (fun _ _ => rfl)]
        have : 2 ^ width c ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (widthLe c cb)
        omega
      have : count * (5 * 2 ^ 8) ≤ 32 * (5 * 2 ^ 8) := Nat.mul_le_mul_right _ countLe
      rw [show (cst rA 0).size = 1 from rfl, show (cst rB (2 ^ ell - 1)).size = 1 from rfl,
        show (ar .and rA rA rB).size = 1 from rfl, size_storeAt]
      omega
  omega

theorem size_sigmaBlock (coordCell sigmaCell m count : Nat) (offset width : Nat → Nat) :
    (sigmaBlock coordCell sigmaCell m count offset width).size = 3 + count * 21 := by
  simp only [sigmaBlock, Prog.size_seq]
  rw [Prog.size_rep _ _ 21 (fun _ _ => rfl), show (cst rAcc 0).size = 1 from rfl, size_storeAt]
  omega

/-! ### The decoding, the key, the masks -/

theorem size_decodeAll_le (dc : DecodeCells) (mods : Nat → Nat) (count wrapB nz S : Nat)
    (countLe : count ≤ 128) (nzLe : nz ≤ 8) (sLe : S ≤ 512) :
    (decodeAll dc mods count wrapB nz S).size ≤ 2 ^ 27 := by
  unfold decodeAll
  have each := size_rep_le S (decodeOne dc mods count wrapB nz) (2 ^ 17) fun e _ => by
    simp only [decodeOne, gatherResidues, reconstruct, garnerDigits, garnerHorner, zeroLimbs, limbLess,
      limbModP, Prog.size_seq]
    rw [Prog.size_rep _ _ 4 (fun _ _ => rfl)]
    have digits := size_rep_le count (garnerDigitProg mods dc.gbase dc.vaddr) (32 + 5 * 128) fun i ib => by
      simp only [garnerDigitProg, Prog.size_seq]
      rw [Prog.size_rep _ _ 5 (fun _ _ => rfl), size_barrett, size_barrett, size_loadAt, size_storeAt]
      simp only [cst, ar, Prog.size]
      omega
    have horner := size_rep_le count (fun t => hornerStep mods dc.vaddr dc.zbase nz (count - 1 - t))
      (3 + 7 * 8) fun t _ => by
        simp only [hornerStep, Prog.size_seq]
        rw [size_mulSmallAdd, size_loadAt]
        simp only [cst, Prog.size]
        omega
    have zl : (Prog.rep nz fun k => storeAt (dc.zbase + k) rA).size = nz * 2 :=
      Prog.size_rep _ _ 2 (fun _ _ => rfl)
    have ll : (Prog.rep nz fun t => lessStep wrapB dc.zbase (nz - 1 - t)).size = nz * 10 :=
      Prog.size_rep _ _ 10 (fun _ _ => rfl)
    have ml : (Prog.rep nz (modPStep dc.zbase)).size = nz * 5 := Prog.size_rep _ _ 5 (fun _ _ => rfl)
    rw [show (wrapCombine (prefixProd mods count % BN254.baseFieldModulus)
        (dc.hintBase + e) (dc.decodedBase + e)).size = 8 from rfl]
    simp only [cst, Prog.size]
    have : count * (32 + 5 * 128) ≤ 128 * (32 + 5 * 128) := Nat.mul_le_mul_right _ countLe
    have : count * (3 + 7 * 8) ≤ 128 * (3 + 7 * 8) := Nat.mul_le_mul_right _ countLe
    omega
  have : S * 2 ^ 17 ≤ 512 * 2 ^ 17 := Nat.mul_le_mul_right _ sLe
  omega

theorem size_keyBlock (kc : KeyCells) : (keyBlock kc).size = 42 := rfl

theorem size_maskStage (mc : MaskCells) : (maskStage mc Kriterion.ArgoMAC.PlanB.digitCount).size = 182 * 55 := by
  simp only [maskStage, Prog.size_seq]
  rw [Prog.size_rep _ _ 55 (fun k _ => by
    simp only [maskPairSite, Prog.size_seq, castQueries]
    rw [Prog.size_rep _ _ 9 (fun _ _ => rfl)]
    rfl)]
  rw [if_neg (by decide)]
  rfl

/-! ### The whole replay -/

open Machine in
theorem size_modProg_le (κ S : Nat) (sLe : S ≤ 512)
    (convLe : ∀ i, (convProg κ i).size ≤ 2 ^ 36) (i : Nat) :
    (modProg Entry.table S κ (coordCells κ) (modBase κ) (joinBaseOf κ) (convProg κ)
      (fun i => windowAt κ i + 2 ^ 12) (fun i => windowAt κ i + 2 ^ 12 + 2 ^ 11) i).size ≤ 2 ^ 37 := by
  unfold modProg
  split
  · next h =>
      have mLe : Entry.table.modulus ⟨i, h⟩ ≤ 2 ^ 10 := (TableFacts.modulus_le _).trans (by norm_num)
      have qLt := TableFacts.padAnswers_lt S sLe ⟨i, h⟩
      split
      · have body := size_bodyBlock_le (windowBody (modBase κ + 2 ^ 20 * i) (coordCells κ).leafBase
          (modBase κ + 2 ^ 20 * i) (joinBaseOf κ i)) _ S _ (bodyTag κ i) mLe sLe qLt
        simp only [modZeroProg, mod256Block, Prog.size_seq]
        rw [show (chunkPrefix (coordCells κ).coordCell _ 0 _).size = 8 from rfl]
        omega
      · next row _ =>
          have body := size_bodyBlock_le (windowBody (modBase κ + 2 ^ 20 * i) (windowAt κ i + 2 ^ 12)
            (windowAt κ i + 2 ^ 12 + 2 ^ 11) (joinBaseOf κ i)) _ S _ (bodyTag κ i) mLe sLe qLt
          have words := size_truthWordBlock_le (coordCells κ).castBase (modBase κ + 2 ^ 20 * i)
            (Entry.table.truth (Entry.table.modulus ⟨i, h⟩)) Entry.table.chunkWidth Entry.table.chunkCount
            row.ell (by rw [TableFacts.chunkCount]) (fun c cb => TableFacts.shape.widthSmall c cb)
          have conv := convLe i
          simp only [modOddProg, Prog.size_seq]
          rw [size_sigmaBlock]
          have := TableFacts.chunkCount
          omega
  · exact Nat.zero_le _

open Machine in
theorem size_coordProg_le (κ S : Nat) (sLe : S ≤ 512) (convLe : ∀ i, (convProg κ i).size ≤ 2 ^ 36) :
    (coordProg κ S).size ≤ 2 ^ 45 := by
  simp only [coordProg, coordReplay, Prog.size_seq]
  have chunks := size_chunkLoop_le (coordCells κ) Entry.table.chunkOffset Entry.table.chunkWidth
    (chunkTreeTag κ) (chunkCastTag κ) Entry.table.castWidth Entry.table.chunkCount
    (by rw [TableFacts.chunkCount]) (fun c cb => TableFacts.shape.widthSmall c cb) TableFacts.castAnswers_le
  have mods := size_rep_le Entry.table.count _ (2 ^ 37) fun i _ => size_modProg_le κ S sLe convLe i
  have decode := size_decodeAll_le (decodeCells κ) (modNat Entry.table) Entry.table.count
    Entry.table.wrapBound 6 S (by rw [TableFacts.count]; norm_num) (by norm_num) sLe
  have cnt : Entry.table.count = 85 := TableFacts.count
  omega

/-- Every conversion of the real table is below `2 ^ 36` (`size_conversionReplay_le`). -/
theorem size_convProg_le (κ i : Nat) : (Machine.convProg κ i).size ≤ 2 ^ 36 := by
  unfold Machine.convProg
  split
  · next h =>
      split
      · next row kind =>
          obtain ⟨w0Pos, w1Pos, ellEq, keepGe, keepLe, ellLe, _⟩ := TableFacts.odd_facts ⟨i, h⟩ row kind
          exact size_conversionReplay_le κ i row _ _ _ _ _ _ w0Pos (by omega) (by omega) keepGe (by omega)
            (by omega) (by omega) ((TableFacts.modulus_le _).trans (by norm_num))
      · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- **The replay's size and cost** are below `2 ^ 47`, far below `Design.totalCost_le`'s `2 ^ 55`. -/
theorem replay_size_cost_le : Machine.replay.size ≤ 2 ^ 47 ∧ Machine.replay.cost ≤ 2 ^ 47 := by
  have x := size_coordProg_le 0 Entry.xCount (by norm_num [Entry.xCount]) (size_convProg_le 0)
  have y := size_coordProg_le 1 Entry.yCount (by norm_num [Entry.yCount]) (size_convProg_le 1)
  have split : Machine.replay.size = (Machine.coordProg 0 Entry.xCount).size +
      ((Machine.coordProg 1 Entry.yCount).size + ((keyBlock entryKeyCells).size +
        (maskStage (entryMaskCells Machine.maskScratch) Kriterion.ArgoMAC.PlanB.digitCount).size)) := by
    unfold Machine.replay entryReplay
    rw [Prog.size_seq, Prog.size_seq, Prog.size_seq]
  have size : Machine.replay.size ≤ 2 ^ 47 := by
    rw [split, size_keyBlock, size_maskStage]
    have bound : (2 : Nat) ^ 45 + (2 ^ 45 + (42 + 182 * 55)) ≤ 2 ^ 47 := by norm_num
    exact le_trans (Nat.add_le_add x (Nat.add_le_add y le_rfl)) bound
  exact ⟨size, (cost_le_size _).trans size⟩

/-- The form `Design.Blocks.Within (2 ^ 55)` needs. -/
theorem replay_within : Machine.replay.size ≤ 2 ^ 55 ∧ Machine.replay.cost ≤ 2 ^ 55 :=
  ⟨replay_size_cost_le.1.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)),
    replay_size_cost_le.2.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))⟩

end CostFacts

end Kriterion.CRT.SimMachine
