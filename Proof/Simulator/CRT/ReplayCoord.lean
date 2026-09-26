/-
**The replay of one coordinate agrees with `coordEvalM`** (`agree_coordReplay`): the chunk loop,
the moduli (each under a per-modulus contract, `ModContract`, discharged by the modulus-256 path and
the odd path), and the decoding, whose Garner value is the table's idempotent combination
(`crtWith_eq_garnerValue`).
-/

import Proof.Simulator.CRT.ReplayChunks
import Proof.Simulator.CRT.ReplayDecode
import Proof.Correctness.CRT.BodyStep
import Construction.Simulator.CRT.ReplayCoord

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset
open scoped Function

/-! ### Garner is the table's CRT -/

/-- A family on `Fin count` by natural index (`0` off range). -/
def natOf {count : Nat} (r : Fin count → Nat) (i : Nat) : Nat := if h : i < count then r ⟨i, h⟩ else 0

theorem prefixProd_modNat (T : CrtTable) : prefixProd (modNat T) T.count = T.product := by
  unfold prefixProd CrtTable.product
  rw [← Fin.prod_univ_eq_prod_range (modNat T) T.count]
  refine prod_congr rfl fun i _ => ?_
  simp [modNat, i.isLt]

/-- The side conditions of Garner's blocks from the table's facts. -/
theorem garnerTable_of (T : CrtTable) (hpos : ∀ i, 0 < T.modulus i)
    (hco : Pairwise (Nat.Coprime on T.modulus)) (small : ∀ i, T.modulus i < 2 ^ 11)
    (sum : ∑ i : Fin T.count, T.modulus i ≤ garnerLift) : GarnerTable (modNat T) T.count where
  pos i hi := by simp [modNat, hi, hpos]
  small i hi := by
    simp only [modNat, dif_pos hi]
    exact small _
  sum := by
    rw [← Fin.sum_univ_eq_sum_range (modNat T) T.count]
    refine le_trans (le_of_eq (sum_congr rfl fun i _ => ?_)) sum
    simp [modNat, i.isLt]
  coprime i hi := by
    unfold prefixProd
    apply Nat.Coprime.prod_left
    intro k hk
    have kLt : k < i := mem_range.mp hk
    simp only [modNat, dif_pos hi, dif_pos (show k < T.count by omega)]
    exact hco (show (⟨k, by omega⟩ : Fin T.count) ≠ ⟨i, hi⟩ from fun h => by
      simp only [Fin.mk.injEq] at h
      omega)

/-- **The table's idempotent combination is Garner's value.** -/
theorem crtWith_eq_garnerValue (T : CrtTable) (hpos : ∀ i, 0 < T.modulus i)
    (hco : Pairwise (Nat.Coprime on T.modulus)) (table : GarnerTable (modNat T) T.count)
    (r : Fin T.count → Nat) :
    crtWith T.product (stored T.idempotent) r = garnerValue (modNat T) (natOf r) T.count := by
  apply garnerValue_unique (modNat T) (natOf r) T.count table
  · rw [prefixProd_modNat]
    exact SliceC.table_crt_lt T hpos r
  · intro i hi
    have := SliceC.table_crt_mod T hpos hco r ⟨i, hi⟩
    simp only [modNat, natOf, dif_pos hi]
    exact this

/-! ### The moduli -/

section Mods

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The per-modulus contract**: modulus `i`'s program, run on any memory that agrees with `base`
outside the moduli's windows, asks what `modEvalM` asks, leaves the residues at `outOf i + e`, and
writes only inside its own window. -/
def ModContract (T : CrtTable) (S coord : Nat) (pub : ConvPublic) (joins : Fin T.count → Fin S → Nat)
    (v : Nat) (chunks : Nat → ChunkEval T.castWidth) (modProg : Nat → Prog) (modBase : Nat)
    (outOf : Nat → Nat) (modClobbers : Clobbers) (base : Memory) : Prop :=
  ∀ (i : Fin T.count) (memory : Memory),
    (∀ x, x < 2 ^ 256 → (x < modBase ∨ modBase + 2 ^ 20 * T.count ≤ x) →
      memory.ram (word x) = base.ram (word x)) →
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (res : Fin S → Nat) after =>
        (∀ e : Fin S, after.ram (word (outOf i.val + e.val)) = word (res e)) ∧
          (∀ e, res e < T.modulus i) ∧ Frame (modWindow modBase i.val) modClobbers memory after)
      ((modProg i.val).tree memory) (liftHash (modEvalM T S coord pub joins v chunks i))

/-- The invariant of the moduli loop after `k` moduli. -/
def ModsInv (T : CrtTable) (S modBase : Nat) (outOf : Nat → Nat) (modClobbers : Clobbers)
    (base : Memory) (k : Nat) (values : Vector (Fin S → Nat) k) (memory : Memory) : Prop :=
  (∀ i (bound : i < k), ∀ e : Fin S,
      memory.ram (word (outOf i + e.val)) = word ((values[i]'bound) e) ∧ (values[i]'bound) e < modNat T i) ∧
    Frame (modsRegion modBase k) modClobbers base memory

/-- **The moduli loop.** -/
theorem agree_modsLoop (T : CrtTable) (S coord : Nat) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → Nat) (v : Nat) (chunks : Nat → ChunkEval T.castWidth)
    (modProg : Nat → Prog) (modBase : Nat) (outOf : Nat → Nat) (modClobbers : Clobbers)
    (base : Memory) (modsFit : modBase + 2 ^ 20 * T.count < 2 ^ 256)
    (outIn : ∀ i, i < T.count → modBase + 2 ^ 20 * i ≤ outOf i ∧ outOf i + S ≤ modBase + 2 ^ 20 * (i + 1))
    (contract : ModContract (FixedIndex := FixedIndex) (EncIndex := EncIndex) T S coord pub joins v
      chunks modProg modBase outOf modClobbers base) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (residue : Fin T.count → Fin S → Nat) after =>
        (∀ i (ib : i < T.count) (e : Fin S),
          after.ram (word (outOf i + e.val)) = word (residue ⟨i, ib⟩ e) ∧ residue ⟨i, ib⟩ e < modNat T i) ∧
          Frame (modsRegion modBase T.count) modClobbers base after)
      ((Prog.rep T.count modProg).tree base)
      (liftHash (tableM T.count (modEvalM T S coord pub joins v chunks))) := by
  have loop := agree_rep_vector_plain (FixedIndex := FixedIndex) (EncIndex := EncIndex) modProg
    (ModsInv T S modBase outOf modClobbers base) T.count
    (fun i => liftHash (modEvalM T S coord pub joins v chunks i))
    (fun index values memory holds => by
      obtain ⟨k, kb⟩ := index
      simp only at values holds ⊢
      obtain ⟨done, frame⟩ := holds
      refine (contract ⟨k, kb⟩ memory fun x xSmall side => frame.ram _ fun ⟨y, yLow, yHigh, same⟩ => by
          have := word_inj xSmall (by omega) same
          have : 2 ^ 20 * k ≤ 2 ^ 20 * T.count := Nat.mul_le_mul_left _ kb.le
          omega).mono fun res after post => ?_
      obtain ⟨outs, bounds, frameK⟩ := post
      refine ⟨fun i bound e => ?_, ?_⟩
      · by_cases last : i = k
        · subst last
          simp only [Vector.getElem_push_eq]
          refine ⟨outs e, ?_⟩
          simp only [modNat, dif_pos kb]
          exact bounds e
        · have lt : i < k := by omega
          simp only [Vector.getElem_push_lt lt]
          have ⟨low, high⟩ := outIn i (by omega)
          have ⟨lowK, _⟩ := outIn k kb
          have eb := e.isLt
          have step : 2 ^ 20 * (i + 1) ≤ 2 ^ 20 * k := Nat.mul_le_mul_left _ (by omega)
          have stepK : 2 ^ 20 * (k + 1) ≤ 2 ^ 20 * T.count := Nat.mul_le_mul_left _ (by omega)
          rw [frameK.ram _ fun ⟨y, yLow, yHigh, same⟩ => by
            dsimp only at yLow yHigh
            have ySmall : y < 2 ^ 256 :=
              lt_of_lt_of_le yHigh (le_of_lt (lt_of_le_of_lt (Nat.add_le_add_left stepK _) modsFit))
            have xSmall : outOf i + e.val < 2 ^ 256 :=
              lt_of_le_of_lt (le_trans (by omega) (Nat.add_le_add_left (le_trans step
                (Nat.mul_le_mul_left _ kb.le)) _)) modsFit
            have := word_inj xSmall ySmall same
            omega]
          exact done i lt e
      · refine (frame.trans frameK).mono ?_ (fun register inside => by
          rcases inside with inside | inside <;> exact inside)
        rintro address (⟨y, yLow, yHigh, same⟩ | ⟨y, yLow, yHigh, same⟩)
        · exact ⟨y, yLow, by
            have : 2 ^ 20 * k ≤ 2 ^ 20 * (k + 1) := Nat.mul_le_mul_left _ (by omega)
            omega, same⟩
        · exact ⟨y, by omega, yHigh, same⟩)
    base ⟨fun i bound => absurd bound (Nat.not_lt_zero _), ⟨fun address outside => rfl, rfl,
      fun register outside => rfl⟩⟩
  unfold tableM
  rw [TreeLaws.monad_bind, liftHash_bind, liftHash_vector,
    ← bindOpt_pure_right ((Prog.rep T.count modProg).tree base)]
  refine Agree.bindOpt (fun values after inv => ?_) loop
  obtain ⟨done, frame⟩ := inv
  refine .leaf ⟨fun i ib e => ?_, frame⟩
  rw [Vector.get_eq_getElem]
  exact done i ib e

/-! ### The coordinate -/

/-- The facts the chunk loop leaves: every chunk's casts and leaves, and its frame. -/
def ChunkOut (cc : CoordCells) (T : CrtTable) (chunkTable : Fin T.chunkCount → ChunkEval T.castWidth)
    (start after : Memory) : Prop :=
  (∀ c (cb : c < T.chunkCount), ∀ leaf, leaf < 2 ^ T.chunkWidth c → ∀ i (ib : i < laneCount),
      after.ram (word (cc.castBase + 32768 * c + 128 * leaf + i)) =
        word (((chunkTable ⟨c, cb⟩).casts leaf) ⟨i, ib⟩).val) ∧
    (∀ c (cb : c < T.chunkCount), ∀ leaf, leaf < 2 ^ T.chunkWidth c →
      after.ram (word (cc.leafBase + 256 * c + leaf)) = blockWord ((chunkTable ⟨c, cb⟩).leaves leaf)) ∧
    Frame (chunkLoopWrites cc T.chunkCount) chunkLoopClobbers start after

/-- The residue joins as `coordEvalM` reads them from the records. -/
def recordJoins (T : CrtTable) {S : Nat} (records : Fin S → Nat) : Fin T.count → Fin S → Nat :=
  stored fun i => stored fun e => recordJoin T T.product (stored T.radix) (records e) i

/-- **One coordinate**: the replay asks what `coordEvalM` asks and leaves every decoded value
`toField (decoded e)` at `decodedBase + e`, with the frame of its three phases. -/
theorem agree_coordReplay (T : CrtTable) (S coord : Nat) (coordLt : coord < 2) (cc : CoordCells)
    (countLe : T.chunkCount ≤ 128) (chain : CoordChain cc T.chunkCount T.castWidth)
    (shape : ChunkShape T.chunkOffset T.chunkWidth T.chunkCount T.inputBits)
    (lPos : 0 < T.castWidth) (lSmall : T.castWidth ≤ 128) (answersLe : castAnswers T.castWidth ≤ 64)
    (hpos : ∀ i, 0 < T.modulus i) (hco : Pairwise (Nat.Coprime on T.modulus))
    (table : GarnerTable (modNat T) T.count)
    (pub : ConvPublic) (records : Fin S → Nat) (v : Nat) (vSmall : v < 2 ^ 256) (labels : Nat → Block)
    (modProg : Nat → Prog) (modBase : Nat) (modClobbers : Clobbers)
    (dc : DecodeCells) (nz : Nat) (dchain : DecodeChain dc T.count nz S)
    (valueFits : T.product ≤ 2 ^ (128 * nz)) (boundFits : T.wrapBound < 2 ^ (128 * nz))
    (decodedBelow : dc.decodedBase + S ≤ cc.alpha)
    (leavesBelow : cc.leafBase + 256 * T.chunkCount ≤ modBase)
    (modsBelow : modBase + 2 ^ 20 * T.count ≤ dc.gbase)
    (outIn : ∀ i, i < T.count →
      modBase + 2 ^ 20 * i ≤ dc.outOf i ∧ dc.outOf i + S ≤ modBase + 2 ^ 20 * (i + 1))
    (memory : Memory)
    (coordVal : memory.ram (word cc.coordCell) = word v)
    (labelCells : ∀ j, j < T.inputBits → memory.ram (word (cc.labelBase + j)) = blockWord (labels j))
    (joinCells : ∀ c, c < T.chunkCount → ∀ n, 1 ≤ n → n < T.chunkWidth c →
      memory.ram (word (cc.chunkJoin c n)) = blockWord (pub.chunkJoin c n))
    (pinCells : ∀ c, c < T.chunkCount → ∀ i (ib : i < laneCount),
      memory.ram (word (cc.pinBase + 128 * c + i)) =
        word ((pinOfBlocks T.castWidth fun k => pub.chunkPin c k.val) ⟨i, ib⟩).val)
    (hints : ∀ e : Fin S, memory.ram (word (dc.hintBase + e.val)) =
      word (if decide (T.product ≤ records e) then 1 else 0))
    (contract : ∀ (chunkTable : Fin T.chunkCount → ChunkEval T.castWidth) (base : Memory),
      ChunkOut cc T chunkTable memory base →
      ModContract (FixedIndex := FixedIndex) (EncIndex := EncIndex) T S coord pub (recordJoins T records)
        v (atNat chunkTable (ChunkEval.empty _)) modProg modBase dc.outOf modClobbers base) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (ce : CoordEval T S) after =>
        (∀ e : Fin S, after.ram (word (dc.decodedBase + e.val)) =
          fieldWord ((ce.decoded e : Nat) : BN254.BaseField)) ∧
          Frame (((chunkLoopWrites cc T.chunkCount).union (modsRegion modBase T.count)).union
              (decodeWrites dc nz S))
            ((chunkLoopClobbers.union modClobbers).union reconstructClobbers) memory after)
      ((coordReplay cc T coord modProg dc nz S).tree memory)
      (liftHash (coordEvalM T S coord pub records v labels)) := by
  have := chain.alphaBelow; have := chain.levelsBelow; have := chain.matsBelow
  have := chain.ansBelow; have := chain.castBelow; have := chain.leafFits
  have := dchain.hintBelow; have := dchain.gatherBelow; have := dchain.digitsBelow
  have := dchain.limbsFit
  unfold coordReplay coordEvalM
  dsimp only
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun chunkTable base post => ?_)
    (agree_chunkLoop_tags T coord coordLt cc T.chunkCount countLe chain T.inputBits shape lPos lSmall answersLe
      labels v vSmall pub.chunkJoin (fun c => pinOfBlocks T.castWidth fun k => pub.chunkPin c k.val)
      memory coordVal labelCells joinCells pinCells)
  have frameC := post.2.2
  rw [tree_seq, TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun residue after inv => ?_)
    (agree_modsLoop T S coord pub (recordJoins T records) v _ modProg modBase dc.outOf modClobbers base
      (by omega) outIn (contract chunkTable base post))
  obtain ⟨outs, frameM⟩ := inv
  -- the hints are intact
  have hintNow : ∀ e : Fin S, after.ram (word (dc.hintBase + e.val)) =
      word (if decide (T.product ≤ records e) then 1 else 0) := fun e => by
    have eb := e.isLt
    rw [frameM.ram _ fun ⟨y, yLow, yHigh, same⟩ => by
        have := word_inj (by omega) (by omega) same
        omega,
      frameC.ram _ fun ⟨y, yLow, yHigh, same⟩ => by
        have := word_inj (by omega) (by omega) same
        omega]
    exact hints e
  let L : Nat → Nat → Nat := fun i e =>
    if h : i < T.count then (if he : e < S then residue ⟨i, h⟩ ⟨e, he⟩ else 0) else 0
  let hint : Nat → Bool := fun e => if he : e < S then decide (T.product ≤ records ⟨e, he⟩) else false
  obtain ⟨final, run, dec, frameD⟩ := exec_decodeAll dc (modNat T) T.count T.wrapBound nz S dchain table
    (by rw [prefixProd_modNat]; exact valueFits) boundFits L hint after
    (fun i ib e eb => by
      simp only [L, dif_pos ib, dif_pos eb]
      exact (outs i ib ⟨e, eb⟩).1)
    (fun i ib e eb => by
      simp only [L, dif_pos ib, dif_pos eb]
      exact (outs i ib ⟨e, eb⟩).2)
    (fun e eb => by
      simp only [hint, dif_pos eb]
      exact hintNow ⟨e, eb⟩)
  rw [tree_eq_exec _ (det_decodeAll _ _ _ _ _ _), run]
  refine .leaf ⟨fun e => ?_, (frameC.trans frameM).trans frameD⟩
  rw [dec e.val e.isLt]
  congr 1
  unfold decodedValue
  simp only [stored_eq]
  have garner : garnerValue (modNat T) (fun i => L i e.val) T.count =
      crtWith T.product (stored T.idempotent) fun i => residue i e := by
    rw [crtWith_eq_garnerValue T hpos hco table]
    congr 1
    funext i
    simp only [L, natOf, dif_pos e.isLt]
  rw [prefixProd_modNat, garner]
  simp only [hint, dif_pos e.isLt, stored_eq]

end Mods

end Kriterion.CRT.SimMachine
