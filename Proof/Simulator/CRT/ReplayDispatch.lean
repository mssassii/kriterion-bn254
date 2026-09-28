/-
**The per-modulus programs agree with `modEvalM`** in their windows: `agree_modZero` (the
modulus-256 path) and `agree_modOdd` (an odd modulus: words, `σ`, the conversion under its
contract, the body).
-/

import Proof.Simulator.CRT.ReplayMod
import Proof.Simulator.CRT.ReplayWords
import Proof.Simulator.CRT.ReplayOdd
import Proof.Simulator.CRT.ReplayCoord
import Construction.Simulator.CRT.ReplayDispatch

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-- The window of `2 ^ 20` cells from `W`. -/
def window (W : Nat) : Writes := fun address => ∃ x, W ≤ x ∧ x < W + 2 ^ 20 ∧ address = word x

/-- The body's writes lie in its window. -/
theorem bodyWrites_window (W vec hot joinBase S q : Nat) (qSmall : 2 * q ≤ 1024) (sSmall : S ≤ 512)
    (address : Word) (inside : bodyWrites (windowBody W vec hot joinBase) S q address) :
    window W address := by
  rcases inside with ((⟨k, kb, same⟩ | ⟨k, kb, same⟩) | (⟨k, kb, same⟩ | ⟨k, kb, same⟩)) | ⟨k, kb, same⟩ <;>
    dsimp only [windowBody] at kb same <;> exact ⟨_, by omega, by omega, same⟩

theorem det_truthWordBlock (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (count ell : Nat) : (truthWordBlock castBase wordBase truthOf width count ell).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨trivial, det_rep _ _ (fun _ _ => det_rep _ _ fun _ _ =>
    ⟨⟨trivial, trivial⟩, trivial, trivial, trivial⟩), trivial, trivial, ⟨trivial, trivial⟩⟩

theorem det_sigmaBlock (coordCell sigmaCell m count : Nat) (offset width : Nat → Nat) :
    (sigmaBlock coordCell sigmaCell m count offset width).OpsSatisfy Op.Det :=
  ⟨trivial, det_rep _ _ (fun _ _ =>
    ⟨⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial⟩, det_barrett _ _ _ _,
      trivial⟩), ⟨trivial, trivial⟩⟩

section Dispatch

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The modulus-256 path in its window.** -/
theorem agree_modZero (T : CrtTable) (S coord : Nat) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → Nat) (v : Nat) (vSmall : v < 2 ^ 256)
    (chunks : Nat → ChunkEval T.castWidth) (i : Fin T.count) (kind : T.kind i = .chunkZero)
    (width : Nat) (modulus : T.modulus i = 2 ^ width) (widthSmall : width < 256)
    (mSmall : T.modulus i ≤ 2 ^ 10) (qSmall : 2 * T.padAnswers S i ≤ 1024) (sSmall : S ≤ 512)
    (coordCell leafBase W joinBase : Nat) (joinBelow : joinBase + S ≤ leafBase)
    (leafBelow : leafBase + T.modulus i ≤ W) (windowFits : W + 2 ^ 20 < 2 ^ 256)
    (memory : Memory) (coordVal : memory.ram (word coordCell) = word v)
    (leafCells : ∀ ρ, ρ < T.modulus i →
      memory.ram (word (leafBase + ρ)) = labelWord ((chunks 0).leaves ρ))
    (joinCells : ∀ e : Fin S, memory.ram (word (joinBase + e.val)) = word (joins i e))
    (joinsLt : ∀ e, joins i e < T.modulus i)
    (tagSmall : ∀ ρ j, ρ < T.modulus i → j < T.padAnswers S i → bodyTag coord i.val ρ j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (res : Fin S → Nat) after =>
        (∀ e : Fin S, after.ram (word (windowOut W + e.val)) = word (res e)) ∧
          (∀ e, res e < T.modulus i) ∧ Frame (window W) bodyClobbers memory after)
      ((modZeroProg coordCell leafBase W joinBase (T.modulus i) width S (T.padAnswers S i)
        (bodyTag coord i.val)).tree memory)
      (liftHash (modEvalM T S coord pub joins v chunks i)) := by
  have mPos : 0 < T.modulus i := by rw [modulus]; exact Nat.two_pow_pos _
  have chain : BodyChain (windowBody W leafBase W joinBase) (T.modulus i) S (T.padAnswers S i) :=
    ⟨mPos, mSmall, joinBelow, leafBelow, by show W < W + 2 ^ 18; omega,
      by show W + 2 ^ 18 + 2 * _ ≤ W + 2 ^ 18 + 1024; omega,
      by show W + 2 ^ 18 + 1024 + S ≤ W + 2 ^ 18 + 2048; omega,
      by show W + 2 ^ 18 + 2048 + S ≤ W + 2 ^ 18 + 2560; omega,
      by show W + 2 ^ 18 + 2560 + S ≤ W + 2 ^ 18 + 3072; omega,
      by show W + 2 ^ 18 + 3072 + S < 2 ^ 256; omega⟩
  refine (agree_mod256Block T S coord pub joins v vSmall chunks i kind width modulus widthSmall coordCell
    (windowBody W leafBase W joinBase) chain memory coordVal leafCells joinCells joinsLt tagSmall).mono
    fun res after post => ⟨post.1, post.2.1, post.2.2.mono (fun address inside => ?_) fun _ h => h⟩
  rcases inside with inside | same
  · exact bodyWrites_window W leafBase W joinBase S _ qSmall sSmall address inside
  · exact ⟨W, le_rfl, by omega, same⟩

/-- The conversion's region inside the window. -/
def convRegion (W : Nat) : Writes :=
  fun address => ∃ x, W + 256 ≤ x ∧ x < W + 2 ^ 18 ∧ address = word x

/-- **An odd modulus in its window**, given its conversion block's agreement (`convOK`): the truth-word lanes, the word value, the
conversion, the body. -/
theorem agree_modOdd (T : CrtTable) (S coord : Nat) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → Nat) (v : Nat) (vSmall : v < 2 ^ 256)
    (chunks : Nat → ChunkEval T.castWidth) (i : Fin T.count) (row : OddRow)
    (kind : T.kind i = .odd row) (ellLe : row.ell ≤ T.castWidth) (ellSmall : row.ell ≤ 256)
    (mPos : 0 < T.modulus i) (mSmall : T.modulus i ≤ 2 ^ 10) (qSmall : 2 * T.padAnswers S i ≤ 1024)
    (sSmall : S ≤ 512) (countSmall : T.chunkCount ≤ 2 ^ 10)
    (offsetSmall : ∀ c, c < T.chunkCount → T.chunkOffset c < 2 ^ 256)
    (widthSmall : ∀ c, c < T.chunkCount → T.chunkWidth c ≤ 8)
    (coordCell castBase W joinBase : Nat) (convProg : Prog) (vec hot : Nat) (convClobbers : Clobbers)
    (coordBelow : coordCell < W) (castsBelow : castBase + 32768 * T.chunkCount ≤ W)
    (joinBelow : joinBase + S ≤ W) (vecIn : W + 256 ≤ vec) (vecBelow : vec + T.modulus i ≤ hot)
    (hotBelow : hot < W + 2 ^ 18) (windowFits : W + 2 ^ 20 < 2 ^ 256)
    (memory : Memory) (coordVal : memory.ram (word coordCell) = word v)
    (castCells : ∀ c, c < T.chunkCount → ∀ leaf, leaf < 2 ^ T.chunkWidth c → ∀ j (jb : j < laneCount),
      memory.ram (word (castBase + 32768 * c + 128 * leaf + j)) = word (((chunks c).casts leaf) ⟨j, jb⟩).val)
    (joinCells : ∀ e : Fin S, memory.ram (word (joinBase + e.val)) = word (joins i e))
    (joinsLt : ∀ e, joins i e < T.modulus i)
    (tagSmall : ∀ ρ j, ρ < T.modulus i → j < T.padAnswers S i → bodyTag coord i.val ρ j < 2 ^ 127)
    (convOK : ∀ m0 : Memory,
      (∀ j (jb : j < laneCount), m0.ram (word (W + j)) =
        word ((truthWord T (T.modulus i) row.ell fun c leaf => (chunks c).casts leaf) ⟨j, jb⟩).val) →
      m0.ram (word (W + 128)) = word (T.wordValue (T.modulus i) v) →
      (∀ x, x < W → m0.ram (word x) = memory.ram (word x)) →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
        (fun (conv : (Fin (T.modulus i) → Label) × Nat) after =>
          (∀ ρ : Fin (T.modulus i), after.ram (word (vec + ρ.val)) = labelWord (conv.1 ρ)) ∧
            after.ram (word hot) = word conv.2 ∧ conv.2 < T.modulus i ∧
            Frame (convRegion W) convClobbers m0 after)
        (convProg.tree m0)
        (liftHash (conversionEvalM coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v)
          (truthWord T (T.modulus i) row.ell fun c leaf => (chunks c).casts leaf) pub))) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (res : Fin S → Nat) after =>
        (∀ e : Fin S, after.ram (word (windowOut W + e.val)) = word (res e)) ∧
          (∀ e, res e < T.modulus i) ∧ Frame (window W) (bodyClobbers.union convClobbers) memory after)
      ((modOddProg coordCell castBase W joinBase (T.modulus i) row.ell S (T.padAnswers S i) T.chunkCount
        (T.truth (T.modulus i)) T.chunkOffset T.chunkWidth convProg vec hot (bodyTag coord i.val)).tree
        memory)
      (liftHash (modEvalM T S coord pub joins v chunks i)) := by
  have lc : laneCount = 104 := rfl
  -- the truth-word lanes
  let X : Nat → Nat → Nat → Nat := fun j c leaf =>
    if jb : j < laneCount then (((chunks c).casts leaf) ⟨j, jb⟩).val else 0
  have castIn : ∀ c, c < T.chunkCount → ∀ leaf, leaf < 2 ^ T.chunkWidth c → ∀ j, j < 128 →
      castBase + 32768 * c + 128 * leaf + j < castBase + 32768 * T.chunkCount := fun c cb leaf lb j jb => by
    have := widthSmall c cb
    have : 2 ^ T.chunkWidth c ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) this
    have : 32768 * c + 32768 ≤ 32768 * T.chunkCount := by omega
    omega
  obtain ⟨m1, run1, lanes1, frame1, bits1, regs1⟩ := exec_truthWordBlock castBase W
    (T.truth (T.modulus i)) T.chunkWidth T.chunkCount row.ell memory X ellSmall (by omega)
    (fun c cb leaf lb j jb j' jb' => by have := castIn c cb leaf lb j (by omega); omega)
    (fun c cb leaf lb j jb => by have := castIn c cb leaf lb j (by omega); omega)
    (fun c cb leaf lb j jb => by
      simp only [X, dif_pos (show j < laneCount from jb)]
      exact castCells c cb leaf lb j jb)
  have below1 : ∀ x, x < W → m1.ram (word x) = memory.ram (word x) := fun x xb =>
    frame1 _ fun j jb same => by
      have := word_inj (by omega) (by omega) same
      omega
  -- the word value
  obtain ⟨m2, run2, ram2, bits2, regs2⟩ := exec_sigmaBlock coordCell (W + 128) (T.modulus i)
    T.chunkCount T.chunkOffset T.chunkWidth m1 v (by rw [below1 _ coordBelow]; exact coordVal) vSmall
    mPos mSmall countSmall offsetSmall widthSmall (by omega)
  rw [sigmaPartial_eq] at ram2
  have below2 : ∀ x, x < W → m2.ram (word x) = memory.ram (word x) := fun x xb => by
    rw [ram2, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), below1 x xb]
  have lanes2 : ∀ j (jb : j < laneCount), m2.ram (word (W + j)) =
      word ((truthWord T (T.modulus i) row.ell fun c leaf => (chunks c).casts leaf) ⟨j, jb⟩).val :=
    fun j jb => by
      rw [ram2, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), lanes1 j jb,
        truthWord_val T (T.modulus i) row.ell ellLe _ ⟨j, jb⟩]
      congr 3
      funext c leaf
      simp only [X, dif_pos jb]
  have sigma2 : m2.ram (word (W + 128)) = word (T.wordValue (T.modulus i) v) := by
    rw [ram2, Function.update_self]
  -- the tree
  unfold modOddProg
  rw [tree_seq_exec _ _ (det_truthWordBlock _ _ _ _ _ _) memory m1 run1,
    tree_seq_exec _ _ (det_sigmaBlock _ _ _ _ _ _) m1 m2 run2, tree_seq]
  simp only [modEvalM, kind]
  rw [TreeLaws.monad_bind, liftHash_bind, liftHash_materializeM]
  show Agree _ _ (liftHash (conversionEvalM coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v)
      (truthWord T (T.modulus i) row.ell fun c leaf => (chunks c).casts leaf) pub >>= fun conversion =>
    bodyEvalM (T.modulus i) S (T.padAnswers S i) coord i.val conversion.1 conversion.2 (joins i)))
  rw [TreeLaws.monad_bind, liftHash_bind]
  refine Agree.bindOpt (fun conv m3 cpost => ?_) (convOK m2 lanes2 sigma2 below2)
  obtain ⟨vecCells, hotCell, hotLt, frameC⟩ := cpost
  have below3 : ∀ x, x < W → m3.ram (word x) = memory.ram (word x) := fun x xb => by
    rw [frameC.ram _ fun ⟨y, yLow, yHigh, same⟩ => by
      have := word_inj (by omega) (by omega) same
      omega]
    exact below2 x xb
  have chain : BodyChain (windowBody W vec hot joinBase) (T.modulus i) S (T.padAnswers S i) :=
    ⟨mPos, mSmall, by show joinBase + S ≤ vec; omega, vecBelow, by show hot < W + 2 ^ 18; omega,
      by show W + 2 ^ 18 + 2 * _ ≤ W + 2 ^ 18 + 1024; omega,
      by show W + 2 ^ 18 + 1024 + S ≤ W + 2 ^ 18 + 2048; omega,
      by show W + 2 ^ 18 + 2048 + S ≤ W + 2 ^ 18 + 2560; omega,
      by show W + 2 ^ 18 + 2560 + S ≤ W + 2 ^ 18 + 3072; omega,
      by show W + 2 ^ 18 + 3072 + S < 2 ^ 256; omega⟩
  refine (agree_bodyBlock (windowBody W vec hot joinBase) (T.modulus i) S (T.padAnswers S i) coord i.val
    chain conv.1 conv.2 hotLt (joins i) joinsLt m3 hotCell vecCells
    (fun e => by
      rw [show (windowBody W vec hot joinBase).joinBase = joinBase from rfl,
        below3 _ (by have := e.isLt; omega)]
      exact joinCells e)
    tagSmall).mono fun res after post => ⟨post.1, post.2.1, ?_⟩
  -- the frame: words, word value, conversion, body
  have frameW : Frame (window W) (bodyClobbers.union convClobbers) memory m2 :=
    ⟨fun address outside => by
        rw [ram2, Function.update_of_ne (fun same => outside ⟨W + 128, by omega, by omega, same⟩)]
        exact frame1 address fun j jb same => outside ⟨W + j, by omega, by omega, same⟩,
      by rw [bits2, bits1],
      fun register outside => by
        have ne : ∀ r, r ∈ [rAcc, rOut, rA, rB, rC, rD, rE, rF, rAddr, rM, rMask, rK128, rInput, rFirst,
            rSecond] → register ≠ r := fun r mem h => outside (Or.inl (h ▸ mem))
        rw [regs2 register fun inside => by
            simp only [sigmaClobbers, Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with h | h | h | h | h | h | h | h <;> exact ne _ (by simp) h,
          regs1 register (ne rA (by simp)) (ne rB (by simp)) (ne rC (by simp)) (ne rAddr (by simp))]⟩
  refine ((frameW.trans frameC).trans post.2.2).mono ?_ ?_
  · rintro address ((inside | ⟨y, yLow, yHigh, same⟩) | inside)
    · exact inside
    · exact ⟨y, by omega, by omega, same⟩
    · exact bodyWrites_window W vec hot joinBase S _ qSmall sSmall address inside
  · rintro register ((inside | inside) | inside)
    · exact inside
    · exact Or.inr inside
    · exact Or.inl inside

theorem window_modWindow (modBase i : Nat) (address : Word) (inside : window (modBase + 2 ^ 20 * i) address) :
    modWindow modBase i address := by
  obtain ⟨x, low, high, same⟩ := inside
  refine ⟨x, low, ?_, same⟩
  calc x < modBase + 2 ^ 20 * i + 2 ^ 20 := high
    _ = modBase + 2 ^ 20 * (i + 1) := by ring

/-- **The per-modulus contract of the dispatch**, from the chunk loop's outputs, the initial
memory's inputs and the conversions' agreements (`convAll`). -/
theorem modContract_of (T : CrtTable) (S coord : Nat) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → Nat) (v : Nat) (vSmall : v < 2 ^ 256) (cc : CoordCells)
    (chain : CoordChain cc T.chunkCount T.castWidth) (modBase : Nat) (joinBaseOf : Nat → Nat)
    (convProgOf : Nat → Prog) (vecOf hotOf : Nat → Nat) (convClobbers : Clobbers)
    (chunkZeroFacts : ∀ i, T.kind i = .chunkZero → T.modulus i = 2 ^ T.chunkWidth 0 ∧ 0 < T.chunkCount)
    (oddFacts : ∀ i row, T.kind i = .odd row → row.ell ≤ T.castWidth ∧ row.ell ≤ 256)
    (mPos : ∀ i, 0 < T.modulus i) (mSmall : ∀ i, T.modulus i ≤ 2 ^ 10)
    (qSmall : ∀ i, 2 * T.padAnswers S i ≤ 1024) (sSmall : S ≤ 512) (countSmall : T.chunkCount ≤ 2 ^ 10)
    (offsetSmall : ∀ c, c < T.chunkCount → T.chunkOffset c < 2 ^ 256)
    (widthSmall : ∀ c, c < T.chunkCount → T.chunkWidth c ≤ 8)
    (tagSmall : ∀ (i : Fin T.count) ρ j, ρ < T.modulus i → j < T.padAnswers S i →
      bodyTag coord i.val ρ j < 2 ^ 127)
    (leavesBelow : cc.leafBase + 256 * T.chunkCount ≤ modBase)
    (modsFit : modBase + 2 ^ 20 * T.count < 2 ^ 256)
    (joinsBelow : ∀ i, i < T.count → joinBaseOf i + S ≤ cc.alpha)
    (convIn : ∀ i, i < T.count → modBase + 2 ^ 20 * i + 256 ≤ vecOf i ∧ vecOf i + modNat T i ≤ hotOf i ∧
      hotOf i < modBase + 2 ^ 20 * i + 2 ^ 18)
    (memory0 : Memory) (coordVal : memory0.ram (word cc.coordCell) = word v)
    (joinCells : ∀ (i : Fin T.count) (e : Fin S),
      memory0.ram (word (joinBaseOf i.val + e.val)) = word (joins i e))
    (joinsLt : ∀ i e, joins i e < T.modulus i)
    (chunkTable : Fin T.chunkCount → ChunkEval T.castWidth) (base : Memory)
    (out : ChunkOut cc T chunkTable memory0 base)
    (convAll : ∀ (i : Fin T.count) (row : OddRow), T.kind i = .odd row → ∀ m0 : Memory,
      (∀ j (jb : j < laneCount), m0.ram (word (modBase + 2 ^ 20 * i.val + j)) =
        word ((truthWord T (T.modulus i) row.ell fun c leaf =>
          (atNat chunkTable (ChunkEval.empty _) c).casts leaf) ⟨j, jb⟩).val) →
      m0.ram (word (modBase + 2 ^ 20 * i.val + 128)) = word (T.wordValue (T.modulus i) v) →
      (∀ x, x < cc.alpha → m0.ram (word x) = memory0.ram (word x)) →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
        (fun (conv : (Fin (T.modulus i) → Label) × Nat) after =>
          (∀ ρ : Fin (T.modulus i), after.ram (word (vecOf i.val + ρ.val)) = labelWord (conv.1 ρ)) ∧
            after.ram (word (hotOf i.val)) = word conv.2 ∧ conv.2 < T.modulus i ∧
            Frame (convRegion (modBase + 2 ^ 20 * i.val)) convClobbers m0 after)
        ((convProgOf i.val).tree m0)
        (liftHash (conversionEvalM coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v)
          (truthWord T (T.modulus i) row.ell fun c leaf =>
            (atNat chunkTable (ChunkEval.empty _) c).casts leaf) pub))) :
    ModContract (FixedIndex := FixedIndex) (EncIndex := EncIndex) T S coord pub joins v
      (atNat chunkTable (ChunkEval.empty _)) (modProg T S coord cc modBase joinBaseOf convProgOf vecOf hotOf)
      modBase (fun i => windowOut (modBase + 2 ^ 20 * i)) (bodyClobbers.union convClobbers) base := by
  have := chain.coordBelow; have := chain.alphaBelow; have := chain.levelsBelow
  have := chain.matsBelow; have := chain.ansBelow; have := chain.castBelow; have := chain.leafFits
  obtain ⟨casts, leaves, frameC⟩ := out
  intro ⟨i, ib⟩ memory agrees
  have wStep : 2 ^ 20 * i + 2 ^ 20 ≤ 2 ^ 20 * T.count := by
    have : 2 ^ 20 * (i + 1) = 2 ^ 20 * i + 2 ^ 20 := by ring
    rw [← this]; exact Nat.mul_le_mul_left _ ib
  have wLow : modBase ≤ modBase + 2 ^ 20 * i := Nat.le_add_right _ _
  -- the memory agrees with the initial one below `alpha`
  have low : ∀ x, x < cc.alpha → memory.ram (word x) = memory0.ram (word x) := fun x xb => by
    rw [agrees x (by omega) (Or.inl (by omega)), frameC.ram _ fun ⟨y, yLow, yHigh, same⟩ => by
      have := word_inj (by omega) (by omega) same
      omega]
  have chunkAt : ∀ c (cb : c < T.chunkCount), atNat chunkTable (ChunkEval.empty _) c = chunkTable ⟨c, cb⟩ :=
    fun c cb => by simp [atNat, cb]
  have joinsNow : ∀ e : Fin S, memory.ram (word (joinBaseOf i + e.val)) = word (joins ⟨i, ib⟩ e) :=
    fun e => by
      have := joinsBelow i ib
      rw [low _ (by have := e.isLt; omega)]
      exact joinCells ⟨i, ib⟩ e
  unfold modProg
  rw [dif_pos ib]
  split
  · next heq =>
      obtain ⟨zeroMod, countPos⟩ := chunkZeroFacts ⟨i, ib⟩ heq
      have w0 := widthSmall 0 countPos
      have mLe : T.modulus ⟨i, ib⟩ ≤ 256 := by
        rw [zeroMod]; exact (Nat.pow_le_pow_right (by norm_num) w0).trans (by norm_num)
      have := joinsBelow i ib
      refine (agree_modZero T S coord pub joins v vSmall _ ⟨i, ib⟩ heq (T.chunkWidth 0) zeroMod (by omega)
        (mSmall _) (qSmall _) sSmall cc.coordCell cc.leafBase (modBase + 2 ^ 20 * i) (joinBaseOf i)
        (by omega) (by omega) (by omega) memory (by rw [low _ (by omega)]; exact coordVal)
        (fun ρ ρb => by
          rw [agrees _ (by omega) (Or.inl (by omega)), chunkAt 0 countPos]
          have := leaves 0 countPos ρ (by rw [← zeroMod]; exact ρb)
          rw [Nat.mul_zero, Nat.add_zero] at this
          exact this)
        joinsNow (joinsLt _) (tagSmall _)).mono fun res after post =>
          ⟨post.1, post.2.1, post.2.2.mono (window_modWindow modBase i) fun _ h => Or.inl h⟩
  · next row heq =>
      obtain ⟨ellLe, ellSmall⟩ := oddFacts ⟨i, ib⟩ row heq
      obtain ⟨vecIn, vecBelow, hotBelow⟩ := convIn i ib
      have modEq : modNat T i = T.modulus ⟨i, ib⟩ := by simp [modNat, ib]
      have := joinsBelow i ib
      refine (agree_modOdd T S coord pub joins v vSmall _ ⟨i, ib⟩ row heq ellLe ellSmall (mPos _)
        (mSmall _) (qSmall _) sSmall countSmall offsetSmall widthSmall cc.coordCell cc.castBase
        (modBase + 2 ^ 20 * i) (joinBaseOf i) (convProgOf i) (vecOf i) (hotOf i) convClobbers
        (by omega) (by omega) (by omega) vecIn (by rw [← modEq]; exact vecBelow) hotBelow (by omega)
        memory (by rw [low _ (by omega)]; exact coordVal)
        (fun c cb leaf lb j jb => by
          have w8 := widthSmall c cb
          have : 2 ^ T.chunkWidth c ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) w8
          have : 32768 * c + 32768 ≤ 32768 * T.chunkCount := by omega
          have jb' : j < 128 := lt_of_lt_of_le jb (by decide : laneCount ≤ 128)
          rw [agrees _ (by omega) (Or.inl (by omega)), chunkAt c cb]
          exact casts c cb leaf lb j jb)
        joinsNow (joinsLt _) (tagSmall _)
        (fun m0 lanes sigma below => convAll ⟨i, ib⟩ row heq m0 lanes sigma fun x xb => by
          rw [below x (by omega), low x xb])).mono fun res after post =>
          ⟨post.1, post.2.1, post.2.2.mono (window_modWindow modBase i) fun _ h => h⟩

end Dispatch

end Kriterion.CRT.SimMachine
