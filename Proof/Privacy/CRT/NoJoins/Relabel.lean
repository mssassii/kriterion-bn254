/-
**No chunk joins, the garbler relabelling**: the coordinate garbler reads its zero labels only at each chunk's first
bit (to start the chunk tree); the zero labels of the other bits enter only the chunk joins, as `J = levelSum ⊕ Z`.

So two runs of `coordGarbleM` on the same hash with zero labels `Z`, `Z'` that agree at every chunk's first bit
(`FirstAgree`) ask the same inputs (`asked_coordGarbleM_zero`), and give the same residues, pad sums, offsets and
hints, the same published material off the chunk joins, and chunk joins differing by `Z ⊕ Z'`
(`coordGarbleM_zero`). With `Z' = Z ⊕ chunkShift J` (the actual zero labels, low parts) the relabelled run has zero
chunk joins: this reduces the no-joins relational argument to the one with joins (`Core/CoordRelational.lean`).
-/

import Proof.Privacy.CRT.Hidden.Align
import Proof.Correctness.CRT.Delivery
import Proof.Correctness.CRT.FlatLayout

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.NoJoins

open Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_tableM asked_chunkGarbleM)

/-- Zero labels that agree at every chunk's first bit. -/
def FirstAgree (T : CrtTable) (Z Z' : ℕ → Label) : Prop := ∀ c, Z' (T.chunkOffset c + 0) = Z (T.chunkOffset c + 0)

theorem xor_resplit {w : ℕ} (t z z' : BitVec w) : t ^^^ z' = t ^^^ z ^^^ z ^^^ z' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases t.getLsbD i <;> cases z.getLsbD i <;> cases z'.getLsbD i <;> rfl

section Zero

variable (H : HashN) (T : CrtTable) (S coord : ℕ) (Δ : Label)

/-- One chunk: the same leaves, casts and pin; joins shifted by `Z ⊕ Z'`. -/
theorem chunkGarbleM_zero (Z Z' : ℕ → Label) (first : FirstAgree T Z Z') (c : ℕ) :
    ((chunkGarbleM T coord Δ Z' c).eval H).leaves = ((chunkGarbleM T coord Δ Z c).eval H).leaves ∧
      ((chunkGarbleM T coord Δ Z' c).eval H).casts = ((chunkGarbleM T coord Δ Z c).eval H).casts ∧
      ((chunkGarbleM T coord Δ Z' c).eval H).pin = ((chunkGarbleM T coord Δ Z c).eval H).pin ∧
      ∀ n, ((chunkGarbleM T coord Δ Z' c).eval H).joins n =
        ((chunkGarbleM T coord Δ Z c).eval H).joins n ^^^ Z (T.chunkOffset c + n) ^^^ Z' (T.chunkOffset c + n) := by
  simp only [chunkGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]
  rw [first c]
  exact ⟨rfl, rfl, rfl, fun n => xor_resplit _ _ _⟩

theorem asked_chunkGarbleM_zero (Z Z' : ℕ → Label) (first : FirstAgree T Z Z') (c : ℕ) :
    asked H (chunkGarbleM T coord Δ Z' c) = asked H (chunkGarbleM T coord Δ Z c) := by
  rw [asked_chunkGarbleM, asked_chunkGarbleM, first c]

/-- A modulus reads its chunks' casts and leaves only. -/
theorem modGarbleM_congr (chunks chunks' : ℕ → ChunkGarbled T.castWidth)
    (casts : ∀ c, (chunks' c).casts = (chunks c).casts) (leaves : ∀ c, (chunks' c).leaves = (chunks c).leaves)
    (i : Fin T.count) : modGarbleM T S coord Δ chunks' i = modGarbleM T S coord Δ chunks i := by
  unfold modGarbleM
  simp only [casts, leaves]

/-- The chunk table read by natural index, for two first-agreeing zero labels: same casts and leaves. -/
theorem chunks_zero (Z Z' : ℕ → Label) (first : FirstAgree T Z Z') :
    (∀ c, (atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z' c.val).eval H) (ChunkGarbled.empty _) c).casts =
      (atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z c.val).eval H) (ChunkGarbled.empty _) c).casts) ∧
    (∀ c, (atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z' c.val).eval H) (ChunkGarbled.empty _) c).leaves =
      (atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z c.val).eval H) (ChunkGarbled.empty _) c).leaves) := by
  refine ⟨fun c => ?_, fun c => ?_⟩ <;> unfold atNat <;> split
  · exact (chunkGarbleM_zero H T coord Δ Z Z' first c).2.1
  · rfl
  · exact (chunkGarbleM_zero H T coord Δ Z Z' first c).1
  · rfl

/-- **The garbler asks the same inputs** on first-agreeing zero labels. -/
theorem asked_coordGarbleM_zero (Z Z' : ℕ → Label) (first : FirstAgree T Z Z') :
    asked H (coordGarbleM T S coord Δ Z') = asked H (coordGarbleM T S coord Δ Z) := by
  obtain ⟨casts, leaves⟩ := chunks_zero H T coord Δ Z Z' first
  unfold coordGarbleM
  rw [asked_bind, asked_bind, asked_tableM, asked_tableM]
  have hc : ((List.finRange T.chunkCount).flatMap fun i => asked H (chunkGarbleM T coord Δ Z' i.val)) =
      (List.finRange T.chunkCount).flatMap fun i => asked H (chunkGarbleM T coord Δ Z i.val) := by
    simp only [asked_chunkGarbleM_zero H T coord Δ Z Z' first]
  rw [hc, asked_bind, asked_bind, asked_tableM, asked_tableM]
  simp only [eval_tableM]
  simp only [modGarbleM_congr T S coord Δ _ _ casts leaves, Align.asked_pure]

/-- **The garbler's outputs on first-agreeing zero labels**: the same residues, pad sums, offsets and hints, the
same published material off the chunk joins, and chunk joins shifted by `Z ⊕ Z'`. -/
theorem coordGarbleM_zero (Z Z' : ℕ → Label) (first : FirstAgree T Z Z') :
    ((coordGarbleM T S coord Δ Z').eval H).residue = ((coordGarbleM T S coord Δ Z).eval H).residue ∧
      ((coordGarbleM T S coord Δ Z').eval H).padSum = ((coordGarbleM T S coord Δ Z).eval H).padSum ∧
      ((coordGarbleM T S coord Δ Z').eval H).offset = ((coordGarbleM T S coord Δ Z).eval H).offset ∧
      ((coordGarbleM T S coord Δ Z').eval H).hint = ((coordGarbleM T S coord Δ Z).eval H).hint ∧
      FlatLayout.ConvAgree T ((coordGarbleM T S coord Δ Z').eval H).pub.dropChunkJoins
        ((coordGarbleM T S coord Δ Z).eval H).pub.dropChunkJoins ∧
      ∀ c < T.chunkCount, ∀ n, ((coordGarbleM T S coord Δ Z').eval H).pub.chunkJoin c n =
        ((coordGarbleM T S coord Δ Z).eval H).pub.chunkJoin c n ^^^ Z (T.chunkOffset c + n) ^^^
          Z' (T.chunkOffset c + n) := by
  obtain ⟨casts, leaves⟩ := chunks_zero H T coord Δ Z Z' first
  have mods : ∀ i : Fin T.count, (modGarbleM T S coord Δ
      (atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z' c.val).eval H) (ChunkGarbled.empty _)) i).eval H =
      (modGarbleM T S coord Δ
        (atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z c.val).eval H) (ChunkGarbled.empty _)) i).eval H :=
    fun i => by rw [modGarbleM_congr T S coord Δ _ _ casts leaves i]
  obtain ⟨fJ, fP, fM, fS, fO, fH⟩ := SliceC.coordGarbleM_fields H T S coord Δ Z
  obtain ⟨fJ', fP', fM', fS', fO', fH'⟩ := SliceC.coordGarbleM_fields H T S coord Δ Z'
  dsimp only at fJ fP fM fS fO fH fJ' fP' fM' fS' fO' fH'
  have padSum : ((coordGarbleM T S coord Δ Z').eval H).padSum = ((coordGarbleM T S coord Δ Z).eval H).padSum :=
    funext fun i => funext fun e => by rw [fS' i e, fS i e, mods i]
  have residue : ((coordGarbleM T S coord Δ Z').eval H).residue =
      ((coordGarbleM T S coord Δ Z).eval H).residue := by
    simp only [coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]
    funext i
    rw [mods i]
  have offset : ((coordGarbleM T S coord Δ Z').eval H).offset = ((coordGarbleM T S coord Δ Z).eval H).offset :=
    funext fun e => by
      rw [fO' e, fO e]
      exact congrArg _ (funext fun i => by rw [mods i])
  refine ⟨residue, padSum, offset, funext fun e => by rw [fH' e, fH e, offset], ⟨fun _ _ _ _ _ => rfl,
    fun c hc k hk => ?_, fun i row _ => ?_⟩, fun c hc n => ?_⟩
  · show ((coordGarbleM T S coord Δ Z').eval H).pub.chunkPin c k = ((coordGarbleM T S coord Δ Z).eval H).pub.chunkPin c k
    have e := congrFun (fP' c hc) ⟨k, hk⟩
    have e' := congrFun (fP c hc) ⟨k, hk⟩
    simp only at e e'
    rw [e, e', (chunkGarbleM_zero H T coord Δ Z Z' first c).2.2.1]
  · obtain ⟨j', p', g', f'⟩ := fM' i
    obtain ⟨j, p, g, f⟩ := fM i
    refine ⟨fun n _ _ => ?_, fun n _ _ => ?_, fun k _ => ?_, fun k _ => ?_, fun n _ _ => ?_, fun n _ _ => ?_⟩
    · show ((coordGarbleM T S coord Δ Z').eval H).pub.stageJoin i.val 0 n =
        ((coordGarbleM T S coord Δ Z).eval H).pub.stageJoin i.val 0 n
      rw [j', j, mods i]
    · show ((coordGarbleM T S coord Δ Z').eval H).pub.stageJoin i.val 1 n =
        ((coordGarbleM T S coord Δ Z).eval H).pub.stageJoin i.val 1 n
      rw [j', j, mods i]
    · show ((coordGarbleM T S coord Δ Z').eval H).pub.stagePin i.val 0 k =
        ((coordGarbleM T S coord Δ Z).eval H).pub.stagePin i.val 0 k
      rw [p', p, mods i]
    · show ((coordGarbleM T S coord Δ Z').eval H).pub.stagePin i.val 1 k =
        ((coordGarbleM T S coord Δ Z).eval H).pub.stagePin i.val 1 k
      rw [p', p, mods i]
    · show ((coordGarbleM T S coord Δ Z').eval H).pub.growJoin i.val n =
        ((coordGarbleM T S coord Δ Z).eval H).pub.growJoin i.val n
      rw [g', g, mods i]
    · show ((coordGarbleM T S coord Δ Z').eval H).pub.foldJoin i.val n =
        ((coordGarbleM T S coord Δ Z).eval H).pub.foldJoin i.val n
      rw [f', f, mods i]
  · rw [fJ' c, fJ c, SliceC.atNat_of_lt _ _ hc, SliceC.atNat_of_lt _ _ hc]
    exact (chunkGarbleM_zero H T coord Δ Z Z' first c).2.2.2 n

end Zero

end Kriterion.CRT.Privacy.NoJoins
