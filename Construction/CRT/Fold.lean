/-
The kept one-hot, its reindex modulo `m`, and the folds.

Growth of the kept one-hot is `Tree.growGarbleM` / `Tree.growEvalM` at the grow tags; the
evaluator's active slot at the level with `2 ^ n` entries is `σ_m mod 2 ^ n`.

Reindex: `h[ρ] = XOR_{α < 2 ^ keep, α ≡ ρ (mod m)} K_α`; its hot index is `(σ mod 2 ^ keep) mod m`
(L12). Fold at bit position `j` (`keep ≤ j < ell`), shift `s_j = 2 ^ j mod m`: materials
`u_ρ = h128(h[ρ], fold tag (j, ρ))`, join `(XOR_ρ u_ρ) ⊕ b_j`, new vector
`h'[ρ] = h[ρ] ⊕ u_ρ ⊕ u_{(ρ - s_j) mod m}`; the evaluator hashes the `m - 1` cold slots (ascending),
solves `u_hot = b_j^E ⊕ join ⊕ (XOR_{ρ ≠ hot} u_ρ)`, and the hot index moves by `b_j * s_j` (L13).
-/

import Construction.CRT.Extract

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC

/-- The reindex of a one-hot of `2 ^ n` labels modulo `m`. -/
def reindex (n : Nat) (labels : Fin (2 ^ n) → Block) (m : Nat) : Fin m → Block :=
  stored fun residue =>
    Fin.foldl (2 ^ n) (fun acc leaf => if leaf.val % m = residue.val then acc ^^^ labels leaf else acc) 0

/-- `(ρ - shift) mod m`. -/
def foldSource {m : Nat} (residue : Fin m) (shift : Nat) : Fin m :=
  ⟨(residue.val + m - shift % m) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) residue.isLt)⟩

/-- The fold shift of bit position `j`. -/
def foldShift (m j : Nat) : Nat := 2 ^ j % m

/-- The garbler's fold: the new vector and the published join. -/
def foldGarbleM (m : Nat) (tagOf : Nat → Nat) (shift : Nat) (bitMask : Block)
    (labels : Fin m → Block) : CM ((Fin m → Block) × Block) :=
  tableM m (fun residue => h128M (labels residue) (tagOf residue.val)) >>= fun materials =>
    pure (stored (fun residue =>
        labels residue ^^^ materials residue ^^^ materials (foldSource residue shift)),
      xorFold materials ^^^ bitMask)

/-- The evaluator's fold at hot index `hot`. -/
def foldEvalM (m : Nat) (tagOf : Nat → Nat) (shift : Nat) (hot : Nat) (bitLabel join : Block)
    (labels : Fin m → Block) : CM (Fin m → Block) :=
  tableM m (fun residue =>
    if residue.val = hot then pure 0 else h128M (labels residue) (tagOf residue.val)) >>= fun cold =>
      let materials : Fin m → Block := stored fun residue =>
        if residue.val = hot then
          bitLabel ^^^ join ^^^ Fin.foldl m (fun acc other => if other.val = hot then acc else acc ^^^ cold other) 0
        else cold residue
      pure (stored fun residue =>
        labels residue ^^^ materials residue ^^^ materials (foldSource residue shift))

/-- The garbler's folds at bit positions `start, ..., start + count - 1`: the final vector and the
join of each position. `tagOf position residue` is the fold tag. -/
def foldsGarbleM (m : Nat) (tagOf : Nat → Nat → Nat) (bitMask : Nat → Block) :
    (count start : Nat) → (Fin m → Block) → CM ((Fin m → Block) × (Nat → Block))
  | 0, _, labels => pure (labels, fun _ => 0)
  | count + 1, position, labels =>
      foldGarbleM m (tagOf position) (foldShift m position) (bitMask position) labels >>= fun step =>
        foldsGarbleM m tagOf bitMask count (position + 1) step.1 >>= fun rest =>
          pure (rest.1, fun at_ => if at_ = position then step.2 else rest.2 at_)

/-- The evaluator's folds; `value` is `σ_m` (its bit `j` moves the hot index by `s_j`). Returns the
final vector and the final hot index. -/
def foldsEvalM (m : Nat) (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel join : Nat → Block) :
    (count start hot : Nat) → (Fin m → Block) → CM ((Fin m → Block) × Nat)
  | 0, _, hot, labels => pure (labels, hot)
  | count + 1, position, hot, labels =>
      foldEvalM m (tagOf position) (foldShift m position) hot (bitLabel position) (join position)
          labels >>= fun next =>
        foldsEvalM m tagOf value bitLabel join count (position + 1)
          ((hot + (if value.testBit position then foldShift m position else 0)) % m) next

end Kriterion.CRT
