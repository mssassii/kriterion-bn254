import Encoding
-- Opus probe: can the interpreter run a 36,424-byte `Encoding.natural` round trip?
def probeValue : Fin (256 ^ 36424) :=
  ⟨(2 ^ 291384 + 12345) % 256 ^ 36424, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

#eval ((Kriterion.Encoding.natural 36424).encode probeValue).length
#eval (((Kriterion.Encoding.natural 36424).decode
  ((Kriterion.Encoding.natural 36424).encode probeValue)).map (fun r => (r.1.val % 2 ^ 20, r.1.val / 2 ^ 291384)))
