import Collatz.AscentExact

/-!
# Satz 86: Die Aufstiegsphase ist affin in der Restklasse

Hat `m` genau `o` Aufstiegsschritte (`m + 1 = 2^o · t` mit `t` ungerade), so hat
jede Zahl `m + 2^(o+1) · k` ebenfalls genau `o` Aufstiegsschritte, und das Ende der
Aufstiegsphase verschiebt sich affin:

  `T^o(m + 2^(o+1) k) = T^o(m) + 2 · 3^o · k`.

Die Aufstiegsphase ist also auf der ganzen Restklasse `m mod 2^(o+1)` eine affine
Abbildung mit Steigung `(3/2)^o`. Das ist die exakte, allgemeine Form der
Beobachtung, dass die ersten Schritte nur von den unteren Bits abhängen.
-/

namespace Collatz

theorem ascent_affine (o m t k : Nat) (h : m + 1 = 2 ^ o * t) (ht : t % 2 = 1) :
    (∀ j, j < o → Titer j (m + 2 ^ (o + 1) * k) % 2 = 1) ∧
    Titer o (m + 2 ^ (o + 1) * k) = Titer o m + 2 * 3 ^ o * k ∧
    Titer o (m + 2 ^ (o + 1) * k) % 2 = 0 := by
  have h' : m + 2 ^ (o + 1) * k + 1 = 2 ^ o * (t + 2 * k) := by
    rw [Nat.pow_succ, Nat.mul_add]; grind
  have ht' : (t + 2 * k) % 2 = 1 := by omega
  obtain ⟨hodd, hval⟩ := ascent_exact o _ _ h'
  obtain ⟨_, hval0⟩ := ascent_exact o m t h
  obtain ⟨_, heven⟩ := ascent_stops o _ _ h' ht'
  refine ⟨hodd, ?_, heven⟩
  have e : 3 ^ o * (t + 2 * k) = 3 ^ o * t + 2 * 3 ^ o * k := by grind
  omega

end Collatz
