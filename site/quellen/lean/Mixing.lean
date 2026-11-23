import Collatz.Counterexample

/-!
# `T` ist masstreu, und die Vergangenheit ist unabhängig von der Zukunft

Auf den 2-adischen Zahlen ist `T` die Verschiebung der Paritätsfolge (Satz 30). Daraus folgt der
Satz von Lagarias (1985), dass `T` das Haar-Mass erhält und sogar ein Bernoulli-Shift ist. Hier
die endliche, für **alle** `j, k` gültige Form, direkt mit dem Satz von Terras bewiesen:

* `parVec_add`: Der Paritätsvektor der Länge `j + k` ist der der Länge `j`, gefolgt vom
  Paritätsvektor der Länge `k` von `T^j(n)`.
* **Satz** (`past_future_independent`): Zu jedem Paritätsmuster `u` der Länge `j` und jedem
  Rest `s < 2^k` gibt es **genau ein** `r < 2^(j+k)` mit Paritäten `u` und `T^j(r) ≡ s (mod 2^k)`.
* Folgerung (`T_measure`): Jeder Rest `s` modulo `2^k` hat unter `T` genau `2^j` Urbilder
  modulo `2^(j+k)` (einmal für jedes `u`). Für `j = 1`: genau zwei, `2s` und ein ungerades.

Bedeutung: Die ersten `j` Paritäten verraten **nichts** über `T^j(n)` modulo `2^k`. Jede Aussage
der Art „nach vielen ungeraden Schritten wird die Zahl gezwungen …“ ist modulo Zweierpotenzen
falsch. Ein Beweis der Vermutung muss also Information benutzen, die nicht in endlich vielen
Binärziffern steckt, etwa die Grösse von `n` (Archimedes) statt seiner 2-adischen Gestalt.
-/

namespace Collatz

/-- Paritätsvektoren lassen sich zusammensetzen. -/
theorem parVec_add : ∀ j k n, parVec (j + k) n = parVec j n ++ parVec k (Titer j n) := by
  intro j
  induction j with
  | zero => intro k n; simp [parVec, Titer]
  | succ j ih =>
    intro k n
    rw [Nat.add_right_comm]
    show (n % 2 == 1) :: parVec (j + k) (T n) = ((n % 2 == 1) :: parVec j (T n)) ++ _
    rw [ih]
    rfl

/-- **Vergangenheit und Zukunft sind unabhängig (Existenz).** -/
theorem past_future_exists (j k : Nat) (u : List Bool) (hu : u.length = j) (s : Nat)
    (hs : s < 2 ^ k) : ∃ r, r < 2 ^ (j + k) ∧ parVec j r = u ∧ Titer j r % 2 ^ k = s := by
  obtain ⟨r, hr, hv⟩ := parVec_surjective (u ++ parVec k s)
  have hlen : (u ++ parVec k s).length = j + k := by
    rw [List.length_append, hu, parVec_length]
  rw [hlen, parVec_add] at hv
  rw [hlen] at hr
  obtain ⟨h1, h2⟩ := List.append_inj hv (by rw [parVec_length, hu])
  refine ⟨r, hr, h1, ?_⟩
  rw [parVec_mod k (Titer j r)] at h2
  exact parVec_injective k _ _ (Nat.mod_lt _ (Nat.two_pow_pos k)) hs h2

/-- **Vergangenheit und Zukunft sind unabhängig (Eindeutigkeit).** -/
theorem past_future_unique (j k r r' : Nat) (hr : r < 2 ^ (j + k)) (hr' : r' < 2 ^ (j + k))
    (hp : parVec j r = parVec j r') (ht : Titer j r % 2 ^ k = Titer j r' % 2 ^ k) : r = r' := by
  apply parVec_injective (j + k) r r' hr hr'
  rw [parVec_add, parVec_add, hp, parVec_mod k (Titer j r), parVec_mod k (Titer j r'), ht]

/-- **Satz (Lagarias, endliche Form).** Für jedes Muster `u` der Länge `j` und jeden Rest
`s < 2^k` gibt es genau ein `r < 2^(j+k)` mit den Paritäten `u` und `T^j(r) ≡ s (mod 2^k)`. -/
theorem past_future_independent (j k : Nat) (u : List Bool) (hu : u.length = j) (s : Nat)
    (hs : s < 2 ^ k) :
    ∃ r, (r < 2 ^ (j + k) ∧ parVec j r = u ∧ Titer j r % 2 ^ k = s) ∧
      ∀ r', r' < 2 ^ (j + k) → parVec j r' = u → Titer j r' % 2 ^ k = s → r' = r := by
  obtain ⟨r, hr, h1, h2⟩ := past_future_exists j k u hu s hs
  exact ⟨r, ⟨hr, h1, h2⟩, fun r' hr' h1' h2' =>
    past_future_unique j k r' r hr' hr (by rw [h1, h1']) (by rw [h2, h2'])⟩

/-- **`T` ist zwei-zu-eins.** Jeder Rest `s < 2^k` hat modulo `2^(k+1)` genau zwei Urbilder
unter `T`: das gerade `2s` und genau ein ungerades. -/
theorem T_measure (k s : Nat) (hs : s < 2 ^ k) :
    T (2 * s) % 2 ^ k = s ∧
    (∃ r, r < 2 ^ (k + 1) ∧ r % 2 = 1 ∧ T r % 2 ^ k = s) ∧
    ∀ r r', r < 2 ^ (k + 1) → r' < 2 ^ (k + 1) → r % 2 = r' % 2 →
      T r % 2 ^ k = s → T r' % 2 ^ k = s → r = r' := by
  refine ⟨?_, ?_, ?_⟩
  · unfold T; rw [if_pos (by omega)]
    rw [show 2 * s / 2 = s by omega]; exact Nat.mod_eq_of_lt hs
  · obtain ⟨r, hr, h1, h2⟩ := past_future_exists 1 k [true] rfl s hs
    refine ⟨r, by rwa [Nat.add_comm] at hr, ?_, h2⟩
    simp only [parVec, List.cons.injEq, and_true] at h1
    revert h1; cases Nat.mod_two_eq_zero_or_one r <;> simp_all
  · intro r r' hr hr' hp h h'
    apply past_future_unique 1 k r r' (by rwa [Nat.add_comm]) (by rwa [Nat.add_comm])
    · simp only [parVec, hp]
    · show T r % 2 ^ k = T r' % 2 ^ k
      rw [h, h']

end Collatz
