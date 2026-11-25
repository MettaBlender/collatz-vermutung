import Collatz.DoubleOddMod4

/-!
# Satz 66: Schärfere Konstante – mehr als 26 % der Schritte liegen bei Rest 3 modulo 4

Satz 64/65 nutzten die Näherung `5/8` für `log 2 / log 3 ≈ 0,6309`. Hier wird die Abschätzung
allgemein für jeden Bruch `p/q` mit `(3m+1)^p ≤ 2^q · m^p` geführt und mit `p/q = 41/65 ≈ 0,63077`
angewendet (`3^41 < 2^65`). Ergebnis: Ab dem kleinsten Glied `m ≥ 2^27` eines Gegenbeispiels gilt

  `17 · J ≤ 65 · (#{i < J : x_i ≡ 3 mod 4} + 1)`,

also ein Anteil von mindestens `17/65 ≈ 26,15 %` statt `25 %`. Die Methode (Läufe-Kombinatorik
plus Dichteschranke) kann höchstens `2·log 2/log 3 − 1 ≈ 26,19 %` liefern; viel mehr ist auf
diesem Weg also nicht zu holen.
-/

namespace Collatz

/-- Aus `2^j · b^o ≤ a^o` mit `a^p ≤ 2^q · b^p` und `b < a` folgt `p·j ≤ q·o`. -/
theorem ms_ratio {a b o j p q : Nat} (hab : b < a) (h : 2 ^ j * b ^ o ≤ a ^ o)
    (hpq : a ^ p ≤ 2 ^ q * b ^ p) : p * j ≤ q * o := by
  apply Nat.le_of_not_lt
  intro hlt
  obtain ⟨d, hd⟩ : ∃ d, p * j = q * o + (d + 1) := ⟨p * j - q * o - 1, by omega⟩
  have hq : (2 ^ j * b ^ o) ^ q ≤ (a ^ o) ^ q := Nat.pow_le_pow_left h q
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hq
  have hp : (a ^ p) ^ j ≤ (2 ^ q * b ^ p) ^ j := Nat.pow_le_pow_left hpq j
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hp
  rw [hd, show q * j = j * q by rw [Nat.mul_comm]] at hp
  rw [Nat.pow_add a (q * o) (d + 1), Nat.pow_add b (q * o) (d + 1)] at hp
  have hlt' : b ^ (d + 1) < a ^ (d + 1) := Nat.pow_lt_pow_left hab (by omega)
  have hpos : 0 < a ^ (q * o) := Nat.pow_pos (by omega)
  rw [show o * q = q * o by rw [Nat.mul_comm]] at hq
  have h9 : 2 ^ (j * q) * (b ^ (q * o) * b ^ (d + 1)) ≤ a ^ (q * o) * b ^ (d + 1) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hq
  have h10 : a ^ (q * o) * a ^ (d + 1) ≤ a ^ (q * o) * b ^ (d + 1) := Nat.le_trans hp h9
  have := Nat.le_of_mul_le_mul_left h10 hpos
  omega

/-- Allgemeine Form: Gilt `(3m+1)^p ≤ 2^q · m^p` für ein Bahnminimum `m ≥ 1`, so ist
`(2p − q)·J ≤ q·(#Rest-3-Stellen + 1)`. -/
theorem orbitMin_mod4_general {m p q : Nat} (h1 : 1 ≤ m) (hmin : IsOrbitMin m)
    (hpq : (3 * m + 1) ^ p ≤ 2 ^ q * m ^ p) (J : Nat) :
    2 * p * J ≤ q * J + q * (mod4Cnt m J + 1) := by
  have hd := orbitMin_density h1 hmin J
  have hr := ms_ratio (by omega) hd hpq
  have h2 := odds_le_double_odd J m
  rw [doCnt_eq_mod4Cnt] at h2
  have h3 : q * (2 * oddsT J m) ≤ q * (J + mod4Cnt m J + 1) := Nat.mul_le_mul_left q h2
  have e1 : q * (2 * oddsT J m) = 2 * (q * oddsT J m) := by
    rw [← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc]
  have e2 : q * (J + mod4Cnt m J + 1) = q * J + q * (mod4Cnt m J + 1) := by
    rw [Nat.add_assoc, Nat.mul_add]
  have e3 : 2 * p * J = 2 * (p * J) := Nat.mul_assoc 2 p J
  omega

theorem ms_const : (3 * 134217728 + 1) ^ 41 ≤ 2 ^ 65 * 134217728 ^ 41 := by decide

/-- Monotonie: Gilt die Ungleichung für `M ≤ m`, so auch für `m`. -/
theorem ms_mono {M m p q : Nat} (hM : 1 ≤ M) (hMm : M ≤ m)
    (h : (3 * M + 1) ^ p ≤ 2 ^ q * M ^ p) : (3 * m + 1) ^ p ≤ 2 ^ q * m ^ p := by
  have h1 : (3 * m + 1) * M ≤ (3 * M + 1) * m := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc,
      Nat.mul_comm m M]
    omega
  have h2 : ((3 * m + 1) * M) ^ p ≤ ((3 * M + 1) * m) ^ p := Nat.pow_le_pow_left h1 p
  rw [Nat.mul_pow, Nat.mul_pow] at h2
  have h3 : (3 * M + 1) ^ p * m ^ p ≤ 2 ^ q * M ^ p * m ^ p := Nat.mul_le_mul_right _ h
  have h4 : (3 * m + 1) ^ p * M ^ p ≤ 2 ^ q * m ^ p * M ^ p := by
    calc (3 * m + 1) ^ p * M ^ p ≤ 2 ^ q * M ^ p * m ^ p := Nat.le_trans h2 h3
      _ = 2 ^ q * m ^ p * M ^ p := by
        rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (M ^ p)]
  exact Nat.le_of_mul_le_mul_right h4 (Nat.pow_pos (by omega))

/-- **Satz 66.** Ab dem kleinsten Glied `m ≥ 2^27` eines Gegenbeispiels gilt
`17·J ≤ 65·(#{i < J : x_i ≡ 3 mod 4} + 1)`. -/
theorem orbitMin_mod4_sharp {m : Nat} (hbig : 134217728 ≤ m) (hmin : IsOrbitMin m)
    (J : Nat) : 17 * J ≤ 65 * (mod4Cnt m J + 1) := by
  have h := orbitMin_mod4_general (by omega) hmin (ms_mono (by decide) hbig ms_const) J
  omega

end Collatz
