import Collatz.Verified24

/-!
# Nachrechnung von 2^26 bis 2^27 über das Sieb modulo 2^20

Wie `Verified24`, aber für `2^26 ≤ m < 2^27`: pro offener Klasse modulo `2^20` die
64 Zahlen `2^20·a + r` mit `64 ≤ a < 128`, zusammen `27 328 · 64 = 1 748 992` Zahlen.
Die 512 Teile (je 128 Klassen modulo `2^16`) stehen in `Collatz/V27/I000` bis `I511`;
die CI baut sie in acht parallelen Jobs.
-/

namespace Collatz

/-- Prüft für alle offenen Klassen `r mod 2^20` über den Klassen `lo ≤ s < lo + len`
modulo `2^16`, dass die Zahlen `2^20·a + r` mit `64 ≤ a < 128` abfallen. -/
def verifyOpen27 (lo len : Nat) : Bool :=
  (lift 65536 1048576 16 100 (openIn 65536 100 lo len)).all
    (fun r => verifyClass 1048576 (r + 67108864) 500 64)

theorem verifyOpen27_join' {a b c : Nat} (h1 : verifyOpen27 0 a = true)
    (h2 : verifyOpen27 a b = true) (hc : a + b = c) : verifyOpen27 0 c = true := by
  subst hc
  unfold verifyOpen27 at *
  rw [openIn_append, lift_append, List.all_append, Nat.zero_add, h1, h2]
  rfl

theorem descends_of_verifyOpen27 (h : verifyOpen27 0 65536 = true) {m : Nat}
    (hlo : 67108864 ≤ m) (hhi : m < 134217728) : Descends m := by
  have h1 : 1 < m := by omega
  cases h16 : check 65536 (m % 65536) 100 65536 (m % 65536) with
  | true => exact descends_of_check h16 rfl h1
  | false =>
    cases h20 : check 1048576 (m % 1048576) 100 1048576 (m % 1048576) with
    | true => exact descends_of_check h20 rfl h1
    | false =>
      have ht : m % 1048576 = m % 65536 + 65536 * (m % 1048576 / 65536) := by omega
      have hm := mem_openIn h16 65536 0 (Nat.zero_le _) (by omega)
      rw [ht] at h20
      have hmem := mem_lift (K := 16) hm (by omega) h20
      rw [← ht] at hmem
      unfold verifyOpen27 at h
      rw [List.all_eq_true] at h
      have hv := h _ hmem
      have hd : 1048576 * (m / 1048576 - 64) + (m % 1048576 + 67108864) = m := by omega
      have := descends_of_verifyClass 64 hv (m / 1048576 - 64) (by omega) (by omega)
      rwa [hd] at this

end Collatz
