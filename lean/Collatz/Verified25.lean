import Collatz.Verified24

/-!
# Nachrechnung von 2^24 bis 2^25 über das Sieb modulo 2^20

Wie `Verified24`, aber für `2^24 ≤ m < 2^25`: pro offener Klasse modulo `2^20` die
16 Zahlen `2^20·a + r` mit `16 ≤ a < 32`, zusammen `27 328 · 16 = 437 248` Zahlen.
Die 128 Blöcke (je 512 Klassen modulo `2^16`) stehen in `Collatz/V25/G00` bis `G63`
(je 2 Blöcke, damit eine Datei unter etwa 4 GB Speicher bleibt).
-/

namespace Collatz

/-- Prüft für alle offenen Klassen `r mod 2^20` über den Klassen `lo ≤ s < lo + len`
modulo `2^16`, dass die Zahlen `2^20·a + r` mit `16 ≤ a < 32` abfallen. -/
def verifyOpen25 (lo len : Nat) : Bool :=
  (lift 65536 1048576 16 100 (openIn 65536 100 lo len)).all
    (fun r => verifyClass 1048576 (r + 16777216) 500 16)

theorem verifyOpen25_join' {a b c : Nat} (h1 : verifyOpen25 0 a = true)
    (h2 : verifyOpen25 a b = true) (hc : a + b = c) : verifyOpen25 0 c = true := by
  subst hc
  unfold verifyOpen25 at *
  rw [openIn_append, lift_append, List.all_append, Nat.zero_add, h1, h2]
  rfl

theorem descends_of_verifyOpen25 (h : verifyOpen25 0 65536 = true) {m : Nat}
    (hlo : 16777216 ≤ m) (hhi : m < 33554432) : Descends m := by
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
      unfold verifyOpen25 at h
      rw [List.all_eq_true] at h
      have hv := h _ hmem
      have hd : 1048576 * (m / 1048576 - 16) + (m % 1048576 + 16777216) = m := by omega
      have := descends_of_verifyClass 16 hv (m / 1048576 - 16) (by omega) (by omega)
      rwa [hd] at this

end Collatz
