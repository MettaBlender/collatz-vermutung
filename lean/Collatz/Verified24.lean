import Collatz.VerifiedHuge

/-!
# Nachrechnung von 2^22 bis 2^24 über das Sieb modulo 2^20

Nur Zahlen `m` mit `m mod 2^20` in einer der 27 328 offenen Klassen (`survivors20`) müssen
noch nachgerechnet werden. Für `2^22 ≤ m < 2^24` sind das `27 328 · 12 = 327 936` Zahlen.
Die offenen Klassen werden in 128 Blöcken (je 512 Klassen modulo `2^16`) erzeugt und geprüft;
die Blöcke stehen in `Collatz/V24/F00` bis `F31` und werden in `Verified24All` zusammengesetzt.
-/

namespace Collatz

/-- Prüft für alle offenen Klassen `r mod 2^20` über den Klassen `lo ≤ s < lo + len`
modulo `2^16`, dass die Zahlen `2^20·a + r` mit `4 ≤ a < 16` abfallen. -/
def verifyOpen24 (lo len : Nat) : Bool :=
  (lift 65536 1048576 16 100 (openIn 65536 100 lo len)).all
    (fun r => verifyClass 1048576 (r + 4194304) 500 12)

theorem verifyOpen24_join {a b : Nat} (h1 : verifyOpen24 0 a = true)
    (h2 : verifyOpen24 a b = true) : verifyOpen24 0 (a + b) = true := by
  unfold verifyOpen24 at *
  rw [openIn_append, lift_append, List.all_append, Nat.zero_add, h1, h2]
  rfl

theorem descends_of_verifyOpen24 (h : verifyOpen24 0 65536 = true) {m : Nat}
    (hlo : 4194304 ≤ m) (hhi : m < 16777216) : Descends m := by
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
      unfold verifyOpen24 at h
      rw [List.all_eq_true] at h
      have hv := h _ hmem
      have hd : 1048576 * (m / 1048576 - 4) + (m % 1048576 + 4194304) = m := by omega
      have := descends_of_verifyClass 12 hv (m / 1048576 - 4) (by omega) (by omega)
      rwa [hd] at this

end Collatz
