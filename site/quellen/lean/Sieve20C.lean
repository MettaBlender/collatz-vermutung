import Collatz.Sieve20

/-! Blöcke 8 bis 11 für `survivors20_length` (eigene Datei, damit der Kernel-Speicher klein bleibt). -/

namespace Collatz

theorem d20_8 : d20 32768 = 1683 := by decide +kernel
theorem d20_9 : d20 36864 = 1681 := by decide +kernel
theorem d20_10 : d20 40960 = 1726 := by decide +kernel
theorem d20_11 : d20 45056 = 1706 := by decide +kernel

end Collatz
