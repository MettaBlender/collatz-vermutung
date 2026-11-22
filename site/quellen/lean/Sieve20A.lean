import Collatz.Sieve20

/-! Blöcke 0 bis 3 für `survivors20_length` (eigene Datei, damit der Kernel-Speicher klein bleibt). -/

namespace Collatz

theorem d20_0 : d20 0 = 1705 := by decide +kernel
theorem d20_1 : d20 4096 = 1663 := by decide +kernel
theorem d20_2 : d20 8192 = 1805 := by decide +kernel
theorem d20_3 : d20 12288 = 1646 := by decide +kernel

end Collatz
