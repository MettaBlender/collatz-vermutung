import Collatz.Sieve20

/-! Blöcke 4 bis 7 für `survivors20_length` (eigene Datei, damit der Kernel-Speicher klein bleibt). -/

namespace Collatz

theorem d20_4 : d20 16384 = 1774 := by decide +kernel
theorem d20_5 : d20 20480 = 1662 := by decide +kernel
theorem d20_6 : d20 24576 = 1694 := by decide +kernel
theorem d20_7 : d20 28672 = 1737 := by decide +kernel

end Collatz
