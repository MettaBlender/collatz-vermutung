import Collatz.Sieve20

/-! Blöcke 12 bis 15 für `survivors20_length` (eigene Datei, damit der Kernel-Speicher klein bleibt). -/

namespace Collatz

theorem d20_12 : d20 49152 = 1737 := by decide +kernel
theorem d20_13 : d20 53248 = 1698 := by decide +kernel
theorem d20_14 : d20 57344 = 1707 := by decide +kernel
theorem d20_15 : d20 61440 = 1704 := by decide +kernel

end Collatz
