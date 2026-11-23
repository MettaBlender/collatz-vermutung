import Collatz.KrasikovData

/-! Etappe der Tabelle, Tiefe 0 bis 5: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem seg5 : tabQ 4 12 106 5 = K5 := by decide +kernel

end Collatz
