import Collatz.KrasikovData

/-! Etappe der Tabelle, Tiefe 15 bis 20: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem seg20 : tabFrom 4 12 106 K15 5 = K20 := by decide +kernel

end Collatz
