import Collatz.KrasikovData

/-! Etappe der Tabelle, Tiefe 20 bis 25: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem seg25 : tabFrom 4 12 106 K20 5 = K25 := by decide +kernel

end Collatz
