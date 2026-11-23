import Collatz.KrasikovData

/-! Etappe der Tabelle, Tiefe 10 bis 15: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem seg15 : tabFrom 4 12 106 K10 5 = K15 := by decide +kernel

end Collatz
