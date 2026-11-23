import Collatz.KrasikovB25

/-! Etappe der Tabelle modulo 243, Tiefe 25 bis 30: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB30 : fastFrom 5 14 163 Q25 5 = Q30 := by decide +kernel

end Collatz
