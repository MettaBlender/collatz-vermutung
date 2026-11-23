import Collatz.KrasikovB20

/-! Etappe der Tabelle modulo 243, Tiefe 20 bis 25: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB25 : fastFrom 5 14 163 Q20 5 = Q25 := by decide +kernel

end Collatz
