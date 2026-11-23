import Collatz.KrasikovB15

/-! Etappe der Tabelle modulo 243, Tiefe 15 bis 20: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB20 : fastFrom 5 14 163 Q15 5 = Q20 := by decide +kernel

end Collatz
