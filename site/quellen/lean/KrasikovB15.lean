import Collatz.KrasikovB10

/-! Etappe der Tabelle modulo 243, Tiefe 10 bis 15: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB15 : fastFrom 5 14 163 Q10 5 = Q15 := by decide +kernel

end Collatz
