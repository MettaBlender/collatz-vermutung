import Collatz
/-! Zeigt, auf welchen Axiomen die Hauptsätze beruhen. Erwartet: nur die
Standard-Axiome von Lean (`propext`, `Classical.choice`, `Quot.sound`), kein `sorryAx`. -/
#print axioms Collatz.reachesOne_pow_two
#print axioms Collatz.conjecture_of_descends
#print axioms Collatz.conjecture_of_descends_mod_sixteen
#print axioms Collatz.reachesOne_four_mul_add_one_iff
#print axioms Collatz.survivors_256
#print axioms Collatz.conjecture_of_descends_mod_65536
#print axioms Collatz.reachesOne_upto_10000
#print axioms Collatz.iter_111_27
#print axioms Collatz.periodic_reachesOne
#print axioms Collatz.no_small_cycle
#print axioms Collatz.counterexample_structure
