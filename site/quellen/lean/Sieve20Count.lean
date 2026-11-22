import Collatz.Sieve20A
import Collatz.Sieve20B
import Collatz.Sieve20C
import Collatz.Sieve20D

namespace Collatz

/-- **Modulo 2^20 bleiben höchstens 27 328 von 1 048 576 Restklassen offen (2.6 %).** -/
theorem survivors20_length : survivors20.length = 27328 := by
  show D20 65536 = 27328
  have e0 : D20 4096 = d20 0 := rfl
  have e1 : D20 8192 = _ := D20_split 4096
  have e2 : D20 12288 = _ := D20_split 8192
  have e3 : D20 16384 = _ := D20_split 12288
  have e4 : D20 20480 = _ := D20_split 16384
  have e5 : D20 24576 = _ := D20_split 20480
  have e6 : D20 28672 = _ := D20_split 24576
  have e7 : D20 32768 = _ := D20_split 28672
  have e8 : D20 36864 = _ := D20_split 32768
  have e9 : D20 40960 = _ := D20_split 36864
  have e10 : D20 45056 = _ := D20_split 40960
  have e11 : D20 49152 = _ := D20_split 45056
  have e12 : D20 53248 = _ := D20_split 49152
  have e13 : D20 57344 = _ := D20_split 53248
  have e14 : D20 61440 = _ := D20_split 57344
  have e15 : D20 65536 = _ := D20_split 61440
  rw [e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0,
    d20_0, d20_1, d20_2, d20_3, d20_4, d20_5, d20_6, d20_7, d20_8, d20_9, d20_10, d20_11, d20_12, d20_13, d20_14, d20_15]

end Collatz
