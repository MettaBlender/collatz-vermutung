import Collatz.Terras

/-!
# 2-adische Zahlen: Paritätsfolgen sind eine Bijektion (Terras, Lagarias)

Der Satz von Terras (`Terras.lean`) sagt für jede Länge `k`: Die ersten `k` Paritäten
bestimmen `n mod 2^k`, und jede 0/1-Folge der Länge `k` kommt genau einmal vor. Hier setzen
wir das für **unendliche** Folgen zusammen:

* Eine 2-adische Zahl ist eine verträgliche Folge von Resten `x_k mod 2^k`.
* Ihre Paritätsfolge `Q x : Nat → Bool` ist die Folge der Paritäten von `x, T x, T² x, …`.
* **Satz:** `Q` ist eine Bijektion zwischen den 2-adischen Zahlen und allen unendlichen
  0/1-Folgen (`Q_injective`, `Q_surjective`).
* **Konjugation:** `T` setzt sich auf die 2-adischen Zahlen fort, und `Q` übersetzt `T` in die
  Verschiebung der Folge um eine Stelle (`Q_T`).

Bedeutung: Auf den 2-adischen Zahlen ist die Collatz-Abbildung "nichts anderes" als das
Verschieben einer beliebigen 0/1-Folge. Jedes Verhalten (auch Divergenz) kommt dort vor.
Die Vermutung ist eine Aussage darüber, welche Folgen von **gewöhnlichen** natürlichen
Zahlen herkommen. Darum kann ein Beweis nicht nur mit Restklassen argumentieren.
-/

namespace Collatz

/-- Die `i`-te Parität von `n` (`true` = ungerade): die Parität von `T^i(n)`. -/
def nthPar (i n : Nat) : Bool := Titer i n % 2 == 1

theorem nthPar_succ (i n : Nat) : nthPar (i + 1) n = nthPar i (T n) := rfl

/-- Der Paritätsvektor ist die Liste der ersten `k` Paritäten. -/
theorem parVec_eq_map : ∀ k n, parVec k n = (List.range k).map (fun i => nthPar i n) := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show (n % 2 == 1) :: parVec k (T n) = _
    rw [ih]
    rfl

/-- Die `i`-te Parität hängt nur von `n mod 2^(i+1)` ab. -/
theorem nthPar_mod (i n : Nat) : nthPar i n = nthPar i (n % 2 ^ (i + 1)) := by
  have h := parVec_mod (i + 1) n
  rw [parVec_eq_map, parVec_eq_map] at h
  exact (List.map_inj_left.mp h) i (List.mem_range.mpr (Nat.lt_succ_self i))

/-! ## 2-adische Zahlen -/

/-- Eine 2-adische Zahl: verträgliche Reste `val k < 2^k` mit `val (k+1) ≡ val k (mod 2^k)`. -/
structure Z2 where
  val : Nat → Nat
  lt : ∀ k, val k < 2 ^ k
  compat : ∀ k, val (k + 1) % 2 ^ k = val k

/-- Die natürlichen Zahlen sind 2-adische Zahlen. -/
def Z2.ofNat (n : Nat) : Z2 where
  val k := n % 2 ^ k
  lt k := Nat.mod_lt _ (Nat.pow_pos (by decide))
  compat k := Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 (Nat.le_succ k))

theorem Z2.compat_add (x : Z2) (j : Nat) : ∀ d, x.val (j + d) % 2 ^ j = x.val j := by
  intro d
  induction d with
  | zero => exact Nat.mod_eq_of_lt (x.lt j)
  | succ d ih =>
    rw [← Nat.add_assoc, ← Nat.mod_mod_of_dvd (x.val (j + d + 1))
      (Nat.pow_dvd_pow 2 (Nat.le_add_right j d)), x.compat, ih]

theorem Z2.compat_le (x : Z2) {j k : Nat} (h : j ≤ k) : x.val k % 2 ^ j = x.val j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact x.compat_add j d

/-- **Die Paritätsfolge** einer 2-adischen Zahl. -/
def Q (x : Z2) (i : Nat) : Bool := nthPar i (x.val (i + 1))

/-- Für natürliche Zahlen ist das die gewöhnliche Paritätsfolge. -/
theorem Q_ofNat (n i : Nat) : Q (Z2.ofNat n) i = nthPar i n :=
  (nthPar_mod i n).symm

/-- Die ersten `k` Paritäten von `val k` sind die ersten `k` Glieder von `Q x`. -/
theorem parVec_val (x : Z2) (k : Nat) : parVec k (x.val k) = (List.range k).map (Q x) := by
  rw [parVec_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i + 1 ≤ k := List.mem_range.mp hi
  show nthPar i (x.val k) = nthPar i (x.val (i + 1))
  rw [nthPar_mod, x.compat_le hi']

/-- **Injektiv:** Zwei 2-adische Zahlen mit derselben Paritätsfolge sind gleich. -/
theorem Q_injective {x y : Z2} (h : Q x = Q y) : x.val = y.val := by
  funext k
  apply parVec_injective k _ _ (x.lt k) (y.lt k)
  rw [parVec_val, parVec_val, h]

/-- Zu jeder Folge `v` und Länge `k` der Rest `r < 2^k` mit den Paritäten `v 0, …, v (k-1)`. -/
theorem exists_res (v : Nat → Bool) (k : Nat) :
    ∃ r, r < 2 ^ k ∧ parVec k r = (List.range k).map v := by
  obtain ⟨r, hr, hv⟩ := parVec_surjective ((List.range k).map v)
  rw [List.length_map, List.length_range] at hr hv
  exact ⟨r, hr, hv⟩

/-- Aus `parVec k r = map v (range k)` folgt `nthPar i r = v i` für `i < k`. -/
theorem nthPar_of_parVec {k r : Nat} {v : Nat → Bool} (h : parVec k r = (List.range k).map v)
    {i : Nat} (hi : i < k) : nthPar i r = v i := by
  rw [parVec_eq_map] at h
  exact (List.map_inj_left.mp h) i (List.mem_range.mpr hi)

/-- Die 2-adische Zahl mit der Paritätsfolge `v`. -/
noncomputable def Z2.ofSeq (v : Nat → Bool) : Z2 where
  val k := Classical.choose (exists_res v k)
  lt k := (Classical.choose_spec (exists_res v k)).1
  compat k := by
    have h1 := (Classical.choose_spec (exists_res v (k + 1))).2
    have h0 := Classical.choose_spec (exists_res v k)
    generalize Classical.choose (exists_res v (k + 1)) = a at h1
    generalize Classical.choose (exists_res v k) = b at h0
    apply parVec_injective k _ _ (Nat.mod_lt _ (Nat.pow_pos (by decide))) h0.1
    rw [← parVec_mod, h0.2, parVec_eq_map]
    apply List.map_congr_left
    intro i hi
    exact nthPar_of_parVec h1 (Nat.lt_succ_of_lt (List.mem_range.mp hi))

/-- **Surjektiv:** Jede unendliche 0/1-Folge ist die Paritätsfolge einer 2-adischen Zahl. -/
theorem Q_surjective (v : Nat → Bool) : Q (Z2.ofSeq v) = v := by
  funext i
  exact nthPar_of_parVec (Classical.choose_spec (exists_res v (i + 1))).2 (Nat.lt_succ_self i)

/-! ## `T` auf den 2-adischen Zahlen ist die Verschiebung -/

/-- `T` auf 2-adischen Zahlen: `(T x)_k = T(x_{k+1}) mod 2^k`. -/
def Z2.T (x : Z2) : Z2 where
  val k := Collatz.T (x.val (k + 1)) % 2 ^ k
  lt k := Nat.mod_lt _ (Nat.pow_pos (by decide))
  compat k := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ k))]
    -- x_{k+2} = x_{k+1} + 2^(k+1)·a
    have hc := x.compat (k + 1)
    have hd := Nat.mod_add_div (x.val (k + 2)) (2 ^ (k + 1))
    rw [hc] at hd
    generalize x.val (k + 2) / 2 ^ (k + 1) = a at hd
    rw [← hd, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, T_add_two_mul]
    split
    · rw [show 3 * (2 ^ k * a) = 2 ^ k * (3 * a) by
        rw [Nat.mul_left_comm], Nat.add_mul_mod_self_left]
    · rw [Nat.add_mul_mod_self_left]

/-- **Konjugation:** Die Paritätsfolge von `T x` ist die um eine Stelle verschobene Folge. -/
theorem Q_T (x : Z2) (i : Nat) : Q x.T i = Q x (i + 1) := by
  show nthPar i (Collatz.T (x.val (i + 2)) % 2 ^ (i + 1)) = nthPar (i + 1) (x.val (i + 2))
  rw [← nthPar_mod, nthPar_succ]

end Collatz
