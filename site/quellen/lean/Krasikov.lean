import Collatz.Crandall

/-!
# Rückwärtsbaum mit Buchführung modulo `3^J` (Methode von Krasikov)

Ein ungerader Vorfahre von `n` ist `c = (2^E·n − 1)/3`, sobald `2^E·n ≡ 1 (mod 3)`. Er ist nicht
durch 3 teilbar, genau wenn `2^E·n ≢ 1 (mod 9)`. Seine Restklasse modulo `3^(J−1)` hängt nur von
`n mod 3^J` und `E` ab. Die Klasse von `c` modulo `3^J` kennt man nicht, man nimmt das Minimum über
die drei Möglichkeiten (Hebungen).

Das ergibt eine Rekursion für eine untere Schranke `q d t S`: Unter einem Knoten `n` mit
`n ≡ t (mod 3^(J−1))` liegen mindestens `q d t S` verschiedene Zahlen `m` in Tiefe `d` mit
`3^d · m ≤ 2^S · n`, die alle `n` erreichen. Jede Funktion `q`, die die Rekursion als Ungleichung
erfüllt (ein *Zertifikat*), liefert diese Schranke (`tree_count`).
-/

namespace Collatz

/-- Der ungerade Anteil. -/
def oddPart (n : Nat) : Nat := if h : n % 2 = 0 ∧ 0 < n then oddPart (n / 2) else n
termination_by n
decreasing_by omega

theorem oddPart_odd {n : Nat} (h : n % 2 = 1) : oddPart n = n := by
  unfold oddPart; rw [dif_neg (by omega)]

theorem oddPart_two_pow : ∀ E n, n % 2 = 1 → oddPart (2 ^ E * n) = n := by
  intro E
  induction E with
  | zero => intro n h; rw [Nat.pow_zero, Nat.one_mul]; exact oddPart_odd h
  | succ E ih =>
    intro n h
    have hp : 0 < 2 ^ E * n := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) (by omega)
    have e : 2 ^ (E + 1) * n = 2 * (2 ^ E * n) := by rw [Nat.pow_succ]; grind
    rw [e]; unfold oddPart
    rw [dif_pos (by omega)]
    have : 2 * (2 ^ E * n) / 2 = 2 ^ E * n := by omega
    rw [this]; exact ih n h

/-- Ein Schritt nach oben im Rückwärtsbaum: vom ungeraden `m` zum ungeraden Anteil von `3m + 1`. -/
def up (m : Nat) : Nat := oddPart (3 * m + 1)

/-- `d` Schritte nach oben. -/
def upIter : Nat → Nat → Nat
  | 0, m => m
  | d + 1, m => up (upIter d m)

/-- Der Vorfahre mit Exponent `E`. -/
def anc (n E : Nat) : Nat := (2 ^ E * n - 1) / 3

/-- Restklasse von `2^E · s` modulo `3^J`. -/
def vv (J s E : Nat) : Nat := (2 ^ E * s) % 3 ^ J

/-- Zulässig: `2^E·s ≡ 1 (mod 3)`, und der Vorfahre ist nicht durch 3 teilbar. -/
def valid (J s E : Nat) : Bool := vv J s E % 3 == 1 && (vv J s E - 1) / 3 % 3 != 0

/-- Klasse des Vorfahren modulo `3^(J−1)`. -/
def cls (J s E : Nat) : Nat := (vv J s E - 1) / 3

theorem anc_props {J n E : Nat} (hJ : 2 ≤ J) (hE : 1 ≤ E)
    (hv : valid J (n % 3 ^ J) E = true) :
    3 * anc n E + 1 = 2 ^ E * n ∧ anc n E % 2 = 1 ∧ anc n E % 3 ≠ 0 ∧
      anc n E % 3 ^ (J - 1) = cls J (n % 3 ^ J) E := by
  obtain ⟨P, hP⟩ : ∃ P, 3 ^ (J - 1) = P := ⟨_, rfl⟩
  have h3J : 3 ^ J = 3 * P := by
    rw [← hP, ← Nat.pow_succ']; congr 1; omega
  have hP3 : P % 3 = 0 := by
    rw [← hP]; obtain ⟨i, hi⟩ : ∃ i, J - 1 = i + 1 := ⟨J - 2, by omega⟩
    rw [hi, Nat.pow_succ]; simp
  have hPpos : 0 < P := by rw [← hP]; exact Nat.pow_pos (by decide : 0 < 3)
  have hvv : vv J (n % 3 ^ J) E = (2 ^ E * n) % 3 ^ J := by
    unfold vv; rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  unfold valid at hv; rw [hvv] at hv
  unfold cls; rw [hvv]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [h3J] at hv1 hv2 ⊢
  have hNodd : (2 ^ E * n) % 2 = 0 := by
    obtain ⟨i, hi⟩ : ∃ i, E = i + 1 := ⟨E - 1, by omega⟩
    rw [hi, Nat.pow_succ]; rw [Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]; simp
  unfold anc
  generalize 2 ^ E * n = N at hv1 hv2 hNodd ⊢
  -- N = 3P·q + v
  have hd := Nat.div_add_mod N (3 * P)
  generalize N / (3 * P) = q at hd
  generalize hvdef : N % (3 * P) = v at hv1 hv2 hd
  have hvlt : v < 3 * P := by rw [← hvdef]; exact Nat.mod_lt _ (by omega)
  have hPq : (3 * P * q) % 3 = 0 := by rw [Nat.mul_assoc]; simp
  have e1 : (N - 1) / 3 = P * q + (v - 1) / 3 := by
    have : N = 3 * (P * q) + v := by rw [← hd, Nat.mul_assoc]
    omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [e1]
    have : (P * q) % 3 = 0 := by rw [Nat.mul_mod, hP3]; simp
    omega
  · rw [e1, hP, Nat.add_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)

theorem up_anc {n E : Nat} (h1 : n % 2 = 1) (h : 3 * anc n E + 1 = 2 ^ E * n) : up (anc n E) = n := by
  unfold up; rw [h]; exact oddPart_two_pow E n h1

theorem anc_reaches {n E : Nat} (hc : anc n E % 2 = 1) (h : 3 * anc n E + 1 = 2 ^ E * n) :
    iter (1 + E) (anc n E) = n := by
  rw [iter_add]
  have : iter 1 (anc n E) = 2 ^ E * n := by
    show step (anc n E) = 2 ^ E * n
    rw [step_odd hc, h]
  rw [this, iter_double_pow]

/-- Die zulässigen Exponenten `1 ≤ E ≤ min S Emax` für die Klasse `s`. -/
def Es (J Emax s S : Nat) : List Nat := (List.range' 1 (min S Emax)).filter (valid J s)

/-- Rechte Seite der Rekursion. -/
def rhs (J Emax : Nat) (q : Nat → Nat → Nat) (s S : Nat) : Nat :=
  ((Es J Emax s S).map (fun E => q (cls J s E) (S - E))).sum

/-- **Zertifikat**: `q` erfüllt die Rekursion als Ungleichung, für Tiefen `< D` und `S ≤ Smax`,
für jede der drei Hebungen `t + k·3^(J−1)`. -/
def Cert (J Emax D Smax : Nat) (q : Nat → Nat → Nat → Nat) : Prop :=
  (∀ t S, q 0 t S ≤ 1) ∧
  ∀ d, d < D → ∀ t, t < 3 ^ (J - 1) → t % 3 ≠ 0 → ∀ S, S ≤ Smax → ∀ k, k < 3 →
    q (d + 1) t S ≤ rhs J Emax (q d) (t + k * 3 ^ (J - 1)) S

/-- Eigenschaften der gezählten Knoten. -/
def Good (d S n m : Nat) : Prop :=
  m % 2 = 1 ∧ m % 3 ≠ 0 ∧ 3 ^ d * m ≤ 2 ^ S * n ∧ upIter d m = n ∧ ∃ j, iter j m = n

theorem Es_mem {J Emax s S E : Nat} (h : E ∈ Es J Emax s S) :
    1 ≤ E ∧ E ≤ S ∧ valid J s E = true := by
  unfold Es at h
  rw [List.mem_filter, List.mem_range'_1] at h
  obtain ⟨hi, hv⟩ := h
  exact ⟨by omega, by omega, hv⟩

theorem Es_nodup (J Emax s S : Nat) : (Es J Emax s S).Nodup := by
  unfold Es
  exact List.Nodup.sublist List.filter_sublist List.nodup_range'


/-- Zusammensetzen über eine Liste von Exponenten. -/
theorem collect {J n d : Nat} (hJ : 2 ≤ J) (h1 : n % 2 = 1) (f : Nat → Nat) (S : Nat)
    (sub : ∀ E, 1 ≤ E → E ≤ S → valid J (n % 3 ^ J) E = true →
      ∃ L : List Nat, L.Nodup ∧ f E ≤ L.length ∧ ∀ m ∈ L, Good d (S - E) (anc n E) m) :
    ∀ l : List Nat, l.Nodup → (∀ E ∈ l, 1 ≤ E ∧ E ≤ S ∧ valid J (n % 3 ^ J) E = true) →
      ∃ L : List Nat, L.Nodup ∧ (l.map f).sum ≤ L.length ∧
        ∀ m ∈ L, Good (d + 1) S n m ∧ ∃ E ∈ l, upIter d m = anc n E := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨[], List.nodup_nil, by simp, by simp⟩
  | cons E l ih =>
    intro hnd hl
    rw [List.nodup_cons] at hnd
    obtain ⟨hE1, hES, hEv⟩ := hl E (List.mem_cons_self ..)
    obtain ⟨L1, hn1, hlen1, hg1⟩ := sub E hE1 hES hEv
    obtain ⟨L2, hn2, hlen2, hg2⟩ := ih hnd.2 (fun E' h => hl E' (List.mem_cons_of_mem _ h))
    obtain ⟨hk, hkodd, hk3, _⟩ := anc_props hJ hE1 hEv
    refine ⟨L1 ++ L2, ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hn1, hn2, fun a ha b hb hab => ?_⟩
      subst hab
      obtain ⟨_, E', hE', hu⟩ := hg2 a hb
      have hu1 := (hg1 a ha).2.2.2.1
      rw [hu1] at hu
      obtain ⟨hk', _, _, _⟩ := anc_props hJ (hl E' (List.mem_cons_of_mem _ hE')).1
        (hl E' (List.mem_cons_of_mem _ hE')).2.2
      have : 2 ^ E * n = 2 ^ E' * n := by rw [← hk, ← hk', hu]
      have hn0 : 0 < n := by omega
      have : 2 ^ E = 2 ^ E' := Nat.eq_of_mul_eq_mul_right hn0 this
      have : E = E' := by
        rcases Nat.lt_trichotomy E E' with h | h | h
        · have := Nat.pow_lt_pow_right (by decide : 1 < 2) h; omega
        · exact h
        · have := Nat.pow_lt_pow_right (by decide : 1 < 2) h; omega
      exact hnd.1 (this ▸ hE')
    · rw [List.map_cons, List.sum_cons, List.length_append]; omega
    · intro m hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨g1, g2, g3, g4, j, hj⟩ := hg1 m hm
        refine ⟨⟨g1, g2, ?_, ?_, j + (1 + E), ?_⟩, E, List.mem_cons_self .., g4⟩
        · have : 3 ^ (d + 1) * m = 3 * (3 ^ d * m) := by rw [Nat.pow_succ]; grind
          rw [this]
          have h2 : 3 * (3 ^ d * m) ≤ 3 * (2 ^ (S - E) * anc n E) := Nat.mul_le_mul_left 3 g3
          have h3 : 3 * (2 ^ (S - E) * anc n E) ≤ 2 ^ (S - E) * (2 ^ E * n) := by
            rw [← hk]; grind
          have h4 : 2 ^ (S - E) * (2 ^ E * n) = 2 ^ S * n := by
            rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
          omega
        · show up (upIter d m) = n
          rw [g4]; exact up_anc h1 hk
        · rw [iter_add, hj]; exact anc_reaches hkodd hk
      · obtain ⟨g, E', hE', hu⟩ := hg2 m hm
        exact ⟨g, E', List.mem_cons_of_mem _ hE', hu⟩

/-- **Zählsatz.** Erfüllt `q` das Zertifikat, so liegen unter jedem ungeraden `n` mit `3 ∤ n`
mindestens `q d (n mod 3^(J−1)) S` verschiedene Zahlen `m` (Tiefe `d`) mit `3^d·m ≤ 2^S·n`,
die alle `n` erreichen. -/
theorem tree_count {J Emax D Smax : Nat} {q : Nat → Nat → Nat → Nat} (hJ : 2 ≤ J)
    (hc : Cert J Emax D Smax q) :
    ∀ d, d ≤ D → ∀ n S, n % 2 = 1 → n % 3 ≠ 0 → S ≤ Smax →
      ∃ L : List Nat, L.Nodup ∧ q d (n % 3 ^ (J - 1)) S ≤ L.length ∧ ∀ m ∈ L, Good d S n m := by
  intro d
  induction d with
  | zero =>
    intro _ n S h1 h3 _
    refine ⟨[n], by simp, by simpa using hc.1 _ S, ?_⟩
    intro m hm
    rw [List.mem_singleton] at hm; subst hm
    have : 1 ≤ 2 ^ S := Nat.one_le_two_pow
    refine ⟨h1, h3, ?_, rfl, 0, rfl⟩
    rw [Nat.pow_zero, Nat.one_mul]; exact Nat.le_mul_of_pos_left m (by omega)
  | succ d ih =>
    intro hd n S h1 h3 hS
    obtain ⟨P, hP⟩ : ∃ P, 3 ^ (J - 1) = P := ⟨_, rfl⟩
    have h3J : 3 ^ J = 3 * P := by
      rw [← hP, ← Nat.pow_succ']; congr 1; omega
    have hdvd : P ∣ 3 ^ J := by rw [h3J]; exact Nat.dvd_mul_left P 3
    have hP3 : 3 ∣ P := by
      rw [← hP]; obtain ⟨i, hi⟩ : ∃ i, J - 1 = i + 1 := ⟨J - 2, by omega⟩
      rw [hi, Nat.pow_succ]; exact Nat.dvd_mul_left 3 _
    have ht : (n % 3 ^ J) % P = n % P := Nat.mod_mod_of_dvd n hdvd
    have hdm := Nat.div_add_mod (n % 3 ^ J) P
    have hlt : n % 3 ^ J < 3 * P := by rw [← h3J]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hk : (n % 3 ^ J) / P < 3 := by
      have hPpos : 0 < P := by rw [← hP]; exact Nat.pow_pos (by decide)
      exact (Nat.div_lt_iff_lt_mul hPpos).2 (by omega)
    have hs : n % P + (n % 3 ^ J) / P * P = n % 3 ^ J := by
      rw [← ht]; rw [Nat.mul_comm]; omega
    have ht3 : n % P % 3 ≠ 0 := by
      rw [Nat.mod_mod_of_dvd n hP3]; exact h3
    have htlt : n % P < 3 ^ (J - 1) := by rw [hP]; exact Nat.mod_lt _ (by rw [← hP]; exact Nat.pow_pos (by decide))
    have key := hc.2 d (by omega) (n % P) htlt ht3 S hS _ hk
    rw [hP, hs] at key
    rw [hP]
    unfold rhs at key
    obtain ⟨L, hn, hlen, hg⟩ := collect hJ h1 (fun E => q d (cls J (n % 3 ^ J) E) (S - E)) S
      (fun E hE1 hES hEv => by
        obtain ⟨_, ho, h3', hcl⟩ := anc_props hJ hE1 hEv
        obtain ⟨L, hn, hlen, hg⟩ := ih (by omega) (anc n E) (S - E) ho h3' (by omega)
        exact ⟨L, hn, by show q d _ _ ≤ _; rw [← hcl]; exact hlen, hg⟩)
      (Es J Emax (n % 3 ^ J) S) (Es_nodup _ _ _ _) (fun E h => Es_mem h)
    exact ⟨L, hn, Nat.le_trans key hlen, fun m hm => (hg m hm).1⟩

/-! ## Die Tabelle: die Rekursion selbst als Zertifikat -/

/-- Eine Zeile der Tabelle aus der vorigen. -/
def getT (tab : List (List Nat)) (t S : Nat) : Nat := (tab.getD t []).getD S 0

def rhsT (J Emax : Nat) (tab : List (List Nat)) (s S : Nat) : Nat :=
  ((Es J Emax s S).map (fun E => getT tab (cls J s E) (S - E))).sum

def nextT (J Emax Smax : Nat) (tab : List (List Nat)) : List (List Nat) :=
  (List.range (3 ^ (J - 1))).map fun t => (List.range (Smax + 1)).map fun S =>
    min (rhsT J Emax tab t S) (min (rhsT J Emax tab (t + 3 ^ (J - 1)) S)
      (rhsT J Emax tab (t + 2 * 3 ^ (J - 1)) S))

def tabQ (J Emax Smax : Nat) : Nat → List (List Nat)
  | 0 => (List.range (3 ^ (J - 1))).map fun _ => (List.range (Smax + 1)).map fun _ => 1
  | d + 1 => nextT J Emax Smax (tabQ J Emax Smax d)

def qQ (J Emax Smax : Nat) (d t S : Nat) : Nat := getT (tabQ J Emax Smax d) t S

theorem getD_map_range {α : Type} (f : Nat → α) (n i : Nat) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl

theorem tabQ_cert (J Emax Smax D : Nat) : Cert J Emax D Smax (qQ J Emax Smax) := by
  refine ⟨fun t S => ?_, fun d _ t ht _ S hS k hk => ?_⟩
  · unfold qQ getT tabQ
    by_cases h : t < 3 ^ (J - 1)
    · rw [getD_map_range _ _ _ _ h]
      by_cases h' : S < Smax + 1
      · rw [getD_map_range _ _ _ _ h']; exact Nat.le_refl 1
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; simp
    · have : ((List.range (3 ^ (J - 1))).map fun _ => (List.range (Smax + 1)).map fun _ => 1)[t]? = none :=
        List.getElem?_eq_none (by simp; omega)
      rw [List.getD_eq_getElem?_getD (l := List.map _ _) (i := t), this]; simp
  · show getT (nextT J Emax Smax (tabQ J Emax Smax d)) t S ≤ rhs J Emax (qQ J Emax Smax d) _ S
    unfold getT nextT
    rw [getD_map_range _ _ _ _ ht, getD_map_range _ _ _ _ (by omega)]
    have e : ∀ s, rhsT J Emax (tabQ J Emax Smax d) s S = rhs J Emax (qQ J Emax Smax d) s S := by
      intro s; rfl
    rw [e, e, e]
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [Nat.zero_mul, Nat.add_zero]; exact Nat.min_le_left _ _
    · simp only [Nat.one_mul]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

/-! ## Blöcke aneinanderhängen: Schranke für alle Grössen -/

theorem upIter_add (a b m : Nat) : upIter (a + b) m = upIter a (upIter b m) := by
  induction a with
  | zero => simp [upIter]
  | succ a ih => rw [Nat.add_right_comm]; show up (upIter (a + b) m) = up (upIter a (upIter b m)); rw [ih]

theorem concat_lists {P : Nat → Nat → Prop} (key : Nat → Nat) (N : Nat) :
    ∀ A : List Nat, A.Nodup → (∀ a ∈ A, ∃ B : List Nat, B.Nodup ∧ N ≤ B.length ∧
      ∀ m ∈ B, P a m ∧ key m = a) →
    ∃ L : List Nat, L.Nodup ∧ N * A.length ≤ L.length ∧ ∀ m ∈ L, ∃ a ∈ A, P a m ∧ key m = a := by
  intro A
  induction A with
  | nil => intro _ _; exact ⟨[], List.nodup_nil, by simp, by simp⟩
  | cons a A ih =>
    intro hnd hsub
    rw [List.nodup_cons] at hnd
    obtain ⟨B, hB, hBl, hBp⟩ := hsub a (List.mem_cons_self ..)
    obtain ⟨L, hL, hLl, hLp⟩ := ih hnd.2 (fun b hb => hsub b (List.mem_cons_of_mem _ hb))
    refine ⟨B ++ L, ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hB, hL, fun x hx y hy hxy => ?_⟩
      subst hxy
      obtain ⟨b, hb, _, hk⟩ := hLp x hy
      have := (hBp x hx).2
      rw [this] at hk; subst hk
      exact hnd.1 hb
    · rw [List.length_append, List.length_cons, Nat.mul_succ]; omega
    · intro m hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact ⟨a, List.mem_cons_self .., hBp m hm⟩
      · obtain ⟨b, hb, h⟩ := hLp m hm
        exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-- **Block-Iteration.** Liefert ein Block `(d₀, S₀)` überall mindestens `L₀` Knoten, so liefern
`k` Blöcke mindestens `L₀^k` verschiedene Zahlen `m` mit `3^(k d₀)·m ≤ 2^(k S₀)·n`, die `n`
erreichen. -/
theorem block {J Emax D Smax : Nat} {q : Nat → Nat → Nat → Nat} (hJ : 2 ≤ J)
    (hc : Cert J Emax D Smax q) {d0 S0 L0 : Nat} (hd : d0 ≤ D) (hS : S0 ≤ Smax)
    (hL : ∀ t, t < 3 ^ (J - 1) → t % 3 ≠ 0 → L0 ≤ q d0 t S0) :
    ∀ k n, n % 2 = 1 → n % 3 ≠ 0 →
      ∃ L : List Nat, L.Nodup ∧ L0 ^ k ≤ L.length ∧ ∀ m ∈ L, Good (k * d0) (k * S0) n m := by
  intro k
  induction k with
  | zero =>
    intro n h1 h3
    refine ⟨[n], by simp, by simp, ?_⟩
    intro m hm; rw [List.mem_singleton] at hm; subst hm
    exact ⟨h1, h3, by simp, by simp [upIter], 0, by simp⟩
  | succ k ih =>
    intro n h1 h3
    obtain ⟨A, hA, hAl, hAg⟩ := tree_count hJ hc d0 hd n S0 h1 h3 hS
    have hq : L0 ≤ q d0 (n % 3 ^ (J - 1)) S0 := by
      apply hL
      · exact Nat.mod_lt _ (Nat.pow_pos (by decide))
      · have hP3 : 3 ∣ 3 ^ (J - 1) := by
          obtain ⟨i, hi⟩ : ∃ i, J - 1 = i + 1 := ⟨J - 2, by omega⟩
          rw [hi, Nat.pow_succ]; exact Nat.dvd_mul_left 3 _
        rw [Nat.mod_mod_of_dvd n hP3]; exact h3
    obtain ⟨L, hL', hLl, hLp⟩ := concat_lists (P := fun a m => Good (k * d0) (k * S0) a m)
      (upIter (k * d0)) (L0 ^ k) A hA (fun a ha => by
        obtain ⟨g1, g2, _, _, _⟩ := hAg a ha
        obtain ⟨B, hB, hBl, hBp⟩ := ih a g1 g2
        exact ⟨B, hB, hBl, fun m hm => ⟨hBp m hm, (hBp m hm).2.2.2.1⟩⟩)
    refine ⟨L, hL', ?_, ?_⟩
    · rw [Nat.pow_succ]
      have : L0 ^ k * L0 ≤ L0 ^ k * A.length := Nat.mul_le_mul_left _ (Nat.le_trans hq hAl)
      omega
    · intro m hm
      obtain ⟨a, ha, ⟨g1, g2, g3, g4, j, hj⟩, _⟩ := hLp m hm
      obtain ⟨_, _, a3, a4, i, hi⟩ := hAg a ha
      refine ⟨g1, g2, ?_, ?_, j + i, ?_⟩
      · have e1 : 3 ^ ((k + 1) * d0) * m = 3 ^ d0 * (3 ^ (k * d0) * m) := by
          rw [Nat.succ_mul, Nat.pow_add]; grind
        have e2 : 2 ^ ((k + 1) * S0) * n = 2 ^ (k * S0) * (2 ^ S0 * n) := by
          rw [Nat.succ_mul, Nat.pow_add]; grind
        rw [e1, e2]
        have := Nat.mul_le_mul_left (3 ^ d0) g3
        have h2 : 3 ^ d0 * (2 ^ (k * S0) * a) = 2 ^ (k * S0) * (3 ^ d0 * a) := by grind
        have := Nat.mul_le_mul_left (2 ^ (k * S0)) a3
        omega
      · rw [Nat.succ_mul, Nat.add_comm, upIter_add, g4, a4]
      · rw [iter_add, hj, hi]

/-! ## Zwischenstand als Literal (spart Speicher bei grossen Tabellen) -/

theorem nextT_le (J Emax Smax : Nat) (tab : List (List Nat)) {t S k : Nat}
    (ht : t < 3 ^ (J - 1)) (hS : S ≤ Smax) (hk : k < 3) :
    getT (nextT J Emax Smax tab) t S ≤ rhs J Emax (getT tab) (t + k * 3 ^ (J - 1)) S := by
  unfold getT nextT
  rw [getD_map_range _ _ _ _ ht, getD_map_range _ _ _ _ (by omega)]
  have e : ∀ s, rhsT J Emax tab s S = rhs J Emax (getT tab) s S := fun s => rfl
  rw [e, e, e]
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl | rfl
  · simp only [Nat.zero_mul, Nat.add_zero]; exact Nat.min_le_left _ _
  · simp only [Nat.one_mul]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

def tabFrom (J Emax Smax : Nat) (L : List (List Nat)) : Nat → List (List Nat)
  | 0 => L
  | d + 1 => nextT J Emax Smax (tabFrom J Emax Smax L d)

/-- Bis Tiefe `d₁` die Tabelle `tabQ`, danach weiter ab dem Literal `L = tabQ d₁`. -/
def qC (J Emax Smax d1 : Nat) (L : List (List Nat)) (d t S : Nat) : Nat :=
  if d ≤ d1 then qQ J Emax Smax d t S else getT (tabFrom J Emax Smax L (d - d1)) t S

theorem qC_cert (J Emax Smax d1 D : Nat) (L : List (List Nat)) (hL : tabQ J Emax Smax d1 = L) :
    Cert J Emax D Smax (qC J Emax Smax d1 L) := by
  have base := tabQ_cert J Emax Smax D
  refine ⟨fun t S => ?_, fun d hd t ht h3 S hS k hk => ?_⟩
  · unfold qC; rw [if_pos (Nat.zero_le _)]; exact base.1 t S
  · by_cases h : d + 1 ≤ d1
    · have e1 : qC J Emax Smax d1 L (d + 1) = qQ J Emax Smax (d + 1) := by
        funext t S; unfold qC; rw [if_pos h]
      have e2 : qC J Emax Smax d1 L d = qQ J Emax Smax d := by
        funext t S; unfold qC; rw [if_pos (by omega)]
      rw [e1, e2]; exact base.2 d hd t ht h3 S hS k hk
    · have e2 : qC J Emax Smax d1 L d = getT (tabFrom J Emax Smax L (d - d1)) := by
        funext t S; unfold qC
        by_cases h' : d ≤ d1
        · rw [if_pos h']
          have : d = d1 := by omega
          subst this
          rw [Nat.sub_self]; show getT (tabQ J Emax Smax d) t S = getT L t S; rw [hL]
        · rw [if_neg h']
      have e1 : qC J Emax Smax d1 L (d + 1) t S =
          getT (nextT J Emax Smax (tabFrom J Emax Smax L (d - d1))) t S := by
        unfold qC; rw [if_neg h]
        have : d + 1 - d1 = (d - d1) + 1 := by omega
        rw [this]; rfl
      rw [e1, e2]; exact nextT_le J Emax Smax _ ht hS hk

/-- **Verlängern.** Erfüllt `q` das Zertifikat bis Tiefe `D₁` und ist `q D₁` die Tabelle `L`,
so erfüllt die Fortsetzung ab `L` das Zertifikat bis zu jeder Tiefe. -/
theorem cert_extend {J Emax Smax D1 : Nat} {q : Nat → Nat → Nat → Nat} (hq : Cert J Emax D1 Smax q)
    (L : List (List Nat)) (hL : q D1 = getT L) (D : Nat) :
    Cert J Emax D Smax (fun d => if d ≤ D1 then q d else getT (tabFrom J Emax Smax L (d - D1))) := by
  refine ⟨fun t S => ?_, fun d _ t ht h3 S hS k hk => ?_⟩
  · simp only [Nat.zero_le, if_true]; exact hq.1 t S
  · by_cases h : d + 1 ≤ D1
    · simp only [h, if_true, show d ≤ D1 by omega]
      exact hq.2 d (by omega) t ht h3 S hS k hk
    · have e2 : (if d ≤ D1 then q d else getT (tabFrom J Emax Smax L (d - D1))) =
          getT (tabFrom J Emax Smax L (d - D1)) := by
        by_cases h' : d ≤ D1
        · rw [if_pos h']
          have : d = D1 := by omega
          subst this; rw [Nat.sub_self, hL]; rfl
        · rw [if_neg h']
      simp only [h, if_false]
      rw [e2]
      have : d + 1 - D1 = (d - D1) + 1 := by omega
      rw [this]
      exact nextT_le J Emax Smax _ ht hS hk

/-- Ein Etappenschritt: aus einem Zertifikat bis `D₁` mit Endtabelle `L` und `tabFrom L k = L'`
wird ein Zertifikat bis `D₁ + k` mit Endtabelle `L'`. -/
theorem ext_step {J Emax Smax D1 : Nat} {q : Nat → Nat → Nat → Nat} (hq : Cert J Emax D1 Smax q)
    {L L' : List (List Nat)} (hL : q D1 = getT L) (k : Nat) (hk : tabFrom J Emax Smax L k = L') :
    ∃ q' : Nat → Nat → Nat → Nat, Cert J Emax (D1 + k) Smax q' ∧ q' (D1 + k) = getT L' := by
  refine ⟨_, cert_extend hq L hL (D1 + k), ?_⟩
  by_cases h : D1 + k ≤ D1
  · have : k = 0 := by omega
    subst this; rw [← hk]; simp only [Nat.add_zero, Nat.le_refl, if_true]; rw [hL]; rfl
  · simp only [h, if_false]; rw [Nat.add_sub_cancel_left, hk]

end Collatz
