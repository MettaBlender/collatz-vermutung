# Lean-4-Formalisierung

Reines Lean 4 (v4.24.0, ohne Mathlib). Bauen mit `lake build`, Axiome prüfen mit
`lake env lean AxiomCheck.lean`.

**Wichtig:** Die Collatz-Vermutung selbst ist **nicht** bewiesen (sie ist ein offenes
Problem). `CollatzConjecture` ist nur als Aussage definiert. Alle Sätze unten sind
vollständig bewiesen, ohne `sorry` und ohne zusätzliche Axiome.

| Datei | Inhalt |
|---|---|
| `Collatz/Basic.lean` | `step`, `iter`, `ReachesOne`, `CollatzConjecture`; Zweierpotenzen erreichen 1; `2n` erreicht 1 ⇔ `n` erreicht 1 |
| `Collatz/Reduction.lean` | Reduktion auf Abstieg (endliche Stoppzeit); Abstieg für gerade Zahlen, `4a+1`, `16a+3`; Reduktion auf `n ≡ 7, 11, 15 (mod 16)`; `4n+1` und `n` (ungerade) laufen zusammen |
| `Collatz/Sieve.lean` | Verifiziertes Restklassen-Sieb mit Korrektheitsbeweis; nachgerechnet: mod 256 bleiben 19 Klassen, mod 4096 bleiben 226 |
| `Collatz/Sieve16.lean` | Sieb mod 2^16: nur 2114 von 65 536 Klassen (3.2 %) bleiben offen |
| `Collatz/Sieve20.lean` (+ `Sieve20A`–`D`, `Sieve20Count`) | Sieb mod 2^20 durch Hochheben der offenen Klassen mod 2^16: höchstens 27 328 von 1 048 576 Klassen (2.6 %) bleiben offen |
| `Collatz/Verified.lean` | Alle Zahlen 1 bis 10 000 erreichen die 1 (vom Kernel nachgerechnet, mit Korrektheitsbeweis des Prüfers) |
| `Collatz/VerifiedLarge.lean` | Alle Zahlen 1 bis 100 000 erreichen die 1 (nur `n ≡ 3 mod 4` geprüft, in Blöcken) |
| `Collatz/Cycles.lean` | Zyklen und Gegenbeispiele: jeder Zyklus, der die 1 erreicht, ist `1 → 4 → 2`; ein Gegenbeispiel enthält nur Zahlen > 100 000, und sein kleinstes Folgenglied liegt in einer der 2114 offenen Restklassen mod 2^16 |
| `Collatz/Tree.lean` | Collatz-Baum: Vorgänger-Charakterisierung; Vielfache von 3 haben nur den Vorgänger `2n`; ungerade Vorgänger genau für `n ≡ 4 (mod 6)`; jede Folge zur 1 läuft über die 16 |
| `Collatz/Climb.lean` | Beliebig lange Anstiege: `2^k·a − 1` wird nach `2k` Schritten zu `3^k·a − 1` und fällt unterwegs nie unter den Start; es gibt keine feste Abstiegszeit |
| `Collatz/Variants.lean` | Varianten qn+1: unter 5n+1 erreicht die 13 nie die 1 (Zyklus), unter n+1 erreicht jede Zahl die 1 |
