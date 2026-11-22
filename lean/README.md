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
| `Collatz/Verified.lean` | Alle Zahlen 1 bis 10 000 erreichen die 1 (vom Kernel nachgerechnet, mit Korrektheitsbeweis des Prüfers) |
| `Collatz/Cycles.lean` | Zyklen und Gegenbeispiele: jeder Zyklus, der die 1 erreicht, ist `1 → 4 → 2`; ein Gegenbeispiel enthält nur Zahlen > 10 000, und sein kleinstes Folgenglied liegt in einer der 2114 offenen Restklassen mod 2^16 |
