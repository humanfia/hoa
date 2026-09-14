# IChO 2026, Problem 3.1 (T3-A1) — Answer

## Requested outputs

1. **Empirical formula of COF-1:** **C₉H₄BO₂**
2. **Mass percentage of carbon in COF-1 (%, two decimal places):** **69.77 %**

## How the answer follows from the problem statement alone

### Reading the building blocks (problem figure, Q3-1, theory_problem.pdf p. 25)

The figure prints the two precursors explicitly:

* **B3** (the honeycomb *vertex* building block): a four-ring fused
  triphenylene core bearing **six –OH groups** arranged as three catechol
  pairs (2,3 / 6,7 / 10,11). Triphenylene is C₁₈H₁₂; replacing six aromatic
  hydrogens by six hydroxyls gives **C₁₈H₆(OH)₆ = C₁₈H₁₂O₆**.
* **A2** (the honeycomb *edge* building block): one benzene ring bearing a
  –B(OH)₂ group at each of two para positions — benzene-1,4-diboronic acid,
  **C₆H₄(B(OH)₂)₂ = C₆H₈B₂O₄**.
* The printed COF-1 network shows each edge formed by two six-membered
  boronate-ester rings B–O–B–O–C–C closing one linker ring between two B3
  nuclei; alongside the figure the arrow label "−H₂O" marks that each
  C–OH/B–OH pair condenses to a C–O–B ester bond with loss of water.

### Honeycomb stoichiometry

In an infinite honeycomb lattice every vertex belongs to 3 hexagons and every
edge to 2 hexagons. Per hexagon the *independent* contents are therefore

* vertices: 6 × 1/3 = **2 B3 units**
* edges: 6 × 1/2 = **3 A2 units**

Atom balance per hexagon before condensation:

| element | 2 × B3 | 3 × A2 | total |
|---|---|---|---|
| C | 36 | 18 | 54 |
| H | 24 | 24 | 48 |
| B | 0 | 6 | 6 |
| O | 12 | 12 | 24 |

Condensation balance: the 3 A2 units contribute 6 B(OH)₂ groups (12 OH),
exactly matching the 12 OH of the 2 B3 units, so **12 H₂O** are eliminated
per hexagon (subtract H₂₄O₁₂):

| element | raw count per hexagon | ÷ gcd 6 |
|---|---|---|
| C | 54 | 9 |
| H | 24 | 4 |
| B | 6 | 1 |
| O | 12 | 2 |

Hence the empirical formula is **C₉H₄BO₂**. (The same ratio is obtained by
any periodic counting scheme, e.g. 9 boronate rings per hexagon with each
ring's middle O shared between two rings, each linker ring shared between two
hexagons, and each B3 nucleus shared among three.)

### Mass percentage of carbon

Using the atomic masses printed on the IChO 2026 periodic table (G1-5, p. 5
of the PDF): A(H) = 1.008, A(B) = 10.81, A(C) = 12.01, A(O) = 16.00.

* M(C₉H₄BO₂) = 9(12.01) + 4(1.008) + 10.81 + 2(16.00) = **154.932 g mol⁻¹**
* carbon mass per empirical unit: 9 × 12.01 = 108.09 g mol⁻¹
* w(C) = 108.09 / 154.932 × 100 % = 69.766 090 9… %

Rounded to two decimal places as requested: **69.77 %**.
(With standard four-figure masses 12.011/15.999 the value is 69.7687 %, which
rounds to the same 69.77 %, so the answer is insensitive to the mass
convention.)

## Answer-sheet entries (A3-1, p. 32)

```
COF-1: C₉H₄BO₂
C: 69.77 %
```

## Source-grounding notes

* All structural inputs (identities of B3 and A2, the −H₂O condensation, the
  honeycomb 3-share/2-share counting) come from the figure and text of Q3-1
  only; no external structural data are used. Triphenylene's hydrocarbon
  skeleton C₁₈H₁₂ is general textbook knowledge consistent with the printed
  four-ring fused nucleus.
* Atomic masses are taken from the paper's own periodic table (G1-5); no
  constant not printed in the problem materials is required. The sensitivity
  check with four-figure masses (Lean theorem
  `carbon_percent_four_figure_masses`) shows the last reported digit does not
  change.
* The final rounding follows the requested two-decimal display with the
  half-away-from-zero tie rule; the exact value 900750/12911 ≈ 69.76609 lies
  strictly inside [69.765, 69.775), so the tie rule is not actually invoked.
