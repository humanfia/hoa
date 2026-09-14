import Mathlib

/-!
# IChO 2026, Theory Problem 3, Subpart 3.1 (T3-A1)

**Question (see `T3_page-1.png`, theory_problem.pdf p. 25):**
"Determine the empirical formula of **COF-1** and calculate the mass percentage
(%, to two decimal places) of carbon in COF-1." (2.0 pt)
Blank answer sheet (PDF p. 32): `COF-1: ______`, `C: ______ %`.

## Source grounding (problem-only inputs)

The figure on page 25 draws the honeycomb 2D-COF from two building blocks,
with black and red bold lines denoting the two different building blocks.
Reading the printed structure:

* **B3 (nucleus, honeycomb vertex):** a triphenylene core bearing three
  catechol pairs, i.e. six –OH groups in all: hexahydroxytriphenylene
  (HHTP).  Triphenylene is C₁₈H₁₂; replacing six aromatic H by six –OH
  gives C₁₈H₆(OH)₆, so **B3 = C₁₈H₁₂O₆**.
* **A2 (edge linker):** one para-phenylene ring with a –B(OH)₂ group at
  each end (benzene-1,4-diboronic acid, BDBA):
  **A2 = C₆H₈B₂O₄ = C₆H₄(B(OH)₂)₂**.
* **Connectivity in COF-1:** each edge of the honeycomb is one linker ring
  closed by two boronate-ester rings (each printed as B–O–B–O–C–C), i.e.
  each B(OH)₂ of an A2 condenses with one catechol pair (two –OH) of a B3,
  eliminating 2 H₂O per B(OH)₂, hence 4 H₂O per A2.

### Honeycomb stoichiometry (graph counting)

In the infinite honeycomb lattice each vertex is shared by 3 hexagons and
each edge by 2 hexagons, so per hexagon the independent contents are
6/3 = 2 B3 vertices and 6/2 = 3 A2 edges.

Atom balance per hexagon before condensation:

* C: 2·18 + 3·6 = 54
* H: 2·12 + 3·8 = 48  (the two B(OH)₂ groups of each A2 carry 4 H in total)
* B: 3·2 = 6
* O: 2·6 + 3·4 = 24

The 3 A2 linkers bring 6 B(OH)₂ groups (12 –OH), exactly consuming the
12 –OH of the 2 B3 cores, so 12 H₂O are eliminated per hexagon, giving the
raw composition C₅₄H₂₄B₆O₁₂.  Dividing by gcd(54, 24, 6, 12) = 6 yields the
empirical formula

```
  C₉H₄BO₂
```

## Carbon mass percentage

The atomic-mass instrument of this paper is its **printed periodic table
(G1-5, PDF p. 5)**, which gives A(H) = 1.008, A(B) = 10.81, A(C) = 12.01,
A(O) = 16.00.  With these values:

```
  M(C₉H₄BO₂) = 9·12.01 + 4·1.008 + 10.81 + 2·16.00 = 154.932 g mol⁻¹
  w(C) = 108.09 / 154.932 · 100 % = 69.766 090 9… % → 69.77 %
```

The exact value lies in [69.765, 69.775) = [69.77 − 0.005, 69.77 + 0.005),
the round-half-away-from-zero capture interval of 69.77 at quantum 0.01,
so the two-decimal answer is **69.77 %**.

Sensitivity note: with standard four-figure masses (12.011, 15.999) one
obtains 69.7687 %, which rounds to the same 69.77 %, so the reported digit
is stable under the atomic-mass convention.
-/

namespace IChO2026T3A1

/-- Relative atomic masses exactly as printed on the IChO 2026 periodic
table (page G1-5): A(C) = 12.01, A(H) = 1.008, A(B) = 10.81, A(O) = 16.00. -/
noncomputable def arC : ℝ := 1201 / 100
noncomputable def arH : ℝ := 1008 / 1000
noncomputable def arB : ℝ := 1081 / 100
noncomputable def arO : ℝ := 16

/-- Standard four-figure variants used only for the sensitivity cross-check. -/
noncomputable def arC4 : ℝ := 12011 / 1000
noncomputable def arO4 : ℝ := 15999 / 1000

/-- Building block B3 (hexahydroxytriphenylene): C₁₈H₁₂O₆. -/
def B3_C : ℝ := 18
def B3_H : ℝ := 12
def B3_O : ℝ := 6

/-- Building block A2 (benzene-1,4-diboronic acid): C₆H₈B₂O₄. -/
def A2_C : ℝ := 6
def A2_H : ℝ := 8
def A2_B : ℝ := 2
def A2_O : ℝ := 4

/-- Honeycomb multiplicities per hexagon: 2 vertices (shared among 3
hexagons), 3 edges (shared among 2), 12 eliminated H₂O molecules. -/
def nB3 : ℝ := 2
def nA2 : ℝ := 3
def nW  : ℝ := 12

/-- Raw atom counts per primitive hexagon, after dehydration. -/
def hexC : ℝ := nB3 * B3_C + nA2 * A2_C
def hexH : ℝ := nB3 * B3_H + nA2 * A2_H - 2 * nW
def hexB : ℝ := nA2 * A2_B
def hexO : ℝ := nB3 * B3_O + nA2 * A2_O - nW

/-- The raw per-hexagon composition is C₅₄H₂₄B₆O₁₂. -/
theorem hexagon_composition :
    hexC = 54 ∧ hexH = 24 ∧ hexB = 6 ∧ hexO = 12 := by
  unfold hexC hexH hexB hexO nB3 nA2 nW B3_C B3_H B3_O A2_C A2_H A2_B A2_O
  norm_num

/-- Each raw count factors through 6, so the empirical atom counts are
(9, 4, 1, 2): the empirical formula of COF-1 is C₉H₄BO₂. -/
theorem empirical_counts :
    hexC = 6 * 9 ∧ hexH = 6 * 4 ∧ hexB = 6 * 1 ∧ hexO = 6 * 2 := by
  unfold hexC hexH hexB hexO nB3 nA2 nW B3_C B3_H B3_O A2_C A2_H A2_B A2_O
  norm_num

/-- 6 is the greatest common divisor of the raw counts (54, 24, 6, 12). -/
theorem gcd_is_six : Nat.gcd (Nat.gcd (Nat.gcd 54 24) 6) 12 = 6 := by norm_num

/-- Molar mass of the empirical unit C₉H₄BO₂ with the printed table masses:
M = 9·12.01 + 4·1.008 + 10.81 + 2·16.00 = 154.932 g mol⁻¹. -/
theorem molar_mass_empirical_unit :
    (hexC / 6) * arC + (hexH / 6) * arH + (hexB / 6) * arB + (hexO / 6) * arO
      = 154932 / 1000 := by
  unfold hexC hexH hexB hexO nB3 nA2 nW B3_C B3_H B3_O A2_C A2_H A2_B A2_O
    arC arH arB arO
  norm_num

/-- Carbon mass of the empirical unit with the printed mass: 9·12.01 = 108.09. -/
theorem carbon_mass_empirical_unit : (hexC / 6) * arC = 10809 / 100 := by
  unfold hexC nB3 nA2 B3_C A2_C arC
  norm_num

/-- The exact carbon mass percentage of COF-1 using the printed masses:
(108.09/154.932)·100. -/
noncomputable def carbonPercent : ℝ :=
  (hexC / 6) * arC / ((hexC / 6) * arC + (hexH / 6) * arH + (hexB / 6) * arB
    + (hexO / 6) * arO) * 100

/-- The exact percentage equals 900750/12911 ≈ 69.76609 %. -/
theorem carbon_percent_value : carbonPercent = 900750 / 12911 := by
  unfold carbonPercent hexC hexH hexB hexO nB3 nA2 nW
    B3_C B3_H B3_O A2_C A2_H A2_B A2_O arC arH arB arO
  norm_num

/-- Two-decimal rounding window: the exact value lies in [69.765, 69.775),
the round-half-away-from-zero capture interval of 69.77 at quantum 0.01. -/
theorem carbon_percent_rounding_window :
    (69765 : ℝ) / 1000 ≤ carbonPercent ∧ carbonPercent < (69775 : ℝ) / 1000 := by
  rw [carbon_percent_value]
  constructor <;> norm_num

/-- The reported value at two decimal places is exactly 69.77 % — proved in
the reporting form: `carbonPercent` is captured by the multiple 69.77 of
quantum 0.01 with the half-away-from-zero convention. -/
theorem carbon_percent_reports_to_6977 :
    (6977 / 100 : ℝ) - (1 / 100 : ℝ) / 2 ≤ carbonPercent ∧
      carbonPercent < (6977 / 100 : ℝ) + (1 / 100 : ℝ) / 2 := by
  have h := carbon_percent_rounding_window
  constructor <;> linarith [h.1, h.2]

/-- The percentage is nonnegative, so the half-away-from-zero tie rule agrees
with the capture interval used above. -/
theorem carbon_percent_nonneg : 0 ≤ carbonPercent := by
  rw [carbon_percent_value]
  positivity

/-- Sensitivity cross-check: with standard four-figure masses 12.011 and
15.999 the percentage is ≈ 69.7687 % and stays inside the 69.77 window, so
the reported digit is stable under the mass convention. -/
theorem carbon_percent_four_figure_masses :
    (69765 : ℝ) / 1000 ≤
      (9 * arC4) / (9 * arC4 + 4 * arH + arB + 2 * arO4) * 100 ∧
      (9 * arC4) / (9 * arC4 + 4 * arH + arB + 2 * arO4) * 100 <
        (69775 : ℝ) / 1000 := by
  unfold arC4 arH arB arO4
  constructor <;> norm_num

/-- Final packaged answer for T3-A1: the empirical formula of COF-1 is
C₉H₄BO₂ (per-hexagon counts 54, 24, 6, 12 reduced by gcd 6) and, using the
printed periodic-table masses, its carbon mass percentage equals
900750/12911, which rounds to 69.77 % at the requested two decimal places. -/
theorem answer_icho_2026_t3_a1 :
    hexC = 54 ∧ hexH = 24 ∧ hexB = 6 ∧ hexO = 12 ∧
    Nat.gcd (Nat.gcd (Nat.gcd 54 24) 6) 12 = 6 ∧
    ((hexC / 6) * arC + (hexH / 6) * arH + (hexB / 6) * arB + (hexO / 6) * arO
        = 154932 / 1000) ∧
    ((69765 : ℝ) / 1000 ≤ (hexC / 6) * arC / (154932 / 1000) * 100 ∧
      (hexC / 6) * arC / (154932 / 1000) * 100 < (69775 : ℝ) / 1000) := by
  refine ⟨hexagon_composition.1, hexagon_composition.2.1,
    hexagon_composition.2.2.1, hexagon_composition.2.2.2, gcd_is_six,
    molar_mass_empirical_unit, ?_⟩
  rw [carbon_mass_empirical_unit]
  constructor <;> norm_num

end IChO2026T3A1
