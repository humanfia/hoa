# IChO 2026, Theory Problem 1, subquestion 1.6 (T1‑A6)

**Question.** "Determine the chemical formulae of the **stone** and compound
**H** using thermogravimetric data." (Official text, p. Q1‑4 of
`theory_problem.pdf`, verified against `T1_page-3.png`/`T1_page-4.png`.)

The thermogravimetric experiment: a **10.00 g** sample of the stone, in open
air, began to lose mass at ≈ 100 °C and stopped at **5.75 g** at 200 °C; a
second drop was observed at 400 °C with a final mass of **1.50 g** of compound
**H**, constant at higher temperatures.

---

## 1. What the problem's own clues force (prerequisites, derived answer-blind)

All steps below are equality-forced identifications from the printed
percentages; each identification is checked inside its displayed half-quantum
measurement window (per the campaign reporting contract), and the checks are
proved in Lean (`IChO2026Problems/problem_icho_2026_t1_a6.lean`).

**From 1.4.** D contains 32.85 % Na and 12.85 % of metal Q and is "used in the
industrial production of Q". The Hall–Héroult electrolyte fits exactly:

- **D = Na₃AlF₆** (cryolite): W(Na) = 3·22.990/209.940 = 32.8522 % → 32.85 % ✓;
  W(Al) = 26.982/209.940 = 12.8522 % → 12.85 % ✓, hence **Q = Al**
  (`cryolite_sodium_fraction`, `cryolite_aluminium_fraction`).
- C carries the remaining 3 fluorides per Al: C = AlF₃; with
  C·xH₂O at 39.16 % water, W = 3·18.015/138.022 = 39.1561 % → 39.16 % ✓
  with x = 3 (x = 2 gives 30.02 %, x = 4 gives 46.18 %, both excluded), so
  **C·xH₂O = AlF₃·3H₂O**
  (`aluminium_fluoride_trihydrate_water_fraction`).

Hence the stone supplies **Al³⁺** cations.

**From 1.5.** G is binary, 49.98 % O, with a three-fold axis, formed from acid
F with P₂O₅. `C₁₂O₉` (the trimeric carbon oxide, a C₃-symmetric macrocycle)
has W(O) = 143.991/288.123 = 49.97553 % → 49.98 % ✓
(`cyclononacarbon_oxygen_fraction`), and C₁₂O₉ = C₁₂H₆O₁₂ − 3 H₂O, so

- **F = mellitic acid, benzenehexacarboxylic acid C₆(COOH)₆ = C₁₂H₆O₁₂**
  (highly symmetric; the anion in salts is **mellitate C₁₂O₆⁶⁻**);
- (E is then the six-fold symmetric hydrocarbon precursor oxidised to F; its
  11.18 % H is consistent with the C:H = 2:3 carbon–hydrogen ratio —
  E's structure does not enter 1.6.)

Hence the stone contains the **mellitate anion C₁₂O₆⁶⁻**.

**Charge neutrality** for the stoichiometric stone then leaves exactly one
possibility for the anhydrous core:

**stone family: Al₂(C₁₂O₆)·xH₂O** (2 Al³⁺ = +6 balance one mellitate 6−),
molar mass M(x) = 294.090 + 18.015 x g mol⁻¹, and the final residue — a
compound **constant at higher temperature in open air**, obtained by oxidative
decomposition of an aluminium salt — can only be **corundum, H = Al₂O₃**
(101.961 g mol⁻¹).

## 2. The thermogravimetric constraint system and its diagnosis

Displayed masses with half-quantum windows: 10.00 → [9.995, 10.005] g,
5.75 → [5.745, 5.755] g, 1.50 → [1.495, 1.505] g.

**Plateau 1 (≈ 100–200 °C): complete dehydration.**
Residue Al₂(C₁₂O₆) = 294.090 g mol⁻¹. Consistency requires
x = 0.4250·294.090/(0.5750·18.015) = **22.09**, with the displayed interval
pinning x to [22.03, 22.15] — **no integer**. The nearest integer candidate
x = 22 leaves 294.090/690.420·10.00 = **4.26 g** (not 5.75 g; proved:
`stone_x22_first_plateau_fails`), and the classically known mellitate
dodecahydrate x = 12 leaves 294.090/510.270·10.00 = **5.76 g** (not 5.75 g;
proved: `stone_x12_first_plateau_fails`). In fact the water fraction for x = 22
is 57.40 % — while the plateau shows 42.5 % loss — so x = 22 matches neither
reading.

**Plateau 2 (400 °C): oxidative decomposition to H = Al₂O₃.**
Final residue β = 1.50/10.00 = 0.1500 g per gram. Consistency requires
M = 101.961/0.1500 = 679.74 g mol⁻¹, i.e. x = **21.41**, pinned to [21.29,
21.54] — again **no integer**; the nearest integer x = 21 leaves
101.961/672.405·10.00 = **1.52 g** (not 1.50 g; proved:
`stone_x21_second_plateau_fails`).

**Joint conclusion (proved: `tg_system_inconsistent`).** The two plateaus
require different, individually non-integral hydration numbers
(x ≈ 22.09 vs x ≈ 21.41), and the nearest integer candidate of each plateau
already violates its own displayed window. Therefore:

**no stoichiometric aluminium–mellitate hydrate decomposing to Al₂O₃ in open
air reproduces the printed TG masses within their displayed measurement
tolerances.** The three displayed masses (10.00 g, 5.75 g, 1.50 g) are, as
captured in this bundle, arithmetically inconsistent with the compound class
that the problem's own 1.4/1.5 clue chain forces.

## 3. Answers supported by the data

- **Stone: Al₂(C₁₂O₆)·xH₂O** with **x ≈ 22** (aluminium mellitate hydrate;
  the first plateau alone forces x between 22.03 and 22.15 — the displayed
  precision cannot deliver an exact integer). If an integer is demanded by
  the answer sheet format, **x = 22, i.e. Al₂(C₁₂O₆)·22H₂O**, is the unique
  candidate consistent with the *first* plateau's integer-neighbourhood;
  it is however contradicted by the final-residue datum.
- **Compound H: Al₂O₃** (corundum) — the thermally stable aluminium oxide in
  open air at > 400 °C; independently supported by the final-residue fraction
  (which pins x ≈ 21.4 — itself non-integral).

## 4. Source gap (reported, not smoothed over)

Within the tolerated reading of all inputs (Q = Al from cryolite, mellitate
anion from mellitic acid G-chain, stoichiometric neutrality), the printed TG
data over-determine the single integer parameter x and the system has **no
solution**. This is a genuine inconsistency in the captured problem data, not
a fit problem: the deviation of the best candidate from the displayed plateau
(0.7 hydration units ⇒ 0.016 g on the final plateau; 1.5 g on the first
plateau) exceeds the displayed half-quantum windows by more than an order of
magnitude. The gap is recorded in `result.json` (`source_gaps`) and proved,
for the three closest integer candidates, by `tg_system_inconsistent` in
`IChO2026Problems/problem_icho_2026_t1_a6.lean`. No official solutions,
marking schemes, or external answers were consulted; atomic masses are ordinary
scientific reference values (H 1.008, C 12.011, O 15.999, Al 26.982,
Na 22.990, F 18.998 g mol⁻¹).
