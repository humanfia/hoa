# Verification record — icho_2026_t3_a1 (IChO 2026 T3, part 3.1)

## Scope of verification

Deliverable file: `IChO2026Problems/problem_icho_2026_t3_a1.lean`
(self-contained, imports only `Mathlib`).

Requested outputs being verified:

1. Empirical formula of COF-1 — expressed as the per-hexagon atom balance
   C₅₄H₂₄B₆O₁₂ and its division by gcd(54, 24, 6, 12) = 6 to the integer
   ratio 9 : 4 : 1 : 2, i.e. the empirical formula **C₉H₄BO₂**.
2. Carbon mass percentage to two decimal places — expressed as the exact
   rational value 900750/12911 ≈ 69.76609 % (printed-table masses) together
   with a machine-checked proof that it lies in the round-half-away-from-zero
   capture interval [69.765, 69.775) of **69.77** at quantum 0.01.

## Exact commands and results

1. Compilation (type checking, elaboration, kernel checking):

   ```
   $ cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t3_a1/campaign/workspace
   $ lake env lean IChO2026Problems/problem_icho_2026_t3_a1.lean
   ```

   Result: exit code 0, no output (no errors, no warnings, no sorries).

2. Axiom inspection. A copy of the file with the appended commands

   ```
   #print axioms IChO2026T3A1.answer_icho_2026_t3_a1
   #print axioms IChO2026T3A1.carbon_percent_reports_to_6977
   #print axioms IChO2026T3A1.empirical_counts
   #print axioms IChO2026T3A1.hexagon_composition
   #print axioms IChO2026T3A1.gcd_is_six
   #print axioms IChO2026T3A1.molar_mass_empirical_unit
   #print axioms IChO2026T3A1.carbon_mass_empirical_unit
   #print axioms IChO2026T3A1.carbon_percent_value
   #print axioms IChO2026T3A1.carbon_percent_rounding_window
   #print axioms IChO2026T3A1.carbon_percent_nonneg
   #print axioms IChO2026T3A1.carbon_percent_four_figure_masses
   ```

   was compiled with `lake env lean --root=. <copy>`. Every theorem reports
   dependence only on the standard Lean logical axioms
   `[propext, Classical.choice, Quot.sound]`. No custom or unchecked axioms.

3. Short-cut scan:

   ```
   $ grep -n "sorry\|admit\|axiom \|unsafe" IChO2026Problems/problem_icho_2026_t3_a1.lean
   ```

   Result: no matches (exit 1).

## Semantic-faithfulness audit (beyond a successful build)

* **Structural inputs are problem-grounded.** The atom counts 18/12/6 for B3
  and 6/8/2/4 for A2 are read directly from the printed molecular structures
  on Q3-1 (theory_problem.pdf p. 25; `T3_page-1.png`): triphenylene core with
  three catechol pairs (six –OH), and para-phenylene with one –B(OH)₂ at each
  end. The −H₂O condensation arrow and the six-membered B–O–B–O–C–C
  boronate-ester rings drawn in the network ground the dehydration count of
  12 H₂O per hexagon.
* **Honeycomb multiplicities** (2 vertices, 3 edges per hexagon) follow from
  the 3-share/2-share counting of the printed honeycomb topology; the Lean
  statements accumulate exactly these multiplicities.
* **Empirical formula theorem** (`answer_icho_2026_t3_a1`) asserts: raw
  counts (54, 24, 6, 12), `gcd(...) = 6`, the molar-mass identity
  9·12.01 + 4·1.008 + 10.81 + 2·16.00 = 154.932, and the rounding window
  [69.765, 69.775) for the carbon percentage computed from the very same
  per-hexagon counts — so the theorem *states and proves the requested
  chemistry*, not merely an unrelated numeric inequality.
* **Atomic masses.** 12.01, 1.008, 10.81, 16.00 are the values printed on the
  paper's own periodic table (G1-5, p. 5). A separate theorem
  (`carbon_percent_four_figure_masses`) documents that standard four-figure
  masses (12.011, 15.999) yield 69.7687 %, inside the same 69.77 window; the
  reported digit is therefore convention-independent.
* **Requested precision.** The problem explicitly requests two decimal
  places; the file proves membership in the exact half-open interval
  corresponding to 69.77 at the 0.01 quantum. No intermediate rounding was
  used anywhere in the derivation (all quantities are exact reals).

## Environment notes

`lake env lean` resolves the pinned Mathlib v4.31.0 dependency tree built
into the shared `.lake` packages directory; the deliverable itself needs only
`import Mathlib`. The project umbrella `IChO2026Problems.lean` imports a
non-present generated `All.lean`, so the target file is checked directly with
`lake env lean` as required by the task contract; no source inputs or generic
infrastructure were modified.
