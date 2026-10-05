# Verification — icho_2026_t8_a8

Date: 2026-09-14 (UTC). Toolchain: Lean 4.31.0 (`leanprover/lean4:v4.31.0`),
Mathlib v4.31.0 via the workspace lakefile (dependencies already built).

## Command and result

```
$ lake env lean IChO2026Problems/problem_icho_2026_t8_a8.lean
(exit code 0; no errors, no warnings)
'IChO2026T8A8.assignment_forced' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T8A8.officialSubmission_matches' does not depend on any axioms
```

The `#print axioms` output shows:

* `assignment_forced` uses only the **standard Lean logical axioms**
  (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`, no custom or
  unchecked axioms anywhere.
* `officialSubmission_matches` (the tick table) uses **no axioms at all**.

## What was independently checked for semantic faithfulness

* The theorem `assignment_forced` concludes exactly the mapping requested by
  8.8 — `barOf .N = .a ∧ barOf .R = .b ∧ barOf .G = .c ∧ barOf .B = .d` —
  i.e. a→N, b→R, c→G, d→B, matching the answer-sheet tick table
  (`theory_problem.pdf` p. 82/A8-6).
* All diagram data entering the proof are read directly from the problem
  pages: bar H₂ percentages (0 %* at a, 29 % at b, 10 % at c, 3 % at d,
  *no bar drawn) from `T8_page-4.png` / p. 75; the Gibbs-energy step values
  (−0.04, +0.02, +0.16, −0.36, −0.22, +0.1 for CO; +0.756, +1.832, −0.168,
  −1.14 for H₂) from `T8_page-3.png` / p. 74 (visually re-checked against a
  zoomed render).
* Auxiliary proved facts cross-check the chemistry encoding:
  `co_sequence_overall_ΔG` (ΣΔG of the CO branch = −0.34 eV),
  `h2_branch_photo_charging_step` (the +1.832 eV step is the strict maximum
  of the H₂ branch), `hcEVnm_exact` (h c = 6621486190496429/5340588780000
  eV·nm = 1239.841984… eV·nm from exact h, c, e), and
  `co_requirement_wavelength` (0.14 eV < h c / 1097 nm ≈ 1.1302 eV),
  `photonEnergy_antitone` (E decreases with λ), `led_wavelength_ordering`
  (λ_B < λ_G < λ_R, all > 0).
* The chemical selectivity principle (shorter λ ⇒ less H₂, i.e.
  χ(H₂,B) < χ(H₂,G) < χ(H₂,R)) and the "dark = no products" reading are
  declared as explicit hypotheses of the main theorem and justified in
  answer.md; they are not smuggled in as axioms.

## Note on the build command

`lake build` in this workspace builds the project libraries
(`IChO2026Run`, `IChO2026Chem`, `IChO2026Problems` umbrella); the target
file is verified with the mandated `lake env lean <file>` invocation above,
which is the required gate per the task contract.
