# Verification record - `icho_2026_t8_a1`

All commands run in the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a1/campaign/workspace`)
on 2026-09-14, toolchain `leanprover/lean4:v4.31.0` (see `lean-toolchain`).

## 1. Source inspection

- `TASK.json` read directly: requested output is a single exact symbolic
  formula ("balanced acidic CO2-to-CO reduction half equation including
  electron count"), 2.0 pt, no units, `official_answer_seen: false`.
- `icho_2026_source/image/T8_page-1.png` viewed: subquestion 8.1 verbatim:
  "**Write** the half equation for the reduction of CO2 to CO in an
  acidic medium. 2.0 pt", with the printed scheme `CO2 --1--> CO` above
  the catalyst arrow, under the heading "T8. Recycling of Carbon
  Dioxide 7%".
- `icho_2026_source/raw/theory_problem.pdf`, source page 72 (index 71),
  text extracted with PyMuPDF (`fitz`): identical question text;
  confirms title, point value, and that no numerical data belongs to
  8.1. The neighboring subquestions (8.2 structures of 3-7, 8.3 geometry
  of 1) and the page's student answer-sheet layout were read and contain
  nothing needed for 8.1.

## 2. Lean build

Command:

    lake env lean IChO2026Problems/problem_icho_2026_t8_a1.lean

Result (final run, after removing an unused-variable linter warning):

    'IChO2026.Problems.T8.A1.half_equation_balanced' depends on axioms: [propext]
    'IChO2026.Problems.T8.A1.coefficients_forced' depends on axioms: [propext, Quot.sound]

Exit code 0, no errors, no warnings, no `sorry`/`admit`. Only the
standard Lean logical axioms `propext` and `Quot.sound` appear; no custom
axioms.

Supporting theorems in the same file (`is_reduction`,
`substrates_as_printed`, `two_electron_reduction`) are proved by `rfl`.

## 3. Semantic faithfulness check (independent of build success)

The theorems are not vacuous:

- `Balanced lhs rhs` unfolds to the four equations
  C: `1 = 1`; O: `2*1 = 1 + 1`; H: `2 = 2*1`; charge: `2 - 2 = 0 - 0`,
  which hold definitionally - so the formal statement really asserts the
  balance of `CO2 + 2 H+ + 2 e- -> CO + H2O`, exactly the equation
  written in `answer.md`.
- `coefficients_forced` is quantified over *arbitrary* coefficient
  functions on both sides that place the species as indicated
  (CO2/e-/H+ left, CO/H2O right, 1 CO2, 1 CO, 2 e-); `omega` derives
  `n(H+) = 2 /\ n(H2O) = 1` purely from the oxygen and hydrogen balance
  hypotheses, so the answer is shown to be the *unique* equation of its
  skeleton, not a cherry-picked one.
- The electron count (2) is grounded twice in `answer.md`: by charge
  balance and, independently, by the +IV -> +II oxidation-state change
  of carbon (used only as a consistency check, not as an unstated
  premise).

## 4. Constraints honored

- No official solution, marking scheme, grading report, historical
  answer, or answer repository consulted (`official_answer_seen` remains
  false).
- No source inputs or generic infrastructure modified; only the new
  files `IChO2026Problems/problem_icho_2026_t8_a1.lean`, `answer.md`,
  `verification.md`, `result.json` were created in the workspace.
- No `sorry`, `admit`, `axiom`, `unsafe`, or unjustified coefficient
  search in the formalization.
