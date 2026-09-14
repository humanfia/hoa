# Verification record — target `icho_2026_t1_a6`

Date: 2026-09-14. Toolchain: leanprover/lean4:v4.31.0 (lakefile requires
mathlib v4.31.0, Physlib, crnt-lean; all pinned).

## Sources inspected

- `TASK.json` (shared official problem context + subquestion 1.6 text).
- `icho_2026_source/image/T1_page-1.png … T1_page-4.png` — official problem
  pages; Q1‑4 contains subquestion **1.6** verbatim; Q1‑3 contains 1.4/1.5
  data and the start of the TG paragraph. Texts match TASK.json exactly.
- `icho_2026_source/raw/theory_problem.pdf` sha256
  af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60 (24.7 MB,
  no text-extraction tool installed in the container; page images used as the
  authoritative readable rendering; T1_page-4.png was additionally verified
  against the TASK.json asset sha256
  a430d0875b35b8bc21e571c8e2fcd931f3db8288fc5cddcb8f62594f241aac46).
  The pages for subquestion 1.6 contain no printed student-answer content
  beyond the subquestion box (page Q1‑4 is otherwise blank).

No official solutions, marking schemes, grading reports, or external answer
repositories were used. Identifications of cryolite / AlF₃·3H₂O / mellitic
acid / C₁₂O₉ were derived from the printed percentages alone (see answer.md).

## Build and verification commands (exact)

```
cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t1_a6/campaign/workspace
lake env lean IChO2026Problems/problem_icho_2026_t1_a6.lean
# -> exit 0, no errors; the eight #print axioms audits print (see below).

lake build IChO2026Problems
# -> Build completed successfully (8564 jobs), including
#    Built IChO2026Problems.problem_icho_2026_t1_a6
#    Built IChO2026Problems.All
#    Built IChO2026Problems
```

## Axiom audit (printed during `lake env lean` / `lake build`)

All eight final theorems depend only on Lean's standard logical axioms:

```
cryolite_sodium_fraction                : [propext, Classical.choice, Quot.sound]
cryolite_aluminium_fraction             : [propext, Classical.choice, Quot.sound]
aluminium_fluoride_trihydrate_water_fraction : [propext, Classical.choice, Quot.sound]
cyclononacarbon_oxygen_fraction         : [propext, Classical.choice, Quot.sound]
stone_x12_first_plateau_fails           : [propext, Classical.choice, Quot.sound]
stone_x22_first_plateau_fails           : [propext, Classical.choice, Quot.sound]
stone_x21_second_plateau_fails          : [propext, Classical.choice, Quot.sound]
tg_system_inconsistent                  : [propext, Classical.choice, Quot.sound]
```

No `sorry` / `admit` anywhere in the file (checked by successful elaboration
— Lean rejects `sorry` silently only with warnings; there is no `sorry`
warning in the build log for this file).  `native_decide` is deliberately
unused, so no `Lean.ofReduceBool` / trusted-compiler axioms appear.

## What is proved (semantic faithfulness check)

- Theorems `cryolite_sodium_fraction`, `cryolite_aluminium_fraction`:
  cryolite Na₃AlF₆ has W(Na) = 32.8522 %, W(Al) = 12.8522 %, both inside the
  displayed half-quantum windows of 32.85 % and 12.85 % — this validates the
  1.4 identification Q = Al, D = Na₃AlF₆ from the printed data.
- Theorem `aluminium_fluoride_trihydrate_water_fraction`: AlF₃·3H₂O has
  W(H₂O) = 39.1561 % inside the 39.16 % window; x = 2 and x = 4 hydrates are
  excluded — validates C·xH₂O = AlF₃·3H₂O.
- Theorem `cyclononacarbon_oxygen_fraction`: C₁₂O₉ has W(O) = 49.97553 %
  inside the 49.98 % window — validates G = C₁₂O₉ and hence F = mellitic acid,
  anion mellitate C₁₂O₆⁶⁻.
- Theorems `stone_x12_first_plateau_fails`, `stone_x22_first_plateau_fails`,
  `stone_x21_second_plateau_fails`: with the neutral anhydrous core
  Al₂(C₁₂O₆) (294.090 g mol⁻¹) forced by charge neutrality, the closest
  integer hydrates fail the displayed TG windows (4.26 g vs 5.75 g for x = 22;
  5.76 g vs 5.75 g for x = 12; 1.52 g vs 1.50 g for x = 21 with H = Al₂O₃).
- Theorem `tg_system_inconsistent`: the conjunction — the printed TG data
  admit no stoichiometric aluminium–mellitate hydrate within tolerance.

The Lean theorems state and prove exactly the claimed chemistry: the mass
balances of the identified compounds and the failure of every nearest integer
hydrate against the displayed measurement windows.  The numeric content was
cross-checked independently in Python (rational arithmetic) before encoding.

## Note on the deliverable's nature

Because the forced candidate class has no element reproducing all displayed
data, the deliverable formalizes (a) the fully proved prerequisite
identifications and (b) the formal inconsistency of the TG data as the
faithful answer; the natural-language `answer.md` gives the forced partial
answers (stone Al₂(C₁₂O₆)·xH₂O, x ≈ 22; H = Al₂O₃) together with an explicit
source-gap report.  This follows the task rule: "if the problem does not
ground a necessary condition, explicitly report the gap instead of claiming
unconditional success."
