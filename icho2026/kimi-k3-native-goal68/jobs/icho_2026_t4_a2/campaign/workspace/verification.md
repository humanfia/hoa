# Verification record — target `icho_2026_t4_a2` (IChO 2026, T4, part 4.2)

All commands were run from the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t4_a2/campaign/workspace`)
with the pinned toolchain `leanprover/lean4:v4.31.0`.

## 1. Source-grounding checks

* Read `TASK.json` (question text, requested outputs `nuclear_a`, `nuclear_b`,
  `nuclear_c`, all of kind `formula` / exact symbolic).
* Viewed the official problem image `icho_2026_source/image/T4_page-1.png`
  (checksum `f3b21152…` per `TASK.json`): it shows sections a) ¹¹B + α,
  b) γ + ²D, c) ⁹Be + α and question 4.2 (3.0 pt).
* Extracted printed page Q4-1 (source page 37) from
  `icho_2026_source/raw/theory_problem.pdf` with PyMuPDF
  (`fitz`): text matches the image verbatim, including
  "a) Reaction of ¹¹B with 𝛼-particles inside the reactor core,
   b) Interaction of 𝛾 rays with ²D nuclei present in the reactor coolant
   water, c) Reaction of ⁹Be with 𝛼-particles produced in an externally
   installed neutron source." and "4.2 Write the nuclear reaction equations
   for (a), (b), and (c). 3.0 pt".
* The blank student answer sheet (page A4-1, index 40) contains exactly the
  free-form slots

      4.2 (3.0 pt)  (a) : ____  (b) : ____  (c) : ____

  with no further constraints (three handwritten equations are expected).

## 2. Compilation

Command:

    lake env lean IChO2026Problems/problem_icho_2026_t4_a2.lean

Result: exit code 0, no errors and no warnings (linter-clean).

## 3. Axiom inspection

Command (temporary copy of the final file with `#print axioms` appended,
compiled identically):

    cp IChO2026Problems/problem_icho_2026_t4_a2.lean /tmp/axcheck_t4/check.lean
    # append the six "#print axioms IChO2026T4.<theorem>" lines
    lake env lean /tmp/axcheck_t4/check.lean

Result (exact output):

    'IChO2026T4.reaction_a_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T4.reaction_b_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T4.reaction_c_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T4.reaction_a_residual_forced' depends on axioms: [propext, Quot.sound]
    'IChO2026T4.reaction_b_residual_forced' depends on axioms: [propext, Quot.sound]
    'IChO2026T4.reaction_c_residual_forced' depends on axioms: [propext, Quot.sound]

Only the standard Lean logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) appear; no custom or unchecked axioms. The file contains no
`sorry`, `admit`, `axiom`, or `unsafe` declarations
(verified by inspection / `grep`).

## 3b. Umbrella library build (non-required sanity check)

Commands:

    lake build IChO2026Chem         # exit 0 (8561 jobs)
    lake build IChO2026Problems     # exit 0 (8564 jobs)

Both libraries build successfully. (`IChO2026Problems/All.lean`, the target
umbrella the fixed infrastructure expects, imports
`IChO2026Problems.problem_icho_2026_t4_a2`.) The inherited fixed file
`IChO2026Problems.lean` emits a pre-existing style linter note (line > 100
chars); it is generic infrastructure and was left untouched.

## 4. Semantic faithfulness check

* `reaction_a/b/c_balanced` state and prove exactly the three displayed
  answers of `answer.md`: conservation of mass number and of atomic number
  for ¹¹B + α → ¹⁴N + n, ²D + γ → ¹H + n, ⁹Be + α → ¹²C + n.
* `reaction_a/b/c_residual_forced` prove that the residual product is
  *forced* to be ¹⁴N / ¹H / ¹²C once the single-neutron output (dictated by
  the problem prose) is fixed — i.e. the equations are not merely consistent
  but uniquely determined by the problem inputs. This rules out the
  alternative (α, p) channel ¹¹B + α → ¹⁴C + p, which would *also* balance:
  it is excluded precisely because the problem states the channel produces
  neutrons.
* Inputs taken from the problem (reactant identities, neutron production) are
  encoded as data (`reactionA/B/C`, target lists in the uniqueness
  hypotheses); derived facts (balance, uniqueness) are proved theorems. No
  premise beyond (A, Z) conservation is assumed.

## 5. Problem inputs not grounded in the statement

None missing: the statement fixes both reactants in all three channels, and
the requirement "a neutron is produced" comes from the surrounding prose of
T4 itself, so no unstated scientific premise is needed to determine the
answers.
