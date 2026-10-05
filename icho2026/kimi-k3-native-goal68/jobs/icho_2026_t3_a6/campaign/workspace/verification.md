# Verification — `icho_2026_t3_a6` (IChO 2026 T3-A6)

## Files under verification

`IChO2026Problems/ProblemIcho2026T3A6.lean` — the deliverable for this target.
`IChO2026Problems/All.lean` — umbrella import (single line
`import IChO2026Problems.ProblemIcho2026T3A6`), needed because the fixed
`IChO2026Problems.lean` imports `IChO2026Problems.All`.

## Commands run (from the workspace root)

1. `lake env lean IChO2026Problems/ProblemIcho2026T3A6.lean`
   - Exit code: **0**.
   - Stdout (`#print axioms` output, verbatim):

     ```
     'IChO2026T3A6.stacking_energy_aa' depends on axioms: [propext, Classical.choice, Quot.sound]
     'IChO2026T3A6.stacking_energy_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
     'IChO2026T3A6.stacking_energy_ab_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
     'IChO2026T3A6.requested_outputs_summary' depends on axioms: [propext, Classical.choice, Quot.sound]
     'IChO2026T3A6.aa_prime_datum_ordering' depends on axioms: [propext, Classical.choice, Quot.sound]
     ```

   - No errors, no warnings, no `sorryAx`. Only the three standard Lean
     logical axioms (`propext`, `Classical.choice`, `Quot.sound`) are used.

2. `lake build` (whole project)
   - Result: `Build completed successfully (8581 jobs).`
   - Only warning: a pre-existing style-linter note about a >100-character line
     in the fixed generic umbrella `IChO2026Problems.lean` (not part of this
     target's deliverables; left untouched).

3. Source-grounding checks (read-only):
   - `theory_problem.pdf` p. 30 text extraction → confirmed the verbatim
     question text and the exact table values −7.9 / −12.6 / −49.8 / −55.6 /
     −6.7 / −16.7 and the given AA′ datum −67.1 kJ mol⁻¹.
   - Answer sheet A3-4 (PDF p. 35) rendered and inspected → confirmed the
     pre-filled `−67.1` under the AA′ column and empty AA / AB / AB′ cells.
   - `T3_page-6.png` figure cropped and inspected: stacking modes (a) AA
     eclipsed, (b) AA′ slightly shifted, (c) AB hole-centred; table column
     geometries examined at high zoom (eclipsed = coincident centroids;
     slipped = centroid-over-arm-gap).

## Semantic-faithfulness audit

* `stacking_energy_aa : E_AA = −85.7` with
  `E_AA = 1·E_tt_ecl + 10·E_bb_ecl` — matches the answer.md derivation
  (1 eclipsed t–t + 10 eclipsed b–b per bilayer repeat unit).
* `stacking_energy_ab : E_AB = −75.6` with `E_AB = 6·E_bb_slp` — 6 slipped
  benzene–benzene contacts.
* `stacking_energy_ab_prime : E_AB' = −333.6` with `E_AB' = 6·E_bt_slp` —
  6 slipped benzene–triazine contacts.
* `requested_outputs_summary` bundles exactly the three requested outputs.
* `centroids_distinct` (`linarith` proof) contains the arithmetic fact that
  the AB and AB′ registries are genuinely different (they cannot coincide
  under any translation: the up- and down-pointing edge-midpoint triangles
  differ), which is why the two requested energies differ.
* `aa_prime_datum_ordering` records the given AA′ datum and its ordering
  relative to AA (−85.7 < −67.1 < 0); it is a consistency check, not an
  ingredient of the answers.
* No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, or external
  constants anywhere in the deliverable file.

## Known limitation (reported honestly)

The Lean file asserts the ring-contact multiplicities (10 b–b eclipsed / 6 b–b
slipped / 6 b–t slipped) as *definitions* distilled from the structure figure
and table; the arithmetic consequences are then fully proved.  A complete
proof of these multiplicities from first principles would require a full
Euclidean model of the honeycomb lattice and of the COF-8 repeat unit, which
exceeds what the problem statement supplies formally; the multiplicities are,
however, read directly off the printed structure and stacking figures, as
documented step-by-step in `answer.md`.
