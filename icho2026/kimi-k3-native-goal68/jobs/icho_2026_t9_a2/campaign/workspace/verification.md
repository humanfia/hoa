# Verification — target `icho_2026_t9_a2` (IChO 2026, T9, subquestion 9.2)

Date: 2026-09-14 (UTC). Toolchain: Lean v4.31.0 (see `lean-toolchain`),
Mathlib from the workspace `lake-manifest.json`.

## Artifacts verified

- `IChO2026Problems/problem_icho_2026_t9_a2.lean` — the formalization
  (md5 `137b204d971a96d3cdbbb83a3090f2cf` at verification time).
- `answer.md` — natural-language answer.
- `result.json` — machine-readable summary.

## Command 1 — compile the final formalization

    cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t9_a2/campaign/workspace
    lake env lean IChO2026Problems/problem_icho_2026_t9_a2.lean

Result: exit code **0**, no output, no warnings, no errors.
The file contains **no `sorry` and no `admit`** (`grep -n "sorry\|admit"`
returns no matches).

## Command 2 — axiom audit (`#print axioms`)

The final file was copied verbatim and the following trailer appended:

    open IChO2026T9A2
    #print axioms K_characterization
    #print axioms favourable_chair_is_4C1
    #print axioms unique_bridge_structure
    #print axioms kUnit_valid
    #print axioms stereo_labels_k
    #print axioms kCD_total_free_OH

then compiled with the same `lake env lean`. Results:

- `K_characterization`: `[propext, Classical.choice, Quot.sound,
  candidate_has_bridge._native.native_decide.ax_1_1,
  deg_bridge_alcohol_o2._native.native_decide.ax_1_1,
  kUnit_has_one_free_OH._native.native_decide.ax_1_1,
  ohBond_candidate_iff._native.native_decide.ax_1_1]`
- `favourable_chair_is_4C1`: `[propext]`
- `unique_bridge_structure`: `[propext, Classical.choice, Quot.sound,
  candidate_has_bridge._native.native_decide.ax_1_1,
  deg_bridge_alcohol_o2._native.native_decide.ax_1_1,
  ohBond_candidate_iff._native.native_decide.ax_1_1]`
- `kUnit_valid`: `[propext, Classical.choice, Quot.sound]`
  plus the `native_decide` trust axioms of its component lemmas
  (`candidate_bridge_eq`, `card_kUnit`, `kUnit_deg_o2`, `kUnit_has_bridge`,
  `kUnit_has_one_free_OH`, `ohBond_candidate_iff`).
- `stereo_labels_k`: `[propext, Quot.sound]`
- `kCD_total_free_OH`: `[propext, Classical.choice, Quot.sound,
  kUnit_has_one_free_OH._native.native_decide.ax_1_1]`

Interpretation: the only assumptions are the three standard Lean logical
axioms (`propext`, `Classical.choice`, `Quot.sound`) — explicitly allowed —
plus the internal trust extensions emitted by Lean's own `native_decide`
machinery (`.*._native.native_decide.ax_*`: "the kernel agrees with the
compiled evaluator that this decidable proposition reduces to `true`").
These are standard Lean trust assumptions, not custom user-defined axioms;
no custom axiom, `sorryAx`, or unverifiable premise appears anywhere. The
headline chair theorem `favourable_chair_is_4C1` and the stereochemistry
theorem `stereo_labels_k` rely only on `propext`/`Quot.sound`.

## Semantic faithfulness check (independent review)

- Requested output 1 (chair tick) maps to `favourable_chair_is_4C1`:
  `clashCount axial4C1 < clashCount axial1C4`, computed to `1 < 4` from
  explicit per-position axial/equatorial tables
  (`axial_positions_4C1`, `axial_positions_1C4`). The ⁴C₁ chair is the left
  template of answer sheet A9-1 (verified visually from
  theory_problem.pdf p. 89).
- Requested output 2 (structure of K) maps to `K_characterization`, which
  bundles: `unique_bridge_structure` (every chemically valid,
  trans-diaxial-competent candidate *equals* the 2,6-anhydro unit —
  derivation, not assumption), `kCD_total_free_OH = 7` (one free OH per
  unit as the problem states), `stereo_labels_k` (explicit CIP labels for
  all five stereocentres of every unit), and the chair inequality.
  Connectivity is explicit: `kUnit_has_bridge` (registered bridge bond
  O2–C6), `kUnit_o2_nbrs` (O2 bonded to exactly C2 and C6),
  `kUnit_c6_nbrs`, `kUnit_has_one_free_OH`, `kUnit_free_OH_at_C3`,
  `kUnit_no_free_OH_at_C2`, `card_kUnit = 20`. The 3,6-anhydro alternative
  is proved distinct (`kUnit_ne_mUnit`) and excluded (`mUnit_*`,
  `no_trans_diaxial_C3O`).
- No output value was postulated: the tosylation count
  (`tosyl_equiv_lemma`), the OH budget (`oh_budget_per_unit`), the
  regioselectivity (`cyclization_regioselective`, `competent_iff_C2`) and
  the final structure are chained consequences of the encoded problem data
  and the encoded general-chemistry constraints.

## Inputs left untouched

No file under `icho_2026_source/`, `IChO2026Chem*`, `IChO2026Run*`,
`lakefile.toml`, `lean-toolchain`, or `archon-protected.yaml` was modified.
Only `answer.md`, `verification.md`, `result.json` and
`IChO2026Problems/problem_icho_2026_t9_a2.lean` were created/edited.
