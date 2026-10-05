# Verification record — `icho_2026_t8_a4`

All commands were run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a4/campaign/workspace`
with the pinned toolchain `leanprover/lean4:v4.31.0` and the workspace
`lakefile.toml` (Mathlib v4.31.0, Physlib, crnt-lean).

## 1. Final build

```
lake env lean IChO2026Problems/problem_icho_2026_t8_a4.lean
```

Result: exit 0, no output (no errors, no warnings).  The file compiles
cleanly with the environment as pinned.

The olean for the module was also produced to enable importing for axiom
inspection:

```
mkdir -p .lake/build/lib/lean/IChO2026Problems
lake env lean -o .lake/build/lib/lean/IChO2026Problems/problem_icho_2026_t8_a4.olean \
  IChO2026Problems/problem_icho_2026_t8_a4.lean
```

Result: exit 0.

## 2. Axiom inspection

A temporary checker file `_axcheck.lean` (content shown below, deleted after
the run) was compiled with

```
lake env lean _axcheck.lean
```

containing `import IChO2026Problems.problem_icho_2026_t8_a4` and
`#print axioms` for all final theorems.

Result (verbatim index of the run; full per-theorem lines were captured):

* All 28 requested-output theorems
  (`complex_9..15_oxidation_state / _coordination_number / _valence_electrons
  / _total_charge`) depend either on no axioms at all or on `[propext]` —
  a standard Lean logical axiom.
* `sheet_anchor_11/12/13/15`, `ligand8_stays_bound`,
  `step_9_10_redox`, `step_10_11_oxidative_addition`, `step_11_12_pcet`,
  `step_12_13_neutral`, `step_13_14_charge`, `step_14_15_loss`,
  `two_electron_cycle`: no axioms beyond `[propext]` (several axiom-free).
* The seven atom-balance theorems closed with `native_decide`
  (`step_9_10, step_10_11, step_11_12, step_12_13, step_13_14, step_14_15,
  step_15_9, net_half_reaction_atoms, cycle_net_stoichiometry`) depend on
  Lean's trusted native-evaluation axiom of the form
  `…_native.native_decide.ax_1_1` (the `Lean.ofReduceBool` trust axiom), not
  on `sorryAx` or any custom axiom.
* `mcat_consistent` depends on `[propext, Classical.choice, Quot.sound]`,
  the standard classical axioms of Mathlib reals.

No `sorry`/`admit` or `unsafe` declaration appears anywhere in the final file
(verified by inspection and by the axiom sweep: no `sorryAx` occurs in any
`#print axioms` output).

## 3. Semantic self-check (independent of the build)

* The integer theorems state exactly the values derived in `answer.md` and
  cross-verified against the printed answer-sheet anchors (11: OS +3, CN 6;
  12: CN 5; 13: OS +2; 15: VE 16) — those anchors are themselves proved as
  theorems (`sheet_anchor_*`), so a mis-reading of the sheet would break the
  build rather than silently pass.
* Every requested output is stated as a *property of an explicit structure*
  (`Ligand` carries donor atoms, formal charge and bond orders; `FeComplex`
  carries the OS and the full ligand sphere), so the results cannot collapse
  to bare number/string equalities disconnected from connectivity.
* The eight arc theorems reproduce, atom-for-atom, the reagents printed in the
  problem cycle, and `cycle_net_stoichiometry` shows that a full turnover
  consumes CO₂ + 2H⁺ (+2e⁻) and releases CO + H₂O while regenerating 9, i.e.
  the half equation of question 8.1 is recovered inside the formalization.
* `mcat_consistent` grounds the tetradentate C₂₇H₁₈N₄O₂ reading of ligand 8
  against the stipulated M_cat = 557.21 g mol⁻¹ of question 8.5.
