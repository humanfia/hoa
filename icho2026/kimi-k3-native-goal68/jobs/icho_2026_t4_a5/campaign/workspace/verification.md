Verification record for target `icho_2026_t4_a5`.

## Commands and results

1. Build the shared libraries plus the target file:

   $ lake build IChO2026Problems

   Result: `Build completed successfully (8564 jobs).`
   (Warnings only: pre-existing docstring-style lints in the shared
   `IChO2026Chem`/`IChO2026Problems.lean` infrastructure files, which the
   task instructions forbid me from modifying.)

2. Compile the final file directly with `lake env lean` (the command
   required by the task):

   $ lake env lean IChO2026Problems/problem_icho_2026_t4_a5.lean

   Result: exit code 0, no errors, no warnings (output: `LEAN_OK` echoed by
   the driver command `lake env lean … && echo LEAN_OK`).

3. Axiom inspection of the final theorems, via
   `IChO2026Run/AxiomCheck.lean` (a workspace-local check file containing)

   ```lean
   import IChO2026Problems
   open IChO2026.T4_A5
   #print axioms ncRaw_lower
   #print axioms ncRaw_upper
   #print axioms ncRaw_bounds
   #print axioms ncRaw_spec
   #print axioms submission_valid
   #print axioms logEnergyAfter_eq
   ```

   compiled with

   $ lake env lean IChO2026Run/AxiomCheck.lean

   Output:

   ```
   'IChO2026.T4_A5.ncRaw_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T4_A5.ncRaw_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T4_A5.ncRaw_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T4_A5.ncRaw_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T4_A5.submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T4_A5.logEnergyAfter_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   No custom or unchecked axioms; no `sorry`/`admit`; no `native_decide`
   (so no `Lean.ofReduceBool`); the only axioms are Lean's three standard
   logical axioms.

## Independent semantic check

- The statement determines the average number of collisions per the problem's
  own definition of the logarithmic energy decrement ξ.  `logEnergyAfter_eq`
  is a direct induction on the printed per-collision model, and `ncRaw` is
  defined as the unique solution (`averageCollisions_unique`) of
  `ξWater · n = log (Einitial / Etarget)`, i.e. n_c = ln(E₀/E_target)/ξ.
- Inputs used: E₀ = 2 MeV = 2·10⁶ eV, E_target = 0.012 eV, ξ = 0.948 — all
  printed on the problem page (see T4_page-2.png and theory_problem.pdf,
  source page 38).  The unit relation 1 MeV = 10⁶ eV is a standard
  definition (trusted general law), and is only used to put both printed
  energies into the common unit eV.
- Numerical value cross-checked independently (Python `math.log`):
  ln(2·10⁶/0.012) = 18.9315063677…, n_c = 19.96994…, matching the certified
  bounds 19.96 ≤ ncRaw < 19.98 proved in Lean.  Three-significant-figure
  report: 20.0 collisions (the certified bounds are strictly inside
  [19.95, 20.05)).

## Files

- `IChO2026Problems/problem_icho_2026_t4_a5.lean` — the formalization.
- `IChO2026Problems/All.lean` — umbrella importing the target (this module
  was absent from the workspace; it is referenced by the fixed
  `IChO2026Problems.lean` umbrella and is regenerated here for the
  authorized single target only).
- `IChO2026Run/AxiomCheck.lean` — the `#print axioms` check above.
- `answer.md` — natural-language solution and source grounding.
