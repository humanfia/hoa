# Verification record — icho_2026_t4_a4

## Environment

- Lean toolchain: `leanprover/lean4:v4.31.0` (pinned in `lean-toolchain`)
- Project: `icho_2026_run` with pinned Mathlib v4.31.0, Physlib, crnt-lean
- Working directory: the campaign workspace root

## Commands and results

### 1. Build shared chemistry infrastructure (dependency of the target file)

    lake build IChO2026Chem

Result: `Build completed successfully (8561 jobs).` — only pre-existing style
linter warnings about the file header in the untouched infrastructure files.

### 2. Compile the final problem file

    lake env lean IChO2026Problems/problem_icho_2026_t4_a4.lean

Result: exit code 0, no errors, no warnings. The only output is the axiom
audit line (see below).

### 3. Axiom audit of the final theorem

The last line of the problem file is

    #print axioms IChO2026.T4.A4.t4_a4_answer

and the observed output of the command in step 2 is:

    'IChO2026.T4.A4.t4_a4_answer' depends on axioms: [propext, Classical.choice, Quot.sound]

These are exactly the standard Lean logical axioms. There is no `sorryAx`
(so no `sorry`/`admit` anywhere in the dependency chain) and no custom
axiom. The file also contains no `unsafe` code and no `axiom` declarations.

## Independent semantic check

Beyond the successful build, the theorem's content was checked against the
printed problem:

- `fissionEnergy` is defined as
  `(233 : ℝ) * 8.45 - (235 : ℝ) * 7.59`, i.e. (bound product nucleons) ×
  BE(fis.) − (²³⁵U nucleons) × BE(²³⁵U), with the free neutrons contributing
  nothing, exactly as the question prescribes.
- The stoichiometry theorems `mass_balance` (93 + 140 + 3 = 236) and
  `charge_balance` (37 + 55 = 92) prove that the 4.3 equation used for "this
  reaction" is balanced.
- `fissionEnergy_value` proves the raw value is exactly 185.2 MeV;
  `submission_valid` proves the displayed answer 185 MeV satisfies the
  project-wide `ReportsAtQuantum` contract at quantum 1 MeV (three significant
  figures), with no intermediate rounding anywhere in the file.
- `fission_releases_energy` proves ΔE > 0, matching the problem's statement
  that fission releases energy.

## Numeric cross-check (outside Lean)

    235 × 7.59 = 1783.65 ; 233 × 8.45 = 1968.85 ; 1968.85 − 1783.65 = 185.2

Three-significant-figure display: 185 MeV. Consistent with the problem's own
4.9 fallback instruction (ΔE = 200 MeV) being only a rough substitute.
