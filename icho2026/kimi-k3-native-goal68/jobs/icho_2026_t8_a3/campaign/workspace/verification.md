# Verification — IChO 2026 · T8‑A3 (`icho_2026_t8_a3`)

Target: classification of the geometry of complex **1** (question 8.3).
Final artifact: [`IChO2026Problems/problem_icho_2026_t8_a3.lean`](IChO2026Problems/problem_icho_2026_t8_a3.lean).

## Environment

* Toolchain: `leanprover/lean4:v4.31.0` (`lake --version` →
  `Lake version 5.0.0-src+68218e8 (Lean version 4.31.0)`).
* Local lean libraries `IChO2026Chem`, `IChO2026Problems`, `IChO2026Run`
  build against the pinned, pre‑built `Mathlib` / `Physlib` / `crnt-lean`
  caches listed in `lakefile.toml`.

## Commands and results

### 1. Whole‑project build (authorised target library)

```
lake build IChO2026Problems
```

**Result:** `Build completed successfully (8564 jobs).` Exit status `0`.
Only a pre‑existing style linter note on the generic umbrella file
`IChO2026Problems.lean` (`linter.style.longLine`, a >100‑char comment on the
fixed generic header) is reported; no errors and no `sorry` warnings from the
target file.

### 2. Direct check of the final file (per the goal)

```
lake env lean IChO2026Problems/problem_icho_2026_t8_a3.lean
```

**Result:** no output (no errors, no warnings). Exit status `0`.

### 3. Axiom inspection of the final theorems

A scratch file `/tmp/axcheck.lean` containing

```
import IChO2026Problems.problem_icho_2026_t8_a3
open IChO2026.T8_A3
#print axioms correct_geometry_1_is_trans_dichloro
#print axioms option_vii_isCorrect
#print axioms no_other_option_is_correct
#print axioms valid_geometry_has_trans_chlorides
#print axioms valid_geometry_chlorides_not_cis
#print axioms geometry_1_is_correct
#print axioms geometry_1_chlorides_trans
```

was checked with `lake env lean /tmp/axcheck.lean` (exit status `0`):

```
'IChO2026.T8_A3.correct_geometry_1_is_trans_dichloro' depends on axioms: [propext]
'IChO2026.T8_A3.option_vii_isCorrect' depends on axioms: [propext]
'IChO2026.T8_A3.no_other_option_is_correct' depends on axioms: [propext]
'IChO2026.T8_A3.valid_geometry_has_trans_chlorides' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T8_A3.valid_geometry_chlorides_not_cis' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T8_A3.geometry_1_is_correct' depends on axioms: [propext]
'IChO2026.T8_A3.geometry_1_chlorides_trans' depends on axioms: [propext]
```

Only standard Lean logical axioms appear (`propext`, `Classical.choice`,
`Quot.sound`).  There is **no `sorry`/`admit`** and **no custom/unchecked
axiom**.

## Sanity `decide` checks inside the file

The following facts are proved by `decide` (kernel‑checked):

* `equatorial_card : equatorialSites.card = 4`
* `axial_card : axialSites.card = 2`
* `axial_disjoint_equatorial : Disjoint axialSites equatorialSites`
* `complex1_CN : complex1_coordinationNumber = 6`  (4 N donors + 2 Cl)
* `complex1_two_chlorides : complex1_chlorideCount = 2`

## Semantic faithfulness self‑check

The formal statement models exactly the chemistry asked in 8.3:

* the seven tick options are enumerated in the order printed on answer‑sheet
  A8‑2;
* the problem inputs (four linear N donors from ligand **8**; two chlorides
  from FeCl₂, confirmed by the “− 2 Cl⁻” activation step on Q8‑2) select only
  options with 4 N and 2 Cl;
* the trusted span law for a linear tetradentate polypyridyl forces the four
  N donors into the equatorial plane, which in turn forces the two chlorides
  to be *trans* axial;
* `correct_geometry_1_is_trans_dichloro` proves the unique option satisfying
  all of this is **vii**; `no_other_option_is_correct` proves every other
  option is excluded; `geometry_1_is_correct` fixes the submitted tick.

Faithful to the requested output `geometry_1`: the answer is the
trans‑dichlorido octahedron **[Fe(8)Cl₂]**, answer‑sheet box **(vii)**.
