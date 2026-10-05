# Verification record — icho_2026_t1_a2 (IChO 2026 T1-A2)

Run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t1_a2/campaign/workspace`
on 2026-09-14, Lean toolchain `leanprover/lean4:v4.31.0` (see `lean-toolchain`).

## Commands and recorded results

1. Shared molecule/skeleton infrastructure (carbon skeletons, mirror planes, mass
   arithmetic, all `decide`-certified):

   ```
   lake build IChO2026Chem
   ```

   Recorded tail:

   ```
   Build completed successfully (8561 jobs).
   ```

   Exit code 0. (Only benign style-linter notes — copyright-header style — no errors.)

2. Full problem library build:

   ```
   lake build IChO2026Problems
   ```

   Recorded tail:

   ```
   ⚠ [8564/8565] Built IChO2026Problems (28s)
   warning: IChO2026Problems.lean:4:100: This line exceeds the 100 character limit, please shorten it!
   Build completed successfully (8565 jobs).
   ```

   Exit code 0. (The single long-line warning is in the fixed infrastructure umbrella
   `IChO2026Problems.lean`, not in the target file.)

3. Direct elaboration of the final target file (as required by the goal):

   ```
   lake env lean IChO2026Problems/problem_icho_2026_t1_a2.lean
   ```

   Recorded output (stderr; one benign `unnecessarySeqFocus` style linter warning at
   line 152 omitted here in full):

   ```
   'IChO2026Problems.T1A2.Certificates.Z_chloride_ms' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.T1A2.B_structure_is_naphthalene' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.T1A2.answer' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit code 0. All three checked theorems depend only on the **standard Lean logical
   axioms** (`propext`, `Classical.choice`, `Quot.sound`); no custom axioms, no
   `sorry`/`admit`, no unsafe options anywhere in the target file or the shared
   `IChO2026Chem/Molecule.lean` infrastructure (verified by
   `grep -n "sorry\|admit\|axiom"` over both files before each build: only prose mentions).

4. Supporting low-level file compiled identically:

   ```
   lake env lean IChO2026Chem/Molecule.lean
   ```

   Exit code 0 (one harmless style-linter note).

## Toolchain notes

- Toolchain quirk discovered during the run: in this Lean 4.31.0 environment, *any*
  doc comment (`/-- ... -/`) immediately preceding a `#print axioms ...` command produces a
  spurious parse error (`unexpected token '#print'; ...`), reproduced in an isolated scratch
  file with a one-line definition. The `#print axioms` commands in the target file are each
  preceded by a plain line comment instead, which elaborates cleanly and prints the axiom
  lists recorded above.
- The two heavy bond-table certificates (`azuleneReflect_conn`, the ring-exchange
  reflection, and the commutativity of naphthalene's two in-plane reflections) are proved by
  kernel-checked `decide (+kernel)`/finite case analysis on `Fin 10`/`Fin 14`; the skeleton
  symmetry/irreflexivity/positivity of the three bond tables are `decide`-verified.

## Semantic-faithfulness self-check

- `A = azulene`, `B = naphthalene`, `Z = zSkeleton` are concrete `Molecule` values built
  from explicit bond tables (`azuleneBond`, `naphthaleneBond`, `zBond`), not strings or
  assumed equalities; the mirror-plane, formula-comparison and mass identities are *proved*
  theorems over those tables (`Nonempty MirrorPlane`, two commuting perpendicular planes,
  `SameFormula`, `molMassOfFormula … = 218/220`).
- The remaining laboratory predicates of the problem (blue colour, chlorination,
  isomerisation on heating) are stated as schematic relations exactly as the shared context
  asserts them and are discharged only in ways the context licenses (uniqueness of the blue
  chromophore; the full bundle assembled in `theorem answer`).
- The natural-language answer in `answer.md` (Z = compound 7 = 4-ethyl-1,7-dimethylazulene;
  A = azulene; B = naphthalene, with the drawn Kekulé structures) matches the Lean
  definitions atom-for-atom.
