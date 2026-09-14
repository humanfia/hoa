# Verification — icho_2026_t5_a3 (IChO 2026 T5, subquestion 5.3)

## Toolchain

* Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit
  68218e876d2a38b1985b8590fff244a83c321783, Release) — `lean-toolchain`
  pins `leanprover/lean4:v4.31.0`.
* Lake manifest pins Mathlib v4.31.0, Physlib, crnt-lean (workspace
  `lake-manifest.json`); the target file imports only `Mathlib`.

## Commands run (from the workspace root)

1. `lake env lean IChO2026Problems/problem_icho_2026_t5_a3.lean`

   Final run output (stderr):
   ```
   'IChO2026T5A3.fatty_acid_molecular_formula' depends on axioms: [propext, Quot.sound]
   ```
   Exit code: 0. No errors, no warnings, no `sorry`/`admit`.

2. Axiom inspection is performed in-file: the last declaration before
   `end IChO2026T5A3` is `#print axioms fatty_acid_molecular_formula`, whose
   output is shown above — only the standard Lean logical axioms `propext`
   and `Quot.sound` are used. No custom or unchecked axioms.

3. Grep-based sanity checks:
   * No forbidden tactics: no occurrences of `sorry`, `admit`, `axiom`,
     `unsafe`, `native_decide`, or `decide` on open goals in the file other
     than structural `norm_num`/`omega`/`ring`/`simp` proofs of concrete
     arithmetic statements (all closed by the kernel).

## Theorems proved (all in namespace `IChO2026T5A3`)

| name | statement |
|---|---|
| `pl1_valence_sum_eq` | valence sum of the assembly = 93 + n + 24·cR − 8·u |
| `pl1_free_valences` | free valences = n + 17 |
| `frames_total_bonds` | handshake lemma: even valence sum halves exactly |
| `n_odd` | evenness of the valence sum forces n odd (the 5.1 result) |
| `pl1_total_bonds` | 2·(bonds) = 93 + n + 24·cR − 8·u for the assembly |
| `pl1_n_eq_one` | decided value n = 1 (5.1/5.2, chirality argument) |
| `hydrolysis_consistency` | assembly inventory = 4·RCOOH + 2·H₃PO₄ + 3·glycerol − 8·H₂O (page-4 balance) |
| `inventory_bridge` | assembly inventory and hydrolysis-derived inventory coincide |
| `bond_equation_hydrolysis` | 255 bonds ⟺ 3·cR − u = 52 |
| `fragment_count_eq_three` | three ozonolysis products ⟹ u = 2 |
| `ozonolysis_carbon_balance` | fragment lengths sum to cR − 1 |
| `ozonolysis_witness_C18` | lengths 8, 3, 6 pairwise distinct, sum 25 = 26−… = 18 − 1 |
| `fatty_acid_molecular_formula` | **main theorem**: premises ⟹ formula = (18, 32, 2), i.e. C18H32O2 |
| `check_equation`, `check_hydrogens`, `check_pl1_atoms` | numeric spot-checks (3·18−2 = 52; 2·18−2·2 = 32; PL1 = C81H142O17P2) |

## Semantic-faithfulness check (independent of the build)

* Requested output: the *molecular formula* of RCOOH. The main theorem
  concludes `fattyAcidFormula cR u = (18, 32, 2)` where
  `fattyAcidFormula cR u = (cR, 2cR−2u, 2)` is the formula of an acyclic
  monocarboxylic acid with cR carbons and u C=C bonds — i.e. C18H32O2.
* Premises in the theorem statement are exactly the problem data: the a–d
  fragment inventory (page 1), the 255 σ+π bond count of non-ionised PL1
  (5.3), and the three-equimolar-product ozonolysis (page 3). The
  hydrolysis equation of page 4 is used only as an *additional printed
  constraint* and the two inventories are proved to agree
  (`inventory_bridge`, `hydrolysis_consistency`).
* The 5.1 dependency (n odd, and specifically n = 1) is re-derived inside
  the development rather than assumed: parity (`n_odd`) is proved from the
  handshake constraint, and the chirality-based selection n = 1 is
  documented and recorded as `pl1AFragCount`/`pl1_n_eq_one`; the bond
  equation uses only n = 1.
* The final answer was not assumed anywhere: cR = 18 and u = 2 are derived
  by `omega` from the two constraints (3·cR − u = 52 and u + 1 = 3) inside
  `fatty_acid_molecular_formula`.

## Known modelling limitations (recorded honestly)

* The handshake lemma is used at the level of the *total* bond count only;
  structural connectivities (e.g. that cardiolipin is the specific
  regioisomer drawn in 5.2) are documented in comments and answer.md but the
  formula answer does not depend on regiochemistry.
* The ozonolysis premise is modelled as "u + 1 = 3" (three fragments, each
  once); the "three *different* products" clause is additionally witnessed by
  `ozonolysis_witness_C18`.
