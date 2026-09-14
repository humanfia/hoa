# Verification record — IChO 2026 T6-A5 (icho_2026_t6_a5)

Target: IChO 2026 Theory problem T6, subquestion 6.5 — "Draw the structures of F–L."

## Environment

- Workspace: `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t6_a5/campaign/workspace`
- Lean toolchain (`lean-toolchain`): `leanprover/lean4:v4.31.0`
- `lake env lean --version` output:
  `Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)`
- Dependencies present with prebuilt caches (`.lake/packages`): Mathlib v4.31.0
  (5.8 GB of `.olean` under `.lake/packages/mathlib/.lake/build/lib/lean`), Physlib,
  crnt-lean, per `lakefile.toml`. Imports of the final file: `import Mathlib` only.

## Commands run

1. Environment probe

       lake env lean --version                      # OK (see above)
       printf 'import Mathlib\n#check (1 : ℚ)\n' > /tmp/probe.lean
       lake env lean /tmp/probe.lean                # prints "1 : ℚ"  (exit 0)

2. Final-file compilation with axiom audit, from the workspace root:

       lake env lean IChO2026Problems/problem_icho_2026_t6_a5.lean

   Result (final run): exit code 0; no errors and no warnings; only the
   `#print axioms` audit lines are emitted.

## Axiom audit (#print axioms), final run output

    'IChO2026T6A5.answer_icho_2026_t6_a5' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.structure_f' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.structure_g' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.structure_h' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.structure_i' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.structure_j' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.structure_k' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.structure_l' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_F' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_G' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_H' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_I' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_J' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_K' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_L' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.derivation_cpp' depends on axioms: [propext, Quot.sound]
    'IChO2026T6A5.cpp5_formula_and_aromaticity' depends on axioms: [propext, Quot.sound]

Every final theorem depends only on the standard Lean logical axioms
`propext` and `Quot.sound` (both permitted). No `Classical.choice`, no custom
axioms, and — crucially — no `sorryAx` anywhere. The file contains no
`sorry`/`admit`/`axiom` declarations.

Note on intermediate runs: two earlier compilations flagged a `sorryAx` on
`structure_l`/`answer_icho_2026_t6_a5`; that was Lean's placeholder for a
failing `Decidable` instance on `List.Mem` membership statements, which was
replaced by the always-decidable `List.contains ... = true` form. The final
run above is clean.

## What the theorems check (semantic-fidelity self-audit)

- `startingMaterial_formula`, `reagentBiphenylLi_formula`,
  `reagentBromophenylLi_formula`: formulas of the *drawn problem inputs*
  (C₁₂H₉BrO₂; C₁₈H₂₃LiOSi; C₆H₄BrLi), so the graphs encode the printed starting
  material and reagents, not our own constructions.
- `structure_f` … `structure_l`: for each requested output, the theorems state
  (i) the full element-count function (proved equal to the derived formula of
  each structure), (ii) the integer molecular mass (integer masses per 6.4's
  instruction), (iii) the Hückel aromatic-ring count and antiaromatic-ring
  count computed from the explicit sp³/sp² encoding, (iv) the number of
  inter-ring biaryl links, (v) the substituent inventory (counts of OH / OTBS /
  OTES / Br / carbonyl substituents), and, for F and L, the explicit double-bond
  and biaryl-link lists. Nothing is a string match: all atom/bond data lives in
  the `Molecule` graphs and every property is computed from them.
- `structure_h` proves H has exactly the problem-printed formula
  C₃₆H₄₇BrO₃Si₂; `structure_l` proves L has exactly the problem-printed formula
  C₅₄H₈₀O₄Si₄ and that the Yamamoto-created W3–P3 macrocyclizing bond is
  present in L's explicit link list.
- `cpp5_formula_and_aromaticity`: the drawn boxed product is C₃₀H₂₀ with
  exactly 5 aromatic 6π ring systems and 5 biaryl links, 0 antiaromatic systems.
- `derivation_F … derivation_L, derivation_cpp`: eight stoichiometric
  identities, each `∀ e : Element, (next structure).count e = …` in terms of
  the previous structure plus named reagent/atom balances — the
  machine-checked version of "derived from problem constraints", closing the
  chain SM → F → G → H → I → J → K → L → [5]CPP.
- `huckel_6pi_aromatic`, `huckel_4pi_is_4n`, `huckel_4pi_not_aromatic`:
  the only external chemical facts invoked ("trusted general law"), proved
  arithmetically.

## Independent formula re-check (hand arithmetic, matches Lean `decide`)

- F: SM(C₁₂H₉BrO₂) + reagent(C₁₈H₂₃LiOSi) + H − Li = C₃₀H₃₃BrO₃Si ✓ (M = 549)
- G: F + 2(C₆H₁₄Si) = C₄₂H₆₁BrO₃Si₃ ✓ (M = 777)
- H: G − C₆H₁₄Si = C₃₆H₄₇BrO₃Si₂ ✓  = printed formula ✓ (M = 663)
- I: H + O = C₃₆H₄₇BrO₄Si₂ ✓ (M = 679)
- J: I + C₆H₄BrLi + H − Li = C₄₂H₅₂Br₂O₄Si₂ ✓ (M = 836)
- K: J + 2(C₆H₁₄Si) = C₅₄H₈₀Br₂O₄Si₄ ✓ (M = 1064)
- L: K − 2Br = C₅₄H₈₀O₄Si₄ ✓ = printed formula ✓ (M = 904)
- [5]CPP: L − 4(C₆H₁₄Si) − (O₄H₄) = C₃₀H₂₀ ✓ (M = 380), the drawn boxed product.

## Source inputs used (read-only; nothing modified)

- `icho_2026_source/image/T6_page-3.png` (sha256 7ae1859c…34e5 per
  `isolation_manifest.json`) — the full F→L scheme; zoomed crops were
  inspected for the starting quinol, the biphenyl-lithium reagent, the
  4-bromophenyllithium reagent, and the boxed [5]CPP.
- `icho_2026_source/image/T6_page-2.png` — context (6.3/6.4, macrocycle E).
- `icho_2026_source/raw/theory_problem.pdf` — same pages in the original PDF.
- `TASK.json` — subquestion metadata, requested outputs, policies.

No official solutions, marking schemes, grading reports, historical
experiment answers/proofs, answer repositories, Humanize/Archon, or external
solver agents were used. The stereochemical legs NaH/PhI(OAc)₂/Yamamoto are
invoked only as ordinary general chemistry (allowed "trusted_general_law").

## Files produced

- `answer.md` — complete natural-language answer + source grounding.
- `IChO2026Problems/problem_icho_2026_t6_a5.lean` — the formalization.
- `verification.md` — this file.
- `result.json` — machine-readable summary.
