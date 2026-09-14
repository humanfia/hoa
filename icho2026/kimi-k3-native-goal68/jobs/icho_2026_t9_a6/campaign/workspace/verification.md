# Verification — IChO 2026 T9-A6 (`icho_2026_t9_a6`)

## Deliverables

- `answer.md` — natural-language answer: **2 constitutional linkage
  isomers** ("in-line" 1–link–1 and "crossed" 1–link–4 β-CD dimers).
- `IChO2026Problems/problem_icho_2026_t9_a6.lean` — Lean 4 formalization
  (Mathlib only; structure `SiteLabelledDimer` = `Fin 7 × Fin 7` attachment
  site pairs; equivalence `SameConstitution` = equal or opposite directed
  separation mod 7; attainability predicate from the Sinay rule;
  representatives `linkSame`, `linkCross`; completeness, distinctness,
  partition and quotient-cardinality theorems).

## Command

    cd <workspace>
    lake env lean IChO2026Problems/problem_icho_2026_t9_a6.lean

(run with `lean-toolchain` = `leanprover/lean4:v4.31.0`; Mathlib
`v4.31.0` — the project's pinned toolchain; invoked repeatedly during
development, final run exit code 0.)

In addition the umbrella target was verified:

    lake build        # Build completed successfully (8581 jobs)

with `IChO2026Problems/All.lean` containing the single line
`import IChO2026Problems.problem_icho_2026_t9_a6` (the aggregation file that
the fixed umbrella `IChO2026Problems.lean` requires; the trusted controller
normally rewrites it — here it simply re-exports this target).  The header
style warnings seen during `lake build` come from the pre-existing generic
files `IChO2026Run/Basic.lean`, `IChO2026Chem/*.lean`, not from the target.

## Result (final run, exit code 0)

Compiler output (only the `#print axioms` diagnostics; no errors, no
warnings):

    'IChO2026T9A6.dimer_isomer_count' depends on axioms: [propext, Quot.sound]
    'IChO2026T9A6.dimer_isomer_count_attainable_classes' depends on axioms:
        [propext, Classical.choice, Quot.sound,
         IChO2026T9A6.dimer_isomer_count_attainable_classes._native.native_decide.ax_1_1]

Notes:

- The main packaging theorem `dimer_isomer_count` (completeness +
  distinctness + realizability of the two isomers) depends only on the
  standard logical axioms `propext` and `Quot.sound` — no `sorryAx`, no
  custom axioms.
- `dimer_isomer_count_attainable_classes` (the image of the 21 attainable
  site-labelled dimers in the constitutional quotient has exactly 2
  classes) uses `native_decide` to enumerate the 49 × 49 finite cases;
  its extra axiom is the `native_decide` reduce axiom (Lean.ofReduceBool),
  behind Mathlib's trusted compiled evaluation.  `Classical.choice` enters
  via the classical `Finset` quotient image.  No unsafe or custom
  assumptions.
- `grep -n "sorry\|admit" IChO2026Problems/problem_icho_2026_t9_a6.lean`
  returns no matches (exit 1).

## Theorem inventory

| Theorem | Statement | Role |
|---|---|---|
| `sameConstitution_equivalence` | `Equivalence SameConstitution` | the isomer relation is a genuine equivalence |
| `representatives_distinct` | `¬ SameConstitution linkSame linkCross` | the two isomers differ |
| `attainable_eq_linkSame_or_linkCross` | every attainable dimer is isomeric to one of the two | completeness |
| `linkSame_attainable`, `linkCross_attainable` | both classes are actually formed | realizability |
| `nonattainable_not_formed` | separations ±1, ±2 are constitutionally different from every attainable dimer | exclusivity |
| `attainable_partition_of_linkSame` | 7 site-labelled dimers in class 0 | orbit size |
| `attainable_partition_of_linkCross` | 14 site-labelled dimers in class ±3 | orbit size |
| `attainable_card` | 21 attainable site-labelled dimers | 7 + 14 consistency |
| `site_labelled_total` | 49 site-labelled dimers | 7 × 7 ensemble |
| `dimer_quot_classes` | 4 classes in the full constitutional quotient | {0}, ±1, ±2, ±3 |
| `dimer_isomer_count` | completeness ∧ distinctness ∧ realizability | **main statement: N = 2** |
| `dimer_isomer_count_attainable_classes` | quotient image of attainable dimers has card 2 | quotient-form answer |

## Semantic-faithfulness check

The formalized model states the chemistry as follows:

- β-CD has 7 units → `Fin 7` indexing (problem preamble).
- Sinay rule: free OH at unit 1 directs next debenzylation to unit 4
  (3 steps further; labels 1…7 step +1) → attainable separation set
  {0, 3, 4} ∈ `Fin 7` (0 = directing↔directing, 3 = directing↔unit 4,
  4 = unit 4↔directing).  The fallback "unit 3 if unit 4 is not
  available" never occurs in a 7-ring whose units are all initially
  benzylated.
- "Constitutional linkage isomers" (problem phrase) → equivalence classes
  under equal-or-opposite separation, which is exactly the orbit relation
  of the constitution-preserving relabellings (C₇ × C₇ re-charts, ring
  exchange, mirror of the 7-cycle).
- The answer 2 is stated both as a packaged predicate
  (`dimer_isomer_count`) and as an explicit quotient cardinality
  (`..._attainable_classes`), and cross-checked by the orbit sizes
  7 + 14 = 21 attainable dimers and the 4-class decomposition
  7 + 14 + 14 + 14 = 49 of all site-labelled dimers.
