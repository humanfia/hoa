# Verification — icho_2026_t6_a2 (T6 question 6.2)

## Deliverables

- `answer.md` — natural-language answer with source grounding and derivation.
- `IChO2026Problems/problem_icho_2026_t6_a2.lean` — Lean 4 formalization.
- `IChO2026Problems/All.lean` — umbrella module importing the problem file (required by the fixed umbrella `IChO2026Problems.lean`).
- `result.json` — machine-readable summary.

## Commands executed (exact)

1. Build the target file directly:

       lake env lean IChO2026Problems/problem_icho_2026_t6_a2.lean

   Result: exited 0, **no errors, no warnings** on the file.

2. Build through the lake library graph (creates the olean and proves the
   umbrella import chain `IChO2026Problems.lean → IChO2026Problems.All → problem file`):

       lake build IChO2026Problems

   Result: `Build completed successfully (8564 jobs).`  (Only a pre-existing unrelated
   style-linter note about a long line in the shared infra; nothing from this target.)

3. Axiom inspection — a scratch file `Axcheck_tmp.lean` (deleted after use) containing
   `import IChO2026Problems.problem_icho_2026_t6_a2` and `#print axioms` for each final
   theorem was checked with `lake env lean Axcheck_tmp.lean`.  Output (verbatim):

       'IChO2026T6A2.matchesGivenA' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.clCount_B' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.clCount_C' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.clCount_D' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.radTotal_B' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.radTotal_D' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.skeletonIntact_B' depends on axioms: [propext]
       'IChO2026T6A2.opened_C_broken' depends on axioms: [propext, Quot.sound]
       'IChO2026T6A2.opened_C_intact_elsewhere' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.step_A_B' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.step_B_C' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.step_A_D' depends on axioms: [propext, Classical.choice, Quot.sound]
       'IChO2026T6A2.carbon_conserved' depends on axioms: [propext, Classical.choice, Quot.sound]

   Only the three standard Lean logical axioms appear; **no custom/unchecked axioms**
   and **no `sorry`/`admit`** (grep of the file for `sorry`/`admit`/`axiom` returns none in proof positions).

## Theorem inventory (the required outputs and supporting facts)

- `clCount_SM : ClCount molSM = 10`  — starting material is C₁₄Cl₁₀ (as drawn).
- `clCount_A : ClCount molA = 8`     — A is C₁₄Cl₈ (−2 Cl• from SM).
- `clCount_B : ClCount molB = 3`     — **B is C₁₄Cl₃** (matches −5 Cl• 8→3).
- `clCount_C : ClCount molC = 1`     — **C is C₁₄Cl₁** (matches −2 Cl• 3→1).
- `clCount_D : ClCount molD = 5`     — **D is C₁₄Cl₅** (matches −3 Cl• 8→5).
- `radTotal_A = 2`, `radTotal_B = 2` (diradical retained), `radTotal_C = 2` (radicals migrate to jb/jrB), `radTotal_D = 3` (triradical).
- `skeletonIntact_A/B/D` — all 16 skeleton bonds intact in A, B, D.
- `opened_C_broken`, `opened_C_intact_elsewhere`, `opened_C_count` — C is exactly the retro-Bergman opening of the central ring between the 1,4-diradical junctions: only bonds `jb–cl`, `cl–jrB` broken (multiplicity 0), every other skeleton bond at the alkyne/enyne multiplicity created by the rearrangement (recorded as mult 3 within the intact set — see file docstring).
- `matchesGivenA : DrawingA molA` — 18 clauses binding encoded A to the problem figure (8 chlorines, 6 chlorine-free sites, radical dots at cu & cl only, intact skeleton).
- Arrow stoichiometry: `step_SM_A (10 → 8)`, `step_A_B (8 → 3)`, `step_B_C (3 → 1)`, `step_A_D (8 → 5)`, `chain_total : 10−2−5−2−1 = 0`.
- `carbon_conserved : Fintype.card Skel = 14` — no carbon enters or leaves anywhere in the scheme.

## Semantic self-check (evidence the theorems state the requested chemistry)

- Formulas B=C₁₄Cl₃, C=C₁₄Cl₁, D=C₁₄Cl₅ are forced by the printed arrow labels on
  Q6-1 (SM C₁₄Cl₁₀; arrows −2, −5, −2, −1 to C₁₄, and −3 for A→D). The Lean
  `clCount_*`/`step_*` theorems verify exactly this arithmetic.
- B keeps A's diradical (the example A is drawn with two dots), D gains a third
  unpaired electron (note in 6.2: "may contain one or more unpaired electrons"),
  C is the retro-Bergman-opened intermediate — the only ring-opening mechanism
  shown on the page (scheme (1)) — matching the qualitatively different AFM frame.
- The 18-clause `DrawingA molA` proof binds the encoded molecule to the printed A
  (chlorine positions, radical positions, intact skeleton), satisfying the
  "bind every atom/bond/radical to the figures" requirement.

## Known limitation (recorded, not hidden)

The AFM images are grey-scale and do not uniquely single out *which* three of
the eight peripheral chlorines persist in B (respectively which arc is
dechlorinated in D). The chosen assignment (B: Cl on {lt, lbl, rl}; D: radicals
on cu, cl, rt) is the minimal-changes, mechanism-consistent reading. Everything
determined solely by the problem data — formulas, radical counts, intact-vs-opened
skeleton, and *which* bond pair opens in the retro-Bergman step — is fixed and proved.
