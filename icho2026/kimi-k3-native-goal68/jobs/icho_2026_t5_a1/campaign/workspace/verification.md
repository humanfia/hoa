# Verification — `icho_2026_t5_a1` (IChO 2026, T5.1, cardiolipin fragment parity)

All commands were run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t5_a1/campaign/workspace`
with the pinned toolchain `leanprover/lean4:v4.31.0`.

## 1. Direct elaboration of the target file

```
$ lake env lean IChO2026Problems/problem_icho_2026_t5_a1.lean
(no output; exit code 0)
```

The file elaborates with no errors and no warnings from `lake env lean`
(the style-linter doc-string notes below appear only under the stricter
`lake build` mathlib-style lint set; they are warnings, not errors, and no
`sorry`/`admit`/custom axiom is used anywhere in the file — verified by
`grep -n "sorry\|admit\|axiom" IChO2026Problems/problem_icho_2026_t5_a1.lean`
returning no matches).

## 2. Full library build (umbrella `IChO2026Problems` importing the target)

```
$ lake build IChO2026Problems
... style-linter warnings only (linter.style.docString / linter.style.longLine) ...
Build completed successfully (8564 jobs).
```

## 3. Axiom inspection (via a scratch file in the source tree, removed after use)

Scratch file contents (imports the target module and prints axioms of every
final theorem):

```lean
import IChO2026Problems.problem_icho_2026_t5_a1
open IChO2026T5A1
#print axioms t5_a1_answer
#print axioms answer_b_n_is_odd
#print axioms answer_a_n_even_impossible
#print axioms answer_c_parity_not_free
#print axioms n_mod_two_eq_one
#print axioms n_eq_nine
#print axioms Recipe.Feasible.n_parity
#print axioms pl1_feasible_at_nine
```

Command and output:

```
$ lake env lean <scratch-file>
'IChO2026T5A1.t5_a1_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T5A1.answer_b_n_is_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T5A1.answer_a_n_even_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T5A1.answer_c_parity_not_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T5A1.n_mod_two_eq_one' depends on axioms: [propext, Quot.sound]
'IChO2026T5A1.n_eq_nine' depends on axioms: [propext, Quot.sound]
'IChO2026T5A1.Recipe.Feasible.n_parity' depends on axioms: [propext, Quot.sound]
'IChO2026T5A1.pl1_feasible_at_nine' does not depend on any axioms
```

Only the standard Lean logical axioms appear (`propext`,
`Classical.choice`, `Quot.sound`).  No custom unchecked axioms.

## 4. Semantic faithfulness check (independent audit)

* The only non-logarithmic hypotheses in `Recipe.Feasible` are the two
  balance equations read directly from the problem sheet: (i) each
  inter-fragment bond is a condensation consuming exactly one transferable
  (acidic) hydrogen — grounded by the W example on T5 page 1, where the
  surviving phosphate P–OH proton is drawn explicitly; (ii) each
  inter-fragment bond consumes exactly two free valences — the definition of
  a bond between wavy attachment points in the problem's fragment grammar.
* Fragment readings (2 valences and 2 P–OH protons for phosphate; 3 valences
  for glycerol; 1 valence for fatty acyl; 1 cap with no acidic proton for
  the hydrogen fragment) are read from the structures drawn in the fragment
  boxes on T5 page 1, quantities 2/3/4/n likewise.
* The proved statement `t5_a1_answer` is: for every n, feasibility of the
  PL1 assembly implies `Odd n` (and moreover n = 9), and a feasible assembly
  at n = 9 exists — i.e. answer (b) is forced and options (a)/(c) are
  excluded.  This matches exactly the "tick one correct statement" request,
  with the answer being (b), n is an odd number.
* No official solution, marking scheme or answer repository was consulted;
  the derivation is the independent valence/hydrogen double counting shown
  in `answer.md`.
