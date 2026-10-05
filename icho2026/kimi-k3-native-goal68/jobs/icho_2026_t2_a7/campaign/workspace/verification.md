# Verification record - target `icho_2026_t2_a7`

Date: 2026-09-14 (UTC).  Toolchain: Lean 4.31.0
(`leanprover/lean4:v4.31.0`, per `lean-toolchain`), Mathlib v4.31.0,
workspace lakefile `lakefile.toml` with pinned deps (`lake-manifest.json`).

## Files under verification

* `IChO2026Problems/problem_icho_2026_t2_a7.lean` - the formalization.
* `axioms_check_icho_2026_t2_a7.lean` - scratch driver holding the
  `#print axioms` commands (not part of any lake target).
* `IChO2026Problems/All.lean` - one-line re-export used by the umbrella
  `IChO2026Problems.lean` / `IChO2026Run.lean`.

## Command 1: compile the problem file directly

```
lake env lean IChO2026Problems/problem_icho_2026_t2_a7.lean
```

Observed output: no output on stdout/stderr other than none; the compiler
produced no errors and no warnings after the final edit.

```
EXIT_CODE=0
```

## Command 2: umbrella project build

```
lake build IChO2026Problems
```

Observed result:

```
Build completed successfully (8564 jobs).
```

(Only pre-existing style linter notes for untouched shared files such as
`IChO2026Chem/Core.lean` were replayed; nothing from the target file.)

## Command 3: axiom inspection of all final theorems

Scratch driver content (imports Mathlib and the problem module, then lists
`#print axioms` for every exported theorem/lemma):

```
lake env lean axioms_check_icho_2026_t2_a7.lean
```

Observed output (verbatim):

```
'IChO2026T2A7.optionSixShape_fRepr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.answer_is_bottom_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.P1_fRepr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.P2_fRepr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.P3_fRepr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.P4_fRepr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.P5_fRepr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.P6_fRepr' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.positive_violates_P1' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.sine_fails_P1' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.growing_sine_fails_P1' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.constant_rate_fails_P3' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.negative_slope_fails_P3' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.monotone_fails_P5' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A7.optionThree_shape_fails_P5' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT_CODE=0
```

Only the three standard Lean logical axioms (`propext`,
`Classical.choice`, `Quot.sound`) appear; no custom/unchecked axioms, no
`sorryAx`.

## No-sorry / no-unsafe audit

```
grep -n "sorry\|admit\|^axiom\| axiom \|unsafe" IChO2026Problems/problem_icho_2026_t2_a7.lean
```

The only match is line 56, a documentation sentence stating that the file
contains *no* `sorry` ("... in full from Mathlib (no `sorry`, no custom
axioms).").  No `admit`, no `axiom` declarations, no `unsafe` code exist in
the file.

## Semantic-faithfulness check (independent of build success)

* The requested chemistry: option selection among six sketched dG/dt
  candidate graphs for a **closed** oscillatory system.  The theorem
  `answer_is_bottom_right : OptionSixShape fRepr` proves that the
  representative curve `fRepr t = -(2 + cos (8t)) / (2*(t+1))` satisfies the
  six qualitative predicates that exactly characterize the bottom-right
  sketch on answer sheet A2-6 (strictly negative for t > 0; value -3/2 at
  t = 0; limit 0 at infinity; decaying envelope; persistent strict local
  maxima; vanishing oscillation tube).
* The exclusions match the physical arguments in `answer.md`:
  `positive_violates_P1` (with `sine_fails_P1`, `growing_sine_fails_P1`)
  removes the two about-axis oscillations (options 2 and 5);
  `constant_rate_fails_P3` and `negative_slope_fails_P3` remove the two
  never-equilibrating trends (options 1 and 4); `monotone_fails_P5` with
  `optionThree_shape_fails_P5` removes the monotone relaxation (option 3).
* Candidate shapes were grounded by rendering PDF page index 23 (answer
  sheet A2-6) at 200 dpi from
  `icho_2026_source/raw/theory_problem.pdf` (sha256 af51373f...) and reading
  the curve geometry from the rendered image (grid: 3 rows x 2 columns).

## Source fidelity

* Question text verified against `TASK.json` and PDF page index 17
  (sheet Q2-4): "Which graph qualitatively illustrates the rate of change of
  Gibbs energy (dG/dt) of a closed system in which an oscillatory reaction
  occurs? Tick the correct box." - 3.0 pt, part 2.7.
* Candidate graphs verified against PDF page index 23 (sheet A2-6).
* No official solutions, marking schemes, or answer repositories were
  consulted; reasoning uses only the problem text, the rendered answer sheet,
  and the second law of thermodynamics (`trusted_general_law`).
