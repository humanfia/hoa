# Verification record — icho_2026_t1_a3

All commands run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t1_a3/campaign/workspace`
with toolchain `leanprover/lean4:v4.31.0` (`lake`, `lean` via elan).

## 1. Final file compilation

```
$ lake env lean IChO2026Problems/problem_icho_2026_t1_a3.lean
'Problems.Icho2026T1A3.t1_a3_main' depends on axioms: [propext, Classical.choice, Quot.sound]
(exit code 0)
```

The only output is the `#print axioms t1_a3_main` report written into the
file itself. The final theorem depends exactly on Lean's three standard
logical axioms — **no `sorryAx`, no custom axioms**. There are no errors and
no warnings for this file.

## 2. Direct axiom inspection

`#print axioms` is executed as part of the file (see above). Result:
`[propext, Classical.choice, Quot.sound]` — all allowed standard axioms.

## 3. Consistency of the dependency probe (generic infrastructure)

```
$ lake env lean IChO2026Run/Dependencies.lean
(exit code 0, no output; the Mathlib/Physlib/CRNT import graph is intact)
```

## 4. Full project build

```
$ lake build
...
Some required targets logged failures:
- IChO2026Problems.All
- IChO2026Problems
- IChO2026Run
error: build failed
```

This failure is **infrastructure-owned, not target-owned**: the umbrella
module `IChO2026Problems/All.lean` is stated in `IChO2026Problems.lean` to be
"rewritten by the trusted controller from the authorized target scope only"
and does not exist in the workspace. Generic infrastructure must not be
modified, so the mandated per-file verification (§1) is the authoritative
check for this target. Every generic module that does exist
(`IChO2026Chem.Core`, `IChO2026Chem.Reporting`, `IChO2026Run.Basic`,
`IChO2026Run.Dependencies`) compiles.

## 5. Semantic faithfulness check (independent of the build)

The final theorem `Problems.Icho2026T1A3.t1_a3_main` is a conjunction of the
exact items the question asks:

1. the isotope law used — `∀ n ≠ 0, pM p n / pM1 p q n = p/(n·q)` with
   `p = 989/1000`, `q = 11/1000` (proved from the binomial definitions
   `pM`, `pM1`; recurrence grounded in `binomialRecurrence`);
2. the ratio equation has the unique rational solution `n = 989/99`
   (`carbon_count_ratio`);
3. at the printed precision (quantum 1 for the ratio "9"), `n = 10` fits and
   `n = 11` fails (`candidate_arithmetic`);
4. the extraction table's phenolic (Fe³⁺-positive) candidates are exactly
   compounds 1 and 5 (`phenolic_candidates_correct`);
5. filtering those by the ratio fit leaves the singleton `[5]` and every
   survivor has 10 carbons (`identification_of_W`).

Hence the formal statement asserts: **n = 10** and **W = compound 5
(C₁₀H₁₂O₂)** — exactly the natural-language answer in `answer.md`.

## 6. Input / derived-fact separation

* Problem inputs (given, not derived): abundances 0.989 / 0.011 and their
  complementarity (stated: "carbon consists exclusively of ¹²C and ¹³C" and
  abundance of ¹²C "is 98.9 %"); observed ratio 9:1; extraction-table
  structures and formulae; the Fe³⁺ colour observation.
* Ordinary scientific reference (allowed): phenols characteristically
  colour with aqueous Fe³⁺.
* Derived and proved inline: the binomial intensity formulas, the ratio
  law, the solution n = 989/99 ≈ 10, uniqueness over the candidate table.

## 7. Source gaps

None blocking. The only interpretation choices (recorded openly):

* "9:1" is treated as exact for the solve and then validated a posteriori at
  the natural display quantum (half-width 1/2 of the unit 1); n = 10 is the
  unique integer passing this check while 11 fails. This follows the
  measurement policy (`one_half_of_last_displayed_quantum`).
* The abundance of ¹³C (1.1 %) is taken as the complement of the printed
  ¹²C abundance, as licensed by the explicit "consists exclusively of ¹²C
  and ¹³C" clause.
