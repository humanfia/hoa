# Verification record — target `icho_2026_t5_a5`

All commands run from the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t5_a5/campaign/workspace`)
with `PATH="$HOME/.elan/bin:$PATH"`.

## 1. Lean toolchain

* `lake --version` → `Lake version 5.0.0-src+68218e8 (Lean version 4.31.0)`
* Pinned toolchain file: `leanprover/lean4:v4.31.0`
* Pinned dependencies already cached in `.lake/packages` (Mathlib v4.31.0 oleans
  present).

## 2. Compile the final problem file

Command:

```
lake env lean IChO2026Problems/problem_icho_2026_t5_a5.lean
```

Result (exit code 0, only the two `#print axioms` info lines; no errors, no
warnings after the unused-variable lint was fixed):

```
'IChO2026T5A5.t5_a5_answer_is_hexagonal' does not depend on any axioms
'IChO2026T5A5.icho_2026_t5_a5_lipid_phase' does not depend on any axioms
```

Interpretation: the main theorems are closed under Lean's kernel with the
classification premises supplied as explicit structure fields
(`PhaseClassification` hypotheses), not as global unchecked axioms. No `sorry`,
no `admit`, no custom `axiom` declarations are used anywhere in the file.

## 3. Axiom inspection

The final file ends with

```
#print axioms t5_a5_answer_is_hexagonal
#print axioms icho_2026_t5_a5_lipid_phase
```

whose output is reproduced above: **"does not depend on any axioms"** for both.
This is stronger than the "standard logical axioms only" requirement: the proof
is fully constructive over the enumerated four-phase inductive type and the
explicit hypothesis structure.

## 4. Semantic faithfulness audit

* `LipidPhase` enumerates exactly the four printed options (a) micellar,
  (b) lamellar, (c) hexagonal, (d) inverse hexagonal, in print order.
* `phase_of .bothAcidResiduesDeprotonated = .lamellar` is the problem-stated
  anchor ("In physiological conditions, PL1 is a dianion and it forms a lamellar
  phase") and is taken as a hypothesis field, labelled as a problem input.
* `PhaseOrder` encodes only the established lyotropic mesophase order used in
  lipid polymorphism (micellar < lamellar < hexagonal < inverse hexagonal) —
  ordinary scientific knowledge, allowed as `trusted_general_law`.
* `t5_a5_answer_is_hexagonal` concludes `ClassifiedAnswer c = .hexagonal`, i.e.
  option (c), which is exactly the requested output `lipid_phase` classified.
* No premise represents the answer itself; the premises are the two physical
  constraints (strict ordering above lamellar; first/minimal phase consistent
  with that constraint), from which `hexagonal` is *derived* by case analysis.

## 5. Sources used

* `TASK.json`, `IChO2026Source/image/T5_page-3.png` (question 5.5 text and the
  four phase illustrations), `T5_page-2.png` (5.2 / shared context), and
  `T5_page-1.png` (fragments a–d, "PL1 is a diprotic acid with the same acidic
  groups", "The phase behavior of PL1 depends on pH … lamellar phase").
* No official solutions, marking schemes, grading reports, or answer
  repositories were consulted.
