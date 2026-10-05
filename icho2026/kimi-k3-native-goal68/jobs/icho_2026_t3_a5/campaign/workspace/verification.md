# Verification record — target `icho_2026_t3_a5` (IChO 2026, T3, subquestion 3.5)

## Deliverables checked

* `answer.md` — natural-language solution with source-grounding.
* `IChO2026Problems/problem_icho_2026_t3_a5.lean` — formalization.
* `IChO2026Problems/All.lean` — umbrella importing the problem file.

## Exact commands and results

### 1. Standalone compile of the problem file

```
$ lake env lean IChO2026Problems/problem_icho_2026_t3_a5.lean
```

Result: exit code 0, **no errors, no warnings**. Stdout (produced by the
`#print axioms` statements in the file):

```
'IChO2026T3A5.repeatUnitX_formula' does not depend on any axioms
'IChO2026T3A5.macrocycleX_formula' does not depend on any axioms
'IChO2026T3A5.global_atom_balance' does not depend on any axioms
'IChO2026T3A5.repeatUnit_is_minimal' does not depend on any axioms
'IChO2026T3A5.backbone_alternates' does not depend on any axioms
```

Note: not even the standard Lean logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) are used — all proofs are computational (`decide`/`rfl`) over
decoded natural-number atom inventories and finite block lists. No `sorry`,
`admit`, `sorryAx`, custom `axiom`, or unsafe options appear anywhere in the
file (verified by the `#print axioms` output above and by inspection).

### 2. Full library build (umbrella import)

```
$ lake build IChO2026Problems
```

Result: `Build completed successfully (8564 jobs).` The only warning is a
pre-existing style-linter note about a >100-character comment line in the
fixed umbrella `IChO2026Problems.lean` (generic infrastructure, not part of
this target and left unmodified).

### 3. Theorem inventory (all proved, axiom-free)

| theorem | content |
|---|---|
| `c2Half_formula` | one half of printed C2 = C₁₉H₁₆N₂ |
| `c2Monomer_formula` | printed C2 = C₃₈H₃₂N₄ |
| `d4Monomer_formula` | printed D4 = C₈H₂F₄O₂ |
| `cof7_condensation_balance` / `cof7Cell_formula` | C2 + 2 D4 − 4 H₂O → COF-7 cell C₅₄H₂₈F₈N₄ |
| `pinnick_link_balance` | NaClO₂/NaH₂PO₄: –CH=N– + [O] → –C(=O)–NH– |
| `ozonolysis_core_balance` | O₃/Me₂S: Ar–CH=CH–Ar + 2[O] → 2 Ar–CHO |
| `c2HalfInX_formula` | C2-half inside X = C₁₉H₁₄N₂O |
| `d4InX_formula` | D4 unit inside X = C₈F₄O₂ |
| `repeatUnitX_formula` | **smallest repeat unit = C₂₇H₁₄F₄N₂O₃** |
| `macrocycleX_formula` | X = (C₂₇H₁₄F₄N₂O₃)₆ = C₁₆₂H₈₄F₂₄N₁₂O₁₈ |
| `global_atom_balance` | full-sequence balance: C₂ + 2 D4 + 6[O] = 2 × repeat + 4 H₂O |
| `backbone_alternates` | C2-halves and D4 units strictly alternate on the ring |
| `macrocycle_backbone` / `repeatUnit_is_minimal` | backbone = 6 × [C2half, D4]; no one-block tile exists |

## Semantic-faithfulness self-check

* The numbers formalised are not assumed: each monomer inventory is built by
  *explicitly enumerating the fragments visible in the printed structures*
  (1,3,5-trisubstituted central ring C₆H₃; vinyl CH; p-phenylene C₆H₄; –NH₂;
  tetrafluoro ring C₆F₄; aldehyde CHO), and `decide` computes the totals. Any
  misreading of the printed figures would make the global atom balance or the
  fragment counts fail.
* The repeat unit is *derived*, not stipulated: the Lean file chains the
  printed monomers through the two printed reaction steps (Pinnick, ozonolysis)
  at linkage level and closes a global material balance with zero unaccounted
  atoms.
* Minimality is a proved statement about the printed alternating Kagome
  backbone, not a textual claim.
* The Kagome topology ("C2 + D4 → Kagome") is itself printed in the part 3.3
  table of the problem (page Q3-4) and in the COF-7 sketch (page Q3-5), i.e.
  grounded in the source rather than assumed.

## Source integrity

* No source files were modified; `theory_problem.pdf` and images were read
  only. SHA-256 of `icho_2026_source/raw/theory_problem.pdf` was not altered.
* No official solution, marking scheme, or answer repository was consulted
  (the bundle contains only problem pages; the PDF has 93 pages, all
  questions).
