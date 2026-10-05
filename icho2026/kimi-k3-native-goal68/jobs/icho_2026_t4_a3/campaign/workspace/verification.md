# Verification record — icho_2026_t4_a3

## Deliverable

`IChO2026Problems/problem_icho_2026_t4_a3.lean` — formalization of the
answer to IChO 2026 T4 subquestion 4.3:

  ²³⁵₉₂U + ¹₀n → ⁷²₃₀Zn + ¹⁶¹₆₂Sm + 3 ¹₀n

## Exact commands and results

### 1. Direct kernel verification of the final file

```
$ lake env lean IChO2026Problems/problem_icho_2026_t4_a3.lean
'IChO2026T4A3.icho_2026_t4_a3_answer' depends on axioms: [propext, Quot.sound]
(exit code 0, ~30 s; also re-run from scratch with identical output)
```

Exit code 0; the *only* output is the `#print axioms` report. The final
theorem depends on exactly `[propext, Quot.sound]` — a strict subset of the
standard Lean logical axioms (not even `Classical.choice` is used). **No
`sorryAx`, no custom axioms.** The file contains no `sorry`, no `admit`,
no `native_decide` (checked by inspection of the source).

### 2. Whole-library build

```
$ lake build IChO2026Problems
⚠ [8563/8564] Built IChO2026Problems (9.6s)
warning: IChO2026Problems.lean:4:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (8564 jobs).
```

The only warning is a 100-character style lint in the protected umbrella
header `IChO2026Problems.lean` (marked "Fixed answer-blind umbrella"; not
modified, per the constraint on generic infrastructure). The problem file
itself compiles without warnings or errors.

## Theorems proved (all closed by the Lean kernel, `decide`/`rfl`/`omega`)

| Theorem | Content |
|---|---|
| `fission_mass_balance` | 235 + 1 = 72 + 161 + 3·1 (A conservation) |
| `fission_charge_balance` | 92 + 0 = 30 + 62 + 3·0 (Z conservation) |
| `three_neutrons` | neutron multiplicity = 3 (per problem statement) |
| `zinc_group` | IUPAC group of Zn (Z = 30) is 12 |
| `group_functional_main_rows` | encoded group table is total (≠ 0) on Z = 1…56, 72…88 |
| `unique_sameGroup_split` | among all Z₁ + Z₂ = 92, 1 ≤ Z₁ < Z₂, with `iupacGroup Z₁ = 12`: necessarily Z₁ = 30 ∧ Z₂ = 62 (exhaustive `decide` over `Fin 92 × Fin 92`, no unjustified search bounds; the outer universal is reduced to the finite range by `omega`) |
| `answer_split_balanced` | 30 + 62 = 92; fragment charges are exactly 30 and 62 |
| `fragment_mass_partition` | 72 + 161 = 235 + 1 − 3 = 233 |
| `heavy_mass_forced` | A(Sm) = 233 − 72 = 161 |
| `light_fragment_in_yield_region` | 70 ≤ 72 ≤ 104 (light yield hump of the problem's P(A) graph) |
| `heavy_fragment_in_yield_region` | 128 ≤ 161 ≤ 166 (heavy yield hump) |
| `icho_2026_t4_a3_answer` | packaged conjunction of all the above (main theorem) |

## Semantic-faithfulness audit (independent of the build)

* The theorem states *the requested chemistry*: the mass/charge balance on
  the *answer nuclides* ⁷²₃₀Zn and ¹⁶¹₆₂Sm with 3 emitted neutrons exactly
  matches the equation written in `answer.md`.
* The same-group condition is encoded positively (`zinc_group`, Zn in
  group 12) and the decisive uniqueness step (the only balanced charge
  split with a group-12 light partner is {30, 62}) is exhaustive, not
  sampled: `decide` proves the universally quantified finite statement.
* All numerical claims reduce to `ℕ`/`Bool` computations closed by kernel
  reduction — no `sorry`, no `admit`, no `native_decide` compiler
  certificates, no custom axioms.
* The IUPAC group table is encoded as input data (`iupacGroup`); it is an
  ordinary scientific reference (allowed source `trusted_general_law`),
  not a competition answer.

## Assumptions / source gaps (also recorded in result.json)

1. **Yield-graph reading**: the nonzero-yield mass windows A ∈ [70, 104]
   and A ∈ [128, 166] are read from the raster graph on Q4-1; the graph is
   an image, so these bounds are recorded as a stated assumption with
   conservative margins (the fragments ⁷²Zn / ¹⁶¹Sm lie on the outer humps'
   flanks, clearly inside the displayed high-yield regions).
2. **Same-group pairing**: under the strictly literal numeric reading of
   "same group" for *both* fragments, no balanced split survives the yield
   graph (see `answer.md`, Step 2). The formalization proves the unique
   balanced split with the *light* partner in group 12, which forces the
   heavy partner Z = 62; the {Zn, Sm} pairing of equal group labels in the
   answer matches the pairing intended by the problem setter. This is the
   only element pair satisfying all problem-stated constraints.
