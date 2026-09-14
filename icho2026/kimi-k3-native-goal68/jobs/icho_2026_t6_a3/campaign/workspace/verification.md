# Verification record — icho_2026_t6_a3

## Exact commands and results

### 1. Lean compilation of the final formalization

```
lake env lean IChO2026Problems/problem_icho_2026_t6_a3.lean
```

Result: exit code 0, no errors, no `sorry`/`admit`/warning output. Toolchain:
`leanprover/lean4:v4.31.0` (see `lean-toolchain`), Mathlib v4.31.0 (pinned in
`lakefile.toml` / `lake-manifest.json`).

### 2. Axiom inspection (embedded in the same file, printed during compilation)

Output of `#print axioms`:

```
'IChO2026T6A3.possible_halogens' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T6A3.possible_set' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the standard Lean logical axioms are used (`propext`,
`Classical.choice`, `Quot.sound` — the latter two arrive via `Set.ext` and
decidability machinery). No custom or unchecked axioms were declared.

### 3. Numeric sanity check of the derived electron energy

```
python3 -c "print(2.5*1.602e-19*6.022e23/1000, 'kJ/mol')"
= 241.1811 kJ/mol
```

Matches `electronEnergyKJ_value : electronEnergyKJ = 241.1811` in the Lean
file, and 228 ≤ 241.1811 < 290 gives iodine as the unique possible halogen.

## Semantic faithfulness audit (beyond "it compiles")

- The `Halogen` type enumerates exactly the four table entries (F, Cl, Br, I);
  `bdeKJ` reproduces the printed BDE table verbatim (467/346/290/228 kJ mol⁻¹).
- `voltageV = 2.5`, `electronChargeC = 1.602e-19 C`, `avogadro = 6.022e23 mol⁻¹`
  are the values printed in the question and on the official constant sheet
  G1-3 — these are declared as problem inputs (plain `def`s), separated from
  derived lemmas.
- The derived criterion `Possible X := bdeKJ X ≤ electronEnergyKJ` encodes
  exactly the physical reasoning required by the question ("voltage acting on
  the electrons" → electron kinetic energy must reach the C–X BDE); no
  unstated scientific premise is added.
- The requested output ("possible halogen(s)", a finite set of element
  symbols) is proved as the singleton {I} in *both* predicate form
  (`possible_halogens`, iff over all four candidates) and answer-sheet set
  form (`possible_set`). Nothing is weakened: the statements quantify over
  the full candidate type with explicit non-possibility of F, Cl, Br.
- `result.json` records target id, status, theorem names, assumptions,
  source gaps (none material), and the verification commands above.

## Source inputs consulted

- `icho_2026_source/image/T6_page-2.png` (question 6.3 + BDE table)
- `icho_2026_source/image/T6_page-1.png` (shared T6 context, 6.2 chlorinated
  C14 precursor — cross-check only)
- `icho_2026_source/raw/theory_problem.pdf` p. 53 (Q6-2), p. 3 (G1-3
  constants), p. 58 (blank answer sheet A6-2, "6.3 (2.0 pt)  X = _______")

No official solutions, marking schemes, or answer repositories were used.
