# Verification for IChO 2026 T7-A4

All commands were run from
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t7_a4/campaign/workspace`.

## Source integrity

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T7_page-1.png icho_2026_source/image/T7_page-2.png
```

Result (exit code 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
ee7fe1adff7ac3aae8701bf684981bd2b1e21b28f1c9e4b21dd9c38c3bdb79ad  icho_2026_source/image/T7_page-1.png
010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba  icho_2026_source/image/T7_page-2.png
```

These values match `TASK.json`.

## Lean compilation and axiom inspection

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t7_a4.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T7A4.mdea_atom_counts' depends on axioms: [propext]
'IChO2026Problems.T7A4.reaction_conserved_totals' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T7A4.t7_a4_reaction_equation' depends on axioms: [propext, Quot.sound]
```

The three lines are emitted by the file's explicit `#print axioms` commands.
`propext` and `Quot.sound` are standard Lean logical/quotient axioms, permitted
by the task.  There are no custom unchecked axioms.

## Shortcut scan

Command:

```text
grep -nE '\bsorry\b|\badmit\b|\bunsafe\b|^[[:space:]]*axiom\b' IChO2026Problems/problem_icho_2026_t7_a4.lean
```

Result: exit code 1 with no output, meaning that none of the forbidden proof
shortcuts or custom axiom declarations occurs in the final Lean file.

## Deliverable/schema checks

Command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0 with no output.

Command:

```text
test -s answer.md -a -s verification.md -a -s result.json -a -s IChO2026Problems/problem_icho_2026_t7_a4.lean
```

Result: exit code 0 with no output.

## Semantic audit

- The formal reactants are neutral MDEA (`C₅H₁₃NO₂`), CO₂, and H₂O, all
  with coefficient 1.
- The formal products are protonated MDEA (`C₅H₁₄NO₂⁺`) and bicarbonate
  (`HCO₃⁻`), both with coefficient 1.
- `reaction_conserved_totals` proves that each side is `C₆H₁₅NO₅` with net
  charge 0; `t7_a4_reaction_equation` proves balance for every constructor of
  the exhaustive element type and for charge.
- The formal equation is therefore the same equation presented in `answer.md`,
  not a weakened numerical or generic balance statement.
- Lean verifies conservation, while the empirical identification of the
  aqueous tertiary-amine bicarbonate reaction is source-grounded in
  `answer.md`; no claim is made that conservation alone proves reactivity.
