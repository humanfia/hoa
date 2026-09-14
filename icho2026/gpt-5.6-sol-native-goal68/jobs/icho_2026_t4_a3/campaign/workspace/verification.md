# Verification for `icho_2026_t4_a3`

## Source integrity and inspection

The authorized source files named by `TASK.json` were inspected, including the
original PDF question pages, its supplied periodic table, and the blank A4-1
student answer sheet. Their hashes were checked with:

```text
sha256sum GOAL.txt TASK.json icho_2026_source/image/T4_page-1.png icho_2026_source/image/T4_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result:

```text
7af4e4ec0f3b793af260c2353314a2d62a4a192e439f4ca1618cdf6a24bdff51  GOAL.txt
d6cbe105bae2598a60cac8ceeb0e8d43b9323a327d3d2221e92faf258f508967  TASK.json
f3b21152e21992aaa319cd436ffe893d0dff6634488f27663eee85b3cf81ddcf  icho_2026_source/image/T4_page-1.png
60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94  icho_2026_source/image/T4_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

The image and PDF hashes agree with the authorized hashes recorded in
`TASK.json`/`isolation_manifest.json`.

## Lean compilation and axiom audit

Exact command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a3.lean
```

Result: exit code 0. The four `#print axioms` checks at the end of the file
printed:

```text
'IChO2026Problems.T4A3.source_mass_number_balance' depends on axioms: [propext]
'IChO2026Problems.T4A3.emitted_neutron_count_forced' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T4A3.partner_atomic_number_forced' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T4A3.requested_fission_equation' depends on axioms: [propext]
```

`propext` and `Quot.sound` are standard Lean logical axioms, which the task
explicitly permits. No custom unchecked axiom is present.

Proof-shortcut check (exact command):

```text
if grep -RInE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t4_a3.lean; then exit 1; else echo 'no forbidden proof shortcuts or custom axiom declarations'; fi
```

Expected and observed result (exit code 0):

```text
no forbidden proof shortcuts or custom axiom declarations
```

## Semantic audit

The final theorem does more than restate a balanced sum. It proves that the
structured reaction:

1. has uranium-235 and one neutron as reactants;
2. has rubidium-93 and caesium-140 as the two products;
3. emits exactly the problem-stated three neutrons;
4. uses exactly the two mass numbers read at the yield maxima;
5. conserves mass number (`235 + 1 = 93 + 140 + 3`);
6. conserves atomic number (`92 = 37 + 55`); and
7. places both products in periodic-table group 1.

Thus the theorem covers the complete requested formula and the chemistry
conditions that validate it.

## Artifact validation

Exact command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0 with no output, confirming that `result.json` is valid
JSON.
