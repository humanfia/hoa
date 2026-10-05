# Verification: `icho_2026_t8_a6`

## Source integrity and inspection

`GOAL.txt` and `TASK.json` were read before solving. The relevant source images
`T8_page-1.png` and `T8_page-2.png` were visually inspected. The original
`theory_problem.pdf` was inspected at Q8-2 (PDF page 73) and at the blank
student answer sheet A8-5 (PDF page 81). The answer sheet contains no supplied
answer or additional numerical datum.

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T8_page-1.png icho_2026_source/image/T8_page-2.png
```

Result: exit code 0.

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843  icho_2026_source/image/T8_page-1.png
cfd3c6fa64d0126843e3cf65a1235337fa3f869db285f36fbb0a18dddebfacee  icho_2026_source/image/T8_page-2.png
```

These hashes match `TASK.json` and `isolation_manifest.json`.

## Lean verification

The shared local library was first built with:

```text
lake build IChO2026Chem
```

Result: exit code 0, ending with:

```text
✔ [8560/8561] Built IChO2026Chem (10s)
Build completed successfully (8561 jobs).
```

Required target-file command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a6.lean
```

Result: exit code 0. The `#print axioms` output was:

```text
'IChO2026Problems.T8A6.co_half_reaction_balanced' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T8A6.electron_coefficient_from_charge_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T8A6.co_quantum_yield_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A6.co_quantum_yield_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A6.co_quantum_yield_final' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only standard Lean logical axioms appear. In particular, there is no
`sorryAx` and no custom unchecked axiom.

Placeholder/unsafe scan command:

```bash
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe|axiom)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t8_a6.lean; then
  exit 1
fi
```

Result: exit code 0 and no output.

## Independent exact-arithmetic check

Command:

```bash
python3 - <<'PY'
from fractions import Fraction as Q
raw = (Q(2) * Q(8) * Q(10, 1000) * Q(38, 1000)
       * Q(602214076 * 10**15) * Q(662607015, 10**42)
       * Q(299792458) * Q(100)
       / (Q(55721, 100) * Q(50, 1000) * Q(3600)
          * Q(390, 10**9)))
expected = Q(18940872892793693114789369,
             10186495312500000000000000)
assert raw == expected
assert Q(371, 200) <= raw < Q(373, 200)
print(f"raw exact = {raw}")
print(f"raw decimal = {float(raw):.15f}%")
print("rounding interval: 1.855 <= raw < 1.865; report = 1.86%")
PY
```

Result: exit code 0.

```text
raw exact = 18940872892793693114789369/10186495312500000000000000
raw decimal = 1.859410161368362%
rounding interval: 1.855 <= raw < 1.865; report = 1.86%
```

## Semantic completion audit

| Requirement | Evidence |
|---|---|
| Use the printed catalyst loading and TOF | `PrintedInputs`, `catalystAmount_mol`, `catalystMolecules`, and `coMoleculesPerHour`; exact intermediate theorems prove each conversion. |
| Account for electrons reacted per CO | `co_half_reaction_balanced` proves atom and charge balance for the two-electron acidic half-reaction; `electron_coefficient_from_charge_balance` proves uniqueness of the coefficient. |
| Compute incident photons from the LED data | `photonEnergy_J` formalizes `E = hc/λ`; `incidentPhotonsPerHour` formalizes `Pt/E`, including exactly 3600 s per hour. |
| Apply the source quantum-yield formula | `quantumYieldPercent` is reacted electrons divided by incident photons, multiplied by 100. |
| Retain the raw result | `co_quantum_yield_raw` proves the exact rational value. |
| Report three significant figures | `co_quantum_yield_reported` and `co_quantum_yield_final` prove that 1.86 is the nearest multiple of 0.01 to the positive raw percentage. |
| Avoid unsupported proof shortcuts | Direct compilation and the axiom/placeholder checks above. |
| Natural-language deliverable | `answer.md` derives and reports `1.86%` with source grounding. |

The theorem statements use the exact printed quantities. No intermediate
rounding, unjustified search bound, custom axiom, or unreported source gap is
present.
