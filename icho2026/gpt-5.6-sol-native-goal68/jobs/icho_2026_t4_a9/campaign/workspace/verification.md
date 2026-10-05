# Verification for `icho_2026_t4_a9`

All commands below were run from
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t4_a9/campaign/workspace`.

## Shared-library build

Command:

```text
lake build IChO2026Chem
```

Result: exit code 0. Lean replayed `IChO2026Chem.Core` and
`IChO2026Chem.Reporting` and ended with:

```text
Build completed successfully (8561 jobs).
```

The two existing generic modules emitted only their pre-existing
`Copyright too short!` header-style warnings.

## Target compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a9.lean
```

Result: exit code 0. The three final `#print axioms` commands embedded in the
file produced:

```text
'IChO2026Problems.Icho2026T4A9.Derived.total_fissions_output' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T4A9.Derived.enriched_uranium_mass_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.Icho2026T4A9.Derived.requested_outputs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical/foundational axioms permitted by the task;
there is no custom unchecked axiom.

## Forbidden-shortcut and custom-declaration scan

Command:

```text
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|constant)[[:space:]]' IChO2026Problems/problem_icho_2026_t4_a9.lean; then exit 1; else echo 'No sorry, admit, unsafe, or custom axiom/constant declarations found.'; fi
```

Result: exit code 0.

```text
No sorry, admit, unsafe, or custom axiom/constant declarations found.
```

## Source integrity

Command:

```text
sha256sum TASK.json icho_2026_source/image/T4_page-1.png icho_2026_source/image/T4_page-2.png icho_2026_source/image/T4_page-3.png icho_2026_source/raw/theory_problem.pdf
```

Result: exit code 0.

```text
802f100a203df718ec51ee9f611eba897b8695751c4ecacf08b0900015f76dc6  TASK.json
f3b21152e21992aaa319cd436ffe893d0dff6634488f27663eee85b3cf81ddcf  icho_2026_source/image/T4_page-1.png
60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94  icho_2026_source/image/T4_page-2.png
c9d3ffc7f4dcd8176195f846733981e77fe9ac3cf21e5b6a1be89f140eecdbdc  icho_2026_source/image/T4_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

The three image and PDF hashes match `isolation_manifest.json`. The original
PDF has 93 pages; T4 occupies PDF pages 37--39 and its blank student sheets
occupy pages 40--43. The final A4-4 sheet contains only `TN =` and `m = ...
kg`, consistent with the two formalized outputs.

## Result manifest syntax

Command:

```text
python3 -m json.tool result.json >/dev/null && echo 'result.json is valid JSON.'
```

Result: exit code 0.

```text
result.json is valid JSON.
```
