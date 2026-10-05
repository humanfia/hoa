# Verification for IChO 2026 T8-A7

## Source integrity and inspection

The source assets were found read-only under the run's `seed` directory.  They
are the assets named by the task manifest; the hashes match exactly.

Command:

```text
sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T8_page-2.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T8_page-3.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

Result:

```text
cfd3c6fa64d0126843e3cf65a1235337fa3f869db285f36fbb0a18dddebfacee  .../T8_page-2.png
d6431350f32953011648ffe537d8d51ed7dc9dfb5a437a6f1c94620d6041055f  .../T8_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  .../theory_problem.pdf
```

The two PNGs were visually inspected at their original 1191 x 1684
resolution.  The original PDF was opened with PyMuPDF (93 pages); its page 74
(Q8-3) and page 82 (blank answer sheet A8-6 containing the 8.7 boxes) were
rendered at 1191 x 1684 and visually inspected.  PDF text extraction also
located 8.7 on those respective pages.

## Lean verification

Command, run from the workspace root:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a7.lean
```

Result: exit code 0.  The embedded `#print axioms` checks printed:

```text
'IChO2026Problems.T8A7.displayed_rate_indices' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A7.co_rate_trend' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A7.endpoint_rate_increase_under_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A7.physical_rate_increase_under_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A7.co_rate_trend_under_display_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms.  No custom unchecked axiom is used.

Placeholder / unsafe scan command:

```text
! grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t8_a7.lean
```

Expected and obtained result: exit code 0 with no matches.

JSON validation command:

```text
python3 -m json.tool result.json >/dev/null
```

Expected and obtained result: exit code 0.

## Semantic audit

- Requested output: one trend classification.  Proved by `co_rate_trend` and,
  under display intervals, by `co_rate_trend_under_display_rounding`.
- Source data: all seven labelled graph points are represented in
  `displayedGraphPoints`; their seven derived products are proved in
  `displayed_rate_indices`.
- Chemistry/rate connection: the source-defined TOF is multiplied by the
  catalyst count per gram.  The latter is loading times a fixed positive
  conversion factor; `physical_rate_increase_under_rounding` proves that this
  factor preserves the comparison.
- Measurement policy: both endpoint loadings use half of their displayed 0.1%
  quantum, and both integer TOFs use half of their displayed 1 h⁻¹ quantum.
- The theorem claims a net low-to-high increase, not false strict monotonicity
  between every adjacent plotted point.
- No prerequisite numerical answer from T8-A5 or T8-A6 is assumed or needed.
