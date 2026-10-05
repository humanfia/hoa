# Verification record — `icho_2026_t8_a5`

All commands were run in the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a5/campaign/workspace`)
with the pinned Lean toolchain `leanprover/lean4:v4.31.0`.

## Sources consulted (problem-only)

- `icho_2026_source/image/T8_page-1.png`, `T8_page-2.png`: statement of 8.5
  and its printed inputs (ω_cat = 3.8 %, SSA = 17.8 m² g⁻¹, M_cat = 557.21
  g mol⁻¹).
- `icho_2026_source/raw/theory_problem.pdf`, page G1-3 (PDF page 3):
  "Avogadro constant N_A = 6.022 × 10²³ mol–1".
- `icho_2026_source/raw/theory_problem.pdf`, page A8-5: blank student answer
  sheet; contains only "N_cat = ____", i.e. no extra precondition or unit
  hidden on the answer sheet.
- No other subquestion results are needed for 8.5.

## Build / compile

One-time library build (pre-existing workspace libraries):

    lake build IChO2026Chem        # succeeded

Compilation of the deliverable Lean file (exact commands and results):

    timed run: lake env lean IChO2026Problems/problem_icho_2026_t8_a5.lean
    result: exit code 0, no errors, no warnings (final run)

Interpretation: all definitions and theorems type-check under the pinned
Mathlib; in particular

- `IChO2026T8.catalystSurfaceDensity_reports` :
  `ReportsAtQuantum catalystSurfaceDensityRaw 2.31 0.01` — the raw density
  computed from the printed inputs, `0.038·6.022e23/(557.21·17.8·10¹⁸)`,
  lies in the tie-away-from-zero 3 s.f. reporting bin `[2.305, 2.315)` of
  `2.31` molecules nm⁻².
- `IChO2026T8.catalystSurfaceDensityLow_tight`,
  `IChO2026T8.catalystSurfaceDensityHigh_tight`
  — exact certificates [2.3002239, 2.3002240) and [2.3142175, 2.3142176)
  of the two extremal measurement corners (derived from the printed-display
  half-quantum intervals of ω_cat, M_cat, SSA, N_A).
- `IChO2026T8.envelope_consistent_with_report` — the measurement envelope is
  contained in the reporting bin and 2.31 lies strictly inside the envelope.

## Axiom audit

Command (temporary file, removed after the check):

    cat IChO2026Problems/problem_icho_2026_t8_a5.lean \
      and `#print axioms` lines for every final theorem > /tmp/axcheck2.lean
    lake env lean /tmp/axcheck2.lean

Output (verbatim, exit code 0):

    'IChO2026T8.catalystSurfaceDensity_reports' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.catalyst_raw_in_report_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.catalystSurfaceDensity_low_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.catalystSurfaceDensity_high_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.catalystSurfaceDensityRaw_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.envelope_consistent_with_report' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.catalystSurfaceDensityRaw_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.catalystSurfaceDensityLow_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026T8.catalystSurfaceDensityHigh_tight' depends on axioms: [propext, Classical.choice, Quot.sound]

Only the three standard Lean logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) appear; no custom/untrusted axioms and no `sorry`/`admit` were
used.  `grep -n "sorry\|admit\|axiom "` on the final file returns no hits.

## Semantic faithfulness check

- The theorem `catalystSurfaceDensity_reports` states exactly the requested
  chemistry: the catalyst surface density ρ = (ω_cat/100)·N_A /
  (M_cat · SSA · 10¹⁸) in molecules nm⁻² (definition
  `catalystSurfaceDensity`), evaluated at the printed inputs, and it proves
  that this quantity equals 2.31 at the 3 s.f. quantum — i.e.
  N_cat ≈ 2.31 molecules nm⁻².
- The numeric kernel `norm_num` evaluates the exact rational numeral
  (37995·60215·10⁵ / (557215·1785) etc.); the 10²³/10¹⁸ powers are computed
  as exact powers, so no intermediate rounding occurs anywhere in the
  derivation.  This matches the project measurement policy.
- A value derived independently in Python (`0.038*6.022e23/(557.21*17.8*1e18)
  = 2.307202…`) agrees with the certified interval membership
  `2.3072010 ≤ ρ < 2.3072011`.

## Known limitations

- The measurement-envelope corners are proved pointwise (extremal corners),
  relying on the fact that ρ is strictly increasing in (ω, N_A) and strictly
  decreasing in (M, SSA) on the positive orthant; the monotonicity itself is
  stated in the module documentation but not needed for the final reported
  answer, so it is not separately formalized as a theorem.
- Values use the Avogadro constant exactly as printed (6.022×10²³ mol⁻¹);
  using the 2022 SI exact value changes the answer by 2 parts in 10⁵ and does
  not change the reported 3 s.f. value.
