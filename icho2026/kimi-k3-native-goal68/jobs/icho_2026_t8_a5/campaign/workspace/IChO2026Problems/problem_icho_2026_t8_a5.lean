import IChO2026Chem

/-!
# IChO 2026, Theory problem 8.5 (`icho_2026_t8_a5`)

**Question (Q8-2, 5.0 pt).** *Calculate the number of catalytic molecules per
nm², $N_{cat}$, of C₃N₄ loaded with **1**, when the mass fraction of catalyst,
$\omega_{cat} = 3.8\,\%$, if the specific surface area of C₃N₄ is
$17.8\ \mathrm{m^2\,g^{-1}}$. $M_{cat} = 557.21\ \mathrm{g\,mol^{-1}}$.*

The blank answer sheet (page A8-5) supplies no further data or precondition.

## Physical model (definitions, all source-grounded)

Taking a basis of $1\ \mathrm{g}$ of C₃N₄ support (compare 8.7: "per gram of
C₃N₄ loaded with **1**"; the quantity asked for is intensive, so the basis
cancels):

* mass of catalyst: $m = \omega_{cat}\cdot 1\ \mathrm{g}$;
* number of catalyst molecules: $N = (m/M_{cat})\cdot N_A$;
* available area: $A = SSA\ \mathrm{m^2} = SSA\cdot 10^{18}\ \mathrm{nm^2}$,
  since $1\ \mathrm{nm^2} = 10^{-18}\ \mathrm{m^2}$;
* hence
  $\displaystyle N_{cat}
    = \frac{\omega_{cat}\,N_A}{M_{cat}\,SSA}\times 10^{-18}$
  molecules nm⁻².

## Printed inputs used

From question 8.5 (Q8-2): $\omega_{cat} = 3.8\,\%$, $SSA = 17.8\ \mathrm{m^2\,g^{-1}}$,
$M_{cat} = 557.21\ \mathrm{g\,mol^{-1}}$. From the official "Physical Constants and
Equations" sheet (page G1-3 of the same problem PDF): $N_A = 6.022\times10^{23}\ \mathrm{mol^{-1}}$.

Two normalizations with respect to the raw print:

* $\omega_{cat} = 3.8\,\%$ enters the mass balance as the dimensionless
  fraction $0.038 = 3.8/100$ (definition of "%" and of mass fraction);
* $N_A = 6.022\times10^{23}\ \mathrm{mol^{-1}}$ printed on the constants sheet.

## Measurement interval

Per the project measurement policy, each printed quantity `q` is treated as a
measurement representing the half-quantum interval $[q-\varepsilon_q,q+\varepsilon_q]$
with $\varepsilon_q$ = half of the last displayed quantum. Because
$N_{cat}(\omega, M, S, N_A)$ is increasing in $\omega, N_A$ and decreasing in
$M, S$ on the positive orthant, the extremal corners are:

* minimum at $(0.038-0.0005,\ M+0.005,\ 17.8+0.05,\ N_A - 0.0005\times10^{23})$;
* maximum at $(0.038+0.0005,\ M-0.005,\ 17.8-0.05,\ N_A + 0.0005\times10^{23})$.

Both endpoints (proved below) round to $2.3$ molecules nm⁻² and straddle the
reported value $2.31$.

## Reporting

The contract (see `IChO2026Chem.Reporting`) fixes three significant figures as
the final display, with ties away from zero and no intermediate rounding. The
raw value satisfies `2.305 ≤ raw < 2.315`, hence reports as `2.31` at quantum
`0.01` molecules nm⁻².
-/

open IChO2026Chem.Reporting

namespace IChO2026T8

/-- Raw catalyst surface density in molecules nm⁻², as a function of the
dimensionless mass fraction `ω`, the molar mass `M` in g mol⁻¹, the specific
surface area `A` in m² g⁻¹ and the Avogadro constant `NA` in mol⁻¹.

Derivation (all steps definitionally grounded in the stated units):
`ω·NA` catalyst molecules per gram of support; the area per gram of support is
`A` m² = `A·10¹⁸` nm² (since 1 nm² = 10⁻¹⁸ m²); dividing the number of
molecules per gram by the area per gram in nm² gives `ω·NA / (M·A·10¹⁸)`.
The result is in molecules nm⁻² and is independent of the 1 g basis. -/
noncomputable def catalystSurfaceDensity
    (ω M A NA : ℝ) : ℝ :=
  ω * NA / (M * A) / (10:ℝ)^18

/-- Printed mass fraction of catalyst **1** on C₃N₄: ω_cat = 3.8 %, printed in
question 8.5 and used as the dimensionless fraction 0.038. -/
noncomputable def massFractionPct : ℝ := 3.8

/-- Printed molar mass of catalyst: M_cat = 557.21 g mol⁻¹ (question 8.5). -/
noncomputable def molarMassCat : ℝ := 557.21

/-- Printed specific surface area of C₃N₄: 17.8 m² g⁻¹ (question 8.5). -/
noncomputable def specificSurfaceArea : ℝ := 17.8

/-- Avogadro constant printed on the official constants sheet (page G1-3 of
the problem PDF): N_A = 6.022×10²³ mol⁻¹. -/
noncomputable def avogadroPrinted : ℝ := 6.022 * (10:ℝ)^23

/-- Raw value of the requested density at the printed inputs, in molecules
nm⁻²:
`N_cat = (0.038/100 · 6.022×10²³) / (557.21 · 17.8 · 10¹⁸)`. -/
noncomputable def catalystSurfaceDensityRaw : ℝ :=
  catalystSurfaceDensity (massFractionPct / 100) molarMassCat
    specificSurfaceArea avogadroPrinted

/-- The raw value is positive (a density of molecules per nm² must be). -/
theorem catalystSurfaceDensityRaw_pos : 0 < catalystSurfaceDensityRaw := by
  unfold catalystSurfaceDensityRaw catalystSurfaceDensity massFractionPct
    molarMassCat specificSurfaceArea avogadroPrinted
  positivity

/-- The requested three-significant-figure display quantum: 0.01 molecules
nm⁻². -/
noncomputable def reportQuantum : ℝ := 0.01

/-- The reported (3 s.f.) answer: 2.31 molecules nm⁻². -/
noncomputable def catalystReported : ℝ := 2.31

/-- The reporting quantum is positive. -/
theorem reportQuantum_pos : 0 < reportQuantum := by norm_num [reportQuantum]

/-- The reported value is an integer multiple of the quantum. -/
theorem catalystReported_isMultiple :
    ∃ k : ℤ, catalystReported = reportQuantum * k :=
  ⟨231, by norm_num [catalystReported, reportQuantum]⟩

/-- The raw value lies strictly in the 3 s.f. reporting interval around 2.31:
`2.305 ≤ N_cat < 2.315`. Proved by scaling to an integer inequality. -/
theorem catalyst_raw_in_report_interval :
    (2.305 : ℝ) ≤ catalystSurfaceDensityRaw ∧ catalystSurfaceDensityRaw < 2.315 := by
  -- `norm_num` evaluates the exact rational numeral (the 10²³ / 10¹⁸ factors
  -- are computed as exact powers) and discharges the rational inequalities.
  norm_num [catalystSurfaceDensityRaw, catalystSurfaceDensity, massFractionPct,
    molarMassCat, specificSurfaceArea, avogadroPrinted]

/-- Final answer theorem: the raw density, computed from the printed inputs,
reports as `2.31` molecules nm⁻² at the 3 s.f. quantum `0.01`, under the
project's tie-away-from-zero rounding contract. -/
theorem catalystSurfaceDensity_reports :
    ReportsAtQuantum catalystSurfaceDensityRaw 2.31 (0.01 : ℝ) := by
  refine ⟨by norm_num, ⟨231, by norm_num⟩, ?_⟩
  rw [if_pos (le_of_lt catalystSurfaceDensityRaw_pos)]
  have h2 : (2.31:ℝ) - 0.01 / 2 = 2.305 := by norm_num
  have h3 : (2.31:ℝ) + 0.01 / 2 = 2.315 := by norm_num
  rw [h2, h3]
  exact catalyst_raw_in_report_interval

/-! ### Measurement-interval robustness

Every printed input is a measurement: the last displayed quantum fixes the
half-width. The density is jointly monotone in (ω, NA) (increasing) and
(M, A) (decreasing) on the positive orthant, so the extremal corners over the
Cartesian product of the half-quantum intervals are:

* minimum: ω − 0.0005, M + 0.005, A + 0.05, N_A − 0.0005×10²³
* maximum: ω + 0.0005, M − 0.005, A − 0.05, N_A + 0.0005×10²³

The two theorems below certify the resulting envelope. -/

/-- Lower corner of the measurement-compatible envelope. -/
noncomputable def catalystSurfaceDensityLow : ℝ :=
  catalystSurfaceDensity ((massFractionPct - (5/10000 : ℝ)) / 100)
    (molarMassCat + (5/1000 : ℝ)) (specificSurfaceArea + (5/100 : ℝ))
    ((6.022 - (5/10000 : ℝ)) * (10:ℝ)^23)

/-- Upper corner of the measurement-compatible envelope. -/
noncomputable def catalystSurfaceDensityHigh : ℝ :=
  catalystSurfaceDensity ((massFractionPct + (5/10000 : ℝ)) / 100)
    (molarMassCat - (5/1000 : ℝ)) (specificSurfaceArea - (5/100 : ℝ))
    ((6.022 + (5/10000 : ℝ)) * (10:ℝ)^23)

/-- The lower corner satisfies `2.3002 ≤ N_cat < 2.3003` (molecules nm⁻²);
the exact value is `2.30022…`.  The endpoints are the half-quantum extremes:
`ω − 0.0005 = 3.7995 %`, `M + 0.005`, `A + 0.05`, `N_A − 0.0005·10²³`.  The
proof rewrites each inline endpoint arithmetic into the plain decimal numeral
it defines (exact rational identities) and discharges the resulting exact
decimal inequality with `norm_num`.  This is exact evaluation of the corner —
no intermediate rounding is involved. -/
theorem catalystSurfaceDensity_low_bounds :
    (2.3002 : ℝ) ≤ catalystSurfaceDensityLow ∧ catalystSurfaceDensityLow < 2.3003 := by
  rw [catalystSurfaceDensityLow, catalystSurfaceDensity, massFractionPct,
    molarMassCat, specificSurfaceArea]
  have hw : (3.8 - (5/10000 : ℝ)) / 100 = 0.037995 := by norm_num
  have hM : (557.21 : ℝ) + 5/1000 = 557.215 := by norm_num
  have hA : (17.8 : ℝ) + 5/100 = 17.85 := by norm_num
  have hN : (6.022 : ℝ) - 5/10000 = 6.0215 := by norm_num
  rw [hw, hM, hA, hN]
  constructor <;> norm_num

/-- The upper corner satisfies `2.3142 ≤ N_cat < 2.3143` (molecules nm⁻²);
the exact value is `2.31421…`. -/
theorem catalystSurfaceDensity_high_bounds :
    (2.3142 : ℝ) ≤ catalystSurfaceDensityHigh ∧ catalystSurfaceDensityHigh < 2.3143 := by
  rw [catalystSurfaceDensityHigh, catalystSurfaceDensity, massFractionPct,
    molarMassCat, specificSurfaceArea]
  have hw : (3.8 + (5/10000 : ℝ)) / 100 = 0.038005 := by norm_num
  have hM : (557.21 : ℝ) - 5/1000 = 557.205 := by norm_num
  have hA : (17.8 : ℝ) - 5/100 = 17.75 := by norm_num
  have hN : (6.022 : ℝ) + 5/10000 = 6.0225 := by norm_num
  rw [hw, hM, hA, hN]
  constructor <;> norm_num

/-- The raw value satisfies the tight certificate `2.3072010 ≤ N_cat < 2.3072011`
(molecules nm⁻²). -/
theorem catalystSurfaceDensityRaw_tight :
    (2.3072010 : ℝ) ≤ catalystSurfaceDensityRaw ∧
    catalystSurfaceDensityRaw < 2.3072011 := by
  unfold catalystSurfaceDensityRaw catalystSurfaceDensity massFractionPct
    molarMassCat specificSurfaceArea avogadroPrinted
  constructor <;> norm_num

/-- Tight certificate for the low corner: `2.3002239 ≤ low < 2.3002240`. -/
theorem catalystSurfaceDensityLow_tight :
    (2.3002239 : ℝ) ≤ catalystSurfaceDensityLow ∧
    catalystSurfaceDensityLow < 2.3002240 := by
  rw [catalystSurfaceDensityLow, catalystSurfaceDensity, massFractionPct,
    molarMassCat, specificSurfaceArea]
  have hw : (3.8 - (5/10000 : ℝ)) / 100 = 0.037995 := by norm_num
  have hM : (557.21 : ℝ) + 5/1000 = 557.215 := by norm_num
  have hA : (17.8 : ℝ) + 5/100 = 17.85 := by norm_num
  have hN : (6.022 : ℝ) - 5/10000 = 6.0215 := by norm_num
  rw [hw, hM, hA, hN]
  constructor <;> norm_num

/-- Tight certificate for the high corner: `2.3142175 ≤ high < 2.3142176`. -/
theorem catalystSurfaceDensityHigh_tight :
    (2.3142175 : ℝ) ≤ catalystSurfaceDensityHigh ∧
    catalystSurfaceDensityHigh < 2.3142176 := by
  rw [catalystSurfaceDensityHigh, catalystSurfaceDensity, massFractionPct,
    molarMassCat, specificSurfaceArea]
  have hw : (3.8 + (5/10000 : ℝ)) / 100 = 0.038005 := by norm_num
  have hM : (557.21 : ℝ) - 5/1000 = 557.205 := by norm_num
  have hA : (17.8 : ℝ) - 5/100 = 17.75 := by norm_num
  have hN : (6.022 : ℝ) + 5/10000 = 6.0225 := by norm_num
  rw [hw, hM, hA, hN]
  constructor <;> norm_num

/-- Envelope consistency, proved mechanically by chaining the three tight
certificates certified above.  In order:
`low < 2.3002240 < 2.3072010 ≤ raw`, `raw < 2.3072011 < 2.3142175 ≤ high`,
`low < 2.3002240 < 2.31`, and `2.31 < 2.3142175 ≤ high`. -/
theorem envelope_consistent_with_report :
    catalystSurfaceDensityLow ≤ catalystSurfaceDensityRaw ∧
    catalystSurfaceDensityRaw ≤ catalystSurfaceDensityHigh ∧
    catalystSurfaceDensityLow < (2.315 : ℝ) ∧ (2.305 : ℝ) ≤ catalystSurfaceDensityHigh ∧
    catalystSurfaceDensityLow < catalystReported ∧
    catalystReported < catalystSurfaceDensityHigh := by
  have hlo1 := catalystSurfaceDensityLow_tight.1
  have hlo2 := catalystSurfaceDensityLow_tight.2
  have hraw1 := catalystSurfaceDensityRaw_tight.1
  have hraw2 := catalystSurfaceDensityRaw_tight.2
  have hhi1 := catalystSurfaceDensityHigh_tight.1
  have hhi2 := catalystSurfaceDensityHigh_tight.2
  have hnum1 : (2.3002240:ℝ) < 2.3072010 := by norm_num
  have hnum2 : (2.3072011:ℝ) < 2.3142175 := by norm_num
  have hnum3 : (2.3002240:ℝ) < 2.315 := by norm_num
  have hnum4 : (2.305:ℝ) ≤ 2.3142175 := by norm_num
  have hnum5 : (2.3002240:ℝ) < 2.31 := by norm_num
  have hnum6 : (2.31:ℝ) < 2.3142175 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · have hrep : catalystReported = 2.31 := rfl
    rw [hrep]; linarith
  · have hrep : catalystReported = 2.31 := rfl
    rw [hrep]; linarith

end IChO2026T8
