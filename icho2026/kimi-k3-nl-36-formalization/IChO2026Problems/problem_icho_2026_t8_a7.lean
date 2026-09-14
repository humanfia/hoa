import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T8.7

The source graph gives catalyst mass loading (in percent of the total loaded
composite) and the corresponding CO turnover frequency.  Since TOF is product
molecules per active catalyst molecule per hour, the CO rate per gram of loaded
composite is

`(catalyst mass fraction / catalyst molar mass) * Avogadro constant * TOF`.

Only the sign of a change is requested.  The positive common conversion factor
therefore cancels.  The graph's complete seven-point readout is retained below,
including the small fall in the central-value product between 2.9% and 3.8%.
Accordingly, `increases` is formalized as the coarse *overall* (lowest displayed
loading to highest displayed loading) trend asked for by the three-box question;
no monotonic interpolation between all experimental points is asserted.
-/

namespace IChO2026Problems.T8A7

open IChO2026Chem.Reporting

noncomputable section

/-! ## Source quantities and graph readout -/

/-- One point read from the T8.7 graph.  `catalystMassFraction` is a
dimensionless fraction of total loaded-composite mass, whereas the graph prints
the same number in percent.  `shownTofPerHour` has unit `h⁻¹`. -/
structure TofObservation where
  catalystMassFraction : ℝ
  shownTofPerHour : ℝ

/-- The catalyst molar mass printed in T8.5, `557.21 g mol⁻¹`. -/
def catalystMolarMass : ℝ := 55721 / 100

/-- The catalyst loading printed in T8.5 and T8.6, `3.8% = 0.038` of the
total loaded-composite mass. -/
def referenceCatalystMassFraction : ℝ := 38 / 1000

/-- The C₃N₄ specific surface area printed in T8.5, `17.8 m² g⁻¹`. -/
def supportSpecificSurfaceArea : ℝ := 89 / 5

/-- Exact area conversion used by T8.5. -/
def squareNanometresPerSquareMetre : ℝ := (10 : ℝ) ^ 18

/-- Graph point `(0.1%, 62 h⁻¹)`. -/
def observation01 : TofObservation := ⟨1 / 1000, 62⟩

/-- Graph point `(0.3%, 56 h⁻¹)`. -/
def observation03 : TofObservation := ⟨3 / 1000, 56⟩

/-- Graph point `(0.6%, 37 h⁻¹)`. -/
def observation06 : TofObservation := ⟨6 / 1000, 37⟩

/-- Graph point `(1.0%, 29 h⁻¹)`. -/
def observation10 : TofObservation := ⟨1 / 100, 29⟩

/-- Graph point `(2.0%, 15 h⁻¹)`. -/
def observation20 : TofObservation := ⟨2 / 100, 15⟩

/-- Graph point `(2.9%, 11 h⁻¹)`. -/
def observation29 : TofObservation := ⟨29 / 1000, 11⟩

/-- Graph point `(3.8%, 8 h⁻¹)`. -/
def observation38 : TofObservation := ⟨38 / 1000, 8⟩

/-- All graph points, in increasing-loading order.  Provenance:
`problem_image`, `T8_page-3.png`. -/
def tofObservations : List TofObservation :=
  [observation01, observation03, observation06, observation10,
    observation20, observation29, observation38]

/-- The displayed TOF labels are integral, so the source-report measurement
policy assigns them a last-displayed-place quantum of `1 h⁻¹`. -/
def tofDisplayQuantum : ℝ := 1

/-- The loading-times-TOF factor controlling the central-value rate.  The
omitted multiplier `N_A / M_cat` is positive and common to every point. -/
def centralRelativeRate (observation : TofObservation) : ℝ :=
  observation.catalystMassFraction * observation.shownTofPerHour

/-- Exact audit of all seven products read from the graph. -/
def CentralPlotAudit : Prop :=
  centralRelativeRate observation01 = 31 / 500 ∧
  centralRelativeRate observation03 = 21 / 125 ∧
  centralRelativeRate observation06 = 111 / 500 ∧
  centralRelativeRate observation10 = 29 / 100 ∧
  centralRelativeRate observation20 = 3 / 10 ∧
  centralRelativeRate observation29 = 319 / 1000 ∧
  centralRelativeRate observation38 = 38 / 125 ∧
  centralRelativeRate observation01 < centralRelativeRate observation38 ∧
  centralRelativeRate observation38 < centralRelativeRate observation29

/-- Carrier for the complete source-first numerical recount of the graph. -/
theorem central_plot_audit : CentralPlotAudit := by
  norm_num [CentralPlotAudit, centralRelativeRate, observation01, observation03,
    observation06, observation10, observation20, observation29, observation38]

/-! ## Total-mixture mass accounting and the T8.5 prerequisite -/

/-- `w` is a catalyst mass fraction precisely when the numerator is catalyst
mass and the denominator is total loaded-composite mass. -/
def IsCatalystMassFraction
    (catalystMass totalLoadedMass w : ℝ) : Prop :=
  0 ≤ catalystMass ∧ catalystMass ≤ totalLoadedMass ∧ 0 < totalLoadedMass ∧
    w = catalystMass / totalLoadedMass

/-- On a one-gram total-composite basis, 3.8 wt% means `0.038 g` catalyst and
`0.962 g` C₃N₄ support. -/
def ReferenceMassBalance : Prop :=
  IsCatalystMassFraction (38 / 1000) 1 referenceCatalystMassFraction ∧
    1 - referenceCatalystMassFraction = 481 / 500

theorem reference_mass_balance : ReferenceMassBalance := by
  norm_num [ReferenceMassBalance, IsCatalystMassFraction,
    referenceCatalystMassFraction]

/-- Catalyst molecules in one gram of loaded composite.  `avogadro` is kept
symbolic because only its positivity, not its decimal value, is needed here. -/
def catalystMoleculesPerLoadedGram
    (avogadro catalystMassFraction : ℝ) : ℝ :=
  catalystMassFraction / catalystMolarMass * avogadro

/-- C₃N₄ surface area, in nm², on the same one-gram total-composite basis. -/
def supportAreaNm2PerLoadedGram (catalystMassFraction : ℝ) : ℝ :=
  (1 - catalystMassFraction) * supportSpecificSurfaceArea *
    squareNanometresPerSquareMetre

/-- T8.5's catalyst-density expression, derived on the rigorous support-mass
basis without importing a previous-part answer. -/
def catalystMoleculesPerNm2 (avogadro : ℝ) : ℝ :=
  catalystMoleculesPerLoadedGram avogadro referenceCatalystMassFraction /
    supportAreaNm2PerLoadedGram referenceCatalystMassFraction

/-- A division-free specification of the T8.5 result. -/
def T8A5InlineSpec (avogadro density : ℝ) : Prop :=
  0 < avogadro ∧
    density * supportAreaNm2PerLoadedGram referenceCatalystMassFraction =
      catalystMoleculesPerLoadedGram avogadro referenceCatalystMassFraction

/-- Inline carrier for the T8.5 prerequisite. -/
theorem t8a5_inline_result (avogadro : ℝ) (hAvogadro : 0 < avogadro) :
    T8A5InlineSpec avogadro (catalystMoleculesPerNm2 avogadro) := by
  refine ⟨hAvogadro, ?_⟩
  unfold catalystMoleculesPerNm2
  apply div_mul_cancel₀
  norm_num [supportAreaNm2PerLoadedGram, referenceCatalystMassFraction,
    supportSpecificSurfaceArea, squareNanometresPerSquareMetre]

/-! ## The T8.6 prerequisite -/

/-- Coefficients of an acidic CO₂-to-CO reduction half-reaction. -/
structure ReductionCoefficients where
  carbonDioxide : ℕ
  protons : ℕ
  electrons : ℕ
  carbonMonoxide : ℕ
  water : ℕ

/-- Carbon, oxygen, hydrogen, and total-charge balance for the half-reaction
`CO₂ + H⁺ + e⁻ → CO + H₂O`, in that order. -/
def ReductionCoefficients.IsBalanced (r : ReductionCoefficients) : Prop :=
  r.carbonDioxide = r.carbonMonoxide ∧
    2 * r.carbonDioxide = r.carbonMonoxide + r.water ∧
    r.protons = 2 * r.water ∧
    r.protons = r.electrons

/-- The smallest positive balanced coefficients, independently reconstructed
from the source half-reaction request. -/
def co2ToCoReduction : ReductionCoefficients := ⟨1, 2, 2, 1, 1⟩

theorem co2ToCoReduction_balanced : co2ToCoReduction.IsBalanced := by
  norm_num [ReductionCoefficients.IsBalanced, co2ToCoReduction]

/-- Quantum yield in percent, exactly as defined on T8 page 2. -/
def quantumYieldPercent (reactedElectrons incidentPhotons : ℝ) : ℝ :=
  reactedElectrons / incidentPhotons * 100

/-- Source inputs for T8.6 in coherent scalar units. -/
def a6SampleMassGrams : ℝ := 1 / 100
def a6TurnoverFrequencyPerHour : ℝ := 8
def a6WavelengthMetres : ℝ := 390 / (10 : ℝ) ^ 9
def a6PowerWatts : ℝ := 1 / 20
def a6DurationSeconds : ℝ := 3600

/-- Reacted electrons in one hour, using the balanced two-electron CO₂-to-CO
stoichiometry and the source definition of TOF. -/
def a6ReactedElectrons (avogadro : ℝ) : ℝ :=
  (co2ToCoReduction.electrons : ℝ) * a6TurnoverFrequencyPerHour *
    (a6SampleMassGrams * referenceCatalystMassFraction /
      catalystMolarMass * avogadro)

/-- Incident photons in one hour from `E_photon = h*c/λ`.  Planck's constant
and the speed of light remain explicit parameters because their numerical
values are unnecessary for T8.7. -/
def a6IncidentPhotons (planckConstant lightSpeed : ℝ) : ℝ :=
  (a6PowerWatts * a6DurationSeconds) /
    (planckConstant * lightSpeed / a6WavelengthMetres)

/-- Exact, unrounded T8.6 expression reconstructed from the problem data. -/
def a6RawQuantumYieldPercent
    (avogadro planckConstant lightSpeed : ℝ) : ℝ :=
  quantumYieldPercent (a6ReactedElectrons avogadro)
    (a6IncidentPhotons planckConstant lightSpeed)

/-- Specification for the inline T8.6 prerequisite. -/
def T8A6InlineSpec
    (avogadro planckConstant lightSpeed result : ℝ) : Prop :=
  0 < a6IncidentPhotons planckConstant lightSpeed ∧
    result = a6ReactedElectrons avogadro /
      a6IncidentPhotons planckConstant lightSpeed * 100

/-- Inline carrier for T8.6.  The current qualitative trend does not depend on
the numerical values of these three positive physical constants. -/
theorem t8a6_inline_result
    (avogadro planckConstant lightSpeed : ℝ)
    (hAvogadro : 0 < avogadro)
    (hPlanck : 0 < planckConstant)
    (hLightSpeed : 0 < lightSpeed) :
    T8A6InlineSpec avogadro planckConstant lightSpeed
      (a6RawQuantumYieldPercent avogadro planckConstant lightSpeed) := by
  refine ⟨?_, rfl⟩
  have hWavelength : 0 < a6WavelengthMetres := by
    norm_num [a6WavelengthMetres]
  have hPhotonEnergy :
      0 < planckConstant * lightSpeed / a6WavelengthMetres :=
    div_pos (mul_pos hPlanck hLightSpeed) hWavelength
  exact div_pos (by norm_num [a6PowerWatts, a6DurationSeconds]) hPhotonEnergy

/-! ## Rate law and requested classification -/

/-- CO molecules formed per hour per gram of total loaded composite. -/
def coRatePerLoadedCompositeGram
    (avogadro catalystMassFraction tofPerHour : ℝ) : ℝ :=
  catalystMoleculesPerLoadedGram avogadro catalystMassFraction * tofPerHour

/-- The same rate normalized to one gram of C₃N₄ support rather than one gram
of total loaded composite.  This is an audit only; the primary source-report
basis is the total mixture. -/
def coRatePerSupportGram
    (avogadro catalystMassFraction tofPerHour : ℝ) : ℝ :=
  (catalystMassFraction / (1 - catalystMassFraction) /
    catalystMolarMass * avogadro) * tofPerHour

/-- Multiplication by the positive molecular-count conversion factor preserves
the ordering of the loading-times-TOF products. -/
theorem loaded_rate_order_iff
    (avogadro w₁ w₂ tof₁ tof₂ : ℝ)
    (hAvogadro : 0 < avogadro) :
    coRatePerLoadedCompositeGram avogadro w₁ tof₁ <
        coRatePerLoadedCompositeGram avogadro w₂ tof₂ ↔
      w₁ * tof₁ < w₂ * tof₂ := by
  have hMolarMass : 0 < catalystMolarMass := by
    norm_num [catalystMolarMass]
  have hFactor : 0 < avogadro / catalystMolarMass :=
    div_pos hAvogadro hMolarMass
  have h₁ :
      coRatePerLoadedCompositeGram avogadro w₁ tof₁ =
        (avogadro / catalystMolarMass) * (w₁ * tof₁) := by
    simp only [coRatePerLoadedCompositeGram, catalystMoleculesPerLoadedGram]
    ring
  have h₂ :
      coRatePerLoadedCompositeGram avogadro w₂ tof₂ =
        (avogadro / catalystMolarMass) * (w₂ * tof₂) := by
    simp only [coRatePerLoadedCompositeGram, catalystMoleculesPerLoadedGram]
    ring
  rw [h₁, h₂]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h hFactor.le
  · intro h
    exact mul_lt_mul_of_pos_left h hFactor

/-- The three and only three boxes printed in T8.7. -/
inductive RateTrend
  | increases
  | decreases
  | unchanged
  deriving DecidableEq, Repr

/-- Concrete order semantics for each answer box. -/
def RateTrend.Describes (trend : RateTrend) (initial final : ℝ) : Prop :=
  match trend with
  | .increases => initial < final
  | .decreases => final < initial
  | .unchanged => final = initial

/-- Candidate classification preserved from the authorized Kimi draft. -/
def coRateTrend : RateTrend := .increases

/-- Source-grounded specification of the word "overall": compare the lowest
and highest displayed loadings.  The conclusion is robust to the half-unit
TOF display intervals dictated by the source measurement policy. -/
def CoRateTrendSpec (trend : RateTrend) : Prop :=
  (∀ avogadro : ℝ, 0 < avogadro →
    trend.Describes
      (coRatePerLoadedCompositeGram avogadro
        observation01.catalystMassFraction observation01.shownTofPerHour)
      (coRatePerLoadedCompositeGram avogadro
        observation38.catalystMassFraction observation38.shownTofPerHour)) ∧
  ∀ (avogadro actualLowTof actualHighTof : ℝ),
      0 < avogadro →
      ConsistentMeasurement actualLowTof observation01.shownTofPerHour
        tofDisplayQuantum →
      ConsistentMeasurement actualHighTof observation38.shownTofPerHour
        tofDisplayQuantum →
      trend.Describes
        (coRatePerLoadedCompositeGram avogadro
          observation01.catalystMassFraction actualLowTof)
        (coRatePerLoadedCompositeGram avogadro
          observation38.catalystMassFraction actualHighTof)

/-- The requested output carrier `co_rate_trend`. -/
theorem co_rate_trend : CoRateTrendSpec coRateTrend := by
  constructor
  · intro avogadro hAvogadro
    change
      coRatePerLoadedCompositeGram avogadro
          observation01.catalystMassFraction observation01.shownTofPerHour <
        coRatePerLoadedCompositeGram avogadro
          observation38.catalystMassFraction observation38.shownTofPerHour
    rw [loaded_rate_order_iff _ _ _ _ _ hAvogadro]
    norm_num [observation01, observation38]
  · intro avogadro actualLowTof actualHighTof hAvogadro hLow hHigh
    have hLowUpper : actualLowTof ≤ 125 / 2 := by
      have h := (abs_le.mp hLow.2).2
      norm_num [observation01, tofDisplayQuantum] at h ⊢
      linarith
    have hHighLower : 15 / 2 ≤ actualHighTof := by
      have h := (abs_le.mp hHigh.2).1
      norm_num [observation38, tofDisplayQuantum] at h ⊢
      linarith
    change
      coRatePerLoadedCompositeGram avogadro
          observation01.catalystMassFraction actualLowTof <
        coRatePerLoadedCompositeGram avogadro
          observation38.catalystMassFraction actualHighTof
    rw [loaded_rate_order_iff _ _ _ _ _ hAvogadro]
    norm_num [observation01, observation38]
    linarith

/-- The same endpoint conclusion is unchanged if the phrase "per gram of
C₃N₄" is instead audited on a support-only mass basis. -/
theorem support_basis_endpoint_robustness :
    ∀ (avogadro actualLowTof actualHighTof : ℝ),
      0 < avogadro →
      ConsistentMeasurement actualLowTof observation01.shownTofPerHour
        tofDisplayQuantum →
      ConsistentMeasurement actualHighTof observation38.shownTofPerHour
        tofDisplayQuantum →
      coRatePerSupportGram avogadro observation01.catalystMassFraction actualLowTof <
        coRatePerSupportGram avogadro observation38.catalystMassFraction actualHighTof := by
  intro avogadro actualLowTof actualHighTof hAvogadro hLow hHigh
  have hLowUpper : actualLowTof ≤ 125 / 2 := by
    have h := (abs_le.mp hLow.2).2
    norm_num [observation01, tofDisplayQuantum] at h ⊢
    linarith
  have hHighLower : 15 / 2 ≤ actualHighTof := by
    have h := (abs_le.mp hHigh.2).1
    norm_num [observation38, tofDisplayQuantum] at h ⊢
    linarith
  have hMolarMass : 0 < catalystMolarMass := by
    norm_num [catalystMolarMass]
  have hFactor : 0 < avogadro / catalystMolarMass :=
    div_pos hAvogadro hMolarMass
  have hLowRate :
      coRatePerSupportGram avogadro observation01.catalystMassFraction
          actualLowTof =
        (avogadro / catalystMolarMass) *
          ((observation01.catalystMassFraction /
            (1 - observation01.catalystMassFraction)) * actualLowTof) := by
    unfold coRatePerSupportGram
    ring
  have hHighRate :
      coRatePerSupportGram avogadro observation38.catalystMassFraction
          actualHighTof =
        (avogadro / catalystMolarMass) *
          ((observation38.catalystMassFraction /
            (1 - observation38.catalystMassFraction)) * actualHighTof) := by
    unfold coRatePerSupportGram
    ring
  rw [hLowRate, hHighRate]
  apply mul_lt_mul_of_pos_left _ hFactor
  norm_num [observation01, observation38]
  linarith

/-- The displayed central values are not strictly increasing at every adjacent
point: the 2.9% product exceeds the 3.8% product.  Keeping this theorem beside
the output prevents the coarse classification from being read as a stronger
monotonicity claim. -/
theorem final_central_step_decreases :
    centralRelativeRate observation38 < centralRelativeRate observation29 := by
  norm_num [centralRelativeRate, observation38, observation29]

/-! ## Solve-phase result contracts -/

/-- The unrounded semantic result combines the derived overall classification
with the complete graph audit, including the nonmonotone last central step. -/
def RawResult : Prop :=
  CoRateTrendSpec coRateTrend ∧ CentralPlotAudit

/-- `co_rate_trend` has an exact-symbolic reporting policy, so reporting does
not round or otherwise change the classification. -/
def ReportedResult : Prop :=
  CoRateTrendSpec coRateTrend

/-- Raw result contract for `co_rate_trend`. -/
theorem raw_result : RawResult := by
  exact ⟨co_rate_trend, central_plot_audit⟩

/-- Reported result contract for `co_rate_trend`. -/
theorem reported_result : ReportedResult := by
  exact co_rate_trend

end

end IChO2026Problems.T8A7
