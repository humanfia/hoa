/- USER: Keep these narrow imports; Family3 grounding forbids umbrella `import Mathlib`. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import AFPS2017.Analytics.Provenance

/-!
# Signal observations for AFPS2017 analytics

This module implements the narrow signal-observation contract from the
sanitized source `afps2017.analytics.contract:question`. The two reported M-18
relative peak intensities are transcribed from
`afps2017.supplement:Supplementary-Figure-19` in the publisher supplement with
content identifier
`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`.

Relative peak intensity, crude yield, and UV-feature measurements are kept in
distinct structures with no coercions between them. The reported ratio below
is only exact arithmetic on the two transcribed relative peak intensities; it
does not establish purity, identity, coupling success, yield, or statistical
comparability.
-/

namespace AFPS2017.Analytics

/-- A percentage represented by a real value in the closed interval `[0, 100]`. -/
structure Percent : Type where
  value : ℝ
  nonnegative : 0 ≤ value
  atMostHundred : value ≤ 100

/-- The reagent and recorded conditions for a deprotection observation. -/
structure DeprotectionCondition : Type where
  reagent : String
  reagentPercent : Percent
  temperatureCelsius : ℝ

/-- A relative peak intensity, kept distinct from a crude-yield observation. -/
structure RelativePeakIntensity : Type where
  percent : Percent

/-- A relative peak intensity paired with the condition under which it was observed. -/
structure RelativePeakIntensityObservation : Type where
  condition : DeprotectionCondition
  intensity : RelativePeakIntensity

/-- A crude-yield observation, with no coercion from or to relative peak intensity. -/
structure CrudeYieldObservation : Type where
  percent : Percent

/-- Nonnegative measurements of one UV feature, without a chemical interpretation. -/
structure UVFeature : Type where
  area : ℝ
  area_nonnegative : 0 ≤ area
  fullWidthAtHalfMaximum : ℝ
  fullWidthAtHalfMaximum_nonnegative : 0 ≤ fullWidthAtHalfMaximum
  height : ℝ
  height_nonnegative : 0 ≤ height

/--
The Supplementary Figure 19 observation recorded for 2.5% piperazine at 90°C:
7.5% relative M-18 peak intensity.
-/
noncomputable def m18PiperazineIntensity : ReportedDatum RelativePeakIntensityObservation :=
  { source := afps2017Supplement
      "Supplementary-Figure-19: 2.5% piperazine, 7.5% relative M-18 intensity at 90 C"
    value :=
      { condition :=
          { reagent := "piperazine"
            reagentPercent :=
              { value := 5 / 2
                nonnegative := by norm_num
                atMostHundred := by norm_num }
            temperatureCelsius := 90 }
        intensity :=
          { percent :=
              { value := 15 / 2
                nonnegative := by norm_num
                atMostHundred := by norm_num } } } }

/--
The Supplementary Figure 19 observation recorded for 20% piperidine at 90°C:
45% relative M-18 peak intensity.
-/
noncomputable def m18PiperidineIntensity : ReportedDatum RelativePeakIntensityObservation :=
  { source := afps2017Supplement
      "Supplementary-Figure-19: 20% piperidine, 45% relative M-18 intensity at 90 C"
    value :=
      { condition :=
          { reagent := "piperidine"
            reagentPercent :=
              { value := 20
                nonnegative := by norm_num
                atMostHundred := by norm_num }
            temperatureCelsius := 90 }
        intensity :=
          { percent :=
              { value := 45
                nonnegative := by norm_num
                atMostHundred := by norm_num } } } }

/-- The two reported relative M-18 peak intensities satisfy `45 / 7.5 = 6`. -/
theorem m18_relativePeakIntensity_ratio_eq_six :
    m18PiperidineIntensity.value.intensity.percent.value /
      m18PiperazineIntensity.value.intensity.percent.value = 6 := by
  norm_num [m18PiperidineIntensity, m18PiperazineIntensity]

end AFPS2017.Analytics
