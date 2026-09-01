import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T8 (Recycling of Carbon Dioxide), part 8.5 — `icho_2026_t8_a5`

**Question (verbatim, problem text).** Calculate the number of catalytic molecules
per nm², 𝑁_cat, of C₃N₄ loaded with **1**, when the mass fraction of catalyst,
ω_cat = 3.8 %, if the specific surface area of C₃N₄ is 17.8 m² g⁻¹.
M_cat = 557.21 g mol⁻¹.

## Assumption / target split

Problem-stipulated data (provenance `problem_text`, exact as printed):
* `omegaCat = 0.038` — mass fraction of catalyst **1** in the loaded material.
  The numerator is the catalyst mass; the denominator is the *total mixture mass*
  (catalyst + C₃N₄ support).  The problem states no other basis, so the
  total-mixture basis is used and the mass-balance equation is solved before
  substitution.
* `specificSurfaceArea = 17.8` — specific surface area of the C₃N₄ support,
  in m² g⁻¹ (per gram of support).
* `molarMassCat = 557.21` — molar mass of catalyst **1**, in g mol⁻¹.

Universal constant (provenance `trusted_general_law`):
* `avogadroConstant = 6.02214076 × 10²³ mol⁻¹` — the Avogadro constant, an exact
  defining constant of the SI (2019 revision); needed to convert amount of
  substance into a molecule count.

Exact unit conversion (provenance `trusted_general_law`):
* 1 m² = 10¹⁸ nm² (SI prefix relation).

**Target.** The surface density N_cat in molecules nm⁻², raw and unrounded, and
its reported value at the project default of three significant figures
(tie rule: half away from zero).

## Derivation encoded below

For any loaded sample with support mass `m_s > 0` and catalyst mass `m_c > 0`:
* mass-fraction law: `m_c / (m_c + m_s) = ω_cat`, hence
  `m_c / m_s = ω_cat / (1 − ω_cat)`;
* catalyst molecules: `N = m_c · N_A / M_cat`;
* support surface area: `A = S · m_s · 10¹⁸ nm²`;
* surface density: `N_cat = N / A = (ω_cat / (1 − ω_cat)) · N_A / (M_cat · S · 10¹⁸)`,
  independent of the sample size.

The raw value is the exact rational `5721033722/2385360289 ≈ 2.398394`;
the certified enclosure is `(1199/500, 2399/1000) = (2.398, 2.399)`; the reported
value at quantum `0.01` is `2.40` molecules nm⁻².
-/

namespace IChO2026T8A5

open IChO2026Chem.Reporting

/-- Mass fraction of catalyst **1** in the loaded C₃N₄ material,
ω_cat = 3.8 % = 0.038 (catalyst mass over total mixture mass).
Problem-stipulated, exact as printed (T8, part 8.5). -/
noncomputable def omegaCat : ℝ := 0.038

/-- Specific surface area of the crystalline C₃N₄ support, S = 17.8 m² g⁻¹.
Problem-stipulated, exact as printed (T8, part 8.5). -/
noncomputable def specificSurfaceArea : ℝ := 17.8

/-- Molar mass of catalyst **1**, M_cat = 557.21 g mol⁻¹.
Problem-stipulated, exact as printed (T8, part 8.5). -/
noncomputable def molarMassCat : ℝ := 557.21

/-- Avogadro constant N_A = 6.02214076 × 10²³ mol⁻¹, an exact defining constant
of the SI (2019 revision).  Provenance: `trusted_general_law`. -/
noncomputable def avogadroConstant : ℝ := 6.02214076e23

/-- Exact SI prefix relation: one square metre in square nanometres,
1 m² = 10¹⁸ nm². -/
noncomputable def squareMetreInNm2 : ℝ := 1e18

/-- A sample of catalyst **1** loaded on crystalline C₃N₄, as specified in
T8 part 8.5.  The mass-fraction field binds the catalyst mass to the total
mixture mass (catalyst + support); the problem stipulates no other basis. -/
structure LoadedSample where
  /-- Mass of the C₃N₄ support in the sample (g). -/
  supportMass : ℝ
  /-- Mass of catalyst **1** in the sample (g). -/
  catalystMass : ℝ
  supportMass_pos : 0 < supportMass
  catalystMass_pos : 0 < catalystMass
  /-- The stipulated mass-fraction law ω_cat = m_cat / (m_cat + m_support). -/
  mass_fraction : catalystMass / (catalystMass + supportMass) = omegaCat

/-- Number of catalyst molecules in a loaded sample:
N = (m_cat / M_cat) · N_A. -/
noncomputable def catalystMolecules (s : LoadedSample) : ℝ :=
  s.catalystMass / molarMassCat * avogadroConstant

/-- Surface area of the sample's C₃N₄ support, in nm²:
A = S · m_support · 10¹⁸. -/
noncomputable def supportAreaNm2 (s : LoadedSample) : ℝ :=
  specificSurfaceArea * s.supportMass * squareMetreInNm2

/-- Catalyst surface density of a loaded sample, in molecules nm⁻²:
the number of catalyst molecules divided by the support surface area. -/
noncomputable def surfaceDensity (s : LoadedSample) : ℝ :=
  catalystMolecules s / supportAreaNm2 s

/-- The raw, unrounded catalyst surface density (molecules nm⁻²), derived end to
end from the problem-stipulated data with no intermediate rounding:
N_cat = (ω_cat / (1 − ω_cat)) · N_A / (M_cat · S · 10¹⁸). -/
noncomputable def rawSurfaceDensity : ℝ :=
  omegaCat / (1 - omegaCat) * avogadroConstant /
    (molarMassCat * specificSurfaceArea * squareMetreInNm2)

/-- Problem-specific derivation specification for T8-8.5: every loaded sample
obeying the stipulated mass-fraction law has surface density equal to the raw
closed-form expression `rawSurfaceDensity` (sample-size independence). -/
def CatalystSurfaceDensitySpec : Prop :=
  ∀ s : LoadedSample, surfaceDensity s = rawSurfaceDensity

/-- Mass balance from the stipulated mass fraction: the catalyst-to-support mass
ratio equals ω_cat / (1 − ω_cat).  This is the algebraic heart of the raw
derivation, kept as a named step for the proof stage. -/
theorem catalyst_support_mass_ratio (s : LoadedSample) :
    s.catalystMass / s.supportMass = omegaCat / (1 - omegaCat) := by
  have hω1 : (1 : ℝ) - omegaCat ≠ 0 := by
    unfold omegaCat
    norm_num
  have hsum : s.catalystMass + s.supportMass ≠ 0 :=
    ne_of_gt (add_pos s.catalystMass_pos s.supportMass_pos)
  have hms : s.supportMass ≠ 0 := ne_of_gt s.supportMass_pos
  have h1 : s.catalystMass = omegaCat * (s.catalystMass + s.supportMass) := by
    have h := s.mass_fraction
    rwa [div_eq_iff hsum] at h
  rw [div_eq_div_iff hms hω1]
  linarith [h1]

/-- Exact rational evaluation of the raw surface density (target-local
computation bridge): pure exact rational arithmetic on the problem-stipulated
literals gives `rawSurfaceDensity = 5721033722/2385360289 ≈ 2.398394`
molecules nm⁻². -/
theorem rawSurfaceDensity_eq :
    rawSurfaceDensity = (5721033722 : ℝ) / 2385360289 := by
  unfold rawSurfaceDensity omegaCat specificSurfaceArea molarMassCat
    avogadroConstant squareMetreInNm2
  norm_num

/-- Raw result contract (answer-blind): the derivation specification holds for
every admissible loaded sample, and the raw surface density is certified to lie
in the non-degenerate rational enclosure (1199/500, 2399/1000) = (2.398, 2.399).
The raw value itself is the exact expression `rawSurfaceDensity`
(= 5721033722/2385360289 ≈ 2.398394), not a rounded decimal. -/
theorem catalyst_surface_density_raw :
    (IChO2026T8A5.CatalystSurfaceDensitySpec) ∧
      (((1199 : ℝ) / 500) ≤ (IChO2026T8A5.rawSurfaceDensity) ∧
        (IChO2026T8A5.rawSurfaceDensity) ≤ ((2399 : ℝ) / 1000)) := by
  have hM : molarMassCat ≠ 0 := by
    unfold molarMassCat
    norm_num
  have hS : specificSurfaceArea ≠ 0 := by
    unfold specificSurfaceArea
    norm_num
  have hC : squareMetreInNm2 ≠ 0 := by
    unfold squareMetreInNm2
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hms : s.supportMass ≠ 0 := ne_of_gt s.supportMass_pos
    have hratio := catalyst_support_mass_ratio s
    unfold surfaceDensity catalystMolecules supportAreaNm2 rawSurfaceDensity
    rw [← hratio]
    field_simp
  · rw [rawSurfaceDensity_eq]
    norm_num
  · rw [rawSurfaceDensity_eq]
    norm_num

/-- Reported result contract (answer-blind): at the predeclared project default
of three significant figures — quantum 0.01 at this magnitude, ties away from
zero — the raw surface density is reported as 2.40 molecules nm⁻². -/
theorem catalyst_surface_density_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026T8A5.rawSurfaceDensity) ((240 : ℝ) / 100) ((1 : ℝ) / 100) := by
  have hraw_nn : (0 : ℝ) ≤ rawSurfaceDensity := by
    rw [rawSurfaceDensity_eq]
    norm_num
  refine ⟨by norm_num, ⟨240, by norm_num⟩, ?_⟩
  rw [if_pos hraw_nn, rawSurfaceDensity_eq]
  constructor <;> norm_num

/-- The solver-owned numeric submission, keeping the exact raw value separate
from the final reported value and recording the reporting quantum explicitly. -/
noncomputable def submission : NumericSubmission where
  rawValue := rawSurfaceDensity
  reportedValue := 2.40
  reportingQuantum := 0.01

/-- The submission is valid: its raw value is the derived raw expression and the
reported value sits at the declared quantum. -/
theorem submission_valid :
    ValidNumericSubmission rawSurfaceDensity submission := by
  refine ⟨rfl, ?_⟩
  change IChO2026Chem.Reporting.ReportsAtQuantum rawSurfaceDensity 2.40 0.01
  have h240 : (2.40 : ℝ) = 240 / 100 := by norm_num
  have h001 : (0.01 : ℝ) = 1 / 100 := by norm_num
  rw [h240, h001]
  exact catalyst_surface_density_reported

end IChO2026T8A5
