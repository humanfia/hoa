import Mathlib
import IChO2026Chem

/-! # IChO 2026 Theory — T4-A6

Enthalpy of combustion of methane at 298 K, all species gaseous.

Source: 58th IChO Uzbekistan 2026, Theory Q4-2, subquestion 4.6.
-/

namespace IChO2026.Problem

/-- Standard enthalpies of formation at 298 K (kJ mol⁻¹) as given in the
problem data table. -/
def dHf_CH4  : ℝ := -74.8
def dHf_H2O  : ℝ := -241.8
def dHf_CO2  : ℝ := -393.5
def dHf_O2   : ℝ := 0      -- oxygen is an element in its standard state

/-- One mole of methane combustion:
    CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g) -/
def reactionEnthalpy298 : ℝ :=
  (dHf_CO2 + 2 * dHf_H2O) - (dHf_CH4 + 2 * dHf_O2)

theorem reactionEnthalpy298_value :
    reactionEnthalpy298 = -802.3 := by
  unfold reactionEnthalpy298 dHf_CH4 dHf_H2O dHf_CO2 dHf_O2
  norm_num

/-- Three-significant-figure reporting convention (uniform blind-evaluation
default).  The raw value is already exact here, so the reported value equals
the raw value. -/
theorem reactionEnthalpy298_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum reactionEnthalpy298 (-802.3) (0.1) := by
  unfold reactionEnthalpy298 dHf_CH4 dHf_H2O dHf_CO2 dHf_O2
  refine ⟨by norm_num, ⟨-8023, by norm_num⟩, ?_⟩
  norm_num

/-- The submission records the raw and reported values as required by the
answer-blind protocol. -/
def submission : IChO2026Chem.Reporting.NumericSubmission where
  rawValue := reactionEnthalpy298
  reportedValue := -802.3
  reportingQuantum := 0.1

theorem submission_valid :
    IChO2026Chem.Reporting.ValidNumericSubmission reactionEnthalpy298 submission :=
  ⟨rfl, reactionEnthalpy298_reported⟩

end IChO2026.Problem
