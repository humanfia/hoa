import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A8: daily energy from methane combustion

The numerical declarations in `Problem inputs` transcribe the data printed in
the problem and its general constants sheet.  The later declarations derive
T4-A6 and T4-A7 inline before using the ideal-gas law for T4-A8.

The question prints the volumetric-flow value with unit `m^3`, omitting a time
denominator.  Therefore `intendedDailyEnergyRaw` is explicitly the result under
the natural intended reading that the printed volume is the volume delivered
in one day.  `dailyEnergyFromInterval` and
`missing_time_basis_changes_daily_energy` record why this reading is a real
condition rather than a consequence of the dimensionally incomplete datum.
-/

namespace IChO2026Problems.T4A8

open IChO2026Chem.Reporting

noncomputable section

/-! ## Problem inputs -/

/-- Printed standard formation enthalpy of methane at 298 K, in kJ/mol. -/
def methaneFormationEnthalpy298 : ℝ := -748 / 10

/-- Printed standard formation enthalpy of gaseous water at 298 K, in kJ/mol. -/
def waterGasFormationEnthalpy298 : ℝ := -2418 / 10

/-- Printed standard formation enthalpy of carbon dioxide at 298 K, in kJ/mol. -/
def carbonDioxideFormationEnthalpy298 : ℝ := -3935 / 10

/-- Printed constant-pressure heat capacity of methane, in J/(mol K). -/
def methaneHeatCapacity : ℝ := 35

/-- Printed constant-pressure heat capacity of gaseous water, in J/(mol K). -/
def waterGasHeatCapacity : ℝ := 34

/-- Printed constant-pressure heat capacity of oxygen, in J/(mol K). -/
def oxygenHeatCapacity : ℝ := 29

/-- Printed constant-pressure heat capacity of carbon dioxide, in J/(mol K). -/
def carbonDioxideHeatCapacity : ℝ := 37

/-- Initial temperature of the thermochemical data, in K. -/
def initialTemperature : ℝ := 298

/-- Combustion temperature requested in T4-A7 and T4-A8, in K. -/
def combustionTemperature : ℝ := 2000

/-- Methane pressure, obtained exactly from the printed `101.325 kPa`, in Pa. -/
def methanePressure : ℝ := 101325

/-- Temperature of methane before ignition, in K. -/
def methaneInletTemperature : ℝ := 298

/-- Universal gas constant printed on the constants sheet, in J/(mol K). -/
def gasConstant : ℝ := 8314 / 1000

/-- The printed numerical volume `2.2 * 10^5 m^3`, in m^3. -/
def printedMethaneVolume : ℝ := (22 / 10) * 10^5

/-! ## Inline derivation of the preceding thermochemical parts -/

/-- Enthalpy for `CH4 + 2 O2 -> CO2 + 2 H2O(g)` at 298 K, in kJ/mol.
The standard formation enthalpy of elemental oxygen in its standard state is
zero, so its (stoichiometrically doubled) term vanishes. -/
def reactionEnthalpy298 : ℝ :=
  carbonDioxideFormationEnthalpy298 + 2 * waterGasFormationEnthalpy298 -
    methaneFormationEnthalpy298

theorem reactionEnthalpy298_value :
    reactionEnthalpy298 = -8023 / 10 := by
  norm_num [reactionEnthalpy298, carbonDioxideFormationEnthalpy298,
    waterGasFormationEnthalpy298, methaneFormationEnthalpy298]

/-- Stoichiometric heat-capacity change for methane combustion, in J/(mol K). -/
def reactionHeatCapacity : ℝ :=
  carbonDioxideHeatCapacity + 2 * waterGasHeatCapacity -
    (methaneHeatCapacity + 2 * oxygenHeatCapacity)

theorem reactionHeatCapacity_value : reactionHeatCapacity = 12 := by
  norm_num [reactionHeatCapacity, carbonDioxideHeatCapacity,
    waterGasHeatCapacity, methaneHeatCapacity, oxygenHeatCapacity]

/-- Kirchhoff-law reaction enthalpy at 2000 K, in kJ/mol.  Division by
`1000` converts the heat-capacity correction from J/mol to kJ/mol. -/
def reactionEnthalpy2000 : ℝ :=
  reactionEnthalpy298 +
    reactionHeatCapacity * (combustionTemperature - initialTemperature) / 1000

theorem reactionEnthalpy2000_value :
    reactionEnthalpy2000 = -195469 / 250 := by
  norm_num [reactionEnthalpy2000, reactionEnthalpy298,
    reactionHeatCapacity, combustionTemperature, initialTemperature,
    carbonDioxideFormationEnthalpy298, waterGasFormationEnthalpy298,
    methaneFormationEnthalpy298, carbonDioxideHeatCapacity,
    waterGasHeatCapacity, methaneHeatCapacity, oxygenHeatCapacity]

theorem reactionEnthalpy2000_is_exothermic : reactionEnthalpy2000 < 0 := by
  rw [reactionEnthalpy2000_value]
  norm_num

/-! ## Ideal-gas amount and released energy -/

/-- Ideal-gas amount corresponding to `volume` at the printed inlet conditions,
in mol. -/
def methaneMolesForVolume (volume : ℝ) : ℝ :=
  methanePressure * volume / (gasConstant * methaneInletTemperature)

theorem methaneMolesForPrintedVolume_value :
    methaneMolesForVolume printedMethaneVolume =
      5572875000000 / 619393 := by
  norm_num [methaneMolesForVolume, printedMethaneVolume, methanePressure,
    gasConstant, methaneInletTemperature]

/-- Positive energy released by complete combustion of the given methane
volume, in J.  The minus sign converts the negative reaction enthalpy into the
positive magnitude requested as energy released; `1000` converts kJ to J. -/
def releasedEnergyForVolume (volume : ℝ) : ℝ :=
  methaneMolesForVolume volume * (-reactionEnthalpy2000) * 1000

/-- Raw result under the intended reading that the printed volume is delivered
over one day, in J/day. -/
def intendedDailyEnergyRaw : ℝ :=
  releasedEnergyForVolume printedMethaneVolume

theorem intendedDailyEnergyRaw_value :
    intendedDailyEnergyRaw = 4357297213500000000 / 619393 := by
  norm_num [intendedDailyEnergyRaw, releasedEnergyForVolume,
    methaneMolesForVolume, printedMethaneVolume, methanePressure, gasConstant,
    methaneInletTemperature, reactionEnthalpy2000, reactionEnthalpy298,
    reactionHeatCapacity, combustionTemperature, initialTemperature,
    carbonDioxideFormationEnthalpy298, waterGasFormationEnthalpy298,
    methaneFormationEnthalpy298, carbonDioxideHeatCapacity,
    waterGasHeatCapacity, methaneHeatCapacity, oxygenHeatCapacity]

theorem intendedDailyEnergyRaw_positive : 0 < intendedDailyEnergyRaw := by
  rw [intendedDailyEnergyRaw_value]
  norm_num

/-! ## Three-significant-figure report -/

/-- `7.03 * 10^12 J/day`, whose last displayed-place quantum is `10^10`. -/
def dailyEnergySubmission : NumericSubmission where
  rawValue := intendedDailyEnergyRaw
  reportedValue := 703 * 10^10
  reportingQuantum := 10^10

theorem dailyEnergySubmission_valid :
    ValidNumericSubmission intendedDailyEnergyRaw dailyEnergySubmission := by
  constructor
  · rfl
  · refine ⟨by norm_num [dailyEnergySubmission], ?_, ?_⟩
    · refine ⟨(703 : ℤ), ?_⟩
      norm_num [dailyEnergySubmission]
    · simp only [dailyEnergySubmission]
      rw [intendedDailyEnergyRaw_value]
      norm_num

theorem dailyEnergy_reported_value :
    dailyEnergySubmission.reportedValue = 7030000000000 := by
  norm_num [dailyEnergySubmission]

/-! ## Explicit source-gap model -/

/-- If the printed `2.2 * 10^5 m^3` is the volume accumulated over
`intervalDays`, this is the corresponding energy per day. -/
def dailyEnergyFromInterval (intervalDays : ℝ) : ℝ :=
  intendedDailyEnergyRaw / intervalDays

theorem dailyEnergy_if_interval_is_one_day :
    dailyEnergyFromInterval 1 = intendedDailyEnergyRaw := by
  simp [dailyEnergyFromInterval]

/-- Two possible time bases for the dimensionally incomplete printed volume
give different daily energies.  Thus the omitted denominator cannot be
recovered from the numerical volume alone. -/
theorem missing_time_basis_changes_daily_energy :
    dailyEnergyFromInterval 1 ≠ dailyEnergyFromInterval 2 := by
  rw [dailyEnergyFromInterval, dailyEnergyFromInterval,
    intendedDailyEnergyRaw_value]
  norm_num

#print axioms reactionEnthalpy2000_value
#print axioms methaneMolesForPrintedVolume_value
#print axioms intendedDailyEnergyRaw_value
#print axioms dailyEnergySubmission_valid
#print axioms missing_time_basis_changes_daily_energy

end

end IChO2026Problems.T4A8
