import IChO2026Chem.Reporting

/-!
# IChO 2026 T8-A6: quantum yield of CO formation

This file keeps the quantities printed in the problem separate from the
physical constants and from every derived quantity.  All calculations are in
one consistent set of units: grams, moles, seconds, joules, metres, and hours.
The factor `secondsPerHour` is inserted exactly once when the photon flux is
compared with the hourly turnover frequency.
-/

namespace IChO2026Problems.T8A6

open IChO2026Chem.Reporting

noncomputable section

/-! ## Source data -/

/-- The numerical data printed in T8-A6, converted to coherent units. -/
structure PrintedInputs where
  supportBatchMass_g : ℝ
  catalystMassFraction : ℝ
  catalystMolarMass_gPerMol : ℝ
  turnoverFrequency_perHour : ℝ
  wavelength_m : ℝ
  lampPower_W : ℝ

/--
The source values are `10 mg`, `3.8%`, `557.21 g mol⁻¹`, `8 h⁻¹`,
`390 nm`, and `50 mW`, respectively.  In accordance with the task contract,
they are used exactly as printed; there is no intermediate rounding.
-/
def printedInputs : PrintedInputs where
  supportBatchMass_g := 10 / 1000
  catalystMassFraction := 38 / 1000
  catalystMolarMass_gPerMol := 55721 / 100
  turnoverFrequency_perHour := 8
  wavelength_m := 390 / 10 ^ 9
  lampPower_W := 50 / 1000

/-! ## Trusted general laws and exact SI constants -/

/-- Exact Avogadro constant in `mol⁻¹`. -/
def avogadro_perMol : ℝ := 602214076 * 10 ^ 15

/-- Exact Planck constant in `J s`. -/
def planck_Js : ℝ := 662607015 / 10 ^ 42

/-- Exact speed of light in `m s⁻¹`. -/
def lightSpeed_mPerS : ℝ := 299792458

/-- Unit conversion used to compare photon flux with an hourly TOF. -/
def secondsPerHour : ℝ := 3600

/--
The acidic reduction half-reaction is
`CO₂ + 2 H⁺ + 2 e⁻ ⟶ CO + H₂O`, so one CO requires two electrons.
-/
def electronsPerCO : ℝ := 2

/-- The displayed half-reaction conserves C, O, H, and electric charge. -/
theorem co_half_reaction_balanced :
    (1 : ℤ) = 1 ∧
    (2 : ℤ) = 1 + 1 ∧
    (2 : ℤ) = 2 ∧
    (2 : ℤ) + 2 * (-1) = 0 := by
  norm_num

/-- Charge balance uniquely forces the electron coefficient to be two. -/
theorem electron_coefficient_from_charge_balance
    (electronCoefficient : ℝ)
    (hcharge : 2 + electronCoefficient * (-1) = 0) :
    electronCoefficient = electronsPerCO := by
  norm_num [electronsPerCO] at hcharge ⊢
  linarith

/-! ## Derived chemistry and photophysics -/

/-- Moles of catalyst in the stated supported-catalyst batch. -/
def catalystAmount_mol (x : PrintedInputs) : ℝ :=
  x.supportBatchMass_g * x.catalystMassFraction /
    x.catalystMolarMass_gPerMol

/-- Number of catalyst molecules represented by the stated loading. -/
def catalystMolecules (x : PrintedInputs) : ℝ :=
  catalystAmount_mol x * avogadro_perMol

/-- The TOF definition gives this many CO molecules per hour. -/
def coMoleculesPerHour (x : PrintedInputs) : ℝ :=
  catalystMolecules x * x.turnoverFrequency_perHour

/-- Electron equivalents consumed per hour by CO formation. -/
def reactedElectronsPerHour (x : PrintedInputs) : ℝ :=
  coMoleculesPerHour x * electronsPerCO

/-- Photon energy from the Planck relation `E = h c / λ`. -/
def photonEnergy_J (x : PrintedInputs) : ℝ :=
  planck_Js * lightSpeed_mPerS / x.wavelength_m

/-- Incident photons in one hour from `N = P t / E`. -/
def incidentPhotonsPerHour (x : PrintedInputs) : ℝ :=
  x.lampPower_W * secondsPerHour / photonEnergy_J x

/-- The quantum-yield formula supplied by the problem, expressed in percent. -/
def quantumYieldPercent (x : PrintedInputs) : ℝ :=
  reactedElectronsPerHour x / incidentPhotonsPerHour x * 100

theorem catalyst_amount_exact :
    catalystAmount_mol printedInputs = 19 / 27860500 := by
  norm_num [catalystAmount_mol, printedInputs]

theorem catalyst_molecule_count_exact :
    catalystMolecules printedInputs =
      22884134888000000000000 / 55721 := by
  norm_num [catalystMolecules, catalystAmount_mol, printedInputs,
    avogadro_perMol]

theorem co_molecule_rate_exact :
    coMoleculesPerHour printedInputs =
      183073079104000000000000 / 55721 := by
  norm_num [coMoleculesPerHour, catalystMolecules, catalystAmount_mol,
    printedInputs, avogadro_perMol]

theorem reacted_electron_rate_exact :
    reactedElectronsPerHour printedInputs =
      366146158208000000000000 / 55721 := by
  norm_num [reactedElectronsPerHour, electronsPerCO, coMoleculesPerHour,
    catalystMolecules, catalystAmount_mol, printedInputs, avogadro_perMol]

theorem photon_energy_exact :
    photonEnergy_J printedInputs =
      6621486190496429 / 13000000000000000000000000000000000 := by
  norm_num [photonEnergy_J, planck_Js, lightSpeed_mPerS, printedInputs]

theorem incident_photon_rate_exact :
    incidentPhotonsPerHour printedInputs =
      2340000000000000000000000000000000000 / 6621486190496429 := by
  norm_num [incidentPhotonsPerHour, photonEnergy_J, secondsPerHour,
    planck_Js, lightSpeed_mPerS, printedInputs]

/--
Exact unrounded requested output.  Its decimal value begins
`1.859410161368362... %`.
-/
theorem co_quantum_yield_raw :
    quantumYieldPercent printedInputs =
      18940872892793693114789369 / 10186495312500000000000000 := by
  norm_num [quantumYieldPercent, reactedElectronsPerHour,
    coMoleculesPerHour, catalystMolecules, catalystAmount_mol,
    incidentPhotonsPerHour, photonEnergy_J, electronsPerCO,
    avogadro_perMol, planck_Js, lightSpeed_mPerS, secondsPerHour,
    printedInputs]

/-! ## Final three-significant-figure report -/

/-- Solver-owned answer with raw value and reporting boundary kept separate. -/
def coQuantumYieldSubmission : NumericSubmission where
  rawValue := quantumYieldPercent printedInputs
  reportedValue := 186 / 100
  reportingQuantum := 1 / 100

/-- `1.86%` is the nearest `0.01%`, hence the requested three-significant-figure result. -/
theorem co_quantum_yield_reported :
    ValidNumericSubmission (quantumYieldPercent printedInputs)
      coQuantumYieldSubmission := by
  constructor
  · rfl
  · rw [ReportsAtQuantum]
    refine ⟨?_, ?_, ?_⟩
    · norm_num [coQuantumYieldSubmission]
    · refine ⟨186, ?_⟩
      norm_num [coQuantumYieldSubmission]
    · simp only [coQuantumYieldSubmission]
      rw [co_quantum_yield_raw]
      norm_num [coQuantumYieldSubmission]

/--
Complete requested output: the exact raw percentage together with its
three-significant-figure report `1.86%` (nearest `0.01%`).
-/
theorem co_quantum_yield_final :
    quantumYieldPercent printedInputs =
        18940872892793693114789369 / 10186495312500000000000000 ∧
      ReportsAtQuantum (quantumYieldPercent printedInputs) (186 / 100) (1 / 100) := by
  constructor
  · exact co_quantum_yield_raw
  · simpa [coQuantumYieldSubmission, ValidNumericSubmission] using
      co_quantum_yield_reported.2

#print axioms co_half_reaction_balanced
#print axioms electron_coefficient_from_charge_balance
#print axioms co_quantum_yield_raw
#print axioms co_quantum_yield_reported
#print axioms co_quantum_yield_final

end

end IChO2026Problems.T8A6
