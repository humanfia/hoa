import IChO2026Chem.Reporting

/-!
# IChO 2026 T7-A2: annual methane requirement

This file formalizes the material balance shown in Fig. 1 and the requested
three-significant-figure numerical report.  The source data and the derived
quantities are deliberately separated below.
-/

namespace IChO2026Problems.T7A2

open IChO2026Chem.Reporting

noncomputable section

/-! ## Problem inputs -/

/-- Printed relative atomic mass of hydrogen (periodic table, PDF page 5). -/
def hydrogenAtomicMass : ℝ := 1008 / 1000

/-- Printed relative atomic mass of carbon (periodic table, PDF page 5). -/
def carbonAtomicMass : ℝ := 1201 / 100

/-- Printed relative atomic mass of nitrogen (periodic table, PDF page 5). -/
def nitrogenAtomicMass : ℝ := 1401 / 100

/-- Requested annual mass of actually produced ammonia, in tons. -/
def annualAmmoniaMass : ℝ := 660000

/-- The stated 97.0 percent overall yield, treated as the exact stipulated
fraction `97 / 100` under the task's measurement policy. -/
def overallYield : ℝ := 97 / 100

/-! ## Fig. 1 material-balance model

Let `x` be the methane feed and `y` the steam-reformed amount, in a common
molar unit.  Quantitative steam reforming consumes `y` methane, so `x-y`
methane reaches partial oxidation.  From `2 CH4 + O2 -> 2 CO + 4 H2`, the
oxygen requirement is `(x-y)/2`.  The diagram supplies four nitrogen per
oxygen.  Quantitative water-gas shift converts every CO to CO2 and adds one H2
per CO; scrubbing removes CO2 without changing the N2 and H2 amounts.
-/

def methaneAfterReforming (x y : ℝ) : ℝ := x - y

def carbonMonoxideAfterReforming (_x y : ℝ) : ℝ := y

def hydrogenAfterReforming (_x y : ℝ) : ℝ := 3 * y

def oxygenForPartialOxidation (x y : ℝ) : ℝ := (x - y) / 2

def nitrogenAfterScrubber (x y : ℝ) : ℝ :=
  4 * oxygenForPartialOxidation x y

def carbonMonoxideAfterPartialOxidation (x y : ℝ) : ℝ :=
  carbonMonoxideAfterReforming x y + methaneAfterReforming x y

def hydrogenAfterPartialOxidation (x y : ℝ) : ℝ :=
  hydrogenAfterReforming x y + 2 * methaneAfterReforming x y

def hydrogenAfterScrubber (x y : ℝ) : ℝ :=
  hydrogenAfterPartialOxidation x y +
    carbonMonoxideAfterPartialOxidation x y

/-- A physically admissible Fig. 1 feed has nonnegative reacted steam, no more
steam-reformed methane than methane fed, and the `N2 : H2 = 1 : 3` balance
displayed by the Haber--Bosch equation in Fig. 1. -/
def Fig1StoichiometricFeed (x y : ℝ) : Prop :=
  0 ≤ y ∧ y ≤ x ∧
    hydrogenAfterScrubber x y = 3 * nitrogenAfterScrubber x y

/-- Theoretical ammonia before applying the stated overall yield.  The
displayed equation `N2 + 3 H2 -> 2 NH3` gives two ammonia per nitrogen. -/
def theoreticalAmmonia (x y : ℝ) : ℝ :=
  2 * nitrogenAfterScrubber x y

/-! ## Derived stoichiometry -/

/-- The stagewise Fig. 1 balance forces `3x = 7y`. -/
theorem fig1_feed_relation {x y : ℝ}
    (h : Fig1StoichiometricFeed x y) :
    3 * x = 7 * y := by
  rcases h with ⟨_, _, hHaber⟩
  dsimp [hydrogenAfterScrubber, hydrogenAfterPartialOxidation,
    hydrogenAfterReforming, methaneAfterReforming,
    carbonMonoxideAfterPartialOxidation, carbonMonoxideAfterReforming,
    nitrogenAfterScrubber, oxygenForPartialOxidation] at hHaber
  linarith

/-- Consequently, the process has the mole relation
`16 * n(CH4) = 7 * n(NH3,theoretical)`. -/
theorem fig1_methane_ammonia_relation {x y : ℝ}
    (h : Fig1StoichiometricFeed x y) :
    16 * x = 7 * theoreticalAmmonia x y := by
  have hxy : 3 * x = 7 * y := fig1_feed_relation h
  dsimp [theoreticalAmmonia, nitrogenAfterScrubber,
    oxygenForPartialOxidation]
  linarith

/-- The one-mole-O2 label and the Haber stoichiometry uniquely determine the
feed amounts on that basis; they are not guessed numerical coefficients. -/
theorem fig1_labeled_air_unique {x y : ℝ}
    (h : Fig1StoichiometricFeed x y)
    (hOxygen : oxygenForPartialOxidation x y = 1) :
    x = 7 / 2 ∧ y = 3 / 2 := by
  have hxy : 3 * x = 7 * y := fig1_feed_relation h
  dsimp [oxygenForPartialOxidation] at hOxygen
  constructor <;> linarith

/-- On the literal one-mole-O2 air basis in Fig. 1, 3.5 methane and 1.5 steam
give 4 nitrogen and 12 hydrogen, hence 8 theoretical ammonia.  This is a
stage-by-stage check of the coefficient ratio used in the mass calculation. -/
theorem fig1_labeled_air_basis :
    Fig1StoichiometricFeed (7 / 2 : ℝ) (3 / 2 : ℝ) ∧
    methaneAfterReforming (7 / 2 : ℝ) (3 / 2 : ℝ) = 2 ∧
    oxygenForPartialOxidation (7 / 2 : ℝ) (3 / 2 : ℝ) = 1 ∧
    carbonMonoxideAfterPartialOxidation (7 / 2 : ℝ) (3 / 2 : ℝ) = 7 / 2 ∧
    hydrogenAfterPartialOxidation (7 / 2 : ℝ) (3 / 2 : ℝ) = 17 / 2 ∧
    nitrogenAfterScrubber (7 / 2 : ℝ) (3 / 2 : ℝ) = 4 ∧
    hydrogenAfterScrubber (7 / 2 : ℝ) (3 / 2 : ℝ) = 12 ∧
    theoreticalAmmonia (7 / 2 : ℝ) (3 / 2 : ℝ) = 8 := by
  norm_num [Fig1StoichiometricFeed, methaneAfterReforming,
    oxygenForPartialOxidation, carbonMonoxideAfterPartialOxidation,
    carbonMonoxideAfterReforming, hydrogenAfterPartialOxidation,
    hydrogenAfterReforming, nitrogenAfterScrubber, hydrogenAfterScrubber,
    theoreticalAmmonia]

/-- Methane per theoretical ammonia, defined from the verified Fig. 1 basis. -/
def fig1MethanePerTheoreticalAmmonia : ℝ :=
  (7 / 2 : ℝ) / theoreticalAmmonia (7 / 2 : ℝ) (3 / 2 : ℝ)

theorem fig1_methane_per_theoretical_ammonia :
    fig1MethanePerTheoreticalAmmonia = 7 / 16 := by
  norm_num [fig1MethanePerTheoreticalAmmonia, theoreticalAmmonia,
    nitrogenAfterScrubber, oxygenForPartialOxidation]

/-! ## Exact mass calculation and final report -/

def methaneMolarMass : ℝ :=
  carbonAtomicMass + 4 * hydrogenAtomicMass

def ammoniaMolarMass : ℝ :=
  nitrogenAtomicMass + 3 * hydrogenAtomicMass

/-- The theoretical ammonia mass corresponding to the requested actual output. -/
def theoreticalAnnualAmmoniaMass : ℝ :=
  annualAmmoniaMass / overallYield

/-- Exact raw methane requirement in tons.  The factor `7/16` is proved from
Fig. 1 above; division and multiplication by the molar masses converts the
theoretical ammonia mass through the mole ratio. -/
def rawAnnualMethaneMass : ℝ :=
  theoreticalAnnualAmmoniaMass / ammoniaMolarMass *
    fig1MethanePerTheoreticalAmmonia * methaneMolarMass

theorem printed_molar_masses :
    methaneMolarMass = 8021 / 500 ∧
    ammoniaMolarMass = 8517 / 500 := by
  norm_num [methaneMolarMass, ammoniaMolarMass, carbonAtomicMass,
    nitrogenAtomicMass, hydrogenAtomicMass]

theorem yield_mass_balance :
    annualAmmoniaMass = overallYield * theoreticalAnnualAmmoniaMass := by
  norm_num [annualAmmoniaMass, overallYield,
    theoreticalAnnualAmmoniaMass]

/-- Exact, unrounded annual methane mass. -/
theorem annual_methane_mass_exact :
    rawAnnualMethaneMass = 77202125000 / 275383 := by
  norm_num [rawAnnualMethaneMass, theoreticalAnnualAmmoniaMass,
    annualAmmoniaMass, overallYield, methaneMolarMass, ammoniaMolarMass,
    carbonAtomicMass, nitrogenAtomicMass, hydrogenAtomicMass,
    fig1MethanePerTheoreticalAmmonia, theoreticalAmmonia,
    nitrogenAfterScrubber, oxygenForPartialOxidation]

/-- The required answer as an answer-blind numerical submission.  At
`2.80 * 10^5`, the last displayed quantum is 1000 tons. -/
def annualMethaneSubmission : NumericSubmission where
  rawValue := rawAnnualMethaneMass
  reportedValue := 280000
  reportingQuantum := 1000

theorem annual_methane_submission_valid :
    ValidNumericSubmission rawAnnualMethaneMass annualMethaneSubmission := by
  refine ⟨rfl, ?_⟩
  unfold ReportsAtQuantum
  dsimp [annualMethaneSubmission]
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨(280 : ℤ), by norm_num⟩
  · have hraw : 0 ≤ rawAnnualMethaneMass := by
      norm_num [rawAnnualMethaneMass, theoreticalAnnualAmmoniaMass,
        annualAmmoniaMass, overallYield, methaneMolarMass,
        ammoniaMolarMass, carbonAtomicMass, nitrogenAtomicMass,
        hydrogenAtomicMass, fig1MethanePerTheoreticalAmmonia,
        theoreticalAmmonia, nitrogenAfterScrubber,
        oxygenForPartialOxidation]
    rw [if_pos hraw]
    constructor <;>
      norm_num [rawAnnualMethaneMass, theoreticalAnnualAmmoniaMass,
        annualAmmoniaMass, overallYield, methaneMolarMass,
        ammoniaMolarMass, carbonAtomicMass, nitrogenAtomicMass,
        hydrogenAtomicMass, fig1MethanePerTheoreticalAmmonia,
        theoreticalAmmonia, nitrogenAfterScrubber,
        oxygenForPartialOxidation]

/-- Final theorem for the requested output: the source-grounded Fig. 1 basis,
the exact raw tonnage, and its three-significant-figure report. -/
theorem annual_methane_mass_required :
    Fig1StoichiometricFeed (7 / 2 : ℝ) (3 / 2 : ℝ) ∧
    theoreticalAmmonia (7 / 2 : ℝ) (3 / 2 : ℝ) = 8 ∧
    fig1MethanePerTheoreticalAmmonia = 7 / 16 ∧
    annualMethaneSubmission.rawValue = 77202125000 / 275383 ∧
    annualMethaneSubmission.reportedValue = 280000 ∧
    ValidNumericSubmission rawAnnualMethaneMass annualMethaneSubmission := by
  refine ⟨fig1_labeled_air_basis.1, ?_,
    fig1_methane_per_theoretical_ammonia, ?_, rfl,
    annual_methane_submission_valid⟩
  · norm_num [theoreticalAmmonia, nitrogenAfterScrubber,
      oxygenForPartialOxidation]
  · simpa [annualMethaneSubmission] using annual_methane_mass_exact

#print axioms fig1_methane_ammonia_relation
#print axioms annual_methane_mass_required

end

end IChO2026Problems.T7A2
