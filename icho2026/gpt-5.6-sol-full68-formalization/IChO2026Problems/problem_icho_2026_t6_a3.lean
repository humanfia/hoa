import Mathlib
import Physlib.Units.WithDim.Basic
import IChO2026Chem

/-!
# IChO 2026, problem T6-A3: halogen compatible with a 2.5 V electron

The source gives four C-X bond-dissociation energies and asks which halogenated
reagent can be used when the AFM applies 2.5 V to an electron.  This file keeps
the source table, the electron-through-potential energy law, and the requested
finite-set output separate.

The named retro-Bergman transformation is used only qualitatively here.  No
yield, completeness, product exclusivity, or material balance is asserted.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T6A3

/-- Provenance categories used by this source-scoped formalization. -/
inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- A value paired with its source class and a human-auditable locator. -/
structure Sourced (α : Type) where
  value : α
  provenance : Provenance
  locator : String

/-- The four halogens occurring as rows of the C-X bond-energy table. -/
inductive Halogen where
  | fluorine
  | chlorine
  | bromine
  | iodine
  deriving DecidableEq, Fintype, Repr

/-- A voltage, numerically represented in volts. -/
structure Voltage where
  volts : ℚ
  deriving DecidableEq, Repr

/-- A molar energy, numerically represented in kJ mol⁻¹. -/
structure MolarEnergy where
  kilojoulesPerMole : ℚ
  deriving DecidableEq, Repr

/-- The named transformation specified in the current question. -/
inductive NamedTransformation where
  | retroBergman
  deriving DecidableEq, Repr

/-- Source-bounded context for the requested C₁₈ AFM synthesis. -/
structure AFMSynthesisContext where
  productCarbonCount : ℕ
  transformation : NamedTransformation
  appliedVoltage : Voltage
  deriving DecidableEq, Repr

/-- The current question's C₁₈/retro-Bergman/2.5 V synthesis context. -/
def c18Synthesis : Sourced AFMSynthesisContext where
  value := {
    productCarbonCount := 18
    transformation := .retroBergman
    appliedVoltage := ⟨5 / 2⟩
  }
  provenance := .problemText
  locator := "T6-A3, first sentence and requested C18 retro-Bergman synthesis"

/-- The complete candidate domain supplied by the four rows of the table. -/
def sourceHalogenDomain : Sourced (Finset Halogen) where
  value := Finset.univ
  provenance := .problemImage
  locator := "T6_page-2.png, T6-A3 C-X bond-dissociation-energy table"

/-- Source-stipulated C-X bond-dissociation energy, in kJ mol⁻¹. -/
def carbonHalogenBondEnergy (x : Halogen) : Sourced MolarEnergy :=
  match x with
  | .fluorine =>
      ⟨⟨467⟩, .problemImage, "T6_page-2.png, table row C-F"⟩
  | .chlorine =>
      ⟨⟨346⟩, .problemImage, "T6_page-2.png, table row C-Cl"⟩
  | .bromine =>
      ⟨⟨290⟩, .problemImage, "T6_page-2.png, table row C-Br"⟩
  | .iodine =>
      ⟨⟨228⟩, .problemImage, "T6_page-2.png, table row C-I"⟩

/-- Exact SI magnitude of the elementary charge, in coulombs.

This is the same `1.602176634e-19` value used by
`DimEnergy.electronVolt` in Physlib. -/
def elementaryChargeMagnitudeCoulomb : Sourced ℚ where
  value := 1602176634 / (10 : ℚ) ^ 28
  provenance := .trustedGeneralLaw
  locator := "NIST CODATA elementary charge, https://physics.nist.gov/cgi-bin/cuu/Value?e; Physlib DimEnergy.electronVolt"

/-- Exact SI Avogadro constant, in mol⁻¹. -/
def avogadroConstantPerMole : Sourced ℚ where
  value := 602214076 * (10 : ℚ) ^ 15
  provenance := .trustedGeneralLaw
  locator := "NIST CODATA Avogadro constant, https://physics.nist.gov/cgi-bin/cuu/Value?na"

/-- Molar energy delivered to one mole of singly charged electrons through a
potential difference `v`.

The governing relation is `E = |e| V`; multiplication by `N_A` gives J mol⁻¹,
and division by 1000 converts J mol⁻¹ to kJ mol⁻¹. -/
def electronMolarEnergy (v : Voltage) : MolarEnergy :=
  ⟨v.volts * elementaryChargeMagnitudeCoulomb.value *
      avogadroConstantPerMole.value / 1000⟩

/-- The exact unrounded molar energy available at the source-stipulated
2.5 V potential. -/
def appliedElectronMolarEnergy : MolarEnergy :=
  electronMolarEnergy c18Synthesis.value.appliedVoltage

/-- A C-X bond is energy-compatible with the source voltage when its printed
bond-dissociation energy does not exceed the molar energy supplied by one mole
of electrons at that voltage.  This is the quantitative compatibility carrier
used for the otherwise qualitative named transformation. -/
def EnergyCompatibleCXBond (x : Halogen) : Prop :=
  (carbonHalogenBondEnergy x).value.kilojoulesPerMole ≤
    appliedElectronMolarEnergy.kilojoulesPerMole

/-- Decidable form of `EnergyCompatibleCXBond`, used only to filter the finite
source table. -/
instance energyCompatibleCXBondDecidable (x : Halogen) :
    Decidable (EnergyCompatibleCXBond x) := by
  unfold EnergyCompatibleCXBond
  infer_instance

/-- Requested output carrier: every row of the source table that passes the
same energy-compatibility test. -/
def possibleHalogens : Finset Halogen :=
  sourceHalogenDomain.value.filter EnergyCompatibleCXBond

/-- Raw answer-blind result proposition.  The singleton occurs only in the
conclusion after uniformly filtering the four-row source domain. -/
def RawPossibleHalogensResult : Prop :=
  possibleHalogens = {Halogen.iodine}

/-- Exact-symbolic reporting proposition.  Since the output is a finite set,
the reporting policy performs no numerical rounding. -/
def ReportedPossibleHalogensResult : Prop :=
  ∀ x : Halogen, x ∈ possibleHalogens ↔ x = Halogen.iodine

/-- The exact SI conversion puts the applied electron energy strictly between
241 and 242 kJ mol⁻¹.  This exposes the unrounded bridge used by the table
classification rather than assuming a selected halogen. -/
theorem appliedElectronMolarEnergy_bounds :
    (241 : ℚ) < appliedElectronMolarEnergy.kilojoulesPerMole ∧
      appliedElectronMolarEnergy.kilojoulesPerMole < (242 : ℚ) := by
  norm_num [appliedElectronMolarEnergy, electronMolarEnergy, c18Synthesis,
    elementaryChargeMagnitudeCoulomb, avogadroConstantPerMole]

/-- Uniform source-table audit: compatibility is exactly membership in the
computed output carrier. -/
theorem mem_possibleHalogens_iff (x : Halogen) :
    x ∈ possibleHalogens ↔ EnergyCompatibleCXBond x := by
  simp [possibleHalogens, sourceHalogenDomain]

/-- Raw requested result derived from the source domain, table, voltage, and
electron-through-potential law. -/
theorem rawResult : RawPossibleHalogensResult := by
  unfold RawPossibleHalogensResult
  native_decide

/-- Reported exact-symbolic requested result. -/
theorem reportedResult : ReportedPossibleHalogensResult := by
  unfold ReportedPossibleHalogensResult
  native_decide

end ProblemIChO2026T6A3
end IChO2026Problems
