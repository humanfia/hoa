import AFPS2017.Flow.Quantity
import AFPS2017.Sequence.State
import Chemlib.Foundations.Concentration

/-!
# Dimension-safe source arithmetic checks

This module retains the separately reported concentration, volume, resin, and
amino-acid amount data and checks their arithmetic in liters, grams, and moles.
In particular, the reported `5.6 mmol` amino-acid amount remains distinct from
the `0.56 mmol` amount computed from concentration and delivered volume.

Source references:

* Sanitized source-lint question (`afps2017.source_lint:question`).
* Public Supplementary Information
  (`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`).
-/

namespace AFPS2017.Flow

noncomputable section

/-- The chemical dimension of mass. -/
def massDimension : Chemlib.Units.ChemicalDimension :=
  Chemlib.Units.ChemicalDimension.ofPhyslib _root_.Dimension.M𝓭

/-- A nonnegative mass whose numerical value is measured in grams. -/
abbrev Mass : Type :=
  Chemlib.Units.NonnegativeQuantity massDimension

/-- Amount concentration times volume has the amount-of-substance dimension. -/
theorem concentration_times_volume_dimension :
    Chemlib.Units.ChemicalDimension.amountConcentration *
        Chemlib.Units.ChemicalDimension.volume =
      Chemlib.Units.ChemicalDimension.amountOfSubstance := by
  simp [Chemlib.Units.ChemicalDimension.amountConcentration]

/-- Resin loading times mass has the amount-of-substance dimension. -/
theorem resinLoading_times_mass_dimension :
    AFPS2017.Sequence.resinLoadingDimension * massDimension =
      Chemlib.Units.ChemicalDimension.amountOfSubstance := by
  simp [AFPS2017.Sequence.resinLoadingDimension, massDimension]

/-- Construct a nonnegative amount concentration measured in moles per liter. -/
def molesPerLiter (value : ℝ) (nonnegative : 0 ≤ value) :
    Chemlib.Foundations.Concentration :=
  Chemlib.Units.NonnegativeQuantity.ofReal value nonnegative

/-- Construct a nonnegative amount measured in millimoles. -/
def millimoles (value : ℝ) (nonnegative : 0 ≤ value) :
    Chemlib.Foundations.Amount :=
  Chemlib.Units.NonnegativeQuantity.ofReal (value / 1000)
    (div_nonneg nonnegative (by norm_num))

/-- Construct a nonnegative mass measured in milligrams. -/
def milligrams (value : ℝ) (nonnegative : 0 ≤ value) : Mass :=
  Chemlib.Units.NonnegativeQuantity.ofReal (value / 1000)
    (div_nonneg nonnegative (by norm_num))

/-- Multiply concentration in moles per liter by volume in liters. -/
def amountFromConcentrationVolume
    (concentration : Chemlib.Foundations.Concentration)
    (volume : Chemlib.Foundations.Volume) :
    Chemlib.Foundations.Amount :=
  Chemlib.Units.NonnegativeQuantity.ofReal
    (concentration.1.value * volume.1.value)
    (mul_nonneg concentration.2 (le_of_lt volume.2))

/-- Multiply resin loading in moles per gram by resin mass in grams. -/
def amountOnResin (loading : AFPS2017.Sequence.ResinLoading) (mass : Mass) :
    Chemlib.Foundations.Amount :=
  Chemlib.Units.NonnegativeQuantity.ofReal
    (loading.1.value * mass.1.value)
    (mul_nonneg loading.2 mass.2)

/-- The reported amino-acid stock concentration, `0.2 mol/L`. -/
def reportedAminoAcidConcentration : Chemlib.Foundations.Concentration :=
  molesPerLiter (1 / 5) (by norm_num)

/-- The reported activator stock concentration, `0.17 mol/L`. -/
def reportedActivatorConcentration : Chemlib.Foundations.Concentration :=
  molesPerLiter (17 / 100) (by norm_num)

/-- The reported delivered volume, `2.8 mL`. -/
def reportedDeliveredVolume : Chemlib.Foundations.Volume :=
  milliliters (14 / 5) (by norm_num)

/-- The reported resin loading, `0.45 mmol/g`. -/
def reportedResinLoading : AFPS2017.Sequence.ResinLoading :=
  Chemlib.Units.NonnegativeQuantity.ofReal (9 / 20000) (by norm_num)

/-- The reported resin mass, `200 mg`. -/
def reportedResinMass : Mass :=
  milligrams 200 (by norm_num)

/-- Amino-acid amount computed from reported concentration and volume. -/
def computedAminoAcidAmount : Chemlib.Foundations.Amount :=
  amountFromConcentrationVolume
    reportedAminoAcidConcentration reportedDeliveredVolume

/-- Activator amount computed from reported concentration and volume. -/
def computedActivatorAmount : Chemlib.Foundations.Amount :=
  amountFromConcentrationVolume
    reportedActivatorConcentration reportedDeliveredVolume

/-- Resin amount computed from reported loading and mass. -/
def computedResinAmount : Chemlib.Foundations.Amount :=
  amountOnResin reportedResinLoading reportedResinMass

/-- The separately reported amino-acid amount, `5.6 mmol`. -/
def reportedAminoAcidAmount : Chemlib.Foundations.Amount :=
  millimoles (28 / 5) (by norm_num)

/-- The computed activator amount is exactly `0.476 mmol`. -/
theorem computedActivatorAmount_millimoles :
    1000 * computedActivatorAmount.1.value = (119 / 250 : ℝ) := by
  norm_num [computedActivatorAmount, amountFromConcentrationVolume,
    reportedActivatorConcentration, molesPerLiter, reportedDeliveredVolume,
    milliliters, Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.PositiveQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal]

/-- The computed amino-acid amount is exactly `0.56 mmol`. -/
theorem computedAminoAcidAmount_millimoles :
    1000 * computedAminoAcidAmount.1.value = (14 / 25 : ℝ) := by
  norm_num [computedAminoAcidAmount, amountFromConcentrationVolume,
    reportedAminoAcidConcentration, molesPerLiter, reportedDeliveredVolume,
    milliliters, Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.PositiveQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal]

/-- The computed resin amount is exactly `0.09 mmol`. -/
theorem computedResinAmount_millimoles :
    1000 * computedResinAmount.1.value = (9 / 100 : ℝ) := by
  norm_num [computedResinAmount, amountOnResin, reportedResinLoading,
    reportedResinMass, milligrams,
    Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal]

/-- Reagent equivalents are reagent amount divided by resin amount. -/
def reagentEquivalents (reagentAmount resinAmount : Chemlib.Foundations.Amount) : ℝ :=
  reagentAmount.1.value / resinAmount.1.value

/-- The activator-to-resin ratio is exactly `238/45`. -/
theorem activator_equivalents_exact :
    reagentEquivalents computedActivatorAmount computedResinAmount =
      (238 / 45 : ℝ) := by
  norm_num [reagentEquivalents, computedActivatorAmount,
    amountFromConcentrationVolume, reportedActivatorConcentration,
    molesPerLiter, reportedDeliveredVolume, milliliters,
    computedResinAmount, amountOnResin, reportedResinLoading,
    reportedResinMass, milligrams,
    Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.PositiveQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal]

/-- The activator equivalents round to `5.29` within half a hundredth. -/
theorem activator_equivalents_rounds_to_5_29 :
    |reagentEquivalents computedActivatorAmount computedResinAmount -
        (529 / 100 : ℝ)| < (1 / 200 : ℝ) := by
  rw [activator_equivalents_exact]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- The amino-acid-to-resin ratio is exactly `56/9`. -/
theorem aminoAcid_equivalents_exact :
    reagentEquivalents computedAminoAcidAmount computedResinAmount =
      (56 / 9 : ℝ) := by
  norm_num [reagentEquivalents, computedAminoAcidAmount,
    amountFromConcentrationVolume, reportedAminoAcidConcentration,
    molesPerLiter, reportedDeliveredVolume, milliliters,
    computedResinAmount, amountOnResin, reportedResinLoading,
    reportedResinMass, milligrams,
    Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.PositiveQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal]

/-- The amino-acid equivalents round to `6.22` within half a hundredth. -/
theorem aminoAcid_equivalents_rounds_to_6_22 :
    |reagentEquivalents computedAminoAcidAmount computedResinAmount -
        (311 / 50 : ℝ)| < (1 / 200 : ℝ) := by
  rw [aminoAcid_equivalents_exact]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- The reported amino-acid amount is ten times the computed amount. -/
theorem reportedAminoAcidAmount_is_ten_times_computed :
    reportedAminoAcidAmount.1.value =
      10 * computedAminoAcidAmount.1.value := by
  norm_num [reportedAminoAcidAmount, millimoles, computedAminoAcidAmount,
    amountFromConcentrationVolume, reportedAminoAcidConcentration,
    molesPerLiter, reportedDeliveredVolume, milliliters,
    Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.PositiveQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal]

/-- The reported and concentration-derived amino-acid amounts are unequal. -/
theorem reportedAminoAcidAmount_inconsistent :
    reportedAminoAcidAmount ≠ computedAminoAcidAmount := by
  intro amounts_equal
  have values_equal := congrArg (fun amount ↦ amount.1.value) amounts_equal
  norm_num [reportedAminoAcidAmount, millimoles, computedAminoAcidAmount,
    amountFromConcentrationVolume, reportedAminoAcidConcentration,
    molesPerLiter, reportedDeliveredVolume, milliliters,
    Chemlib.Units.NonnegativeQuantity.ofReal,
    Chemlib.Units.PositiveQuantity.ofReal,
    Chemlib.Units.Quantity.ofReal] at values_equal

end

end AFPS2017.Flow
