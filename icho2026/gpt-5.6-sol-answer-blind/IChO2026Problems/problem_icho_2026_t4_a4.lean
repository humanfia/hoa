import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T4-A4

Only the mass-number part of the preceding fission equation is needed for the
requested energy. The supplied graph has maxima at mass numbers 93 and 140,
while the printed reaction absorbs one free neutron and emits three. Hence the
two bound products contain 93 + 140 = 233 nucleons and the complete ledger is
235 + 1 = 93 + 140 + 3.

This file deliberately does not select element identities for the two peaks.
Their same-periodic-group condition is needed to name the isotopes in T4-A3,
but it cannot change T4-A4: the source supplies one common average binding
energy per nucleon for all bound fission products. The theorem
releasedEnergy_eq_raw_of_sourceCounts makes that invariance explicit, so no
finite element-candidate domain or empirical isotope-feasibility filter is an
assumption of the numerical result.
-/

namespace IChO2026Problems
namespace T4A4

noncomputable section

/-- Energy measured in MeV. -/
abbrev MeV := ℝ

/-- Binding energy per nucleon, measured in MeV/nucleon. -/
abbrev MeVPerNucleon := ℝ

/-!
STAGED-TRANSFORMATION CLASSIFICATION: quantitative_material_stage.

The requested energy consumes the mass-number ledger, so the finite material
domain below names every stream used by that ledger: the bound uranium-235
parent, one absorbed free neutron, two bound product fragments, and three
emitted free neutrons. No charge or phase balance is used to compute the
requested output.
-/

/-- Outcome-decisive streams for the fission mass-number ledger. -/
structure QuantitativeFissionStage where
  parentBoundMassNumber : ℕ
  absorbedFreeNeutronCount : ℕ
  lightProductMassNumber : ℕ
  heavyProductMassNumber : ℕ
  emittedFreeNeutronCount : ℕ
  deriving DecidableEq, Repr

/-- Integer mass number read at the light maximum of the supplied graph. -/
def graphLightPeakMassNumber : ℕ := 93

/-- Integer mass number read at the heavy maximum of the supplied graph. -/
def graphHeavyPeakMassNumber : ℕ := 140

/-- The complete source-derived quantitative stage used in T4-A4. -/
def sourceFissionStage : QuantitativeFissionStage :=
  { parentBoundMassNumber := 235
    absorbedFreeNeutronCount := 1
    lightProductMassNumber := graphLightPeakMassNumber
    heavyProductMassNumber := graphHeavyPeakMassNumber
    emittedFreeNeutronCount := 3 }

/-- Total bound nucleons before fission. -/
def boundNucleonCountBefore (s : QuantitativeFissionStage) : ℕ :=
  s.parentBoundMassNumber

/-- Total free neutrons before fission. -/
def freeNucleonCountBefore (s : QuantitativeFissionStage) : ℕ :=
  s.absorbedFreeNeutronCount

/-- Total bound nucleons in the two fission products. -/
def boundProductNucleonCount (s : QuantitativeFissionStage) : ℕ :=
  s.lightProductMassNumber + s.heavyProductMassNumber

/-- Total free neutrons after fission. -/
def freeNucleonCountAfter (s : QuantitativeFissionStage) : ℕ :=
  s.emittedFreeNeutronCount

/-- The outcome-decisive mass-number conservation carrier. -/
def MassNumberLedger (s : QuantitativeFissionStage) : Prop :=
  boundNucleonCountBefore s + freeNucleonCountBefore s =
    boundProductNucleonCount s + freeNucleonCountAfter s

/-- Source facts from the printed reaction and graph, followed by their
mass-number conservation check. -/
def SourceFissionStageSpec (s : QuantitativeFissionStage) : Prop :=
  s.parentBoundMassNumber = 235 ∧
    s.absorbedFreeNeutronCount = 1 ∧
    s.lightProductMassNumber = graphLightPeakMassNumber ∧
    s.heavyProductMassNumber = graphHeavyPeakMassNumber ∧
    s.emittedFreeNeutronCount = 3 ∧
    MassNumberLedger s

/-- The graph readouts and printed neutron counts form a balanced ledger. -/
theorem sourceFissionStage_verified :
    SourceFissionStageSpec sourceFissionStage := by
  norm_num [SourceFissionStageSpec, MassNumberLedger,
    boundNucleonCountBefore, freeNucleonCountBefore,
    boundProductNucleonCount, freeNucleonCountAfter, sourceFissionStage,
    graphLightPeakMassNumber, graphHeavyPeakMassNumber]

/-- Mass-number conservation alone fixes the total number of bound product
nucleons; neither fragment identity nor the split between the two fragments is
needed. -/
theorem boundProductNucleonCount_of_massNumberLedger
    (s : QuantitativeFissionStage)
    (hParent : s.parentBoundMassNumber = 235)
    (hAbsorbed : s.absorbedFreeNeutronCount = 1)
    (hEmitted : s.emittedFreeNeutronCount = 3)
    (hLedger : MassNumberLedger s) :
    boundProductNucleonCount s = 233 := by
  unfold MassNumberLedger boundNucleonCountBefore freeNucleonCountBefore
    boundProductNucleonCount freeNucleonCountAfter at hLedger
  unfold boundProductNucleonCount
  omega

/-- The previous part's energy-relevant conclusion, derived inline from the
problem-only graph and reaction text. -/
theorem sourceBoundProductNucleonCount :
    boundProductNucleonCount sourceFissionStage = 233 := by
  apply boundProductNucleonCount_of_massNumberLedger sourceFissionStage
  · rfl
  · rfl
  · rfl
  · exact sourceFissionStage_verified.2.2.2.2.2

/-- Source-stipulated average binding energy of uranium-235. -/
def uranium235BindingEnergyPerNucleonMeV : MeVPerNucleon :=
  (759 : ℝ) / 100

/-- Source-stipulated average binding energy of each bound fission product. -/
def fissionProductBindingEnergyPerNucleonMeV : MeVPerNucleon :=
  (845 : ℝ) / 100

/-- Source instruction to neglect the binding energy of every free neutron. -/
def freeNeutronBindingEnergyPerNucleonMeV : MeVPerNucleon := 0

/-- Binding energy contributed by a bound or free stream. -/
def totalBindingEnergyMeV
    (nucleonCount : ℕ) (bindingEnergyPerNucleon : MeVPerNucleon) : MeV :=
  (nucleonCount : ℝ) * bindingEnergyPerNucleon

/-- Reactant binding energy, including the absorbed neutron's explicit zero. -/
def initialTotalBindingEnergyMeV (s : QuantitativeFissionStage) : MeV :=
  totalBindingEnergyMeV
      s.parentBoundMassNumber uranium235BindingEnergyPerNucleonMeV +
    totalBindingEnergyMeV
      s.absorbedFreeNeutronCount freeNeutronBindingEnergyPerNucleonMeV

/-- Product binding energy with both bound fragments and the emitted-neutron
stream exposed separately. -/
def productTotalBindingEnergyMeV (s : QuantitativeFissionStage) : MeV :=
  totalBindingEnergyMeV
      s.lightProductMassNumber fissionProductBindingEnergyPerNucleonMeV +
    totalBindingEnergyMeV
      s.heavyProductMassNumber fissionProductBindingEnergyPerNucleonMeV +
    totalBindingEnergyMeV
      s.emittedFreeNeutronCount freeNeutronBindingEnergyPerNucleonMeV

/-- Released energy has the source-appropriate sign: final binding energy
minus initial binding energy. -/
def releasedEnergyMeV (s : QuantitativeFissionStage) : MeV :=
  productTotalBindingEnergyMeV s - initialTotalBindingEnergyMeV s

/-- Exact unrounded requested energy for the source-derived stage. -/
def rawFissionEnergy : MeV := releasedEnergyMeV sourceFissionStage

/-- Any balanced two-fragment fission stage with the source's parent and free
neutron counts has the same released energy under the common product-average
binding energy. This is why element identification is not a premise of T4-A4. -/
theorem releasedEnergy_depends_only_on_massNumberLedger
    (s : QuantitativeFissionStage)
    (hParent : s.parentBoundMassNumber = 235)
    (hAbsorbed : s.absorbedFreeNeutronCount = 1)
    (hEmitted : s.emittedFreeNeutronCount = 3)
    (hLedger : MassNumberLedger s) :
    releasedEnergyMeV s =
      (233 : ℝ) * fissionProductBindingEnergyPerNucleonMeV -
        (235 : ℝ) * uranium235BindingEnergyPerNucleonMeV := by
  have hProductsNat : boundProductNucleonCount s = 233 :=
    boundProductNucleonCount_of_massNumberLedger s hParent hAbsorbed hEmitted hLedger
  have hProductsReal :
      (s.lightProductMassNumber : ℝ) + (s.heavyProductMassNumber : ℝ) = 233 := by
    exact_mod_cast hProductsNat
  have hParentReal : (s.parentBoundMassNumber : ℝ) = 235 := by
    exact_mod_cast hParent
  calc
    releasedEnergyMeV s =
        ((s.lightProductMassNumber : ℝ) +
            (s.heavyProductMassNumber : ℝ)) *
            fissionProductBindingEnergyPerNucleonMeV -
          (s.parentBoundMassNumber : ℝ) *
            uranium235BindingEnergyPerNucleonMeV := by
      simp [releasedEnergyMeV, productTotalBindingEnergyMeV,
        initialTotalBindingEnergyMeV, totalBindingEnergyMeV,
        freeNeutronBindingEnergyPerNucleonMeV]
      ring
    _ = (233 : ℝ) * fissionProductBindingEnergyPerNucleonMeV -
          (235 : ℝ) * uranium235BindingEnergyPerNucleonMeV := by
      rw [hProductsReal, hParentReal]

/-- The output is invariant across every source-count, mass-balanced fragment
split, and agrees with the graph-derived raw carrier. -/
theorem releasedEnergy_eq_raw_of_sourceCounts
    (s : QuantitativeFissionStage)
    (hParent : s.parentBoundMassNumber = 235)
    (hAbsorbed : s.absorbedFreeNeutronCount = 1)
    (hEmitted : s.emittedFreeNeutronCount = 3)
    (hLedger : MassNumberLedger s) :
    releasedEnergyMeV s = rawFissionEnergy := by
  have hs := releasedEnergy_depends_only_on_massNumberLedger
    s hParent hAbsorbed hEmitted hLedger
  have hSource := releasedEnergy_depends_only_on_massNumberLedger
    sourceFissionStage rfl rfl rfl sourceFissionStage_verified.2.2.2.2.2
  exact hs.trans (by simpa [rawFissionEnergy] using hSource.symm)

/-- Raw derivation contract: source stage, conservation-derived bound-product
count, exact printed constants, all free-neutron streams, release sign, and the
identity-independent energy theorem. -/
def FissionEnergyDerivationSpec : Prop :=
  SourceFissionStageSpec sourceFissionStage ∧
    boundProductNucleonCount sourceFissionStage = 233 ∧
    uranium235BindingEnergyPerNucleonMeV = (759 : ℝ) / 100 ∧
    fissionProductBindingEnergyPerNucleonMeV = (845 : ℝ) / 100 ∧
    freeNeutronBindingEnergyPerNucleonMeV = 0 ∧
    rawFissionEnergy =
      ((graphLightPeakMassNumber : ℝ) *
          fissionProductBindingEnergyPerNucleonMeV +
        (graphHeavyPeakMassNumber : ℝ) *
          fissionProductBindingEnergyPerNucleonMeV +
        (3 : ℝ) * freeNeutronBindingEnergyPerNucleonMeV) -
      ((235 : ℝ) * uranium235BindingEnergyPerNucleonMeV +
        (1 : ℝ) * freeNeutronBindingEnergyPerNucleonMeV) ∧
    ∀ s : QuantitativeFissionStage,
      s.parentBoundMassNumber = 235 →
      s.absorbedFreeNeutronCount = 1 →
      s.emittedFreeNeutronCount = 3 →
      MassNumberLedger s →
      releasedEnergyMeV s = rawFissionEnergy

/-- Raw result contract with the exact end-to-end derivation and the
predeclared one-MeV reporting cell as a non-degenerate enclosure. -/
theorem rawFissionEnergyResult :
    FissionEnergyDerivationSpec ∧
      ((369 : ℝ) / 2 ≤ rawFissionEnergy ∧
        rawFissionEnergy ≤ (371 : ℝ) / 2) := by
  constructor
  · refine ⟨sourceFissionStage_verified, sourceBoundProductNucleonCount,
      rfl, rfl, rfl, ?_, ?_⟩
    · simp [rawFissionEnergy, releasedEnergyMeV,
        productTotalBindingEnergyMeV, initialTotalBindingEnergyMeV,
        totalBindingEnergyMeV, sourceFissionStage]
    · intro s hParent hAbsorbed hEmitted hLedger
      exact releasedEnergy_eq_raw_of_sourceCounts
        s hParent hAbsorbed hEmitted hLedger
  · norm_num [rawFissionEnergy, releasedEnergyMeV,
      productTotalBindingEnergyMeV, initialTotalBindingEnergyMeV,
      totalBindingEnergyMeV, sourceFissionStage, graphLightPeakMassNumber,
      graphHeavyPeakMassNumber, uranium235BindingEnergyPerNucleonMeV,
      fissionProductBindingEnergyPerNucleonMeV,
      freeNeutronBindingEnergyPerNucleonMeV]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"fission_energy","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"185","reporting_quantum":"1","raw_declaration":"IChO2026Problems.T4A4.rawFissionEnergy","reporting_declaration":"IChO2026Problems.T4A4.reportedFissionEnergy"}
theorem reportedFissionEnergy :
    IChO2026Chem.Reporting.ReportsAtQuantum
      rawFissionEnergy (185 : ℝ) (1 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  norm_num [rawFissionEnergy, releasedEnergyMeV,
    productTotalBindingEnergyMeV, initialTotalBindingEnergyMeV,
    totalBindingEnergyMeV, sourceFissionStage, graphLightPeakMassNumber,
    graphHeavyPeakMassNumber, uranium235BindingEnergyPerNucleonMeV,
    fissionProductBindingEnergyPerNucleonMeV,
    freeNeutronBindingEnergyPerNucleonMeV]
  exact ⟨185, by norm_num⟩

end
end T4A4
end IChO2026Problems
