import AFPS2017.Analytics.Provenance
import Chemlib.Units.Quantity

/-!
# Mass observations for AFPS2017 analytics

This module implements the narrow mass-observation contract from the sanitized
source `afps2017.analytics.contract:question`. It records expected and observed
display precision independently and represents both mass readings with
Chemlib's dimension-indexed nonnegative quantities at the Physlib mass
dimension.

The residual below is only the absolute difference of the two displayed dalton
values. Neither the observation nor its residual establishes molecular identity,
purity, or any other chemical interpretation.
-/

namespace AFPS2017.Analytics

/-- Decimal-place metadata recorded independently for expected and observed mass. -/
structure DisplayedPrecision : Type where
  expectedDecimalPlaces : Nat
  observedDecimalPlaces : Nat

/-- Product-form metadata when the source does not specify a form. -/
inductive ProductForm : Type where
  | unspecified

/-- The Chemlib chemical dimension obtained from Physlib's mass dimension. -/
def massDimension : Chemlib.Units.ChemicalDimension :=
  Chemlib.Units.ChemicalDimension.ofPhyslib _root_.Dimension.M𝓭

/-- A nonnegative Chemlib quantity at the Physlib mass dimension. -/
abbrev MassQuantity : Type :=
  Chemlib.Units.NonnegativeQuantity massDimension

/-- Construct a mass quantity whose stored numerical value is measured in daltons. -/
def ofDaltons (value : ℝ) (nonnegative : 0 ≤ value) : MassQuantity :=
  Chemlib.Units.NonnegativeQuantity.ofReal value nonnegative

/--
Expected and observed displayed masses with deliberately narrow product-form and
precision metadata. This record carries no identity or purity proposition.
-/
structure MassObservation : Type where
  expectedMass : MassQuantity
  observedMass : MassQuantity
  productForm : ProductForm
  displayedPrecision : DisplayedPrecision

/-- The absolute difference between the displayed expected and observed dalton values. -/
def massResidualDaltons (observation : MassObservation) : ℝ :=
  |observation.expectedMass.1.value - observation.observedMass.1.value|

/-- An absolute displayed-mass residual is nonnegative. -/
theorem massResidualDaltons_nonnegative (observation : MassObservation) :
    0 ≤ massResidualDaltons observation := by
  exact abs_nonneg _

end AFPS2017.Analytics
