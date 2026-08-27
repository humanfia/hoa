import Chemlib.Units.Quantity

/-!
# Amount-of-substance domains

This module distinguishes nonnegative stock amounts, signed changes in amount,
and strictly positive mixture volumes.  Extent rates and reaction rates remain
signed because they may describe either forward or reverse progress.

The chemical interpretation is grounded in
`IUPAC-GOLDBOOK-5.0.0:A00295 definition 1` and
`IUPAC-GOLDBOOK-5.0.0:E02283 definition 1`, together with the sanitized
build-corpus items `icho_2026_t2_a2:T2-A2`, `icho_2026_t3_a7:T3-A7`,
`icho_2026_t4_a8:T4-A8`, and `icho_2026_t7_a3:T7-A3`.
-/

namespace Chemlib.Foundations

/-- A nonnegative stock amount with the amount-of-substance dimension. -/
abbrev Amount : Type :=
  Units.NonnegativeQuantity Units.ChemicalDimension.amountOfSubstance

/-- A signed change in amount of substance. -/
abbrev AmountChange : Type :=
  Units.Quantity Units.ChemicalDimension.amountOfSubstance

/-- A signed rate of reaction extent. -/
abbrev ExtentRate : Type :=
  Units.Quantity Units.ChemicalDimension.extentRate

/-- A signed reaction rate per unit volume. -/
abbrev ReactionRate : Type :=
  Units.Quantity Units.ChemicalDimension.reactionRate

/-- A strictly positive mixture volume. -/
abbrev Volume : Type :=
  Units.PositiveQuantity Units.ChemicalDimension.volume

end Chemlib.Foundations
