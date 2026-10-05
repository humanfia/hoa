import Chemlib.Foundations.Amount

/-!
# Amount concentration and concentration profiles

Amount concentration is the amount of substance of a constituent divided by
the volume of the mixture.  A concentration profile applies this construction
pointwise to a species-indexed family of amounts; no finiteness assumption on
the species type is needed.

The definitions follow `IUPAC-GOLDBOOK-5.0.0:A00295 definition 1` and
`IUPAC-GOLDBOOK-5.0.0:CT01038 definition 1`.  Their use in kinetic calculations
is represented in the sanitized build-corpus items `icho_2026_t2_a2:T2-A2`,
`icho_2026_t2_a3:T2-A3`, and `icho_2026_t2_a5:T2-A5`.
-/

namespace Chemlib.Foundations

/-- A nonnegative amount of substance per unit volume. -/
abbrev Concentration : Type :=
  Units.NonnegativeQuantity Units.ChemicalDimension.amountConcentration

/-- A species-indexed family of amount concentrations. -/
abbrev ConcentrationProfile : Type → Type :=
  fun Species ↦ Species → Concentration

/-- The amount concentration obtained by dividing an amount by a volume. -/
noncomputable def amountConcentration (n : Amount) (V : Volume) : Concentration :=
  ⟨Units.Quantity.div n.1 V.1, div_nonneg n.2 (le_of_lt V.2)⟩

/-- Amount concentration is nonnegative. -/
theorem amountConcentration_nonnegative (n : Amount) (V : Volume) :
    0 ≤ (amountConcentration n V).1.value :=
  (amountConcentration n V).2

/-- The numerical value of amount concentration is amount divided by volume. -/
theorem amountConcentration_value (n : Amount) (V : Volume) :
    (amountConcentration n V).1.value = n.1.value / V.1.value :=
  rfl

/-- Form the concentration of each species from its amount and the common volume. -/
noncomputable def concentrationProfile {Species : Type}
    (n : Species → Amount) (V : Volume) : ConcentrationProfile Species :=
  fun s ↦ amountConcentration (n s) V

/-- A concentration profile applies the amount-over-volume construction pointwise. -/
theorem concentrationProfile_apply {Species : Type}
    (n : Species → Amount) (V : Volume) (s : Species) :
    concentrationProfile n V s = amountConcentration (n s) V :=
  rfl

end Chemlib.Foundations
