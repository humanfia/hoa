import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, Theory Problem 4, Part 4.7 (target icho_2026_t4_a7)

**Question.** Calculate ΔrH₂₀₀₀ (kJ mol⁻¹) per mole of methane combustion
reaction at 2000 K. Assume all species are gaseous.

## Chemistry and source grounding (problem-only inputs)

The combustion reaction, stipulated in the shared context of Problem 4 (Part
4.6), with all species gaseous:

    CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)

Part 4.6 stipulates the following thermodynamic data (printed on the problem
page Q4-2):

* ΔfH°₂₉₈(CH₄) = −74.8 kJ mol⁻¹
* ΔfH°₂₉₈(H₂O, gas) = −241.8 kJ mol⁻¹
* ΔfH°₂₉₈(CO₂) = −393.5 kJ mol⁻¹
* Cₚ(CH₄) = 35 J mol⁻¹ K⁻¹, Cₚ(H₂O, gas) = 34 J mol⁻¹ K⁻¹,
  Cₚ(O₂) = 29 J mol⁻¹ K⁻¹, Cₚ(CO₂) = 37 J mol⁻¹ K⁻¹

Elements in their standard state (here O₂(g)) have ΔfH°₂₉₈ = 0 (a trusted
general law; consistent with the problem's "use ΔH₂₉₈ = −750" fallback arrow).

### Part 4.6 prerequisite, derived here inline (Hess's law)

    ΔrH°₂₉₈ = [ΔfH°₂₉₈(CO₂) + 2·ΔfH°₂₉₈(H₂O,g)] − [ΔfH°₂₉₈(CH₄) + 2·0]
            = −393.5 − 483.6 + 74.8 = −802.3 kJ mol⁻¹

### Kirchhoff's law with constant heat capacities

The problem supplies constant Cₚ values and no temperature dependence, so the
heat capacities are taken as temperature independent.  Then

    ΔCₚ = Cₚ(CO₂) + 2·Cₚ(H₂O,g) − Cₚ(CH₄) − 2·Cₚ(O₂)
        = 37 + 68 − 35 − 58 = 12 J mol⁻¹ K⁻¹

    ΔrH(T) = ΔrH°₂₉₈ + ΔCₚ·(T − 298)   (Kirchhoff's law, constant Cₚ)

### Part 4.7 evaluation at T = 2000 K

    ΔrH₂₀₀₀ = −802.3 + (12/1000)·(2000 − 298) kJ mol⁻¹
            = −802.3 + 0.012·1702
            = −802.3 + 20.424
            = −781.876 kJ mol⁻¹

Rounded to three significant figures (the answer-blind reporting default) with
the stated half-away-from-zero tie rule: **ΔrH₂₀₀₀ = −782 kJ mol⁻¹**.

The fallback value printed under 4.7 (use ΔH₂₀₀₀ = −700 kJ mol⁻¹ *only if* no
answer for 4.7 was obtained) is conditional and therefore not used: the data
fully determine the value.
-/

namespace IChO2026Problems.Icho2026T4A7

open IChO2026Chem.Reporting

/-- The species involved in methane combustion. -/
inductive Species where
  | CH4 | O2 | CO2 | H2O
  deriving DecidableEq, Repr

/-- Stoichiometric coefficients ν (sign convention: ν > 0 products,
ν < 0 reactants) for CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g).  They are carried
as a structure so that the atom-balance constraints, rather than an asserted
table, determine the recipe. -/
structure CombustionStoichiometry where
  /-- Stoichiometric coefficient of CH₄ (reactant: ν = −1). -/
  nuCH4 : ℤ
  /-- Stoichiometric coefficient of O₂ (reactant: ν = −2). -/
  nuO2 : ℤ
  /-- Stoichiometric coefficient of CO₂ (product: ν = +1). -/
  nuCO2 : ℤ
  /-- Stoichiometric coefficient of H₂O (product: ν = +2). -/
  nuH2O : ℤ
  /-- Atom balance for carbon. -/
  cBalance : nuCO2 + nuCH4 = 0
  /-- Atom balance for hydrogen: 4 per CH₄, 2 per H₂O. -/
  hBalance : 2 * nuH2O + 4 * nuCH4 = 0
  /-- Atom balance for oxygen: 2 per CO₂, 1 per H₂O, 2 per O₂. -/
  oBalance : 2 * nuCO2 + nuH2O + 2 * nuO2 = 0
  /-- One mole of methane is consumed per mole of reaction. -/
  methaneConsumed : nuCH4 = -1

/-- The atom balances, together with "one mole of methane consumed", force the
complete stoichiometry of methane combustion. -/
theorem CombustionStoichiometry.unique (s : CombustionStoichiometry) :
    s.nuCH4 = -1 ∧ s.nuO2 = -2 ∧ s.nuCO2 = 1 ∧ s.nuH2O = 2 := by
  have h1 : s.nuCH4 = -1 := s.methaneConsumed
  have h2 : s.nuCO2 = 1 := by
    have := s.cBalance; omega
  have h3 : s.nuH2O = 2 := by
    have := s.hBalance; omega
  have h4 : s.nuO2 = -2 := by
    have := s.oBalance; omega
  exact ⟨h1, h4, h2, h3⟩

/-- Species-indexed stoichiometric coefficients from ν. -/
def stoich (s : CombustionStoichiometry) : Species → ℤ
  | .CH4 => s.nuCH4
  | .O2 => s.nuO2
  | .CO2 => s.nuCO2
  | .H2O => s.nuH2O

/-- Formation enthalpies at 298 K from the Part 4.6 data table (kJ mol⁻¹);
O₂(g) is an element in its standard state, so its formation enthalpy is 0. -/
def formationEnthalpy298 : Species → ℝ
  | .CH4 => -74.8
  | .O2 => 0
  | .CO2 => -393.5
  | .H2O => -241.8

/-- Constant heat capacities from the Part 4.6 data table (J mol⁻¹ K⁻¹). -/
def heatCapacity : Species → ℝ
  | .CH4 => 35
  | .O2 => 29
  | .CO2 => 37
  | .H2O => 34

/-- Hess's law: reaction enthalpy at 298 K from formation enthalpies,
ΔrH°₂₉₈ = Σ ν·ΔfH°₂₉₈ (with ν > 0 for products). -/
noncomputable def reactionEnthalpy298 (s : CombustionStoichiometry) : ℝ :=
  (stoich s .CH4 : ℝ) * formationEnthalpy298 .CH4 +
  (stoich s .O2 : ℝ) * formationEnthalpy298 .O2 +
  (stoich s .CO2 : ℝ) * formationEnthalpy298 .CO2 +
  (stoich s .H2O : ℝ) * formationEnthalpy298 .H2O

/-- Reaction heat capacity, ΔCₚ = Σ ν·Cₚ (J mol⁻¹ K⁻¹). -/
noncomputable def reactionHeatCapacity (s : CombustionStoichiometry) : ℝ :=
  (stoich s .CH4 : ℝ) * heatCapacity .CH4 +
  (stoich s .O2 : ℝ) * heatCapacity .O2 +
  (stoich s .CO2 : ℝ) * heatCapacity .CO2 +
  (stoich s .H2O : ℝ) * heatCapacity .H2O

/-- Kirchhoff's law with temperature-independent heat capacities (the Cₚ data
supplied by the problem carry no temperature dependence):
ΔrH(T) = ΔrH°₂₉₈ + ΔCₚ·(T − 298).  `T` is in kelvin and `dCpKJ` in
kJ mol⁻¹ K⁻¹. -/
noncomputable def reactionEnthalpyAt (s : CombustionStoichiometry)
    (dCpKJ : ℝ) (T : ℝ) : ℝ :=
  reactionEnthalpy298 s + dCpKJ * (T - 298)

/-- The stoichiometry used for the numerical evaluation, satisfying the atom
balances by construction. -/
noncomputable def combustion : CombustionStoichiometry :=
  ⟨-1, -2, 1, 2, by omega, by omega, by omega, rfl⟩

/-- The exact raw value of the requested output: the methane combustion
enthalpy at 2000 K (kJ mol⁻¹), before any reporting rounding. -/
noncomputable def rawAnswer2000 : ℝ :=
  reactionEnthalpyAt combustion (reactionHeatCapacity combustion / 1000) 2000

/-- **Part 4.6 prerequisite, proved from the problem data (Hess's law):**
ΔrH°₂₉₈ = −802.3 kJ mol⁻¹ for CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g). -/
theorem reaction_enthalpy_298 : reactionEnthalpy298 combustion = -802.3 := by
  unfold reactionEnthalpy298 stoich formationEnthalpy298 combustion
  norm_num

/-- **Reaction heat capacity from the problem data:** ΔCₚ = 12 J mol⁻¹ K⁻¹. -/
theorem reaction_heat_capacity : reactionHeatCapacity combustion = 12 := by
  unfold reactionHeatCapacity stoich heatCapacity combustion
  norm_num

/-- **Part 4.7 answer (Kirchhoff's law, constant Cₚ):**
ΔrH₂₀₀₀ = −781.876 kJ mol⁻¹, exactly, from the problem data. -/
theorem reaction_enthalpy_2000_exact :
    reactionEnthalpyAt combustion (reactionHeatCapacity combustion / 1000) 2000
      = -781.876 := by
  rw [reactionEnthalpyAt, reaction_enthalpy_298, reaction_heat_capacity]
  norm_num

/-- The raw-answer definition evaluates to the same exact value. -/
theorem rawAnswer2000_eq : rawAnswer2000 = -781.876 :=
  reaction_enthalpy_2000_exact

/-- **Reporting certificate:** −782 kJ mol⁻¹ is the three-significant-figure
round-to-nearest (ties away from zero) display of the raw value at quantum
1 kJ mol⁻¹.  Since the raw value is negative, the contract requires
`(−782) − 1/2 < −781.876 ≤ (−782) + 1/2`, i.e. the nearest integer multiple
of 1 to −781.876 is −782. -/
theorem reported_at_2000 : ReportsAtQuantum (-781.876 : ℝ) (-782) 1 := by
  refine ⟨by norm_num, ⟨-782, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num : ¬(0 : ℝ) ≤ -781.876)]
  constructor <;> norm_num

/-- **Final submission validity:** the solver-facing submission with raw value
−781.876 kJ mol⁻¹, reported value −782 kJ mol⁻¹ at quantum 1 kJ mol⁻¹,
satisfies the answer-blind reporting contract for the target's exact raw
expression. -/
theorem final_submission_valid :
    ValidNumericSubmission rawAnswer2000 ⟨-781.876, -782, 1⟩ :=
  ⟨rawAnswer2000_eq.symm, reported_at_2000⟩

end IChO2026Problems.Icho2026T4A7

#print axioms IChO2026Problems.Icho2026T4A7.reaction_enthalpy_2000_exact
#print axioms IChO2026Problems.Icho2026T4A7.final_submission_valid
