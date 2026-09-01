import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T4 (Q4-2) — Standard enthalpy of methane combustion at 298 K

**Source contract** (problem_text, Q4-2 box 4.6 on `T4_page-2.png`):

* Requested output: `ΔrH°₂₉₈` in `kJ mol⁻¹` for **one mole of methane
  combustion reaction** at `298 K`, with **all species gaseous**.
* Stipulated thermodynamic data (problem_image, table on `T4_page-2.png`;
  stipulated constants exact as printed):
  `ΔfH°₂₉₈(CH₄) = -74.8 kJ mol⁻¹`, `ΔfH°₂₉₈(H₂O, gas) = -241.8 kJ mol⁻¹`,
  `ΔfH°₂₉₈(CO₂) = -393.5 kJ mol⁻¹`, `C_P(CH₄) = 35 J mol⁻¹ K⁻¹`,
  `C_P(H₂O, gas) = 34 J mol⁻¹ K⁻¹`, `C_P(O₂) = 29 J mol⁻¹ K⁻¹`,
  `C_P(CO₂) = 37 J mol⁻¹ K⁻¹`.
* The italic line `If you did not get a result for 4.6, use
  ΔH₂₉₈ = -750 kJ mol⁻¹ for further calculations` is a printed fallback
  authorized only for later parts; it is **not** used for this part.

**Governing relation** (trusted_general_law, Hess's law): for the stipulated
reaction written per mole of methane,

```
CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)
```

the standard reaction enthalpy at the reference temperature 298 K is the
stoichiometric sum of standard formation enthalpies,

```
ΔrH°₂₉₈ = Σ νₛ · ΔfH°₂₉₈(s)
        = ΔfH°₂₉₈(CO₂) + 2·ΔfH°₂₉₈(H₂O,g) − ΔfH°₂₉₈(CH₄) − 2·ΔfH°₂₉₈(O₂)
        = (−393.5) + 2·(−241.8) − (−74.8) − 2·(0) = −802.3 kJ mol⁻¹,
```

using `ΔfH°₂₉₈(O₂, g) = 0` for an element in its standard state
(trusted_general_law).  Because 298 K is the reference temperature of the
formation data, the printed heat capacities are not needed for this part;
they are preserved as data for faithfulness.  No intermediate rounding is
applied (source reporting policy).

**Reporting** (uniform blind evaluation default; the problem requests no
explicit precision): three significant figures, ties half away from zero.
At magnitude `8.023·10²` the quantum is `1 kJ mol⁻¹`; the raw value
`−802.3` lies in `(−802.5, −801.5]`, so the reported value is `−802`.

The two result contracts at the end are the answer-blind certificates: the
raw contract carries the derivation spec together with a non-degenerate
certified rational interval `[−802.4, −802.2]` (raw ± one displayed decimal
quantum `0.1 kJ mol⁻¹` of the source data table) for the unrounded value, and
the reported contract carries the `ReportsAtQuantum` certificate for `−802`.
-/

namespace IChO2026.T4.A6

/-- The four chemical species of the methane combustion reaction at 298 K,
every one in the gas phase as stipulated (problem_text, T4-A6: "Assume all
species are gaseous").  Water appears only as `waterGas`, matching the
printed table entry `ΔfH°₂₉₈(H₂O, gas)`. -/
inductive Species
  | methane
  | oxygen
  | carbonDioxide
  | waterGas
deriving DecidableEq

/-- Signed stoichiometric coefficients `ν` for the combustion of one mole of
methane, `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)` (products positive, reactants
negative).  The per-mole-of-methane basis is the problem's requested basis
("for one mole of methane combustion reaction"). -/
def stoichiometricCoefficient : Species → ℝ
  | .methane => -1
  | .oxygen => -2
  | .carbonDioxide => 1
  | .waterGas => 2

/-- Standard molar formation enthalpies at 298 K in `kJ mol⁻¹`, as printed in
the problem's thermodynamic data table (problem_image, `T4_page-2.png`;
stipulated constants exact as printed).  `O₂(g)` is an element in its
standard state, so `ΔfH°₂₉₈(O₂) = 0` (trusted_general_law). -/
def standardFormationEnthalpy298 : Species → ℝ
  | .methane => -74.8
  | .oxygen => 0
  | .carbonDioxide => -393.5
  | .waterGas => -241.8

/-- Molar heat capacities at constant pressure in `J mol⁻¹ K⁻¹`, as printed in
the problem's thermodynamic data table (problem_image, `T4_page-2.png`).
These data are stipulated by the problem but are not needed at 298 K, the
reference temperature of the formation enthalpies; they are preserved here
for faithfulness to the source contract. -/
def heatCapacityP : Species → ℝ
  | .methane => 35
  | .oxygen => 29
  | .carbonDioxide => 37
  | .waterGas => 34

/-- Number of carbon atoms per formula unit of each species. -/
def carbonCount : Species → ℝ
  | .methane => 1
  | .oxygen => 0
  | .carbonDioxide => 1
  | .waterGas => 0

/-- Number of hydrogen atoms per formula unit of each species. -/
def hydrogenCount : Species → ℝ
  | .methane => 4
  | .oxygen => 0
  | .carbonDioxide => 0
  | .waterGas => 2

/-- Number of oxygen atoms per formula unit of each species. -/
def oxygenCount : Species → ℝ
  | .methane => 0
  | .oxygen => 2
  | .carbonDioxide => 2
  | .waterGas => 1

/-- Atom conservation for the stipulated reaction on the element counted by
`atomCount`: `Σₛ νₛ · atomCount s = 0` over the four-species reaction domain
(problem_text stoichiometry `CH₄ + 2 O₂ → CO₂ + 2 H₂O`). -/
def AtomConserved (atomCount : Species → ℝ) : Prop :=
  stoichiometricCoefficient .methane * atomCount .methane
    + stoichiometricCoefficient .oxygen * atomCount .oxygen
    + stoichiometricCoefficient .carbonDioxide * atomCount .carbonDioxide
    + stoichiometricCoefficient .waterGas * atomCount .waterGas = 0

/-- **Raw (unrounded) standard reaction enthalpy at 298 K** in `kJ mol⁻¹` for
the combustion of one mole of methane with all species gaseous, by Hess's law:
`ΔrH°₂₉₈ = Σₛ νₛ · ΔfH°₂₉₈(s)` over the four species of the stipulated
reaction.  No intermediate rounding is applied; the body is the explicit
source-derived formula over the printed data, not a precomputed decimal. -/
def methaneCombustionEnthalpy298Raw : ℝ :=
  stoichiometricCoefficient .carbonDioxide * standardFormationEnthalpy298 .carbonDioxide
    + stoichiometricCoefficient .waterGas * standardFormationEnthalpy298 .waterGas
    + stoichiometricCoefficient .methane * standardFormationEnthalpy298 .methane
    + stoichiometricCoefficient .oxygen * standardFormationEnthalpy298 .oxygen

/-- **Raw derivation specification** for the methane combustion enthalpy at
298 K: the stipulated reaction `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)` is
atom-balanced on carbon, hydrogen, and oxygen; oxygen is an element in its
standard state with zero formation enthalpy; and the raw carrier is exactly
the Hess-law stoichiometric sum of the printed formation enthalpies. -/
def MethaneCombustionEnthalpy298Spec : Prop :=
  AtomConserved carbonCount
    ∧ AtomConserved hydrogenCount
    ∧ AtomConserved oxygenCount
    ∧ standardFormationEnthalpy298 .oxygen = 0
    ∧ methaneCombustionEnthalpy298Raw =
        stoichiometricCoefficient .carbonDioxide * standardFormationEnthalpy298 .carbonDioxide
          + stoichiometricCoefficient .waterGas * standardFormationEnthalpy298 .waterGas
          + stoichiometricCoefficient .methane * standardFormationEnthalpy298 .methane
          + stoichiometricCoefficient .oxygen * standardFormationEnthalpy298 .oxygen

/-- **Raw result contract** (answer-blind): the derivation specification
`MethaneCombustionEnthalpy298Spec` holds for the source-derived raw
expression `methaneCombustionEnthalpy298Raw = Σ ν·ΔfH°₂₉₈ = −802.3 kJ mol⁻¹`,
together with the certified non-degenerate interval
`−802.4 = −4012/5 ≤ raw ≤ −4011/5 = −802.2` (raw ± the displayed decimal
quantum `0.1 kJ mol⁻¹` of the printed formation-enthalpy data). -/
theorem raw_result_contract :
    (IChO2026.T4.A6.MethaneCombustionEnthalpy298Spec) ∧
      (((-4012 : ℝ) / 5) ≤ (IChO2026.T4.A6.methaneCombustionEnthalpy298Raw) ∧
        (IChO2026.T4.A6.methaneCombustionEnthalpy298Raw) ≤ ((-4011 : ℝ) / 5)) := by
  -- Hess-law sum over the printed data evaluates exactly to `-802.3 kJ mol⁻¹`.
  have hraw : methaneCombustionEnthalpy298Raw = -802.3 := by
    norm_num [methaneCombustionEnthalpy298Raw, stoichiometricCoefficient,
      standardFormationEnthalpy298]
  refine ⟨⟨?_, ?_, ?_, ?_, rfl⟩, ?_, ?_⟩
  · -- Carbon balance: `(-1)·1 + (-2)·0 + 1·1 + 2·0 = 0`.
    norm_num [AtomConserved, stoichiometricCoefficient, carbonCount]
  · -- Hydrogen balance: `(-1)·4 + (-2)·0 + 1·0 + 2·2 = 0`.
    norm_num [AtomConserved, stoichiometricCoefficient, hydrogenCount]
  · -- Oxygen balance: `(-1)·0 + (-2)·2 + 1·2 + 2·1 = 0`.
    norm_num [AtomConserved, stoichiometricCoefficient, oxygenCount]
  · -- `O₂(g)` is an element in its standard state.
    rfl
  · rw [hraw]; norm_num
  · rw [hraw]; norm_num

/-- **Reported result contract** (answer-blind): at the three-significant-
figure quantum `1 kJ mol⁻¹` (ties half away from zero), the raw value
`−802.3 kJ mol⁻¹` is reported as `−802 kJ mol⁻¹`, since
`−802.3 ∈ (−802 − 1/2, −802 + 1/2]`. -/
theorem reported_result_contract :
    IChO2026Chem.Reporting.ReportsAtQuantum (IChO2026.T4.A6.methaneCombustionEnthalpy298Raw)
      (-802 : ℝ) (1 : ℝ) := by
  -- The raw value is negative, so the reporting interval is half-open on the
  -- left: `-802 - 1/2 < raw ≤ -802 + 1/2`, i.e. `-802.5 < -802.3 ≤ -801.5`.
  have hraw : methaneCombustionEnthalpy298Raw = -802.3 := by
    norm_num [methaneCombustionEnthalpy298Raw, stoichiometricCoefficient,
      standardFormationEnthalpy298]
  refine ⟨one_pos, ⟨-802, by norm_num⟩, ?_⟩
  rw [hraw]
  have hneg : ¬ (0 : ℝ) ≤ -802.3 := by norm_num
  rw [if_neg hneg]
  norm_num

end IChO2026.T4.A6
