import ChemistryLib.Thermochemistry.ReactionEnthalpy
import ChemistryLib.Thermodynamics.OpenNetworks.EntropyProduction
import ChemistryLib.Thermodynamics.OpenNetworks.RateEquation

/-!
# Energy and entropy balances for open reaction networks

Chemostats exchange both matter and thermodynamic quantities with an open
reaction network.  Their chemical-work rate is the current-weighted sum of
chemical potentials, while their enthalpy throughput is the analogous sum of
standard enthalpies.  The enthalpy and entropy balances below record the
corresponding first- and second-law decompositions.

This follows Rao and Esposito (2016), Sections III.B--III.E.1, equations (58),
(65), and (67)--(69).  Source artifact: `https://arxiv.org/pdf/1602.07257v3`,
SHA-256 `ed86193f16e3df2561a52fda55bfc63ba6086969494520122485193d9fce77d1`.
Sanitized contract: `research:rao_esposito_2016:entropy_energy_balance`.
-/

namespace ChemistryLib.Thermodynamics.OpenNetworks

/-- The enthalpy balance for an open network: the enthalpy rate is the heat
flow plus the standard-enthalpy throughput carried by chemostat currents. -/
def EnthalpyBalance : ∀ {Species : Type}, Finset Species →
    (Species → ℝ) → (Species → ℝ) → ℝ → ℝ → Prop :=
  fun Y current standardEnthalpy enthalpyRate heatFlow ↦
    enthalpyRate = heatFlow +
      Y.sum (fun species ↦ current species * standardEnthalpy species)

/-- Chemical work supplied by chemostats, obtained by pairing each reservoir
current with the corresponding chemical potential. -/
def chemicalWorkRate : ∀ {Species : Type}, Finset Species →
    (Species → ℝ) → (Species → ℝ) → ℝ :=
  fun Y current chemicalPotential ↦
    Y.sum (fun species ↦ current species * chemicalPotential species)

/-- Enthalpy carried through the chemostats, obtained by pairing each
reservoir current with the corresponding standard enthalpy. -/
def chemostatEnthalpyThroughput : ∀ {Species : Type}, Finset Species →
    (Species → ℝ) → (Species → ℝ) → ℝ :=
  fun Y current standardEnthalpy ↦
    Y.sum (fun species ↦ current species * standardEnthalpy species)

/-- The enthalpy balance exposes the heat-flow and chemostat-throughput
contributions to the total enthalpy rate. -/
theorem enthalpy_rate_eq : ∀ {Species : Type} (Y : Finset Species)
    (current standardEnthalpy : Species → ℝ) (enthalpyRate heatFlow : ℝ),
    EnthalpyBalance Y current standardEnthalpy enthalpyRate heatFlow →
      enthalpyRate = heatFlow +
        chemostatEnthalpyThroughput Y current standardEnthalpy := by
  intro Species Y current standardEnthalpy enthalpyRate heatFlow hBalance
  exact hBalance

/-- Entropy exchanged with the environment: total entropy rate minus the
internally produced entropy rate. -/
def entropyFlowRate : ℝ → ℝ → ℝ :=
  fun entropyRate entropyProductionRate ↦
    entropyRate - entropyProductionRate

/-- The total entropy rate is the sum of entropy production and entropy flow. -/
theorem entropy_rate_balance : ∀ (entropyRate entropyProductionRate : ℝ),
    entropyRate = entropyProductionRate +
      entropyFlowRate entropyRate entropyProductionRate := by
  intro entropyRate entropyProductionRate
  simp [entropyFlowRate]

end ChemistryLib.Thermodynamics.OpenNetworks
