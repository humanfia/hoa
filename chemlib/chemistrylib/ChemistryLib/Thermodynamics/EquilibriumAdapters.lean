import ChemistryLib.Thermodynamics.TemperatureAdapters
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Physlib.Thermodynamics.IdealGas.Basic

/-!
# Equilibrium adapters

Thin, assumption-preserving adapters for Physlib's canonical-ensemble and monophase
ideal-gas equilibrium interfaces.

Grounding sources:

* `grounding:Physlib.StatisticalMechanics.CanonicalEnsemble.Finite` at revision
  `1706ae68b63996f1d97717e672e50c9e3933d933`
* `grounding:Physlib.Thermodynamics.IdealGas.Basic` at revision
  `1706ae68b63996f1d97717e672e50c9e3933d933`
-/

namespace ChemistryLib.Thermodynamics

/-- The canonical probability density, transparently adapted from Physlib. -/
noncomputable abbrev canonicalProbability {ι : Type} [MeasurableSpace ι]
    (ensemble : CanonicalEnsemble ι) (T : Temperature) (i : ι) : ℝ :=
  ensemble.probability T i

/-- The canonical mean energy, transparently adapted from Physlib. -/
noncomputable abbrev canonicalMeanEnergy {ι : Type} [MeasurableSpace ι]
    (ensemble : CanonicalEnsemble ι) (T : Temperature) : ℝ :=
  ensemble.meanEnergy T

/-- The canonical thermodynamic entropy, transparently adapted from Physlib. -/
noncomputable abbrev canonicalEntropy {ι : Type} [MeasurableSpace ι]
    (ensemble : CanonicalEnsemble ι) (T : Temperature) : ℝ :=
  ensemble.thermodynamicEntropy T

/-- The canonical Helmholtz free energy, transparently adapted from Physlib. -/
noncomputable abbrev canonicalHelmholtzFreeEnergy {ι : Type} [MeasurableSpace ι]
    (ensemble : CanonicalEnsemble ι) (T : Temperature) : ℝ :=
  ensemble.helmholtzFreeEnergy T

/-- The monophase ideal-gas entropy, transparently adapted from Physlib. -/
noncomputable abbrev idealGasEntropy :
    ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  entropy

/-- For a finite canonical ensemble, thermodynamic entropy is Shannon entropy. -/
theorem canonicalEntropy_eq_shannonEntropy
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ensemble : CanonicalEnsemble ι) [CanonicalEnsemble.IsFinite ensemble]
    (T : Temperature) :
    canonicalEntropy ensemble T = ensemble.shannonEntropy T := by
  exact ensemble.thermodynamicEntropy_eq_shannonEntropy T

/-- Canonical Helmholtz free energy satisfies `F = U - T S` under Physlib's assumptions. -/
theorem canonicalHelmholtz_eq_meanEnergy_sub_temperature_mul_entropy
    {ι : Type} [MeasurableSpace ι]
    (ensemble : CanonicalEnsemble ι) (T : Temperature)
    [MeasureTheory.IsFiniteMeasure (ensemble.μBolt T)] [NeZero ensemble.μ] :
    0 < T.val →
      MeasureTheory.Integrable ensemble.energy (ensemble.μProd T) →
        canonicalHelmholtzFreeEnergy ensemble T =
          canonicalMeanEnergy ensemble T - T.val * canonicalEntropy ensemble T := by
  intro hT hE
  exact
    ensemble.helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy T hT hE

/-- For a finite canonical ensemble, mean energy is its probability-weighted energy sum. -/
theorem canonicalMeanEnergy_eq_finite_sum
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ensemble : CanonicalEnsemble ι) [CanonicalEnsemble.IsFinite ensemble]
    (T : Temperature) :
    canonicalMeanEnergy ensemble T =
      ∑ i, ensemble.energy i * canonicalProbability ensemble T i := by
  exact ensemble.meanEnergy_of_fintype T

/-- Equal ideal-gas entropies at fixed amount imply the logarithmic adiabatic relation. -/
theorem idealGas_adiabatic_relation_log
    {s0 U0 V0 N0 c R Ua Ub Va Vb N : ℝ} :
    0 < Ua → 0 < Ub → 0 < Va → 0 < Vb → 0 < N →
      0 < U0 → 0 < V0 → 0 < R →
        idealGasEntropy c R s0 U0 V0 N0 Ua Va N =
          idealGasEntropy c R s0 U0 V0 N0 Ub Vb N →
          c * Real.log (Ua / Ub) + Real.log (Va / Vb) = 0 := by
  exact adiabatic_relation_log

/-- Equal ideal-gas entropies at fixed amount imply the product adiabatic relation. -/
theorem idealGas_adiabatic_relation_product
    {s0 U0 V0 N0 c R Ua Ub Va Vb N : ℝ} :
    0 < Ua → 0 < Ub → 0 < Va → 0 < Vb → 0 < N →
      0 < U0 → 0 < V0 → 0 < R →
        idealGasEntropy c R s0 U0 V0 N0 Ua Va N =
          idealGasEntropy c R s0 U0 V0 N0 Ub Vb N →
          Real.rpow (Ua / Ub) c * (Va / Vb) = 1 := by
  exact adiabatic_relation_UaUbVaVb

end ChemistryLib.Thermodynamics
