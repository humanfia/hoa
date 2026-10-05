import Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-!
# IPhO 2026 T3--B2: reversible adiabatic temperature change

This file adapts the answer-free shared paramagnetic model to the source data
of T3--B2.  The requested signed temperature change is constrained by the
unevaluated adiabatic endpoint relation; no closed form or sign for the change
is included in a declaration signature.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_3_B_2

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-- The apparatus, initial state data, and prescribed final field from the
source question.  The final temperature and its signed change are deliberately
not source-data fields. -/
structure SourceData where
  apparatus : ParamagneticData
  initialTemperature : Temperature
  initialFieldStrength : MagneticFieldStrength
  finalFieldStrength : MagneticFieldStrength

/-- Physical apparatus data together with positive absolute initial
temperature and positive initial and final field magnitudes. -/
def SourceData.IsAdmissible (S : SourceData) : Prop :=
  S.apparatus.IsPhysical ∧
  0 < coherentCoordinate S.apparatus.torus.unitSystem S.initialTemperature ∧
  0 < coherentCoordinate S.apparatus.torus.unitSystem S.initialFieldStrength ∧
  0 < coherentCoordinate S.apparatus.torus.unitSystem S.finalFieldStrength

/-- A reversible adiabatic quasistatic leg with exactly the source endpoints.
The shared endpoint-leg predicate supplies positive final temperature, regular
equilibrium, every local source law, and pointwise zero heat. -/
def IsSourceReversibleAdiabaticLeg (S : SourceData) (finalTemperature : Temperature)
    (p : QuasistaticProcess) : Prop :=
  S.IsAdmissible ∧
  IsReversibleAdiabaticEndpointLeg S.apparatus
    S.initialTemperature S.initialFieldStrength
    finalTemperature S.finalFieldStrength p

/-- Every source leg carries the table's equation of state, heat-capacity and
internal-energy laws, the vacuum-subtracted material-work law, the
entering-positive first law, and the adiabatic zero-heat condition.  The
apparatus volume occurring below is fixed data, rather than a path variable. -/
theorem source_laws_of_reversibleAdiabaticLeg (S : SourceData)
    (finalTemperature : Temperature) (p : QuasistaticProcess)
    (hleg : IsSourceReversibleAdiabaticLeg S finalTemperature p) :
    (∀ τ ∈ Set.Icc p.a p.b,
      SatisfiesEquationOfState S.apparatus (p.state τ)) ∧
    (∀ τ ∈ Set.Icc p.a p.b,
      coherentCoordinate S.apparatus.torus.unitSystem
          (heatCapacityAtConstantMagnetization S.apparatus
            (p.state τ).temperature) =
        coherentCoordinate S.apparatus.torus.unitSystem
            S.apparatus.material.amount *
          coherentCoordinate S.apparatus.torus.unitSystem
            S.apparatus.material.heatCapacityCoefficient /
          coherentCoordinate S.apparatus.torus.unitSystem
              (p.state τ).temperature ^ 2) ∧
    SatisfiesInternalEnergyLaw S.apparatus p ∧
    (∀ τ ∈ Set.Icc p.a p.b,
      coherentCoordinate S.apparatus.torus.unitSystem
          (materialWorkIncrement S.apparatus p τ) =
        coherentCoordinate S.apparatus.torus.unitSystem
            S.apparatus.material.vacuumPermeability *
          coherentCoordinate S.apparatus.torus.unitSystem
            S.apparatus.torus.volume *
          coherentCoordinate S.apparatus.torus.unitSystem
            (p.state τ).fieldStrength *
          deriv
            (fun t ↦ coherentCoordinate S.apparatus.torus.unitSystem
              (p.state t).magnetization) τ) ∧
    SatisfiesFirstLaw S.apparatus p ∧
    IsAdiabatic S.apparatus p := by
  rcases hleg with ⟨_, hendpointLeg⟩
  rcases hendpointLeg with
    ⟨_, _, _, _, hrev, hadiabatic, _⟩
  rcases hrev with
    ⟨hregular, hAmpere, hFaraday, hsourceBalance, hsourceWork,
      hinternalEnergy, hfirstLaw⟩
  have hregular' := hregular
  rcases hregular with
    ⟨_, _, _, _, _, _, _, hstate⟩
  refine ⟨?_, ?_, hinternalEnergy, ?_, hfirstLaw, hadiabatic⟩
  · intro τ hτ
    exact (hstate τ hτ).2
  · intro τ hτ
    simp only [heatCapacityAtConstantMagnetization,
      coherentCoordinate_quantityFromCoherentCoordinate]
  · intro τ hτ
    exact
      (source_vacuum_material_work_decomposition S.apparatus p hregular'
        hAmpere hFaraday hsourceBalance hsourceWork τ hτ).2

/-- Answer-free predicate for the requested signed temperature difference.
It imposes the shared governing integral relation on the final absolute
temperature `initialTemperature + temperatureChange`. -/
def IsRequestedTemperatureChange (S : SourceData)
    (temperatureChange : TemperatureDifference) : Prop :=
  IsEndpointTemperatureChangeSolution S.apparatus
    S.initialTemperature S.initialFieldStrength S.finalFieldStrength
    temperatureChange

/-- The signed difference of the endpoints of any physical source leg obeys
the requested-change predicate. -/
theorem temperatureChange_of_reversibleAdiabaticLeg (S : SourceData)
    (finalTemperature : Temperature) (p : QuasistaticProcess)
    (hleg : IsSourceReversibleAdiabaticLeg S finalTemperature p) :
    IsRequestedTemperatureChange S
      (finalTemperature - S.initialTemperature) := by
  rcases hleg with ⟨_, hendpointLeg⟩
  unfold IsRequestedTemperatureChange
  unfold IsEndpointTemperatureChangeSolution
  have hrelation := adiabatic_endpoint_relation_of_leg S.apparatus
    S.initialTemperature S.initialFieldStrength finalTemperature
    S.finalFieldStrength p hendpointLeg
  have hsum :
      S.initialTemperature +
          (finalTemperature - S.initialTemperature) = finalTemperature := by
    exact add_sub_cancel S.initialTemperature finalTemperature
  rw [hsum]
  exact hrelation

/-- An admissible source datum determines a unique signed temperature change
through the governing unevaluated adiabatic endpoint relation. -/
theorem endpointTemperatureChange_existsUnique (S : SourceData)
    (hS : S.IsAdmissible) :
    ∃! temperatureChange : TemperatureDifference,
      IsRequestedTemperatureChange S temperatureChange := by
  rcases hS with ⟨hphysical, hinitialTemperature,
    hinitialFieldStrength, hfinalFieldStrength⟩
  unfold IsRequestedTemperatureChange
  exact
    Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics.endpointTemperatureChange_existsUnique
      S.apparatus S.initialTemperature S.initialFieldStrength
      S.finalFieldStrength hphysical hinitialTemperature
      hinitialFieldStrength hfinalFieldStrength

end Ipho2026Gpt56solBlind.ProblemIPhO2026_3_B_2
