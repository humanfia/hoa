import Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-!
# IPhO 2026 Problem 3 A.3

This file gives an answer-free specification of the signed work increment on
the paramagnetic material in the lossless, densely wound torus of Figure 3a.
The total source work and the corresponding vacuum-core work are specified
independently before their difference is characterized as material work.
-/

noncomputable section

open Set

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_3_A_3

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-- Typed apparatus, quasistatic path, observation point, and signed Joule
heating path for Figure 3a.  The process parameter is dimensionless, so every
work-path value is an energy increment per unit parameter. -/
structure SourceData where
  apparatus : ParamagneticData
  process : QuasistaticProcess
  selectedParameter : ℝ
  wireHeating : ℝ → Energy

/-- The material-filled and vacuum-core windings obey the common, positively
oriented `N A` linked-flux law throughout the physical process interval. -/
def HasFigure3aFluxLinkage (X : SourceData) : Prop :=
  ∀ τ ∈ Set.Icc X.process.a X.process.b,
    coherentCoordinate X.apparatus.torus.unitSystem
        (linkedFlux X.apparatus (X.process.state τ)) =
      (X.apparatus.torus.turns : ℝ) *
        coherentCoordinate X.apparatus.torus.unitSystem
          X.apparatus.torus.crossSectionArea *
        coherentCoordinate X.apparatus.torus.unitSystem
          (magneticFluxDensity X.apparatus (X.process.state τ)) ∧
    coherentCoordinate X.apparatus.torus.unitSystem
        (vacuumLinkedFlux X.apparatus (X.process.state τ)) =
      (X.apparatus.torus.turns : ℝ) *
        coherentCoordinate X.apparatus.torus.unitSystem
          X.apparatus.torus.crossSectionArea *
        coherentCoordinate X.apparatus.torus.unitSystem
          X.apparatus.material.vacuumPermeability *
        coherentCoordinate X.apparatus.torus.unitSystem
          (X.process.state τ).fieldStrength

/-- The resistance of the insulated winding is neglected pointwise, rather
than merely assuming that its net Joule heat vanishes. -/
def HasZeroWireHeating (X : SourceData) : Prop :=
  ∀ τ ∈ Set.Icc X.process.a X.process.b,
    coherentCoordinate X.apparatus.torus.unitSystem (X.wireHeating τ) = 0

/-- All geometric, constitutive, linkage, and oriented circuit laws used in
the lossless Figure 3a model.  The two sign reversals in Faraday's law and the
external-source balance remain separate hypotheses. -/
def SatisfiesSourceLaws (X : SourceData) : Prop :=
  X.apparatus.IsPhysical ∧
  X.process.IsRegular X.apparatus ∧
  X.selectedParameter ∈ Set.Icc X.process.a X.process.b ∧
  (∀ τ ∈ Set.Icc X.process.a X.process.b,
    coherentCoordinate X.apparatus.torus.unitSystem
        (magneticFluxDensity X.apparatus (X.process.state τ)) =
      coherentCoordinate X.apparatus.torus.unitSystem
          X.apparatus.material.vacuumPermeability *
        (coherentCoordinate X.apparatus.torus.unitSystem
            (X.process.state τ).fieldStrength +
          coherentCoordinate X.apparatus.torus.unitSystem
            (X.process.state τ).magnetization)) ∧
  HasFigure3aFluxLinkage X ∧
  SatisfiesAmpereLaw X.apparatus X.process ∧
  SatisfiesFaradayLaw X.apparatus X.process ∧
  SatisfiesSourceBalance X.apparatus X.process ∧
  HasZeroWireHeating X ∧
  SatisfiesSourceWorkLaw X.apparatus X.process

/-- A candidate total source-work increment, stated at circuit level before
using Faraday's law or the torus geometry. -/
def IsSourceWorkIncrement (X : SourceData) (W_source : Energy) : Prop :=
  coherentCoordinate X.apparatus.torus.unitSystem W_source =
    coherentCoordinate X.apparatus.torus.unitSystem
        (X.process.windingCurrent X.selectedParameter) *
      coherentCoordinate X.apparatus.torus.unitSystem
        (X.process.sourceEmfIncrement X.selectedParameter)

/-- A candidate work increment for the same winding, current, applied field,
and geometry after replacing the material by vacuum. -/
def IsVacuumCoreWorkIncrement (X : SourceData) (W_vacuum : Energy) : Prop :=
  coherentCoordinate X.apparatus.torus.unitSystem W_vacuum =
    coherentCoordinate X.apparatus.torus.unitSystem
        (X.process.windingCurrent X.selectedParameter) *
      deriv
        (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
          (vacuumLinkedFlux X.apparatus (X.process.state τ)))
        X.selectedParameter

/-- The derivative of the magnetic-flux density obeys the differentiated
constitutive law at the selected process point.  It is deliberately retained
in unexpanded constitutive form. -/
def SatisfiesConstitutiveDerivativeAt (X : SourceData) : Prop :=
  deriv
      (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
        (magneticFluxDensity X.apparatus (X.process.state τ)))
      X.selectedParameter =
    deriv
      (fun τ ↦
        coherentCoordinate X.apparatus.torus.unitSystem
            X.apparatus.material.vacuumPermeability *
          (coherentCoordinate X.apparatus.torus.unitSystem
              (X.process.state τ).fieldStrength +
            coherentCoordinate X.apparatus.torus.unitSystem
              (X.process.state τ).magnetization))
      X.selectedParameter

/-- A candidate material-work increment is obtained only through a balance
between independently specified source and vacuum-core work increments.  No
closed expression for the requested work is built into this predicate. -/
def IsMaterialWorkIncrement (X : SourceData) (W_material : Energy) : Prop :=
  SatisfiesConstitutiveDerivativeAt X ∧
  ∃ W_source W_vacuum : Energy,
    IsSourceWorkIncrement X W_source ∧
    IsVacuumCoreWorkIncrement X W_vacuum ∧
    W_source = W_vacuum + W_material

/-- Under the lossless source laws, the circuit-level source-work candidate
is precisely the work increment recorded by the quasistatic process. -/
lemma sourceWorkIncrement_iff_process (X : SourceData)
    (hX : SatisfiesSourceLaws X) (W_source : Energy) :
    IsSourceWorkIncrement X W_source ↔
      W_source = X.process.sourceWorkIncrement X.selectedParameter := by
  rcases hX with
    ⟨_, _, hselected, _, _, _, _, _, _, hsourceWork⟩
  unfold IsSourceWorkIncrement
  rw [← hsourceWork X.selectedParameter hselected]
  exact coordinateInSI_eq_iff X.apparatus.torus.unitSystem W_source
    (X.process.sourceWorkIncrement X.selectedParameter)

/-- The local vacuum-core candidate agrees with the shared typed vacuum-work
construction. -/
lemma vacuumCoreWorkIncrement_iff_shared (X : SourceData)
    (hX : SatisfiesSourceLaws X) (W_vacuum : Energy) :
    IsVacuumCoreWorkIncrement X W_vacuum ↔
      W_vacuum = vacuumWorkIncrement X.apparatus X.process
        X.selectedParameter := by
  clear hX
  unfold IsVacuumCoreWorkIncrement
  constructor
  · intro hcoordinate
    simpa only [vacuumWorkIncrement] using
      (quantityFromCoherentCoordinate_unique
        X.apparatus.torus.unitSystem energyDimension
        (coherentCoordinate X.apparatus.torus.unitSystem
            (X.process.windingCurrent X.selectedParameter) *
          deriv
            (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
              (vacuumLinkedFlux X.apparatus (X.process.state τ)))
            X.selectedParameter)
        W_vacuum hcoordinate)
  · rintro rfl
    exact coherentCoordinate_quantityFromCoherentCoordinate
      X.apparatus.torus.unitSystem energyDimension _

/-- The constitutive derivative condition follows from the global
constitutive law and regularity at the selected physical point. -/
lemma constitutiveDerivativeAt_of_sourceLaws (X : SourceData)
    (hX : SatisfiesSourceLaws X) :
    SatisfiesConstitutiveDerivativeAt X := by
  rcases hX with
    ⟨_, hregular, hselected, hconstitutive, _, _, _, _, _, _⟩
  rcases hregular.2.2.1 with
    ⟨neighborhood, hopen, hIcc, _, hH, hM, _, _⟩
  have hselectedNeighborhood : X.selectedParameter ∈ neighborhood :=
    hIcc hselected
  have hHdiff : DifferentiableAt ℝ
      (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
        (X.process.state τ).fieldStrength) X.selectedParameter :=
    (hH.differentiableOn_one X.selectedParameter
      hselectedNeighborhood).differentiableAt
        (hopen.mem_nhds hselectedNeighborhood)
  have hMdiff : DifferentiableAt ℝ
      (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
        (X.process.state τ).magnetization) X.selectedParameter :=
    (hM.differentiableOn_one X.selectedParameter
      hselectedNeighborhood).differentiableAt
        (hopen.mem_nhds hselectedNeighborhood)
  have hconstitutiveDiff : DifferentiableAt ℝ
      (fun τ ↦
        coherentCoordinate X.apparatus.torus.unitSystem
            X.apparatus.material.vacuumPermeability *
          (coherentCoordinate X.apparatus.torus.unitSystem
              (X.process.state τ).fieldStrength +
            coherentCoordinate X.apparatus.torus.unitSystem
              (X.process.state τ).magnetization)) X.selectedParameter :=
    (hHdiff.add hMdiff).const_mul _
  have hfluxDensityDiff : DifferentiableAt ℝ
      (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
        (magneticFluxDensity X.apparatus (X.process.state τ)))
      X.selectedParameter := by
    simpa only [magneticFluxDensity,
      coherentCoordinate_quantityFromCoherentCoordinate] using
        hconstitutiveDiff
  have hunique : UniqueDiffWithinAt ℝ
      (Set.Icc X.process.a X.process.b) X.selectedParameter :=
    (uniqueDiffOn_Icc hregular.2.1) X.selectedParameter hselected
  unfold SatisfiesConstitutiveDerivativeAt
  calc
    deriv
        (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
          (magneticFluxDensity X.apparatus (X.process.state τ)))
        X.selectedParameter =
      derivWithin
        (fun τ ↦ coherentCoordinate X.apparatus.torus.unitSystem
          (magneticFluxDensity X.apparatus (X.process.state τ)))
        (Set.Icc X.process.a X.process.b) X.selectedParameter :=
      (hfluxDensityDiff.derivWithin hunique).symm
    _ = derivWithin
        (fun τ ↦
          coherentCoordinate X.apparatus.torus.unitSystem
              X.apparatus.material.vacuumPermeability *
            (coherentCoordinate X.apparatus.torus.unitSystem
                (X.process.state τ).fieldStrength +
              coherentCoordinate X.apparatus.torus.unitSystem
                (X.process.state τ).magnetization))
        (Set.Icc X.process.a X.process.b) X.selectedParameter :=
      derivWithin_congr hconstitutive (hconstitutive _ hselected)
    _ = deriv
        (fun τ ↦
          coherentCoordinate X.apparatus.torus.unitSystem
              X.apparatus.material.vacuumPermeability *
            (coherentCoordinate X.apparatus.torus.unitSystem
                (X.process.state τ).fieldStrength +
              coherentCoordinate X.apparatus.torus.unitSystem
                (X.process.state τ).magnetization))
        X.selectedParameter :=
      hconstitutiveDiff.derivWithin hunique

/-- A local material-work candidate is characterized by the coherent-SI
coordinate of the answer-free vacuum-subtraction construction. -/
lemma materialWorkIncrement_coordinate_iff (X : SourceData)
    (hX : SatisfiesSourceLaws X) (W_material : Energy) :
    IsMaterialWorkIncrement X W_material ↔
      coherentCoordinate X.apparatus.torus.unitSystem W_material =
        coherentCoordinate X.apparatus.torus.unitSystem
          (materialWorkIncrement X.apparatus X.process
            X.selectedParameter) := by
  rcases hX with
    ⟨hphysical, hregular, hselected, hconstitutive, hlinkage, hAmpere,
      hFaraday, hsourceBalance, hzeroHeating, hsourceWork⟩
  have hX' : SatisfiesSourceLaws X :=
    ⟨hphysical, hregular, hselected, hconstitutive, hlinkage, hAmpere,
      hFaraday, hsourceBalance, hzeroHeating, hsourceWork⟩
  have hdecomposition :=
    (source_vacuum_material_work_decomposition X.apparatus X.process
      hregular hAmpere hFaraday hsourceBalance hsourceWork
      X.selectedParameter hselected).1
  constructor
  · rintro ⟨_, W_source, W_vacuum, hsource, hvacuum, hbalance⟩
    have hsource' := (sourceWorkIncrement_iff_process X hX' W_source).mp hsource
    have hvacuum' :=
      (vacuumCoreWorkIncrement_iff_shared X hX' W_vacuum).mp hvacuum
    rw [hsource', hvacuum', hdecomposition] at hbalance
    have hmaterial : W_material =
        materialWorkIncrement X.apparatus X.process X.selectedParameter :=
      (add_left_cancel hbalance).symm
    exact congrArg
      (coherentCoordinate X.apparatus.torus.unitSystem) hmaterial
  · intro hcoordinate
    have hmaterial : W_material =
        materialWorkIncrement X.apparatus X.process X.selectedParameter :=
      (coordinateInSI_eq_iff X.apparatus.torus.unitSystem W_material
        (materialWorkIncrement X.apparatus X.process
          X.selectedParameter)).mp hcoordinate
    refine ⟨constitutiveDerivativeAt_of_sourceLaws X hX',
      X.process.sourceWorkIncrement X.selectedParameter,
      vacuumWorkIncrement X.apparatus X.process X.selectedParameter,
      ?_, ?_, ?_⟩
    · exact (sourceWorkIncrement_iff_process X hX'
        (X.process.sourceWorkIncrement X.selectedParameter)).2 rfl
    · exact (vacuumCoreWorkIncrement_iff_shared X hX'
        (vacuumWorkIncrement X.apparatus X.process X.selectedParameter)).2 rfl
    · rw [hmaterial]
      exact hdecomposition

/-- The governing lossless source laws determine a unique signed material
work increment without placing its derived value in the theorem statement. -/
theorem materialWorkIncrement_existsUnique (X : SourceData)
    (hX : SatisfiesSourceLaws X) :
    ∃! W_material : Energy, IsMaterialWorkIncrement X W_material := by
  refine ⟨materialWorkIncrement X.apparatus X.process X.selectedParameter,
    ?_, ?_⟩
  · apply (materialWorkIncrement_coordinate_iff X hX
      (materialWorkIncrement X.apparatus X.process X.selectedParameter)).2
    rfl
  · intro W_material hmaterial
    apply (coordinateInSI_eq_iff X.apparatus.torus.unitSystem W_material
      (materialWorkIncrement X.apparatus X.process X.selectedParameter)).mp
    exact (materialWorkIncrement_coordinate_iff X hX W_material).mp hmaterial

end Ipho2026Gpt56solBlind.ProblemIPhO2026_3_A_3
