import Mathlib

/-!
# IChO 2026, problem T8-A8

This file models the assignment of the four panels in the product-composition
chart.  The chart facts are kept separate from the two controller-authorized
model inputs `M001` and `M002`.  In particular, an absent product stack is not
identified with the absence of every possible dark reaction.

The final theorem is conditional: it quantifies over every bijective assignment
that preserves the plotted readouts and satisfies the two authorized inputs.
-/

namespace IChO2026Problems.ProblemIcho2026T8A8

/-- The four experimental conditions named in the problem. -/
inductive Condition where
  | noIrradiation
  | red
  | green
  | blue
  deriving DecidableEq, Fintype, Repr

/-- The three LED conditions to which the photon-energy hypothesis applies. -/
inductive IlluminatedCondition where
  | red
  | green
  | blue
  deriving DecidableEq, Fintype, Repr

/-- Inclusion of an illuminated condition into the four-condition experiment. -/
def IlluminatedCondition.toCondition : IlluminatedCondition → Condition
  | .red => .red
  | .green => .green
  | .blue => .blue

/-- Labels under the four bars in the source figure. -/
inductive Panel where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- Readouts carried by the page-4 chart.  `none` means that no percentage was
plotted; it is deliberately not a numerical zero. -/
structure ProductChart where
  productStackPlotted : Panel → Bool
  h2MolePercent : Panel → Option ℝ
  coMolePercent : Panel → Option ℝ

/-- A displayed H₂/CO stack consists of two nonnegative mole percentages whose
sum is 100 percent. -/
def IsBinaryProductStack (chart : ProductChart) (panel : Panel) : Prop :=
  chart.productStackPlotted panel = true ∧
    ∃ h2 co : ℝ,
      chart.h2MolePercent panel = some h2 ∧
      chart.coMolePercent panel = some co ∧
      0 ≤ h2 ∧ 0 ≤ co ∧ h2 + co = 100

/-- Source-first transcription of the page-4 figure.  Only the strict ordering
of the three visibly separated H₂ segments is used; no unsupported decimal
readout is assigned to those bars. -/
structure Page4FigureFacts (chart : ProductChart) : Prop where
  panelA_noProductStack : chart.productStackPlotted .a = false
  panelA_noH2Readout : chart.h2MolePercent .a = none
  panelA_noCOReadout : chart.coMolePercent .a = none
  panelB_productStack : IsBinaryProductStack chart .b
  panelC_productStack : IsBinaryProductStack chart .c
  panelD_productStack : IsBinaryProductStack chart .d
  h2SegmentsStrictlyDecrease :
    ∃ h2b h2c h2d : ℝ,
      chart.h2MolePercent .b = some h2b ∧
      chart.h2MolePercent .c = some h2c ∧
      chart.h2MolePercent .d = some h2d ∧
      h2d < h2c ∧ h2c < h2b

/-- Experimental quantities indexed by condition rather than by panel.  Photon
energy and product fractions are present only for the three illuminated
conditions; the dark condition therefore receives no fabricated H₂ value. -/
structure ExperimentData where
  productStackPlotted : Condition → Bool
  photonEnergy : IlluminatedCondition → ℝ
  h2MoleFraction : IlluminatedCondition → ℝ
  coMoleFraction : IlluminatedCondition → ℝ

/-- Standard visible-light ordering used only for the named red, green, and
blue LEDs in this experiment.  This is an ordinal comparison, not a choice of
numerical photon energies. -/
def VisibleLEDPhotonEnergyOrder (experiment : ExperimentData) : Prop :=
  experiment.photonEnergy .red < experiment.photonEnergy .green ∧
    experiment.photonEnergy .green < experiment.photonEnergy .blue

/-- `M001`, authorized for this target only: the no-irradiation condition has
no plotted H₂/CO product stack.  It says nothing about other dark reactions. -/
def M001 (experiment : ExperimentData) : Prop :=
  experiment.productStackPlotted .noIrradiation = false

/-- `M002`, authorized for this target only: among the three illuminated
conditions of this experiment, higher photon energy gives a strictly higher
H₂ mole percentage.  It is not a universal selectivity law. -/
def M002 (experiment : ExperimentData) : Prop :=
  ∀ u v : IlluminatedCondition,
    experiment.photonEnergy u < experiment.photonEnergy v →
      experiment.h2MoleFraction u < experiment.h2MoleFraction v

/-- A proposed interpretation of the panel labels is an *actual assignment*
only when it is bijective and preserves both stack visibility and every
illuminated H₂/CO readout.  No particular panel-to-condition answer is stored
in this structure. -/
structure ActualAssignment (chart : ProductChart) (experiment : ExperimentData) where
  conditionAt : Panel → Condition
  bijective : Function.Bijective conditionAt
  preservesProductStack :
    ∀ panel : Panel,
      chart.productStackPlotted panel =
        experiment.productStackPlotted (conditionAt panel)
  preservesIlluminatedReadouts :
    ∀ (panel : Panel) (condition : IlluminatedCondition),
      conditionAt panel = condition.toCondition →
        chart.h2MolePercent panel = some (100 * experiment.h2MoleFraction condition) ∧
        chart.coMolePercent panel = some (100 * experiment.coMoleFraction condition)

/-- Requested output carrier for panel `a`. -/
def condition_a {chart : ProductChart} {experiment : ExperimentData}
    (assignment : ActualAssignment chart experiment) : Prop :=
  assignment.conditionAt .a = .noIrradiation

/-- Requested output carrier for panel `b`. -/
def condition_b {chart : ProductChart} {experiment : ExperimentData}
    (assignment : ActualAssignment chart experiment) : Prop :=
  assignment.conditionAt .b = .blue

/-- Requested output carrier for panel `c`. -/
def condition_c {chart : ProductChart} {experiment : ExperimentData}
    (assignment : ActualAssignment chart experiment) : Prop :=
  assignment.conditionAt .c = .green

/-- Requested output carrier for panel `d`. -/
def condition_d {chart : ProductChart} {experiment : ExperimentData}
    (assignment : ActualAssignment chart experiment) : Prop :=
  assignment.conditionAt .d = .red

/-- The four requested classifications, in source order. -/
structure RequestedAssignment {chart : ProductChart} {experiment : ExperimentData}
    (assignment : ActualAssignment chart experiment) : Prop where
  conditionA : condition_a assignment
  conditionB : condition_b assignment
  conditionC : condition_c assignment
  conditionD : condition_d assignment

/-- Controller-bound provenance for the two supplementary model inputs. -/
def modelAuthorizationSHA256 : String :=
  "a5a2efb40aaee84da0386a961e8e0726350a8223a665c6d45fb57781e8caf5a2"

/-- Frozen Kimi draft hash whose T8-A8 assignment is being preserved. -/
def providedDraftSHA256 : String :=
  "0b3458c73efd638dfddf39b334e02d2068fca8e9ebbe33b143991d5478cfcb7d"

/-- Under the page-4 observations, visible-light energy ordering, and the two
separately named authorized inputs, every actual assignment has the requested
panel classification.  This is the target's `conditional_contest_model`; none
of the four conclusions occurs as a premise. -/
theorem conditional_contest_model
    (chart : ProductChart)
    (experiment : ExperimentData)
    (figure : Page4FigureFacts chart)
    (visibleEnergyOrder : VisibleLEDPhotonEnergyOrder experiment)
    (assignment : ActualAssignment chart experiment)
    (M001_input : M001 experiment)
    (M002_input : M002 experiment) :
    RequestedAssignment assignment := by
  classical
  rcases figure.h2SegmentsStrictlyDecrease with
    ⟨h2b, h2c, h2d, panelB_h2, panelC_h2, panelD_h2, h2d_lt_h2c, h2c_lt_h2b⟩
  have assignment_injective : Function.Injective assignment.conditionAt :=
    assignment.bijective.1
  have assignment_surjective : Function.Surjective assignment.conditionAt :=
    assignment.bijective.2
  have red_lt_green := M002_input .red .green visibleEnergyOrder.1
  have green_lt_blue := M002_input .green .blue visibleEnergyOrder.2
  have red_lt_blue := lt_trans red_lt_green green_lt_blue

  have darkStackAbsent :
      experiment.productStackPlotted .noIrradiation = false := M001_input
  have panelB_stack : chart.productStackPlotted .b = true :=
    figure.panelB_productStack.1
  have panelC_stack : chart.productStackPlotted .c = true :=
    figure.panelC_productStack.1
  have panelD_stack : chart.productStackPlotted .d = true :=
    figure.panelD_productStack.1

  -- M001 and preservation of the plotted-stack flag exclude the dark
  -- condition from each of the three displayed stacks.
  have panelB_notDark : assignment.conditionAt .b ≠ .noIrradiation := by
    intro h
    have preserved := assignment.preservesProductStack .b
    simp [h, darkStackAbsent, panelB_stack] at preserved
  have panelC_notDark : assignment.conditionAt .c ≠ .noIrradiation := by
    intro h
    have preserved := assignment.preservesProductStack .c
    simp [h, darkStackAbsent, panelC_stack] at preserved
  have panelD_notDark : assignment.conditionAt .d ≠ .noIrradiation := by
    intro h
    have preserved := assignment.preservesProductStack .d
    simp [h, darkStackAbsent, panelD_stack] at preserved

  have panelA_dark : assignment.conditionAt .a = .noIrradiation := by
    obtain ⟨panel, hpanel⟩ := assignment_surjective .noIrradiation
    cases panel with
    | a => exact hpanel
    | b => exact (panelB_notDark hpanel).elim
    | c => exact (panelC_notDark hpanel).elim
    | d => exact (panelD_notDark hpanel).elim

  -- Injectivity makes the illuminated assignments on b, c, and d pairwise
  -- distinct.  Supplying the nine possible readout-preservation instances
  -- lets finite case elimination compare the two strict three-element chains.
  have panelBC_ne : assignment.conditionAt .b ≠ assignment.conditionAt .c := by
    intro h
    simpa using assignment_injective h
  have panelBD_ne : assignment.conditionAt .b ≠ assignment.conditionAt .d := by
    intro h
    simpa using assignment_injective h
  have panelCD_ne : assignment.conditionAt .c ≠ assignment.conditionAt .d := by
    intro h
    simpa using assignment_injective h

  have panelB_red := assignment.preservesIlluminatedReadouts .b .red
  have panelB_green := assignment.preservesIlluminatedReadouts .b .green
  have panelB_blue := assignment.preservesIlluminatedReadouts .b .blue
  have panelC_red := assignment.preservesIlluminatedReadouts .c .red
  have panelC_green := assignment.preservesIlluminatedReadouts .c .green
  have panelC_blue := assignment.preservesIlluminatedReadouts .c .blue
  have panelD_red := assignment.preservesIlluminatedReadouts .d .red
  have panelD_green := assignment.preservesIlluminatedReadouts .d .green
  have panelD_blue := assignment.preservesIlluminatedReadouts .d .blue

  cases panelB_condition : assignment.conditionAt .b <;>
    cases panelC_condition : assignment.conditionAt .c <;>
      cases panelD_condition : assignment.conditionAt .d <;>
        simp_all [IlluminatedCondition.toCondition] <;>
          first
          | exact ⟨panelA_dark, panelB_condition, panelC_condition,
              panelD_condition⟩
          | exfalso
            nlinarith

/-- Individual theorem for requested output `condition_a`. -/
theorem condition_a_result
    (chart : ProductChart) (experiment : ExperimentData)
    (figure : Page4FigureFacts chart)
    (visibleEnergyOrder : VisibleLEDPhotonEnergyOrder experiment)
    (assignment : ActualAssignment chart experiment)
    (M001_input : M001 experiment) (M002_input : M002 experiment) :
    condition_a assignment := by
  exact (conditional_contest_model chart experiment figure visibleEnergyOrder
    assignment M001_input M002_input).conditionA

/-- Individual theorem for requested output `condition_b`. -/
theorem condition_b_result
    (chart : ProductChart) (experiment : ExperimentData)
    (figure : Page4FigureFacts chart)
    (visibleEnergyOrder : VisibleLEDPhotonEnergyOrder experiment)
    (assignment : ActualAssignment chart experiment)
    (M001_input : M001 experiment) (M002_input : M002 experiment) :
    condition_b assignment := by
  exact (conditional_contest_model chart experiment figure visibleEnergyOrder
    assignment M001_input M002_input).conditionB

/-- Individual theorem for requested output `condition_c`. -/
theorem condition_c_result
    (chart : ProductChart) (experiment : ExperimentData)
    (figure : Page4FigureFacts chart)
    (visibleEnergyOrder : VisibleLEDPhotonEnergyOrder experiment)
    (assignment : ActualAssignment chart experiment)
    (M001_input : M001 experiment) (M002_input : M002 experiment) :
    condition_c assignment := by
  exact (conditional_contest_model chart experiment figure visibleEnergyOrder
    assignment M001_input M002_input).conditionC

/-- Individual theorem for requested output `condition_d`. -/
theorem condition_d_result
    (chart : ProductChart) (experiment : ExperimentData)
    (figure : Page4FigureFacts chart)
    (visibleEnergyOrder : VisibleLEDPhotonEnergyOrder experiment)
    (assignment : ActualAssignment chart experiment)
    (M001_input : M001 experiment) (M002_input : M002 experiment) :
    condition_d assignment := by
  exact (conditional_contest_model chart experiment figure visibleEnergyOrder
    assignment M001_input M002_input).conditionD

end IChO2026Problems.ProblemIcho2026T8A8
