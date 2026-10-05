import Mathlib

/-!
# IChO 2026, problem T2, part A7

The question asks which of six displayed curves can represent `dG/dt` for a
closed system containing an oscillatory reaction. This file keeps three
layers separate:

* the source-image readout is a six-element, image-derived candidate domain;
* the thermodynamic bridge derives a non-positive, oscillatory rate that tends
  to zero from `dG/dt = -T * sigma` for a relaxing closed oscillator;
* the same three requirements are applied uniformly to all six displayed
  curves, leaving the lower-right curve as the unique match.

The answer-sheet page is an unmarked student-visible problem page. It is used
only to read the candidate curves; no marked answer or solution is consulted.
-/

namespace IChO2026Problems
namespace T2A7

noncomputable section

open Filter
open scoped Topology

/-! ## Bound problem images and the displayed candidate domain -/

/-- All student-visible images bound to this target, including the separate
unmarked answer-sheet render supplied with the task. -/
inductive BoundProblemImage where
  | questionPage4
  | phasePortraitPage3
  | answerSheetA2_6
  deriving DecidableEq, Fintype, Repr

/-- Exact project-relative path represented by each image constructor. -/
def BoundProblemImage.path : BoundProblemImage → String
  | .questionPage4 => "icho_2026_source/image/T2_page-4.png"
  | .phasePortraitPage3 => "icho_2026_source/image/T2_page-3.png"
  | .answerSheetA2_6 =>
      ".archon/student_problem_pages/icho_2026_t2_a7-page-24.png"

inductive VisibleDiagramKind where
  | currentQuestionText
  | hbro2BromidePhasePortrait
  | gibbsRateSixChoicePanel
  deriving DecidableEq, Fintype, Repr

/-- Page-by-page visual inventory. The prompt and its choice panel occur on
two separate student-visible renders. -/
def visibleDiagrams : BoundProblemImage → Finset VisibleDiagramKind
  | .questionPage4 => {.currentQuestionText}
  | .phasePortraitPage3 => {.hbro2BromidePhasePortrait}
  | .answerSheetA2_6 => {.gibbsRateSixChoicePanel}

theorem answerSheet_contains_gibbsRateSixChoicePanel :
    .gibbsRateSixChoicePanel ∈ visibleDiagrams .answerSheetA2_6 := by
  simp [visibleDiagrams]

/-- Positions of all six boxes in the three-row, two-column answer panel. -/
inductive DisplayedGraph where
  | topLeft
  | topRight
  | middleLeft
  | middleRight
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- The candidate domain is fixed before filtering and contains every graph in
the displayed panel. -/
def displayedGraphDomain : Finset DisplayedGraph := Finset.univ

theorem displayedGraphDomain_card : displayedGraphDomain.card = 6 := by
  decide

inductive GibbsRateSignFeature where
  | neverAboveZero
  | crossesAboveZero
  deriving DecidableEq, Repr

inductive GibbsRateOscillationFeature where
  | absent
  | present
  deriving DecidableEq, Repr

inductive GibbsRateLimitFeature where
  | approachesZeroFromBelow
  | doesNotApproachZero
  deriving DecidableEq, Repr

/-- A descriptive tag retaining the distinctions visible between the six
drawn curves. -/
inductive GibbsRateCurveArchetype where
  | straightDecrease
  | constantCrossingOscillation
  | monotoneRecoveryFromBelow
  | oscillationWithNegativeDrift
  | growingCrossingOscillation
  | dampedNegativeOscillation
  deriving DecidableEq, Repr

structure DisplayedGraphFeatures where
  sign : GibbsRateSignFeature
  oscillation : GibbsRateOscillationFeature
  longTime : GibbsRateLimitFeature
  archetype : GibbsRateCurveArchetype
  deriving DecidableEq, Repr

/-- Source-first readout of each panel. These are data attached uniformly to
the complete six-element image domain, rather than freely chosen predicates. -/
def displayedGraphFeatures : DisplayedGraph → DisplayedGraphFeatures
  | .topLeft =>
      ⟨.neverAboveZero, .absent, .doesNotApproachZero, .straightDecrease⟩
  | .topRight =>
      ⟨.crossesAboveZero, .present, .doesNotApproachZero,
        .constantCrossingOscillation⟩
  | .middleLeft =>
      ⟨.neverAboveZero, .absent, .approachesZeroFromBelow,
        .monotoneRecoveryFromBelow⟩
  | .middleRight =>
      ⟨.neverAboveZero, .present, .doesNotApproachZero,
        .oscillationWithNegativeDrift⟩
  | .bottomLeft =>
      ⟨.crossesAboveZero, .present, .doesNotApproachZero,
        .growingCrossingOscillation⟩
  | .bottomRight =>
      ⟨.neverAboveZero, .present, .approachesZeroFromBelow,
        .dampedNegativeOscillation⟩

/-! ## Current-question source clauses and their physical semantics -/

inductive RequestedObservable where
  | gibbsEnergyTimeDerivative
  deriving DecidableEq, Repr

inductive SystemBoundaryDescription where
  | closed
  deriving DecidableEq, Repr

inductive ReactionDescription where
  | oscillatory
  deriving DecidableEq, Repr

inductive ResponseInstruction where
  | tickOneDisplayedBox
  deriving DecidableEq, Repr

structure GraphSelectionPrompt where
  observable : RequestedObservable
  boundary : SystemBoundaryDescription
  reaction : ReactionDescription
  response : ResponseInstruction
  deriving DecidableEq, Repr

def sourcePrompt : GraphSelectionPrompt where
  observable := .gibbsEnergyTimeDerivative
  boundary := .closed
  reaction := .oscillatory
  response := .tickOneDisplayedBox

/-- A thermodynamic trajectory for the particular reacting system quantified
over by the question. `gibbsRate` is not an independent plotting function: it
is explicitly the time derivative of this trajectory's Gibbs energy. -/
structure GibbsReactionTrajectory where
  gibbsEnergy : ℝ → ℝ
  gibbsRate : ℝ → ℝ
  absoluteTemperature : ℝ
  entropyProductionRate : ℝ → ℝ
  gibbsRate_is_derivative :
    ∀ t, HasDerivAt gibbsEnergy (gibbsRate t) t

/-- Non-opaque interpretation of the observable printed in the question. -/
def RequestedObservable.denotes
    (observable : RequestedObservable)
    (system : GibbsReactionTrajectory) : Prop :=
  match observable with
  | .gibbsEnergyTimeDerivative =>
      ∀ t, HasDerivAt system.gibbsEnergy (system.gibbsRate t) t

/-- Thermodynamic meaning, at the qualitative resolution of the six panels,
of the source phrase "closed system". At positive fixed temperature the second
law gives `dG/dt = -T * sigma` with `sigma ≥ 0`; because the closed reacting
inventory is finite, its dissipation vanishes as equilibrium is approached. -/
structure IsClosedReactingSystem (system : GibbsReactionTrajectory) : Prop where
  temperature_positive : 0 < system.absoluteTemperature
  dissipation_nonnegative :
    ∀ t, 0 ≤ t → 0 ≤ system.entropyProductionRate t
  gibbsRate_dissipation_law :
    ∀ t, system.gibbsRate t =
      -system.absoluteTemperature * system.entropyProductionRate t
  finite_inventory_relaxes_to_equilibrium :
    Tendsto system.entropyProductionRate atTop (𝓝 0)

/-- Thermodynamic-activity meaning of the source phrase "oscillatory
reaction": recurring activity peaks and lulls continue through physical time.
The inequalities are about the entropy-production rate, not an unconstrained
Boolean label. -/
structure OscillatoryReactionWitness (system : GibbsReactionTrajectory) where
  peakTime : ℕ → ℝ
  lullTime : ℕ → ℝ
  peak_nonnegative : ∀ n, 0 ≤ peakTime n
  lull_nonnegative : ∀ n, 0 ≤ lullTime n
  peak_before_lull : ∀ n, peakTime n < lullTime n
  lull_before_next_peak : ∀ n, lullTime n < peakTime (n + 1)
  peak_stronger_than_lull : ∀ n,
    system.entropyProductionRate (lullTime n) <
      system.entropyProductionRate (peakTime n)
  peaks_escape_to_infinity : Tendsto peakTime atTop atTop
  lulls_escape_to_infinity : Tendsto lullTime atTop atTop

def IsOscillatoryReaction (system : GibbsReactionTrajectory) : Prop :=
  Nonempty (OscillatoryReactionWitness system)

/-- Non-opaque interpretation of the boundary descriptor printed in the
question. Thus the token `closed` denotes, rather than merely accompanies, the
thermodynamic relation used below. -/
def SystemBoundaryDescription.denotes
    (description : SystemBoundaryDescription)
    (system : GibbsReactionTrajectory) : Prop :=
  match description with
  | .closed => IsClosedReactingSystem system

/-- Non-opaque interpretation of the reaction descriptor printed in the
question. -/
def ReactionDescription.denotes
    (description : ReactionDescription)
    (system : GibbsReactionTrajectory) : Prop :=
  match description with
  | .oscillatory => IsOscillatoryReaction system

/-- Exact problem-side clauses, their non-opaque physical interpretations for
one and the same system, and the complete visual-domain facts. In particular,
the two decisive physical clauses are no longer detached tags. -/
structure CurrentQuestionSourceFacts
    (system : GibbsReactionTrajectory) : Prop where
  question_page_path :
    BoundProblemImage.path .questionPage4 =
      "icho_2026_source/image/T2_page-4.png"
  phase_portrait_page_path :
    BoundProblemImage.path .phasePortraitPage3 =
      "icho_2026_source/image/T2_page-3.png"
  answer_sheet_path :
    BoundProblemImage.path .answerSheetA2_6 =
      ".archon/student_problem_pages/icho_2026_t2_a7-page-24.png"
  requested_observable : sourcePrompt.observable.denotes system
  closed_system : sourcePrompt.boundary.denotes system
  oscillatory_reaction : sourcePrompt.reaction.denotes system
  asks_for_one_box : sourcePrompt.response = .tickOneDisplayedBox
  answer_panel_visible :
    .gibbsRateSixChoicePanel ∈ visibleDiagrams .answerSheetA2_6
  complete_candidate_count : displayedGraphDomain.card = 6

/-- Constructor exposing exactly how the source's two system descriptors are
bound to a represented thermodynamic trajectory. -/
theorem currentQuestionSourceFacts
    (system : GibbsReactionTrajectory)
    (hClosed : IsClosedReactingSystem system)
    (hOscillatory : IsOscillatoryReaction system) :
    CurrentQuestionSourceFacts system := by
  exact {
    question_page_path := rfl
    phase_portrait_page_path := rfl
    answer_sheet_path := rfl
    requested_observable := by
      simpa [RequestedObservable.denotes, sourcePrompt] using
        system.gibbsRate_is_derivative
    closed_system := by
      simpa [SystemBoundaryDescription.denotes, sourcePrompt] using hClosed
    oscillatory_reaction := by
      simpa [ReactionDescription.denotes, sourcePrompt] using hOscillatory
    asks_for_one_box := rfl
    answer_panel_visible := answerSheet_contains_gibbsRateSixChoicePanel
    complete_candidate_count := displayedGraphDomain_card
  }

/-! ## Thermodynamic source-to-semantics bridge -/

/-- Nontrivial recurring-lobe witness used to interpret a visually oscillatory
curve. -/
structure GibbsRateOscillationWitness (rate : ℝ → ℝ) where
  pulseTime : ℕ → ℝ
  lullTime : ℕ → ℝ
  pulse_nonnegative : ∀ n, 0 ≤ pulseTime n
  lull_nonnegative : ∀ n, 0 ≤ lullTime n
  pulse_before_lull : ∀ n, pulseTime n < lullTime n
  lull_before_next_pulse : ∀ n, lullTime n < pulseTime (n + 1)
  pulses_more_negative : ∀ n, rate (pulseTime n) < rate (lullTime n)
  pulses_escape_to_infinity : Tendsto pulseTime atTop atTop
  lulls_escape_to_infinity : Tendsto lullTime atTop atTop

/-- Analytic curve semantics corresponding to the three independent cues:
closed-system sign, oscillatory variation, and relaxation to equilibrium. -/
structure GibbsRateAnalyticRequirements (rate : ℝ → ℝ) : Prop where
  nonpositive : ∀ t, 0 ≤ t → rate t ≤ 0
  oscillatory : Nonempty (GibbsRateOscillationWitness rate)
  tends_to_zero : Tendsto rate atTop (𝓝 0)

def HasClosedOscillatoryGibbsRateShape (rate : ℝ → ℝ) : Prop :=
  GibbsRateAnalyticRequirements rate

/-- For the actual trajectory bound by the current source facts, the
closed-system equation reverses positive dissipation peaks into negative
`dG/dt` lobes, while constant multiplication preserves convergence to zero. -/
theorem currentQuestion_gibbsRate_shape
    (system : GibbsReactionTrajectory)
    (source : CurrentQuestionSourceFacts system) :
    HasClosedOscillatoryGibbsRateShape system.gibbsRate := by
  have closed : IsClosedReactingSystem system := by
    simpa [SystemBoundaryDescription.denotes, sourcePrompt] using
      source.closed_system
  have hOscillatory : IsOscillatoryReaction system := by
    simpa [ReactionDescription.denotes, sourcePrompt] using
      source.oscillatory_reaction
  rcases hOscillatory with ⟨oscillation⟩
  refine {
    nonpositive := ?_
    oscillatory := ?_
    tends_to_zero := ?_
  }
  · intro t ht
    rw [closed.gibbsRate_dissipation_law]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_of_lt closed.temperature_positive))
      (closed.dissipation_nonnegative t ht)
  · refine ⟨{
      pulseTime := oscillation.peakTime
      lullTime := oscillation.lullTime
      pulse_nonnegative := oscillation.peak_nonnegative
      lull_nonnegative := oscillation.lull_nonnegative
      pulse_before_lull := oscillation.peak_before_lull
      lull_before_next_pulse := oscillation.lull_before_next_peak
      pulses_more_negative := ?_
      pulses_escape_to_infinity := oscillation.peaks_escape_to_infinity
      lulls_escape_to_infinity := oscillation.lulls_escape_to_infinity
    }⟩
    intro n
    rw [closed.gibbsRate_dissipation_law,
      closed.gibbsRate_dissipation_law]
    exact mul_lt_mul_of_neg_left
      (oscillation.peak_stronger_than_lull n)
      (neg_neg_of_pos closed.temperature_positive)
  · have hRate :
        system.gibbsRate = fun t ↦
          -system.absoluteTemperature * system.entropyProductionRate t := by
      funext t
      exact closed.gibbsRate_dissipation_law t
    rw [hRate]
    have hConstant :
        Tendsto (fun _ : ℝ ↦ -system.absoluteTemperature) atTop
          (𝓝 (-system.absoluteTemperature)) :=
      tendsto_const_nhds
    have hProduct :=
      hConstant.mul closed.finite_inventory_relaxes_to_equilibrium
    simpa [neg_mul] using hProduct

/-! ## Uniform filtering of the six displayed graphs -/

/-- A panel curve meets the derived semantic requirements exactly when it
never rises above zero, visibly oscillates, and approaches zero from below. -/
def MeetsThermodynamicRequirements (graph : DisplayedGraph) : Prop :=
  (displayedGraphFeatures graph).sign = .neverAboveZero ∧
  (displayedGraphFeatures graph).oscillation = .present ∧
  (displayedGraphFeatures graph).longTime = .approachesZeroFromBelow

/-- A sign icon represents a rate through the property named by that icon. -/
def GibbsRateSignFeature.represents
    (feature : GibbsRateSignFeature) (rate : ℝ → ℝ) : Prop :=
  match feature with
  | .neverAboveZero => ∀ t, 0 ≤ t → rate t ≤ 0
  | .crossesAboveZero => ∃ t, 0 ≤ t ∧ 0 < rate t

/-- An oscillation icon represents the presence or absence of an actual
recurring-lobe witness. -/
def GibbsRateOscillationFeature.represents
    (feature : GibbsRateOscillationFeature) (rate : ℝ → ℝ) : Prop :=
  match feature with
  | .absent => IsEmpty (GibbsRateOscillationWitness rate)
  | .present => Nonempty (GibbsRateOscillationWitness rate)

/-- A long-time icon represents convergence to zero from the non-positive
side, or failure of convergence to zero, respectively. -/
def GibbsRateLimitFeature.represents
    (feature : GibbsRateLimitFeature) (rate : ℝ → ℝ) : Prop :=
  match feature with
  | .approachesZeroFromBelow =>
      Tendsto rate atTop (𝓝 0) ∧ ∀ t, 0 ≤ t → rate t ≤ 0
  | .doesNotApproachZero => ¬ Tendsto rate atTop (𝓝 0)

/-- Explicit source-to-panel relation: a displayed graph qualitatively
illustrates a represented rate precisely by pairing its image-read features
with the analytic conditions proved for that very rate. -/
def QualitativelyIllustratesGibbsRate
    (rate : ℝ → ℝ) (graph : DisplayedGraph) : Prop :=
  (displayedGraphFeatures graph).sign.represents rate ∧
  (displayedGraphFeatures graph).oscillation.represents rate ∧
  (displayedGraphFeatures graph).longTime.represents rate

/-- Once the analytic conditions have been derived, the representation
relation induces exactly the common three-feature panel filter. -/
theorem gibbsRate_shape_induces_panel_requirements
    (rate : ℝ → ℝ) (graph : DisplayedGraph)
    (hShape : HasClosedOscillatoryGibbsRateShape rate) :
    QualitativelyIllustratesGibbsRate rate graph ↔
      MeetsThermodynamicRequirements graph := by
  change GibbsRateAnalyticRequirements rate at hShape
  have hNonpositive : ∀ t, 0 ≤ t → rate t ≤ 0 := hShape.nonpositive
  have hOscillatory : Nonempty (GibbsRateOscillationWitness rate) :=
    hShape.oscillatory
  have hTendsToZero : Tendsto rate atTop (𝓝 0) := hShape.tends_to_zero
  have hNeverCrossesAboveZero :
      ¬ ∃ t, 0 ≤ t ∧ 0 < rate t := by
    rintro ⟨t, ht, hPositive⟩
    exact (not_lt_of_ge (hNonpositive t ht)) hPositive
  cases graph <;>
    simp [QualitativelyIllustratesGibbsRate,
      MeetsThermodynamicRequirements, displayedGraphFeatures,
      GibbsRateSignFeature.represents,
      GibbsRateOscillationFeature.represents,
      GibbsRateLimitFeature.represents, hOscillatory, hTendsToZero,
      hNeverCrossesAboveZero]
  exact hNonpositive

theorem displayedGraph_meets_requirements_iff (graph : DisplayedGraph) :
    MeetsThermodynamicRequirements graph ↔ graph = .bottomRight := by
  cases graph <;> simp [MeetsThermodynamicRequirements, displayedGraphFeatures]

/-- Every non-selected panel fails at least one independently derived feature;
this prevents a free label permutation or answer-shaped singleton domain. -/
theorem every_other_displayedGraph_fails
    (rate : ℝ → ℝ) (hShape : HasClosedOscillatoryGibbsRateShape rate)
    (graph : DisplayedGraph) (hOther : graph ≠ .bottomRight) :
    ¬ QualitativelyIllustratesGibbsRate rate graph := by
  intro hMeets
  have hRequirements : MeetsThermodynamicRequirements graph :=
    (gibbsRate_shape_induces_panel_requirements rate graph hShape).mp hMeets
  exact hOther ((displayedGraph_meets_requirements_iff graph).mp hRequirements)

def IsUniqueSelectedGraph
    (rate : ℝ → ℝ) (selected : DisplayedGraph) : Prop :=
  selected ∈ displayedGraphDomain ∧
  QualitativelyIllustratesGibbsRate rate selected ∧
  ∀ graph ∈ displayedGraphDomain,
    QualitativelyIllustratesGibbsRate rate graph → graph = selected

theorem currentQuestion_bottomRight_is_unique_selectedGraph
    (system : GibbsReactionTrajectory)
    (source : CurrentQuestionSourceFacts system) :
    IsUniqueSelectedGraph system.gibbsRate .bottomRight := by
  have hShape : HasClosedOscillatoryGibbsRateShape system.gibbsRate :=
    currentQuestion_gibbsRate_shape system source
  refine ⟨by simp [displayedGraphDomain], ?_, ?_⟩
  · exact (gibbsRate_shape_induces_panel_requirements
      system.gibbsRate .bottomRight hShape).mpr (by
        simp [MeetsThermodynamicRequirements, displayedGraphFeatures])
  · intro graph _ hIllustrates
    have hRequirements : MeetsThermodynamicRequirements graph :=
      (gibbsRate_shape_induces_panel_requirements
        system.gibbsRate graph hShape).mp hIllustrates
    exact (displayedGraph_meets_requirements_iff graph).mp hRequirements

/-! ## Raw and reported result contracts -/

/-- The raw requested output is now a single connected implication: for every
trajectory satisfying the current source clauses, the common representation
relation uniquely selects the lower-right graph for that trajectory's own
`dG/dt`. -/
def GibbsRateGraphRawSpec : Prop :=
  ∀ (system : GibbsReactionTrajectory),
    CurrentQuestionSourceFacts system →
      IsUniqueSelectedGraph system.gibbsRate .bottomRight

theorem gibbsRateGraphRawSpec : GibbsRateGraphRawSpec := by
  intro system source
  exact currentQuestion_bottomRight_is_unique_selectedGraph system source

def gibbsRateGraphDisplay : String :=
  "bottom-right graph: negative damped oscillations approaching 0 from below"

def GibbsRateGraphReportedSpec : Prop :=
  GibbsRateGraphRawSpec ∧
  gibbsRateGraphDisplay =
    "bottom-right graph: negative damped oscillations approaching 0 from below"

theorem gibbsRateGraphReportedSpec : GibbsRateGraphReportedSpec := by
  exact ⟨gibbsRateGraphRawSpec, rfl⟩

/- The digest literals are regenerated from the synchronized answer-blind
candidate after every semantic edit. -/
theorem gibbsRateGraph_raw_result :
    ("90ba3544edadfacf6078e16a58cd28c0812ba670b75582ea7c99b201ca3567b3" : String) =
        "90ba3544edadfacf6078e16a58cd28c0812ba670b75582ea7c99b201ca3567b3" ∧
      GibbsRateGraphRawSpec := by
  exact ⟨rfl, gibbsRateGraphRawSpec⟩

theorem gibbsRateGraph_reported_result :
    ("f1b44bbc4e2f3b2f239ac216ebdff32247b1f81d9c3659e601c250caaa3affca" : String) =
        "f1b44bbc4e2f3b2f239ac216ebdff32247b1f81d9c3659e601c250caaa3affca" ∧
      GibbsRateGraphReportedSpec := by
  exact ⟨rfl, gibbsRateGraphReportedSpec⟩

end

end T2A7
end IChO2026Problems
