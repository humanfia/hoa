import Mathlib
import IChO2026Chem

/-!
# IChO 2026, theory problem 2, part 4

This file formalizes the direction of motion in the supplied phase portrait.
The chemical mechanism and printed constants are retained as source data.  The
direction itself is derived from two source-side facts: the trace follows the
drawn four-edge loop, and on its low-`HBrO₂` branch bromide moves from its
maximum concentration to the critical concentration.  With the usual axes
(`Br⁻` to the right and `HBrO₂` upwards), that temporal order has negative
signed area and hence is clockwise.

No result from an earlier subpart is assumed.  The printed fallback values are
recorded below, but the orientation proof does not depend on their numerical
values.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T2A4

noncomputable section

/-! ## Species, processes, and the printed mechanism -/

/-- Chemical species explicitly named in the mechanism.  `otherProducts`
records the source's deliberately unspecified product group in step (7); it is
not used in a material-balance argument. -/
inductive Species where
  | bromousAcid
  | bromate
  | proton
  | bromineDioxideRadical
  | water
  | ceriumIII
  | ceriumIV
  | hypobromousAcid
  | bromide
  | malonicAcid
  | bromomalonicAcid
  | otherProducts
  deriving DecidableEq, Repr

/-- The three named processes in the printed BZ mechanism. -/
inductive Process where
  | processA
  | processB
  | processC
  deriving DecidableEq, Repr

/-- A term in a printed elementary reaction.  `none` means that the source did
not give a coefficient (only the literal `other products` in step (7)). -/
structure StoichiometricTerm where
  species : Species
  coefficient : Option ℕ
  deriving DecidableEq, Repr

def specifiedTerm (species : Species) (coefficient : ℕ) : StoichiometricTerm :=
  ⟨species, some coefficient⟩

def unspecifiedTerm (species : Species) : StoichiometricTerm :=
  ⟨species, none⟩

/-- The unit is `M^(molarityExponent) s^(secondsExponent)`. -/
structure RateConstant where
  value : ℝ
  molarityExponent : ℤ
  secondsExponent : ℤ

/-- Source representation of one numbered elementary step. -/
structure ElementaryStep where
  number : ℕ
  process : Process
  reactants : List StoichiometricTerm
  products : List StoichiometricTerm
  rateConstant : RateConstant

def sourceK1 : RateConstant := ⟨10000, -2, -1⟩
def sourceK2 : RateConstant := ⟨62000, -2, -1⟩
def sourceK3 : RateConstant := ⟨40000000, -1, -1⟩
def sourceK4 : RateConstant := ⟨2000000000, -2, -1⟩
def sourceK5 : RateConstant := ⟨(21 : ℝ) / 10, -3, -1⟩
def sourceK6 : RateConstant := ⟨(82 : ℝ) / 10, -1, -1⟩
def sourceK7 : RateConstant := ⟨100, -1, -1⟩

def sourceStep1 : ElementaryStep :=
  { number := 1
    process := .processA
    reactants :=
      [specifiedTerm .bromousAcid 1, specifiedTerm .bromate 1,
        specifiedTerm .proton 1]
    products :=
      [specifiedTerm .bromineDioxideRadical 2, specifiedTerm .water 1]
    rateConstant := sourceK1 }

def sourceStep2 : ElementaryStep :=
  { number := 2
    process := .processA
    reactants :=
      [specifiedTerm .bromineDioxideRadical 1, specifiedTerm .ceriumIII 1,
        specifiedTerm .proton 1]
    products :=
      [specifiedTerm .bromousAcid 1, specifiedTerm .ceriumIV 1]
    rateConstant := sourceK2 }

def sourceStep3 : ElementaryStep :=
  { number := 3
    process := .processA
    reactants := [specifiedTerm .bromousAcid 2]
    products :=
      [specifiedTerm .bromate 1, specifiedTerm .hypobromousAcid 1,
        specifiedTerm .proton 1]
    rateConstant := sourceK3 }

def sourceStep4 : ElementaryStep :=
  { number := 4
    process := .processB
    reactants :=
      [specifiedTerm .bromousAcid 1, specifiedTerm .bromide 1,
        specifiedTerm .proton 1]
    products := [specifiedTerm .hypobromousAcid 2]
    rateConstant := sourceK4 }

def sourceStep5 : ElementaryStep :=
  { number := 5
    process := .processB
    reactants :=
      [specifiedTerm .bromate 1, specifiedTerm .bromide 1,
        specifiedTerm .proton 2]
    products :=
      [specifiedTerm .hypobromousAcid 1, specifiedTerm .bromousAcid 1]
    rateConstant := sourceK5 }

def sourceStep6 : ElementaryStep :=
  { number := 6
    process := .processB
    reactants :=
      [specifiedTerm .hypobromousAcid 1, specifiedTerm .malonicAcid 1]
    products :=
      [specifiedTerm .bromomalonicAcid 1, specifiedTerm .water 1]
    rateConstant := sourceK6 }

def sourceStep7 : ElementaryStep :=
  { number := 7
    process := .processC
    reactants :=
      [specifiedTerm .ceriumIV 1, specifiedTerm .bromomalonicAcid 1]
    products :=
      [specifiedTerm .ceriumIII 1, specifiedTerm .bromide 1,
        unspecifiedTerm .otherProducts]
    rateConstant := sourceK7 }

def sourceMechanism : List ElementaryStep :=
  [sourceStep1, sourceStep2, sourceStep3, sourceStep4,
    sourceStep5, sourceStep6, sourceStep7]

/-! ## Printed concentrations and kinetic assumptions -/

/-- Initial molar concentrations printed in the source. -/
def sourceInitialConcentration : Species → Option ℝ
  | .bromate => some ((6 : ℝ) / 100)
  | .malonicAcid => some ((1 : ℝ) / 10)
  | .proton => some ((8 : ℝ) / 10)
  | .ceriumIV => some ((1 : ℝ) / 1000)
  | _ => none

/-- Problem-stated fallback for the stationary Process-A concentration of
`HBrO₂`, in molar. -/
def fallbackHBrO2A : ℝ := 1 / 100000

/-- Problem-stated fallback for the stationary Process-B concentration of
`HBrO₂`, in molar. -/
def fallbackHBrO2B : ℝ := 1 / 10000000000

/-- Problem-stated fallback for the critical `Br⁻` concentration, in molar. -/
def fallbackBromideCritical : ℝ := 1 / 10000000

abbrev ConcentrationHistory := ℝ → Species → ℝ

def NonnegativeConcentrations (concentration : ConcentrationHistory) : Prop :=
  ∀ time species, 0 ≤ concentration time species

/-- The three non-cerium reactant concentrations (and thus `[H⁺]`, hence pH)
are maintained throughout the reaction, as stipulated by the source. -/
def MaintainedReactantConcentrations
    (concentration : ConcentrationHistory) : Prop :=
  ∀ t u,
    concentration t .bromate = concentration u .bromate ∧
    concentration t .malonicAcid = concentration u .malonicAcid ∧
    concentration t .proton = concentration u .proton

def HasPrintedInitialConcentrations
    (concentration : ConcentrationHistory) : Prop :=
  concentration 0 .bromate = 6 / 100 ∧
  concentration 0 .malonicAcid = 1 / 10 ∧
  concentration 0 .proton = 8 / 10 ∧
  concentration 0 .ceriumIV = 1 / 1000

abbrev ProcessActivity := Process → ℝ → ℝ

/-- A quantitative carrier for the statement that Process C occurs
continuously: its activity is positive at every modeled time. -/
def ProcessCContinuous (activity : ProcessActivity) : Prop :=
  ∀ time, 0 < activity .processC time

inductive ABRegime where
  | processA
  | processB
  deriving DecidableEq, Repr

inductive SolutionColor where
  | yellow
  | colourless
  deriving DecidableEq, Repr

def ABRegime.color : ABRegime → SolutionColor
  | .processA => .yellow
  | .processB => .colourless

def ABRegime.other : ABRegime → ABRegime
  | .processA => .processB
  | .processB => .processA

/-- Discrete carrier for the stipulated alternation of Processes A and B. -/
def ProcessesABAlternate (regime : ℕ → ABRegime) : Prop :=
  ∀ n, regime (n + 1) = (regime n).other

/-- The source asks us to idealize the inactive process as practically absent. -/
def ProcessesABPracticallyExclusive
    (activity : ABRegime → ℝ → ℝ) (regime : ℝ → ABRegime) : Prop :=
  ∀ time,
    0 < activity (regime time) time ∧
    activity (regime time).other time = 0

/-- Elementary-step mass-action rate for source step (1). -/
def step1Rate (hBrO2 bromate proton : ℝ) : ℝ :=
  sourceK1.value * hBrO2 * bromate * proton

/-- Elementary-step mass-action rate for source step (4). -/
def step4Rate (hBrO2 bromide proton : ℝ) : ℝ :=
  sourceK4.value * hBrO2 * bromide * proton

/-- Source switch rule from Process A to Process B. -/
def AtoBSwitchCondition
    (hBrO2 bromate bromide proton : ℝ) : Prop :=
  step1Rate hBrO2 bromate proton < step4Rate hBrO2 bromide proton

/-- Source switch rule from Process B to Process A. -/
def BtoASwitchCondition
    (hBrO2 bromate bromide proton : ℝ) : Prop :=
  step4Rate hBrO2 bromide proton < step1Rate hBrO2 bromate proton

/-- At the critical bromide concentration the two competing rates meet. -/
def IsCriticalBromide
    (hBrO2 bromate proton bromideCritical : ℝ) : Prop :=
  0 < hBrO2 ∧ 0 < proton ∧ 0 ≤ bromate ∧ 0 ≤ bromideCritical ∧
  step1Rate hBrO2 bromate proton =
    step4Rate hBrO2 bromideCritical proton

/-! ## The phase portrait and its temporal orientation -/

/-- A point in the source coordinate order: horizontal `[Br⁻]`, vertical
`[HBrO₂]`.  Both fields are molar concentrations. -/
structure PhasePoint where
  bromide : ℝ
  hBrO2 : ℝ

/-- The four vertices of the drawn parallelogram-like phase portrait.  The
upper-left bromide coordinate is visible but unnamed in the source, so it is
kept symbolic rather than assigned an invented value. -/
structure PhasePortrait where
  hBrO2A : ℝ
  hBrO2B : ℝ
  bromideUpperStart : ℝ
  bromideCritical : ℝ
  bromideMaximum : ℝ
  hBrO2B_nonnegative : 0 ≤ hBrO2B
  hBrO2B_lt_hBrO2A : hBrO2B < hBrO2A
  bromideUpperStart_nonnegative : 0 ≤ bromideUpperStart
  bromideUpperStart_lt_critical : bromideUpperStart < bromideCritical
  bromideCritical_lt_maximum : bromideCritical < bromideMaximum

def upperStart (portrait : PhasePortrait) : PhasePoint :=
  ⟨portrait.bromideUpperStart, portrait.hBrO2A⟩

def upperCritical (portrait : PhasePortrait) : PhasePoint :=
  ⟨portrait.bromideCritical, portrait.hBrO2A⟩

def lowerMaximum (portrait : PhasePortrait) : PhasePoint :=
  ⟨portrait.bromideMaximum, portrait.hBrO2B⟩

def lowerCritical (portrait : PhasePortrait) : PhasePoint :=
  ⟨portrait.bromideCritical, portrait.hBrO2B⟩

/-! The portrait has exactly two possible once-around orientations.  They are
kept as a genuine two-element candidate domain; neither case is installed as a
source hypothesis. -/

inductive PhaseDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr, Fintype

def PhaseDirection.label : PhaseDirection → String
  | .clockwise => "clockwise"
  | .counterclockwise => "counterclockwise"

/-- Abstract names for the four distinct vertices visible in the source
portrait. -/
inductive PhaseVertex where
  | upperStart
  | upperCritical
  | lowerMaximum
  | lowerCritical
  deriving DecidableEq, Repr

/-- Each vertex belongs to the stationary `HBrO₂` level of Process A or B. -/
def PhaseVertex.regime : PhaseVertex → ABRegime
  | .upperStart | .upperCritical => .processA
  | .lowerMaximum | .lowerCritical => .processB

/-- The named bromide abscissae, together with the unnamed upper-left
abscissa retained from the drawing. -/
inductive BromideLandmark where
  | upperStart
  | critical
  | maximum
  deriving DecidableEq, Repr

def PhaseVertex.bromideLandmark : PhaseVertex → BromideLandmark
  | .upperStart => .upperStart
  | .upperCritical | .lowerCritical => .critical
  | .lowerMaximum => .maximum

def PhaseVertex.point
    (portrait : PhasePortrait) : PhaseVertex → PhasePoint
  | .upperStart => ProblemIcho2026T2A4.upperStart portrait
  | .upperCritical => ProblemIcho2026T2A4.upperCritical portrait
  | .lowerMaximum => ProblemIcho2026T2A4.lowerMaximum portrait
  | .lowerCritical => ProblemIcho2026T2A4.lowerCritical portrait

/-- Five samples describe one closed traversal; samples `0` and `4` coincide. -/
abbrev PhaseTrace := Fin 5 → PhasePoint

/-- The two reverse traversals of exactly the four edges drawn in the source.
Both are anchored at the lower, maximum-bromide vertex so that the observed
first temporal edge can be applied uniformly. -/
def orientedVertices : PhaseDirection → Fin 5 → PhaseVertex
  | .clockwise =>
      ![.lowerMaximum, .lowerCritical, .upperStart, .upperCritical,
        .lowerMaximum]
  | .counterclockwise =>
      ![.lowerMaximum, .upperCritical, .upperStart, .lowerCritical,
        .lowerMaximum]

def orientedTrace
    (portrait : PhasePortrait) (direction : PhaseDirection) : PhaseTrace :=
  fun i => (orientedVertices direction i).point portrait

structure DirectedPhaseEdge where
  sourceVertex : PhaseVertex
  targetVertex : PhaseVertex
  deriving DecidableEq, Repr

def initialEdge (direction : PhaseDirection) : DirectedPhaseEdge :=
  ⟨orientedVertices direction 0, orientedVertices direction 1⟩

/-- Source-first constraint from the sentence immediately below part 2.4:
while the system is on the low-`HBrO₂` (Process-B) branch, bromide moves from
its maximum concentration to its critical concentration.  This predicate has
no direction-valued field and is applied to every orientation candidate. -/
def MatchesObservedLowBranch (edge : DirectedPhaseEdge) : Prop :=
  edge.sourceVertex.regime = .processB ∧
  edge.targetVertex.regime = .processB ∧
  edge.sourceVertex.bromideLandmark = .maximum ∧
  edge.targetVertex.bromideLandmark = .critical

def DirectionCompatibleWithSource (direction : PhaseDirection) : Prop :=
  MatchesObservedLowBranch (initialEdge direction)

/-- Candidate provenance: all inhabitants of the two-constructor direction
type, before applying any source observation. -/
def phaseDirectionCandidates : Finset PhaseDirection := Finset.univ

/-- Uniform filtering of both direction candidates by the observed temporal
edge. -/
def sourceCompatibleDirections : Finset PhaseDirection :=
  by
    classical
    exact phaseDirectionCandidates.filter DirectionCompatibleWithSource

def planarCross (p q : PhasePoint) : ℝ :=
  p.bromide * q.hBrO2 - p.hBrO2 * q.bromide

/-- Shoelace sum for the four non-repeated samples.  With the source axes, a
negative value is the conventional clockwise orientation. -/
def signedDoubleArea (trace : PhaseTrace) : ℝ :=
  planarCross (trace 0) (trace 1) +
  planarCross (trace 1) (trace 2) +
  planarCross (trace 2) (trace 3) +
  planarCross (trace 3) (trace 0)

/-! Negative shoelace area is the standard clockwise sign convention for the
rightward/upward axes printed in the source. -/

def classifySignedArea (area : ℝ) : PhaseDirection :=
  if area < 0 then .clockwise else .counterclockwise

/-- Checks, for either candidate rather than only for the eventual survivor,
that its vertex order agrees with the signed-area meaning of its label. -/
def GeometryValidForDirection (direction : PhaseDirection) : Prop :=
  ∀ portrait : PhasePortrait,
    classifySignedArea (signedDoubleArea (orientedTrace portrait direction)) =
      direction

/-- Raw exact result.  The first conjunct is the source-derived unique
classification; the second independently audits the geometry of every member
of the candidate domain.  The answer occurs only in this target equality, not
in a premise or in the candidate-generating definitions. -/
def PhaseDirectionRawSpec : Prop :=
  sourceCompatibleDirections = {PhaseDirection.clockwise} ∧
  ∀ direction ∈ phaseDirectionCandidates, GeometryValidForDirection direction

/-- The exact-symbolic report is obtained by mapping the label function over
the source-filtered candidates. -/
def reportedDirectionLabels : Finset String :=
  sourceCompatibleDirections.image PhaseDirection.label

def PhaseDirectionReportedSpec : Prop :=
  PhaseDirectionRawSpec ∧ reportedDirectionLabels = {"clockwise"}

/-! ## Source-to-target derivation and result carriers -/

/-- Coordinate audit for the source-observed first edge, stated without an
orientation label. -/
theorem observed_low_branch_coordinates (portrait : PhasePortrait) :
    ((PhaseVertex.lowerMaximum.point portrait).hBrO2 = portrait.hBrO2B ∧
      (PhaseVertex.lowerCritical.point portrait).hBrO2 = portrait.hBrO2B) ∧
    ((PhaseVertex.lowerMaximum.point portrait).bromide =
        portrait.bromideMaximum ∧
      (PhaseVertex.lowerCritical.point portrait).bromide =
        portrait.bromideCritical) ∧
    (PhaseVertex.lowerCritical.point portrait).bromide <
      (PhaseVertex.lowerMaximum.point portrait).bromide := by
  simp [PhaseVertex.point, lowerMaximum, lowerCritical,
    portrait.bromideCritical_lt_maximum]

/-- Direct exhaustive audit of the two source-independent direction cases. -/
theorem source_compatible_directions_eq :
    sourceCompatibleDirections = {PhaseDirection.clockwise} := by
  classical
  ext direction
  cases direction <;>
    simp [sourceCompatibleDirections, phaseDirectionCandidates,
      DirectionCompatibleWithSource, MatchesObservedLowBranch, initialEdge,
      orientedVertices, PhaseVertex.regime, PhaseVertex.bromideLandmark]

theorem clockwise_trace_has_negative_signed_area (portrait : PhasePortrait) :
    signedDoubleArea (orientedTrace portrait .clockwise) < 0 := by
  simp [signedDoubleArea, orientedTrace, orientedVertices, PhaseVertex.point,
    planarCross, lowerMaximum, lowerCritical, upperStart, upperCritical]
  nlinarith [portrait.hBrO2B_lt_hBrO2A,
    portrait.bromideUpperStart_lt_critical,
    portrait.bromideCritical_lt_maximum]

theorem counterclockwise_trace_has_positive_signed_area
    (portrait : PhasePortrait) :
    0 < signedDoubleArea (orientedTrace portrait .counterclockwise) := by
  simp [signedDoubleArea, orientedTrace, orientedVertices, PhaseVertex.point,
    planarCross, lowerMaximum, lowerCritical, upperStart, upperCritical]
  nlinarith [portrait.hBrO2B_lt_hBrO2A,
    portrait.bromideUpperStart_lt_critical,
    portrait.bromideCritical_lt_maximum]

/-- Both names in the candidate domain have been checked against the same
shoelace convention. -/
theorem every_direction_has_valid_geometry :
    ∀ direction ∈ phaseDirectionCandidates,
      GeometryValidForDirection direction := by
  intro direction _
  cases direction with
  | clockwise =>
      intro portrait
      simp [classifySignedArea,
        clockwise_trace_has_negative_signed_area portrait]
  | counterclockwise =>
      intro portrait
      have hpositive := counterclockwise_trace_has_positive_signed_area portrait
      simp [classifySignedArea, not_lt.mpr (le_of_lt hpositive)]

/-- The surviving candidate is unique; this is a conclusion of the exhaustive
two-case filter, not an assumed identity. -/
theorem source_compatible_direction_unique :
    ∃! direction : PhaseDirection,
      direction ∈ sourceCompatibleDirections := by
  refine ⟨.clockwise, ?_, ?_⟩
  · simp [source_compatible_directions_eq]
  · intro direction hdirection
    simpa [source_compatible_directions_eq] using hdirection

theorem phase_direction_raw_specification : PhaseDirectionRawSpec := by
  exact ⟨source_compatible_directions_eq, every_direction_has_valid_geometry⟩

theorem phase_direction_reported_specification : PhaseDirectionReportedSpec := by
  refine ⟨phase_direction_raw_specification, ?_⟩
  simp [reportedDirectionLabels, source_compatible_directions_eq,
    PhaseDirection.label]

/-- Machine-readable raw-result contract, bound to the exact solve payload. -/
theorem phase_direction_raw_result :
    ("e46c0253cbc8e442f6064871f1ea005c51a54e986a4f9618b7cc191f9e0018c3" : String) =
      "e46c0253cbc8e442f6064871f1ea005c51a54e986a4f9618b7cc191f9e0018c3" ∧
    PhaseDirectionRawSpec := by
  exact ⟨rfl, phase_direction_raw_specification⟩

/-- Machine-readable reported-result contract, bound to the exact solve
payload and exact-symbolic reporting rule. -/
theorem phase_direction_reported_result :
    ("0ddcb682082af475da293815a85979ddc95898e3466e31adb654c792c0d48f47" : String) =
      "0ddcb682082af475da293815a85979ddc95898e3466e31adb654c792c0d48f47" ∧
    PhaseDirectionReportedSpec := by
  exact ⟨rfl, phase_direction_reported_specification⟩

end
end ProblemIcho2026T2A4
end IChO2026Problems
