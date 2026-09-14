import Mathlib
import CRNT.Basic.Reaction

/-!
# IChO 2026, problem T2, part A4

The horizontal coordinate in the supplied phase portrait is the bromide
concentration and the vertical coordinate is the bromous-acid concentration.
This file records the printed reaction mechanism and reduces the requested
direction to the orientation of the portrayed four-edge cycle.  In particular,
the answer is not assumed as a field of a chemical model: the only directed
edge supplied to the geometric argument is the printed slow Process-B motion
from maximum bromide to critical bromide along the low-bromous-acid edge.
-/

namespace IChO2026Problems.ProblemIChO2026T2A4

noncomputable section

/-! ## Chemical source data -/

/-- Named dissolved species and intermediates that occur in elementary steps
(1)--(7).  Step (7)'s unnamed products are deliberately not represented as a
quantified material stream: this target uses only the explicitly tracked
bromide product of that qualitative mechanism step. -/
inductive Species
  | bromousAcid
  | bromate
  | proton
  | bromineDioxideRadical
  | water
  | ceriumIII
  | ceriumIV
  | bromide
  | hypobromousAcid
  | malonicAcid
  | bromomalonicAcid
  deriving DecidableEq, Fintype, Repr

/-- The four chemicals named as the initial mixture. -/
inductive FeedChemical
  | potassiumBromate
  | malonicAcid
  | ceriumIVSulfate
  | sulfuricAcid
  deriving DecidableEq, Fintype, Repr

/-- The three processes in the printed BZ mechanism. -/
inductive Process
  | processA
  | processB
  | processC
  deriving DecidableEq, Fintype, Repr

/-- Labels of the seven elementary steps printed on page T2-2. -/
inductive ReactionStep
  | step1
  | step2
  | step3
  | step4
  | step5
  | step6
  | step7
  deriving DecidableEq, Fintype, Repr

/-- The source-complex stoichiometric coefficient in each printed elementary
step. -/
def sourceStoichiometry : ReactionStep → Species → ℕ
  | .step1, .bromousAcid => 1
  | .step1, .bromate => 1
  | .step1, .proton => 1
  | .step2, .bromineDioxideRadical => 1
  | .step2, .ceriumIII => 1
  | .step2, .proton => 1
  | .step3, .bromousAcid => 2
  | .step4, .bromousAcid => 1
  | .step4, .bromide => 1
  | .step4, .proton => 1
  | .step5, .bromate => 1
  | .step5, .bromide => 1
  | .step5, .proton => 2
  | .step6, .hypobromousAcid => 1
  | .step6, .malonicAcid => 1
  | .step7, .ceriumIV => 1
  | .step7, .bromomalonicAcid => 1
  | _, _ => 0

/-- The explicitly named part of the target-complex stoichiometry in each
printed elementary step.  For step (7), this is a projection to the three
named species; it makes no assertion about the source's "other products". -/
def targetStoichiometry : ReactionStep → Species → ℕ
  | .step1, .bromineDioxideRadical => 2
  | .step1, .water => 1
  | .step2, .bromousAcid => 1
  | .step2, .ceriumIV => 1
  | .step3, .bromate => 1
  | .step3, .hypobromousAcid => 1
  | .step3, .proton => 1
  | .step4, .hypobromousAcid => 2
  | .step5, .hypobromousAcid => 1
  | .step5, .bromousAcid => 1
  | .step6, .bromomalonicAcid => 1
  | .step6, .water => 1
  | .step7, .ceriumIII => 1
  | .step7, .bromide => 1
  | _, _ => 0

/-- The CRNT reaction obtained from the named stoichiometry of a printed step. -/
def reaction (step : ReactionStep) : CRNT.Reaction Species where
  source := sourceStoichiometry step
  target := targetStoichiometry step

/-- Whether the problem displays the complete product complex of a step or
explicitly leaves additional products unspecified. -/
inductive ProductDisclosure
  | completelyDisplayed
  | additionalProductsUnspecified
  deriving DecidableEq, Repr

/-- Only step (7) is printed with "other products". -/
def productDisclosure : ReactionStep → ProductDisclosure
  | .step7 => .additionalProductsUnspecified
  | _ => .completelyDisplayed

/-- Dimensions attached to the printed numerical rate constants. -/
inductive RateConstantUnit
  | molarNegOneSecondNegOne
  | molarNegTwoSecondNegOne
  | molarNegThreeSecondNegOne
  deriving DecidableEq, Repr

/-- A printed rate constant, retaining its unit separately from its exact
central value. -/
structure PrintedRateConstant where
  value : ℝ
  unit : RateConstantUnit

/-- Exact-as-printed rate constants `k₁`, ..., `k₇`. -/
def printedRateConstant : ReactionStep → PrintedRateConstant
  | .step1 => ⟨10000, .molarNegTwoSecondNegOne⟩
  | .step2 => ⟨62000, .molarNegTwoSecondNegOne⟩
  | .step3 => ⟨40000000, .molarNegOneSecondNegOne⟩
  | .step4 => ⟨2000000000, .molarNegTwoSecondNegOne⟩
  | .step5 => ⟨21 / 10, .molarNegThreeSecondNegOne⟩
  | .step6 => ⟨82 / 10, .molarNegOneSecondNegOne⟩
  | .step7 => ⟨100, .molarNegOneSecondNegOne⟩

/-- The bulk concentrations stated on page T2-2, in mol/L. -/
structure BulkConditions where
  bromate : ℝ
  malonicAcid : ℝ
  proton : ℝ
  ceriumIVInitial : ℝ

/-- Exact-as-printed bulk concentration data. -/
def printedBulkConditions : BulkConditions where
  bromate := 6 / 100
  malonicAcid := 1 / 10
  proton := 8 / 10
  ceriumIVInitial := 1 / 1000

/-- The two colours explicitly assigned to the alternating processes. -/
inductive SolutionColour
  | yellow
  | colourless
  deriving DecidableEq, Repr

/-- Process A is yellow (Ce(IV)); Process B is colourless (Ce(III)). -/
def alternatingProcessColour : Process → Option SolutionColour
  | .processA => some .yellow
  | .processB => some .colourless
  | .processC => none

/-- A concentration vector over the locally enumerated species.  This is the
same mathematical interface as `CRNT.Concentration`; the small local alias is
used because the pinned dependency exposes `CRNT.Reaction` but does not ship
the compiled kinetics module in this workspace. -/
abbrev Concentration := Species → ℝ

/-- Strict positivity of every tracked concentration. -/
def Concentration.Positive (x : Concentration) : Prop :=
  ∀ species : Species, 0 < x species

/-- Mass-action source-complex monomial for the finite tracked species set. -/
def massActionMonomial (complex : CRNT.Complex Species) (x : Concentration) : ℝ :=
  ∏ species : Species, x species ^ complex species

/-- Mass-action rate of one printed elementary step, using the CRNT
mass-action monomial and the problem's exact rate constant. -/
def elementaryRate (step : ReactionStep) (x : Concentration) : ℝ :=
  (printedRateConstant step).value *
    massActionMonomial (reaction step).source x

/-- Net concentration velocity contributed by all displayed steps in one
process.  Step (7) is used only through its named-species projection. -/
def processVelocity (process : Process) (x : Concentration)
    (species : Species) : ℝ :=
  match process with
  | .processA =>
      elementaryRate .step1 x * (reaction .step1).vector species +
      elementaryRate .step2 x * (reaction .step2).vector species +
      elementaryRate .step3 x * (reaction .step3).vector species
  | .processB =>
      elementaryRate .step4 x * (reaction .step4).vector species +
      elementaryRate .step5 x * (reaction .step5).vector species +
      elementaryRate .step6 x * (reaction .step6).vector species
  | .processC =>
      elementaryRate .step7 x * (reaction .step7).vector species

/-- Steps (4) and (5) each consume one bromide ion, so positive Process-B
rates give a leftward bromide velocity. -/
theorem processB_bromide_velocity_negative
    (x : Concentration) (hx : x.Positive) :
    processVelocity .processB x .bromide < 0 := by
  have hmonomial (complex : CRNT.Complex Species) :
      0 < massActionMonomial complex x := by
    unfold massActionMonomial
    exact Finset.prod_pos fun species _ => pow_pos (hx species) _
  have hstep4 : 0 < elementaryRate .step4 x := by
    unfold elementaryRate
    exact mul_pos (by norm_num [printedRateConstant]) (hmonomial _)
  have hstep5 : 0 < elementaryRate .step5 x := by
    unfold elementaryRate
    exact mul_pos (by norm_num [printedRateConstant]) (hmonomial _)
  simp only [processVelocity, reaction, CRNT.Reaction.vector_apply,
    targetStoichiometry, sourceStoichiometry]
  norm_num
  linarith

/-- The named part of Process C produces one bromide ion, so at positive
concentrations it gives a rightward bromide velocity. -/
theorem processC_bromide_velocity_positive
    (x : Concentration) (hx : x.Positive) :
    0 < processVelocity .processC x .bromide := by
  have hmonomial (complex : CRNT.Complex Species) :
      0 < massActionMonomial complex x := by
    unfold massActionMonomial
    exact Finset.prod_pos fun species _ => pow_pos (hx species) _
  have hstep7 : 0 < elementaryRate .step7 x := by
    unfold elementaryRate
    exact mul_pos (by norm_num [printedRateConstant]) (hmonomial _)
  simpa [processVelocity, reaction, CRNT.Reaction.vector_apply,
    targetStoichiometry, sourceStoichiometry] using hstep7

/-! ## Inline derivation of the levels used by the phase portrait -/

/-- Reduced positive steady-state equation for HBrO₂ in Process A, obtained
from `r₁ = 2 r₃` after cancellation of the positive HBrO₂ concentration. -/
def ProcessAStationaryEquation (hbrO2 : ℝ) : Prop :=
  (printedRateConstant .step1).value * printedBulkConditions.bromate *
      printedBulkConditions.proton =
    2 * (printedRateConstant .step3).value * hbrO2

/-- Reduced positive steady-state equation for HBrO₂ in Process B, obtained
from `r₄ = r₅` after cancellation of positive bromide and one proton factor. -/
def ProcessBStationaryEquation (hbrO2 : ℝ) : Prop :=
  (printedRateConstant .step5).value * printedBulkConditions.bromate *
      printedBulkConditions.proton =
    (printedRateConstant .step4).value * hbrO2

/-- Source-derived positive stationary HBrO₂ concentration for Process A. -/
def stationaryHBrO2A : ℝ :=
  (printedRateConstant .step1).value * printedBulkConditions.bromate *
      printedBulkConditions.proton /
    (2 * (printedRateConstant .step3).value)

/-- Source-derived positive stationary HBrO₂ concentration for Process B. -/
def stationaryHBrO2B : ℝ :=
  (printedRateConstant .step5).value * printedBulkConditions.bromate *
      printedBulkConditions.proton /
    (printedRateConstant .step4).value

/-- Critical bromide concentration obtained by equating steps (1) and (4) and
cancelling their common positive HBrO₂ and proton factors. -/
def criticalBromide : ℝ :=
  (printedRateConstant .step1).value * printedBulkConditions.bromate /
    (printedRateConstant .step4).value

/-- The maximum bromide concentration printed immediately below part 2.4. -/
def maximumBromide : ℝ := 7 / 10000

/-- Exact problem-stated fallbacks, available to later parts if an earlier
calculation could not be completed. -/
def fallbackHBrO2A : ℝ := 1 / 100000
def fallbackHBrO2B : ℝ := 1 / 10000000000
def fallbackCriticalBromide : ℝ := 1 / 10000000

/-- The formula-defined levels satisfy their reduced steady-state equations
and are the unique positive solutions of those linear equations. -/
theorem stationary_levels_specification :
    0 < stationaryHBrO2A ∧
    ProcessAStationaryEquation stationaryHBrO2A ∧
    (∀ h : ℝ, 0 < h → ProcessAStationaryEquation h → h = stationaryHBrO2A) ∧
    0 < stationaryHBrO2B ∧
    ProcessBStationaryEquation stationaryHBrO2B ∧
    (∀ h : ℝ, 0 < h → ProcessBStationaryEquation h → h = stationaryHBrO2B) := by
  norm_num [stationaryHBrO2A, stationaryHBrO2B,
    ProcessAStationaryEquation, ProcessBStationaryEquation,
    printedRateConstant, printedBulkConditions]
  constructor <;> intro h _ hequation <;> linarith

/-- Rate comparison used by the printed A/B switch rule. -/
theorem step4_exceeds_step1_iff_above_critical
    (x : Concentration)
    (hbromate : x .bromate = printedBulkConditions.bromate)
    (hhbrO2 : 0 < x .bromousAcid)
    (hproton : 0 < x .proton) :
    elementaryRate .step1 x < elementaryRate .step4 x ↔
      criticalBromide < x .bromide := by
  classical
  have hmonomial1 :
      massActionMonomial (reaction .step1).source x =
        x .bromousAcid * x .bromate * x .proton := by
    unfold massActionMonomial
    calc
      (∏ species : Species, x species ^ (reaction .step1).source species) =
          ∏ species ∈
            ({.bromousAcid, .bromate, .proton} : Finset Species),
              x species ^ (reaction .step1).source species := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro species _ hspecies
        fin_cases species <;>
          simp_all [reaction, sourceStoichiometry]
      _ = x .bromousAcid * x .bromate * x .proton := by
        simp [reaction, sourceStoichiometry, mul_assoc]
  have hmonomial4 :
      massActionMonomial (reaction .step4).source x =
        x .bromousAcid * x .bromide * x .proton := by
    unfold massActionMonomial
    calc
      (∏ species : Species, x species ^ (reaction .step4).source species) =
          ∏ species ∈
            ({.bromousAcid, .bromide, .proton} : Finset Species),
              x species ^ (reaction .step4).source species := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro species _ hspecies
        fin_cases species <;>
          simp_all [reaction, sourceStoichiometry]
      _ = x .bromousAcid * x .bromide * x .proton := by
        simp [reaction, sourceStoichiometry, mul_assoc]
  rw [elementaryRate, elementaryRate, hmonomial1, hmonomial4, hbromate]
  norm_num [printedRateConstant, printedBulkConditions, criticalBromide]
  constructor <;> intro h
  · nlinarith [mul_pos hhbrO2 hproton]
  · nlinarith [mul_pos hhbrO2 hproton]

/-- Arithmetic consequences needed to read the vertical and horizontal
ordering of the phase portrait. -/
theorem source_concentration_orders :
    0 < stationaryHBrO2B ∧ stationaryHBrO2B < stationaryHBrO2A ∧
    0 < criticalBromide ∧ criticalBromide < maximumBromide := by
  norm_num [stationaryHBrO2A, stationaryHBrO2B, criticalBromide,
    maximumBromide, printedRateConstant, printedBulkConditions]

/-! ## Source portrait and its geometric orientation -/

/-- A point in the supplied phase plane: bromide is the horizontal coordinate
and HBrO₂ is the vertical coordinate. -/
structure PhasePoint where
  bromide : ℝ
  bromousAcid : ℝ
  deriving DecidableEq

/-- The four visually distinct corners of the sketched phase portrait. -/
inductive PhaseCorner
  | lowAtMaximum
  | lowAtCritical
  | highAtLeft
  | highAtCritical
  deriving DecidableEq, Fintype, Repr

/-- Metric information read from the axes, labels, and dashed guide lines of
the source portrait.  No pixel-derived numerical value is assigned to the
unlabelled upper-left bromide coordinate. -/
structure PhasePortraitGeometry where
  bromideAtHighLeft : ℝ
  bromideCritical : ℝ
  bromideMaximum : ℝ
  hbrO2B : ℝ
  hbrO2A : ℝ
  highLeft_nonnegative : 0 ≤ bromideAtHighLeft
  highLeft_lt_critical : bromideAtHighLeft < bromideCritical
  critical_lt_maximum : bromideCritical < bromideMaximum
  lowLevel_positive : 0 < hbrO2B
  lowLevel_lt_highLevel : hbrO2B < hbrO2A

/-- Coordinates of each labelled corner in the page T2-3 sketch. -/
def PhasePortraitGeometry.point (p : PhasePortraitGeometry) : PhaseCorner → PhasePoint
  | .lowAtMaximum => ⟨p.bromideMaximum, p.hbrO2B⟩
  | .lowAtCritical => ⟨p.bromideCritical, p.hbrO2B⟩
  | .highAtLeft => ⟨p.bromideAtHighLeft, p.hbrO2A⟩
  | .highAtCritical => ⟨p.bromideCritical, p.hbrO2A⟩

/-- The source portrait, parameterized only by the unlabelled upper-left
bromide coordinate and constrained by what the image visibly establishes. -/
def sourcePortrait (bromideAtHighLeft : ℝ)
    (h : 0 ≤ bromideAtHighLeft ∧ bromideAtHighLeft < criticalBromide) :
    PhasePortraitGeometry where
  bromideAtHighLeft := bromideAtHighLeft
  bromideCritical := criticalBromide
  bromideMaximum := maximumBromide
  hbrO2B := stationaryHBrO2B
  hbrO2A := stationaryHBrO2A
  highLeft_nonnegative := h.1
  highLeft_lt_critical := h.2
  critical_lt_maximum := source_concentration_orders.2.2.2
  lowLevel_positive := source_concentration_orders.1
  lowLevel_lt_highLevel := source_concentration_orders.2.1

/-- Undirected edge relation of the four-sided source portrait. -/
def BoundaryAdjacent : PhaseCorner → PhaseCorner → Prop
  | .lowAtMaximum, .lowAtCritical => True
  | .lowAtCritical, .lowAtMaximum => True
  | .lowAtCritical, .highAtLeft => True
  | .highAtLeft, .lowAtCritical => True
  | .highAtLeft, .highAtCritical => True
  | .highAtCritical, .highAtLeft => True
  | .highAtCritical, .lowAtMaximum => True
  | .lowAtMaximum, .highAtCritical => True
  | _, _ => False

/-- One period represented by four successive distinct portrait corners. -/
structure PhaseTraversal where
  first : PhaseCorner
  second : PhaseCorner
  third : PhaseCorner
  fourth : PhaseCorner
  deriving DecidableEq

/-- A traversal uses every corner once and follows all four boundary edges,
including the closing edge. -/
def IsBoundaryCycle (t : PhaseTraversal) : Prop :=
  t.first ≠ t.second ∧
  t.first ≠ t.third ∧
  t.first ≠ t.fourth ∧
  t.second ≠ t.third ∧
  t.second ≠ t.fourth ∧
  t.third ≠ t.fourth ∧
  BoundaryAdjacent t.first t.second ∧
  BoundaryAdjacent t.second t.third ∧
  BoundaryAdjacent t.third t.fourth ∧
  BoundaryAdjacent t.fourth t.first

/-- The directed observation printed below part 2.4: in Process B, bromide
slowly decreases from its maximum to its critical value while HBrO₂ is at its
low stationary level. -/
def HasPrintedSlowLeg (t : PhaseTraversal) : Prop :=
  t.first = .lowAtMaximum ∧ t.second = .lowAtCritical

/-- Twice the signed area contribution of an oriented edge. -/
def edgeCross (p q : PhasePoint) : ℝ :=
  p.bromide * q.bromousAcid - p.bromousAcid * q.bromide

/-- Twice the signed shoelace area of the four-corner traversal. -/
def traversalTwiceSignedArea (p : PhasePortraitGeometry) (t : PhaseTraversal) : ℝ :=
  edgeCross (p.point t.first) (p.point t.second) +
  edgeCross (p.point t.second) (p.point t.third) +
  edgeCross (p.point t.third) (p.point t.fourth) +
  edgeCross (p.point t.fourth) (p.point t.first)

/-- The two nondegenerate directions available for a planar cycle. -/
inductive PhaseDirection
  | clockwise
  | counterclockwise
  deriving DecidableEq, Fintype, Repr

/-- Standard Cartesian signed-area convention.  A degenerate zero-area input
has no direction rather than being silently assigned to either answer. -/
def directionFromSignedArea (area2 : ℝ) : Option PhaseDirection :=
  if area2 < 0 then some .clockwise
  else if 0 < area2 then some .counterclockwise
  else none

/-- Direction of a given boundary traversal in the source coordinate system. -/
def traversalDirection (p : PhasePortraitGeometry) (t : PhaseTraversal) :
    Option PhaseDirection :=
  directionFromSignedArea (traversalTwiceSignedArea p t)

/-- Once the printed slow edge fixes the first two corners, boundary
connectivity and non-repetition force the remaining two corners. -/
theorem printed_slow_leg_forces_corner_order
    (t : PhaseTraversal) (hcycle : IsBoundaryCycle t)
    (hslow : HasPrintedSlowLeg t) :
    t.third = .highAtLeft ∧ t.fourth = .highAtCritical := by
  rcases t with ⟨first, second, third, fourth⟩
  change first = .lowAtMaximum ∧ second = .lowAtCritical at hslow
  rcases hslow with ⟨rfl, rfl⟩
  change third = .highAtLeft ∧ fourth = .highAtCritical
  fin_cases third <;> fin_cases fourth <;>
    simp_all [IsBoundaryCycle, BoundaryAdjacent]

/-- The resulting traversal has negative signed area for every unlabelled
upper-left coordinate compatible with the source image. -/
theorem printed_traversal_has_negative_signed_area
    (bromideAtHighLeft : ℝ)
    (hleft : 0 ≤ bromideAtHighLeft ∧ bromideAtHighLeft < criticalBromide)
    (t : PhaseTraversal) (hcycle : IsBoundaryCycle t)
    (hslow : HasPrintedSlowLeg t) :
    traversalTwiceSignedArea (sourcePortrait bromideAtHighLeft hleft) t < 0 := by
  have horder := printed_slow_leg_forces_corner_order t hcycle hslow
  rcases t with ⟨first, second, third, fourth⟩
  change first = .lowAtMaximum ∧ second = .lowAtCritical at hslow
  rcases hslow with ⟨rfl, rfl⟩
  change third = .highAtLeft ∧ fourth = .highAtCritical at horder
  rcases horder with ⟨rfl, rfl⟩
  simp only [traversalTwiceSignedArea, edgeCross, PhasePortraitGeometry.point,
    sourcePortrait]
  have hx : bromideAtHighLeft < maximumBromide :=
    lt_trans hleft.2 source_concentration_orders.2.2.2
  have hh : stationaryHBrO2B < stationaryHBrO2A :=
    source_concentration_orders.2.1
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hh) (sub_neg.mpr hx)]

/-! ## Requested exact-symbolic result -/

/-- The source-compatible geometric domain is inhabited; this prevents the
universal direction statement below from succeeding vacuously. -/
def SourceTraversalDomainNonempty : Prop :=
  ∃ (bromideAtHighLeft : ℝ)
    (_hleft : 0 ≤ bromideAtHighLeft ∧ bromideAtHighLeft < criticalBromide)
    (t : PhaseTraversal),
    IsBoundaryCycle t ∧ HasPrintedSlowLeg t

/-- Raw, source-derived specification for the sole requested output.  It is
universal over the visually unlabelled upper-left coordinate and over every
simple boundary traversal compatible with the printed slow leg. -/
def PhaseDirectionRawResult : Prop :=
  SourceTraversalDomainNonempty ∧
    ∀ (bromideAtHighLeft : ℝ)
      (hleft : 0 ≤ bromideAtHighLeft ∧ bromideAtHighLeft < criticalBromide)
      (t : PhaseTraversal),
      IsBoundaryCycle t →
      HasPrintedSlowLeg t →
      traversalDirection (sourcePortrait bromideAtHighLeft hleft) t =
        some .clockwise

/-- Exact-symbolic reporting does not round or otherwise transform the raw
classification. -/
def PhaseDirectionReportedResult : Prop :=
  PhaseDirectionRawResult

/-- Raw-result contract: the source-supported phase-cycle direction is
clockwise. -/
theorem phaseDirectionRawResult : PhaseDirectionRawResult := by
  constructor
  · refine ⟨0, ⟨by norm_num, source_concentration_orders.2.2.1⟩,
      ⟨.lowAtMaximum, .lowAtCritical, .highAtLeft, .highAtCritical⟩, ?_, ?_⟩
    · simp [IsBoundaryCycle, BoundaryAdjacent]
    · simp [HasPrintedSlowLeg]
  · intro bromideAtHighLeft hleft t hcycle hslow
    simp [traversalDirection, directionFromSignedArea,
      printed_traversal_has_negative_signed_area bromideAtHighLeft hleft t hcycle hslow]

/-- Reported-result contract for the exact classification requested by part
2.4. -/
theorem phaseDirectionReportedResult : PhaseDirectionReportedResult := by
  exact phaseDirectionRawResult

end

end IChO2026Problems.ProblemIChO2026T2A4
