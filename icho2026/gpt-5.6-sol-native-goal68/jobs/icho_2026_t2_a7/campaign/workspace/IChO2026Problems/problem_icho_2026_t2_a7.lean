import Mathlib

/-!
# IChO 2026, theory problem 2.7

The source asks which of six qualitative plots can represent `dG/dt` for a
closed oscillatory reaction.  The answer sheet orders the choices in a 3 by 2
grid.  We transcribe that finite choice set and its visible qualitative
features, and then prove that the bottom-right plot is the unique plot which

* oscillates,
* never has positive `dG/dt`, and
* relaxes to zero.

The mathematical part below proves the thermodynamic consequences used in that
classification in both discrete and continuous time.  A lower-bounded,
nonincreasing Gibbs sequence has nonpositive forward changes which tend to
zero.  For a differentiable continuous Gibbs trajectory, antitonicity forces
its literal derivative to be nonpositive.  The nonincreasing premise is the
standard Gibbs criterion for a spontaneous closed system at fixed temperature
and pressure; fixed `T,p` are not stated verbatim in the question and are
therefore kept visible in the model names rather than being smuggled in as a
theorem about every closed system.
-/

namespace IChO2026Problems.T2A7

open Filter
open scoped Topology

/-! ## Thermodynamic model and derived rate constraints -/

/-- The forward finite-difference analogue of `dG/dt`.  A sequence is used
because the requested output is qualitative; no time scale is supplied. -/
def stepGibbsRate (G : ℕ → ℝ) (n : ℕ) : ℝ :=
  G (n + 1) - G n

/-- Premises supplied by the standard fixed-temperature, fixed-pressure Gibbs
criterion for a spontaneous closed-system relaxation, together with the
finite-system lower bound needed for equilibration.  These are model premises,
not unchecked Lean axioms. -/
structure FixedTPClosedEvolution where
  gibbs : ℕ → ℝ
  lowerBound : ℝ
  lowerBound_le : ∀ n, lowerBound ≤ gibbs n
  gibbs_antitone : Antitone gibbs

/-- A qualitative rate oscillates if it is neither globally increasing nor
globally decreasing.  This is deliberately qualitative and does not invent a
period or amplitude absent from the source. -/
def RateOscillates (r : ℕ → ℝ) : Prop :=
  ¬ Monotone r ∧ ¬ Antitone r

/-- The thermodynamic model plus the problem's oscillatory-rate premise. -/
structure ClosedOscillatoryEvolution where
  thermodynamics : FixedTPClosedEvolution
  rateOscillates : RateOscillates
    (stepGibbsRate thermodynamics.gibbs)

/-- Monotone Gibbs-energy decrease forces every forward rate to be
nonpositive. -/
theorem stepGibbsRate_nonpositive (s : FixedTPClosedEvolution) (n : ℕ) :
    stepGibbsRate s.gibbs n ≤ 0 := by
  have hstep : s.gibbs (n + 1) ≤ s.gibbs n :=
    s.gibbs_antitone (Nat.le_succ n)
  exact sub_nonpos.mpr hstep

/-- A Gibbs-energy sequence satisfying the fixed-`T,p` model converges to its
infimum. -/
theorem gibbs_tends_to_infimum (s : FixedTPClosedEvolution) :
    Tendsto s.gibbs atTop (𝓝 (⨅ n, s.gibbs n)) := by
  have hbdd : BddBelow (Set.range s.gibbs) := by
    refine ⟨s.lowerBound, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact s.lowerBound_le n
  exact tendsto_atTop_ciInf s.gibbs_antitone hbdd

/-- Once Gibbs energy converges, its forward finite-difference rate tends to
zero.  This formalizes the dying-out of the rate in the closed system. -/
theorem stepGibbsRate_tends_to_zero (s : FixedTPClosedEvolution) :
    Tendsto (fun n => stepGibbsRate s.gibbs n) atTop (𝓝 0) := by
  have hG := gibbs_tends_to_infimum s
  have hshift :
      Tendsto (fun n : ℕ => s.gibbs (n + 1)) atTop
        (𝓝 (⨅ n, s.gibbs n)) :=
    hG.comp (tendsto_add_atTop_nat 1)
  simpa [stepGibbsRate] using hshift.sub hG

/-- The absolute size of the rate also tends to zero, the precise convergence
fact represented by the damping envelope in the selected drawing. -/
theorem abs_stepGibbsRate_tends_to_zero (s : FixedTPClosedEvolution) :
    Tendsto (fun n => |stepGibbsRate s.gibbs n|) atTop (𝓝 0) := by
  simpa using (stepGibbsRate_tends_to_zero s).abs

/-- All three qualitative constraints used to read the graph are exposed in
one theorem. -/
theorem closed_oscillatory_rate_constraints (s : ClosedOscillatoryEvolution) :
    RateOscillates (stepGibbsRate s.thermodynamics.gibbs) ∧
      (∀ n, stepGibbsRate s.thermodynamics.gibbs n ≤ 0) ∧
      Tendsto (fun n => stepGibbsRate s.thermodynamics.gibbs n) atTop (𝓝 0) := by
  exact ⟨s.rateOscillates,
    stepGibbsRate_nonpositive s.thermodynamics,
    stepGibbsRate_tends_to_zero s.thermodynamics⟩

/-! The following model addresses the literal continuous derivative printed on
the answer sheet. -/

/-- Minimal qualitative oscillation predicate for a real-time rate. -/
def RealRateOscillates (r : ℝ → ℝ) : Prop :=
  ¬ Monotone r ∧ ¬ Antitone r

/-- Continuous-time version of the intended physical setting.  The final field
states relaxation of the derivative to its equilibrium value.  That limit is
kept explicit because lower-bounded monotone differentiable functions do not,
without extra regularity, force their derivatives to converge. -/
structure ContinuousFixedTPClosedOscillatoryEvolution where
  gibbs : ℝ → ℝ
  gibbsRate : ℝ → ℝ
  gibbs_antitone : Antitone gibbs
  hasDerivAt_gibbs : ∀ t, HasDerivAt gibbs (gibbsRate t) t
  rateOscillates : RealRateOscillates gibbsRate
  rate_tends_to_zero : Tendsto gibbsRate atTop (𝓝 0)

/-- The literal Gibbs derivative is nonpositive at every time. -/
theorem gibbsDerivative_nonpositive
    (s : ContinuousFixedTPClosedOscillatoryEvolution) (t : ℝ) :
    s.gibbsRate t ≤ 0 := by
  exact (s.hasDerivAt_gibbs t).nonpos_of_antitone s.gibbs_antitone

/-- The three continuous-time properties used to select the source graph. -/
theorem continuous_gibbs_rate_constraints
    (s : ContinuousFixedTPClosedOscillatoryEvolution) :
    RealRateOscillates s.gibbsRate ∧
      (∀ t, s.gibbsRate t ≤ 0) ∧
      Tendsto s.gibbsRate atTop (𝓝 0) := by
  exact ⟨s.rateOscillates, gibbsDerivative_nonpositive s,
    s.rate_tends_to_zero⟩

/-! ## Transcription and classification of the six source graphs -/

/-- Positions of the six boxes on PDF answer sheet A2-6, read row by row. -/
inductive GibbsRateGraph where
  | topLeft
  | topRight
  | middleLeft
  | middleRight
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Repr

/-- Exactly the three visible graph features dictated by the thermodynamic
argument. -/
structure GraphFeatures where
  oscillatory : Bool
  staysNonpositive : Bool
  relaxesToZero : Bool
  deriving DecidableEq, Repr

/-- Direct transcription of the six red curves in source PDF page 24 (answer
sheet A2-6). -/
def graphFeatures : GibbsRateGraph → GraphFeatures
  | .topLeft =>
      ⟨false, true, false⟩
  | .topRight =>
      ⟨true, false, false⟩
  | .middleLeft =>
      ⟨false, true, true⟩
  | .middleRight =>
      ⟨true, true, false⟩
  | .bottomLeft =>
      ⟨true, false, false⟩
  | .bottomRight =>
      ⟨true, true, true⟩

/-- A plotted candidate matches the oscillatory closed-system constraints. -/
def SatisfiesThermodynamicConstraints (g : GibbsRateGraph) : Prop :=
  (graphFeatures g).oscillatory = true ∧
  (graphFeatures g).staysNonpositive = true ∧
  (graphFeatures g).relaxesToZero = true

/-- Exhausting all six source choices leaves precisely the bottom-right plot. -/
theorem satisfies_constraints_iff_bottomRight (g : GibbsRateGraph) :
    SatisfiesThermodynamicConstraints g ↔ g = .bottomRight := by
  cases g <;> simp [SatisfiesThermodynamicConstraints, graphFeatures]

/-- **Requested output:** the bottom-right box is the unique admissible graph. -/
theorem gibbs_rate_graph_answer :
    ∃! g : GibbsRateGraph, SatisfiesThermodynamicConstraints g := by
  refine ⟨.bottomRight, ?_, ?_⟩
  · simp [SatisfiesThermodynamicConstraints, graphFeatures]
  · intro g hg
    exact (satisfies_constraints_iff_bottomRight g).mp hg

/-- A candidate graph matches a particular modeled evolution when both the
derived rate facts and the candidate's transcribed features meet the same
three constraints. -/
def GraphMatchesEvolution
    (s : ClosedOscillatoryEvolution) (g : GibbsRateGraph) : Prop :=
  RateOscillates (stepGibbsRate s.thermodynamics.gibbs) ∧
  (∀ n, stepGibbsRate s.thermodynamics.gibbs n ≤ 0) ∧
  Tendsto (fun n => stepGibbsRate s.thermodynamics.gibbs n) atTop (𝓝 0) ∧
  SatisfiesThermodynamicConstraints g

/-- The full model-to-answer theorem: for every closed oscillatory evolution
satisfying the explicit fixed-`T,p` thermodynamic premises, the bottom-right
box is the unique matching source graph. -/
theorem closed_oscillatory_system_selects_bottomRight
    (s : ClosedOscillatoryEvolution) :
    ∃! g : GibbsRateGraph, GraphMatchesEvolution s g := by
  rcases closed_oscillatory_rate_constraints s with ⟨hosc, hnonpos, hzero⟩
  refine ⟨.bottomRight, ?_, ?_⟩
  · exact ⟨hosc, hnonpos, hzero,
      by simp [SatisfiesThermodynamicConstraints, graphFeatures]⟩
  · intro g hg
    exact (satisfies_constraints_iff_bottomRight g).mp hg.2.2.2

/-- Matching predicate for the literal derivative model. -/
def GraphMatchesContinuousEvolution
    (s : ContinuousFixedTPClosedOscillatoryEvolution)
    (g : GibbsRateGraph) : Prop :=
  RealRateOscillates s.gibbsRate ∧
  (∀ t, s.gibbsRate t ≤ 0) ∧
  Tendsto s.gibbsRate atTop (𝓝 0) ∧
  SatisfiesThermodynamicConstraints g

/-- **Requested continuous-time output:** the bottom-right source box is the
unique graph matching the qualitative behavior of the literal `dG/dt`. -/
theorem continuous_system_selects_bottomRight
    (s : ContinuousFixedTPClosedOscillatoryEvolution) :
    ∃! g : GibbsRateGraph, GraphMatchesContinuousEvolution s g := by
  rcases continuous_gibbs_rate_constraints s with ⟨hosc, hnonpos, hzero⟩
  refine ⟨.bottomRight, ?_, ?_⟩
  · exact ⟨hosc, hnonpos, hzero,
      by simp [SatisfiesThermodynamicConstraints, graphFeatures]⟩
  · intro g hg
    exact (satisfies_constraints_iff_bottomRight g).mp hg.2.2.2

/-- A named equality form of the requested classification, convenient for
downstream consumers. -/
def selectedGraph : GibbsRateGraph := .bottomRight

theorem selectedGraph_eq_bottomRight :
    selectedGraph = .bottomRight := by
  change GibbsRateGraph.bottomRight = GibbsRateGraph.bottomRight
  rfl

end IChO2026Problems.T2A7

#print axioms IChO2026Problems.T2A7.stepGibbsRate_nonpositive
#print axioms IChO2026Problems.T2A7.gibbs_tends_to_infimum
#print axioms IChO2026Problems.T2A7.stepGibbsRate_tends_to_zero
#print axioms IChO2026Problems.T2A7.closed_oscillatory_rate_constraints
#print axioms IChO2026Problems.T2A7.gibbsDerivative_nonpositive
#print axioms IChO2026Problems.T2A7.continuous_gibbs_rate_constraints
#print axioms IChO2026Problems.T2A7.satisfies_constraints_iff_bottomRight
#print axioms IChO2026Problems.T2A7.gibbs_rate_graph_answer
#print axioms IChO2026Problems.T2A7.closed_oscillatory_system_selects_bottomRight
#print axioms IChO2026Problems.T2A7.continuous_system_selects_bottomRight
#print axioms IChO2026Problems.T2A7.selectedGraph_eq_bottomRight
