import Mathlib

/-!
# IChO 2026 T7-A1: gases in M1 and M2

This file formalizes the species-level information in Fig. 1 of the problem.
`ProblemInput` contains only data printed in the figure: stream labels, reaction
reactants/products, and the stated distinction between quantitative reactions
and the non-quantitative ammonia-formation step.  The requested mixtures are
then computed by finite-set transformations.

For the comparison of `x` and `y`, amounts are real numbers and a quantitative
1:1 reforming step has extent `min x y`.  `ReformerMatchesDiagram` says that
the positive-support of the resulting amount function is exactly the printed
outlet label `CH4, CO, H2`.  In particular, residual methane is an input fact
read from the diagram, not an assumed comparison between `x` and `y`.
-/

namespace IChO2026Problems.Icho2026T7A1

/-- The eight gases offered as tick-box choices on the blank A7-1 answer sheet. -/
inductive Gas where
  | CH4
  | H2O
  | CO
  | O2
  | H2
  | N2
  | NH3
  | CO2
  deriving DecidableEq, Repr

open Gas

/-- Species-level effect of a quantitative reaction: the displayed reactant
species are consumed, inert species are carried through, and product species
are present. -/
def completeReaction
    (feed reactants products : Finset Gas) : Finset Gas :=
  (feed \ reactants) ∪ products

namespace ProblemInput

/-- The stream label immediately after steam reforming in Fig. 1. -/
def reformerEffluent : Finset Gas := {CH4, CO, H2}

/-- The `4 N2 + 1 O2` air feed in Fig. 1, at species-support level. -/
def airFeed : Finset Gas := {N2, O2}

/-- Reactants and products printed in `2 CH4 + O2 ⟶ 2 CO + 4 H2`. -/
def oxidationReactants : Finset Gas := {CH4, O2}
def oxidationProducts : Finset Gas := {CO, H2}

/-- Reactants and products printed in `CO + H2O ⟶ CO2 + H2`. -/
def shiftReactants : Finset Gas := {CO, H2O}
def shiftProducts : Finset Gas := {CO2, H2}

end ProblemInput

/-- Mixture 1, obtained after the quantitative partial-oxidation reactor. -/
def M1 : Finset Gas :=
  completeReaction
    (ProblemInput.reformerEffluent ∪ ProblemInput.airFeed)
    ProblemInput.oxidationReactants
    ProblemInput.oxidationProducts

/-- The outlet of the quantitative water-gas-shift reactor. -/
def shiftedStream : Finset Gas :=
  completeReaction (M1 ∪ {H2O})
    ProblemInput.shiftReactants ProblemInput.shiftProducts

/-- The CO2 scrubber removes carbon dioxide and does not react with N2 or H2. -/
def synthesisFeed : Finset Gas := shiftedStream.erase CO2

/-- Because ammonia formation is not quantitative and Fig. 1 explicitly
recycles unreacted `N2, H2`, the reactor outlet retains its feed gases and also
contains the formed ammonia.  This outlet is M2, before the cooler removes NH3. -/
def M2 : Finset Gas := synthesisFeed ∪ {NH3}

/-- Requested output `gases_m1`: the complete species set in M1. -/
theorem gases_m1 : M1 = {CO, H2, N2} := by
  ext g
  cases g <;>
    simp [M1, completeReaction, ProblemInput.reformerEffluent,
      ProblemInput.airFeed, ProblemInput.oxidationReactants,
      ProblemInput.oxidationProducts]

/-- The computed intermediate stream agrees with the `N2, CO2, H2` label in
the source diagram, providing an internal check on the M1 computation. -/
theorem gases_after_shift : shiftedStream = {N2, CO2, H2} := by
  ext g
  cases g <;>
    simp [shiftedStream, M1, completeReaction,
      ProblemInput.reformerEffluent, ProblemInput.airFeed,
      ProblemInput.oxidationReactants, ProblemInput.oxidationProducts,
      ProblemInput.shiftReactants, ProblemInput.shiftProducts]

/-- The scrubbed gas sent to ammonia synthesis contains just nitrogen and
hydrogen, as also shown on the downward stream after `Z` in Fig. 1. -/
theorem gases_in_synthesis_feed : synthesisFeed = {N2, H2} := by
  rw [synthesisFeed, gases_after_shift]
  ext g
  cases g <;> simp

/-- Requested output `gases_m2`: the complete species set in M2. -/
theorem gases_m2 : M2 = {N2, H2, NH3} := by
  rw [M2, gases_in_synthesis_feed]
  ext g
  cases g <;> simp

/-- Extent of the quantitative 1:1 reaction `CH4 + H2O ⟶ CO + 3 H2`. -/
def reformerExtent (x y : ℝ) : ℝ := min x y

/-- Amount of every answer-sheet species immediately after quantitative steam
reforming of `x` mol CH4 with `y` mol H2O. -/
def reformerOutletAmount (x y : ℝ) : Gas → ℝ
  | CH4 => x - reformerExtent x y
  | H2O => y - reformerExtent x y
  | CO => reformerExtent x y
  | O2 => 0
  | H2 => 3 * reformerExtent x y
  | N2 => 0
  | NH3 => 0
  | CO2 => 0

/-- Source-grounding predicate for the first outlet: amounts are physical and
the gases with positive amount are exactly the printed `CH4, CO, H2` label. -/
structure ReformerMatchesDiagram (x y : ℝ) : Prop where
  x_nonnegative : 0 ≤ x
  y_nonnegative : 0 ≤ y
  support_exact : ∀ g,
    g ∈ ProblemInput.reformerEffluent ↔ 0 < reformerOutletAmount x y g

/-- The source predicate is consistent: it is satisfied by a nonempty family
of feeds (this witness also rules out a vacuous implication below). -/
theorem reformer_source_consistent : ReformerMatchesDiagram 2 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro g
  cases g <;>
    norm_num [ProblemInput.reformerEffluent, reformerOutletAmount,
      reformerExtent] <;>
    decide

/-- Requested output `xy_relation`: the residual CH4 printed in the reformer
outlet forces methane to have been supplied in excess, hence `x > y`. -/
theorem xy_relation {x y : ℝ} (h : ReformerMatchesDiagram x y) : x > y := by
  have hCH4 : CH4 ∈ ProblemInput.reformerEffluent := by
    simp [ProblemInput.reformerEffluent]
  have hpositive : 0 < x - min x y := by
    simpa [reformerOutletAmount, reformerExtent] using
      (h.support_exact CH4).mp hCH4
  by_contra hnot
  have hxy : x ≤ y := le_of_not_gt hnot
  rw [min_eq_left hxy] at hpositive
  linarith

#print axioms gases_m1
#print axioms gases_m2
#print axioms xy_relation

end IChO2026Problems.Icho2026T7A1
