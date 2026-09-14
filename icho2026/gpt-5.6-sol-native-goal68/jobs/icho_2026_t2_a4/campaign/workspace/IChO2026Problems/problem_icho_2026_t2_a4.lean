import Mathlib

/-!
# IChO 2026 T2-A4: direction around the BZ phase portrait

This file formalizes the four arrow diagrams printed on the blank answer sheet.
The vertices are named by their locations in the supplied portrait.  In
particular, the lower horizontal segment is the stationary Process-B branch,
because its ordinate is `[HBrO₂]B`.

The problem text supplies the time-oriented datum that bromide slowly decreases
from `[Br⁻]max` to `[Br⁻]critical`.  Thus the lower segment must be traversed
from `lowerMaximum` to `lowerCritical`.  The phrase “oscillate strictly in
relation to each other” and the closed polygon in the question require the
arrows to form one directed cycle.  The theorem below proves that the
upper-right (clockwise) answer-sheet box is the unique printed diagram with
both properties.
-/

namespace IChO2026Problems.T2A4

/-- The four corners of the polygonal phase portrait in the problem figure. -/
inductive PhaseVertex where
  | upperLowBromide
  | upperCritical
  | lowerMaximum
  | lowerCritical
  deriving DecidableEq, Repr

/-- Locations of the four choices on the blank A2-3 answer sheet. -/
inductive AnswerBox where
  | upperLeft
  | upperRight
  | lowerLeft
  | lowerRight
  deriving DecidableEq, Repr

namespace ProblemInput

/--
Exact transcription of the red arrows printed in the four answer-sheet boxes.
This is graphical problem input, not a derived dynamical law.
-/
def HasPrintedArrow : AnswerBox → PhaseVertex → PhaseVertex → Prop
  | .upperLeft, .upperCritical, .upperLowBromide => True
  | .upperLeft, .upperLowBromide, .lowerCritical => True
  | .upperLeft, .lowerCritical, .lowerMaximum => True
  | .upperLeft, .lowerMaximum, .upperCritical => True
  | .upperRight, .upperLowBromide, .upperCritical => True
  | .upperRight, .upperCritical, .lowerMaximum => True
  | .upperRight, .lowerMaximum, .lowerCritical => True
  | .upperRight, .lowerCritical, .upperLowBromide => True
  | .lowerLeft, .upperCritical, .upperLowBromide => True
  | .lowerLeft, .upperLowBromide, .lowerCritical => True
  | .lowerLeft, .upperCritical, .lowerMaximum => True
  | .lowerLeft, .lowerMaximum, .lowerCritical => True
  | .lowerRight, .upperLowBromide, .upperCritical => True
  | .lowerRight, .lowerCritical, .upperLowBromide => True
  | .lowerRight, .lowerMaximum, .upperCritical => True
  | .lowerRight, .lowerCritical, .lowerMaximum => True
  | _, _, _ => False

end ProblemInput

open ProblemInput

/-- The four arrows consistently traverse the portrait clockwise. -/
def IsClockwiseCycle (box : AnswerBox) : Prop :=
  HasPrintedArrow box .upperLowBromide .upperCritical ∧
  HasPrintedArrow box .upperCritical .lowerMaximum ∧
  HasPrintedArrow box .lowerMaximum .lowerCritical ∧
  HasPrintedArrow box .lowerCritical .upperLowBromide

/-- The four arrows consistently traverse the portrait counterclockwise. -/
def IsCounterclockwiseCycle (box : AnswerBox) : Prop :=
  HasPrintedArrow box .upperCritical .upperLowBromide ∧
  HasPrintedArrow box .upperLowBromide .lowerCritical ∧
  HasPrintedArrow box .lowerCritical .lowerMaximum ∧
  HasPrintedArrow box .lowerMaximum .upperCritical

/-- An oscillatory traversal has no source or sink on the closed portrait. -/
def IsCoherentOscillation (box : AnswerBox) : Prop :=
  IsClockwiseCycle box ∨ IsCounterclockwiseCycle box

/--
On the lower, Process-B branch, the printed arrow agrees with the stated slow
decrease of `[Br⁻]` from its maximum value to its critical value.
-/
def MatchesStatedBromideDecrease (box : AnswerBox) : Prop :=
  HasPrintedArrow box .lowerMaximum .lowerCritical

/-- The complete qualitative criterion supplied by T2-A4 and its context. -/
def FitsProblem (box : AnswerBox) : Prop :=
  IsCoherentOscillation box ∧ MatchesStatedBromideDecrease box

theorem upperRight_is_clockwise : IsClockwiseCycle .upperRight := by
  simp [IsClockwiseCycle, HasPrintedArrow]

theorem upperRight_fits_problem : FitsProblem .upperRight := by
  exact ⟨Or.inl upperRight_is_clockwise, by
    simp [MatchesStatedBromideDecrease, HasPrintedArrow]⟩

/--
Requested output: the unique answer-sheet selection is the upper-right box.
Equivalently, the concentrations traverse the phase portrait clockwise.
-/
theorem icho_2026_t2_a4_phase_direction :
    FitsProblem .upperRight ∧
      ∀ box : AnswerBox, FitsProblem box → box = .upperRight := by
  refine ⟨upperRight_fits_problem, ?_⟩
  intro box hbox
  cases box with
  | upperLeft =>
      simp [FitsProblem, IsCoherentOscillation, IsClockwiseCycle,
        IsCounterclockwiseCycle, MatchesStatedBromideDecrease,
        HasPrintedArrow] at hbox
  | upperRight => rfl
  | lowerLeft =>
      simp [FitsProblem, IsCoherentOscillation, IsClockwiseCycle,
        IsCounterclockwiseCycle, MatchesStatedBromideDecrease,
        HasPrintedArrow] at hbox
  | lowerRight =>
      simp [FitsProblem, IsCoherentOscillation, IsClockwiseCycle,
        IsCounterclockwiseCycle, MatchesStatedBromideDecrease,
        HasPrintedArrow] at hbox

theorem icho_2026_t2_a4_unique_phase_direction :
    ∃! box : AnswerBox, FitsProblem box := by
  refine ⟨.upperRight, icho_2026_t2_a4_phase_direction.1, ?_⟩
  intro box hbox
  exact icho_2026_t2_a4_phase_direction.2 box hbox

end IChO2026Problems.T2A4

#print axioms IChO2026Problems.T2A4.icho_2026_t2_a4_phase_direction
#print axioms IChO2026Problems.T2A4.icho_2026_t2_a4_unique_phase_direction
