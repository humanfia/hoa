import Mathlib

/-!
# IChO 2026 Theory, Problem T2, part 2.4 (target icho_2026_t2_a4)

Source material (problem-only inputs):

* Printed page Q2-3 (`theory_problem.pdf` p. 17, `T2_page-3.png`): the phase
  portrait of `[HBrO₂]` (vertical) vs `[Br⁻]` (horizontal), with
  `[Br⁻]critical < [Br⁻]max` and `[HBrO₂]B < [HBrO₂]A`; the statement that
  switching between Process A and Process B is controlled by whether the rate
  of elementary step (4) exceeds that of elementary step (1); and (between
  items 2.4 and 2.5) the sentence: "the concentration of [Br⁻] slowly
  **decreases** from [Br⁻]max = 7.0 × 10⁻⁴ M to [Br⁻]critical, and then almost
  immediately reaches [Br⁻]max again."
* Printed page Q2-2 (`theory_problem.pdf` p. 16, `T2_page-2.png`): the
  mechanism.  Process B steps (4) and (5) **consume** Br⁻; Process C, which
  "occurs continuously", contains step (7)
  `Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products`, which **produces** Br⁻;
  Process A is autocatalytic in HBrO₂; "when Process A occurs … Process B
  practically does not occur" and conversely.
* Blank student answer sheet A2-3 (`theory_problem.pdf` p. 21): four tick-box
  diagrams that differ only in the directions of the edge arrows.

Requested output (`requested_outputs[phase_direction]`, kind `classification`):
the direction of motion in the supplied phase portrait.

Answer derived here: **counterclockwise** —

* bottom edge (Process B, `[HBrO₂] = [HBrO₂]B`): `[Br⁻]` decreases
  ([Br⁻]max → [Br⁻]critical), motion right → left;
* left edge (B → A switch at `[Br⁻]critical`): `[HBrO₂]` jumps upward
  ([HBrO₂]B → [HBrO₂]A);
* top edge (Process A, `[HBrO₂] = [HBrO₂]A`): `[Br⁻]` increases
  ([Br⁻]critical → [Br⁻]max), motion left → right;
* right edge (A → B switch at `[Br⁻]max`): `[HBrO₂]` falls downward
  ([HBrO₂]A → [HBrO₂]B).

This is the bottom-left tick box on answer sheet A2-3.
-/

namespace IChO2026T2A4

/-! ## Directions on the phase portrait -/

/-- A sign of change along an edge: `inr` = increasing (right/up),
`dec` = decreasing (left/down). -/
inductive ChangeSign where
  | dec
  | inr
  deriving DecidableEq, Repr

/-- A candidate traversal direction for the sketched four-edge limit cycle.
Along each edge one concentration is essentially constant
(`[HBrO₂]` on the horizontal edges, `[Br⁻]` on the switch edges), so the
direction is fully described by the sign of change of the *other*
concentration on each edge. -/
structure Direction where
  /-- Sign of `d[Br⁻]` along the bottom edge (`[HBrO₂] = [HBrO₂]B`, Process B). -/
  bottomBr : ChangeSign
  /-- Sign of `d[HBrO₂]` along the left edge (`[Br⁻] = [Br⁻]critical`, B→A switch). -/
  leftHbro2 : ChangeSign
  /-- Sign of `d[Br⁻]` along the top edge (`[HBrO₂] = [HBrO₂]A`, Process A). -/
  topBr : ChangeSign
  /-- Sign of `d[HBrO₂]` along the right edge (`[Br⁻] = [Br⁻]max`, A→B switch). -/
  rightHbro2 : ChangeSign
  deriving DecidableEq, Repr

/-- The counterclockwise direction: bottom right→left, left bottom→top,
top left→right, right top→bottom.  This is the bottom-left diagram on the
answer sheet A2-3. -/
def counterclockwise : Direction :=
  { bottomBr := .dec, leftHbro2 := .inr, topBr := .inr, rightHbro2 := .dec }

/-- The clockwise direction (bottom left→right, left top→bottom,
top right→left, right bottom→top): the bottom-right diagram on the answer
sheet, i.e. the fully reversed option. -/
def clockwise : Direction :=
  { bottomBr := .inr, leftHbro2 := .dec, topBr := .dec, rightHbro2 := .inr }

/-! ## Problem-stated constraints

These record, as data, what the problem statement fixes about each edge:

1. (Q2-3 text, verbatim, between 2.4 and 2.5) During Process B the bromide
   concentration *decreases* from `[Br⁻]max` to `[Br⁻]critical`; chemically,
   steps (4) and (5) — the bromide-involving steps of Process B — both
   consume Br⁻.  Hence `bottomBr = .dec`.
2. The `vice versa` switch condition in Q2-3: the B → A switch occurs when
   the rate of step (1) exceeds that of step (4), i.e. at
   `[Br⁻] = [Br⁻]critical`; the autocatalytic Process A then drives
   `[HBrO₂]` up to its Process-A steady-state value.  Hence
   `leftHbro2 = .inr`.
3. (Q2-2 text) Process C occurs *continuously* and step (7) *produces* Br⁻;
   while Process A runs, Process B (the bromide sink) "practically does not
   occur", so `[Br⁻]` increases back towards `[Br⁻]max` at the Process-A
   level `[HBrO₂]A`.  Hence `topBr = .inr`.
4. The A → B switch at `[Br⁻]max` (rate(4) > rate(1), as stated in Q2-3)
   quenches HBrO₂ via step (4), so `[HBrO₂]` falls to its Process-B value.
   Hence `rightHbro2 = .dec`.
-/

/-- A direction is compatible with the problem statement iff all four of the
problem-grounded edge signs hold. -/
def CompatibleWithProblem (d : Direction) : Prop :=
  d.bottomBr = .dec ∧ d.leftHbro2 = .inr ∧ d.topBr = .inr ∧ d.rightHbro2 = .dec

/-- The counterclockwise direction satisfies every constraint that the problem
statement imposes. -/
theorem counterclockwise_compatible :
    CompatibleWithProblem counterclockwise :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Compatibility forces *every* component of the direction, so the problem
statement determines the answer uniquely. -/
theorem compatible_eq_counterclockwise {d : Direction}
    (h : CompatibleWithProblem d) : d = counterclockwise := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases d with
  | mk b l t r =>
    subst h1; subst h2; subst h3; subst h4
    rfl

/-- The clockwise option on the answer sheet is *not* compatible with the
problem statement: it asserts that `[Br⁻]` *increases* during Process B,
contradicting the printed sentence "the concentration of [Br⁻] slowly
decreases from [Br⁻]max … to [Br⁻]critical" and the consumption of Br⁻ by
steps (4) and (5). -/
theorem clockwise_not_compatible : ¬ CompatibleWithProblem clockwise := by
  intro h
  exact ChangeSign.noConfusion h.1

/-! ## Geometric reading of the portrait

The marked values satisfy `[Br⁻]critical < [Br⁻]max` (horizontal axis) and
`[HBrO₂]B < [HBrO₂]A` (vertical axis), exactly as printed in the sketch on
Q2-3.  (Numerically this is consistent with 2.3, which gives
`[Br⁻]critical = k₁[BrO₃⁻]/k₄ = 3 × 10⁻⁷ M`, and the printed
`[Br⁻]max = 7.0 × 10⁻⁴ M`.)  We record this ordering and show that each
compatible edge sign moves the system from one marked value *towards* the
other in the correct sense. -/

/-- The marked concentrations, ordered exactly as printed on the axes of the
portrait in Q2-3. -/
structure PortraitData where
  brCrit : ℝ
  brMax : ℝ
  hbro2B : ℝ
  hbro2A : ℝ
  br_ordered : brCrit < brMax
  hbro2_ordered : hbro2B < hbro2A

/-- Along the bottom edge the compatible direction moves from `[Br⁻]max`
towards `[Br⁻]critical` (a strict decrease, right → left). -/
theorem bottom_motion_towards_critical (P : PortraitData) (d : Direction)
    (h : d.bottomBr = .dec) :
    P.brCrit < P.brMax ∧ d.bottomBr = .dec :=
  ⟨P.br_ordered, h⟩

/-- Along the left switch edge the compatible direction moves from
`[HBrO₂]B` up to `[HBrO₂]A` (a strict increase, bottom → top). -/
theorem left_motion_upwards (P : PortraitData) (d : Direction)
    (h : d.leftHbro2 = .inr) :
    P.hbro2B < P.hbro2A ∧ d.leftHbro2 = .inr :=
  ⟨P.hbro2_ordered, h⟩

/-- Along the top edge the compatible direction moves from `[Br⁻]critical`
back to `[Br⁻]max` (a strict increase, left → right). -/
theorem top_motion_towards_max (P : PortraitData) (d : Direction)
    (h : d.topBr = .inr) :
    P.brCrit < P.brMax ∧ d.topBr = .inr :=
  ⟨P.br_ordered, h⟩

/-- Along the right switch edge the compatible direction moves from
`[HBrO₂]A` down to `[HBrO₂]B` (a strict decrease, top → bottom). -/
theorem right_motion_downwards (P : PortraitData) (d : Direction)
    (h : d.rightHbro2 = .dec) :
    P.hbro2B < P.hbro2A ∧ d.rightHbro2 = .dec :=
  ⟨P.hbro2_ordered, h⟩

/-- With the printed axis ordering, the compatible direction traverses the
loop through the four corners in counterclockwise cyclic order:
`([Br⁻]max, [HBrO₂]B) → ([Br⁻]critical, [HBrO₂]B) →
 ([Br⁻]critical, [HBrO₂]A) → ([Br⁻]max, [HBrO₂]A) →
 ([Br⁻]max, [HBrO₂]B)`.  Each leg strictly decreases or increases the moving
coordinate in the stated sense. -/
theorem counterclockwise_traversal (P : PortraitData) :
    P.brCrit < P.brMax ∧ P.hbro2B < P.hbro2A ∧
    counterclockwise.bottomBr = .dec ∧ counterclockwise.leftHbro2 = .inr ∧
    counterclockwise.topBr = .inr ∧ counterclockwise.rightHbro2 = .dec :=
  ⟨P.br_ordered, P.hbro2_ordered, rfl, rfl, rfl, rfl⟩

/-! ## Main results -/

/-- **Main theorem (IChO 2026 T2, part 2.4).**
The direction of motion in the `[HBrO₂]` vs `[Br⁻]` phase portrait that is
forced by the problem statement is the counterclockwise one:

* bottom edge: `[Br⁻]` decreases from `[Br⁻]max` to `[Br⁻]critical`
  (Process B consumes Br⁻ via steps (4) and (5); also printed verbatim below
  item 2.4);
* left edge: `[HBrO₂]` jumps up from `[HBrO₂]B` to `[HBrO₂]A` (B→A switch,
  rate(1) > rate(4));
* top edge: `[Br⁻]` increases from `[Br⁻]critical` to `[Br⁻]max` (Process C
  step (7) regenerates Br⁻ while Process A runs);
* right edge: `[HBrO₂]` falls from `[HBrO₂]A` to `[HBrO₂]B` (A→B switch,
  rate(4) > rate(1)).

Moreover this is the *unique* direction satisfying the problem's constraints,
and the clockwise option printed on the answer sheet is excluded. -/
theorem icho_2026_t2_a4_answer :
    CompatibleWithProblem counterclockwise ∧
    (∀ d : Direction, CompatibleWithProblem d → d = counterclockwise) ∧
    ¬ CompatibleWithProblem clockwise :=
  ⟨counterclockwise_compatible, fun _ h => compatible_eq_counterclockwise h,
    clockwise_not_compatible⟩

/-- Componentwise restatement of the requested output: all four edge
directions, as they must appear in the ticked diagram on answer sheet A2-3. -/
theorem icho_2026_t2_a4_phase_direction_checks :
    counterclockwise.bottomBr = .dec ∧   -- bottom edge: right → left
    counterclockwise.leftHbro2 = .inr ∧  -- left edge:   bottom → top
    counterclockwise.topBr = .inr ∧      -- top edge:    left → right
    counterclockwise.rightHbro2 = .dec := -- right edge: top → bottom
  ⟨rfl, rfl, rfl, rfl⟩

/-- Uniqueness: any direction satisfying the problem-stated constraints *is*
the counterclockwise direction. -/
theorem icho_2026_t2_a4_unique_direction (d : Direction)
    (h : CompatibleWithProblem d) : d = counterclockwise :=
  compatible_eq_counterclockwise h

/-- The four tick-box diagrams on answer sheet A2-3 enumerate candidate
directions; the correct box is precisely the counterclockwise one
(the bottom-left diagram: bottom ←, left ↑, top →, right ↓). -/
def AnswerSheetCorrect (d : Direction) : Prop :=
  d = counterclockwise

/-- An answer-sheet option is the box that should be ticked iff it satisfies
the problem-stated constraints on the direction of motion. -/
theorem icho_2026_t2_a4_supports_choice (d : Direction) :
    AnswerSheetCorrect d ↔ CompatibleWithProblem d := by
  constructor
  · intro h; rw [h]; exact counterclockwise_compatible
  · intro h; exact compatible_eq_counterclockwise h

end IChO2026T2A4

#print axioms IChO2026T2A4.icho_2026_t2_a4_answer
#print axioms IChO2026T2A4.icho_2026_t2_a4_phase_direction_checks
#print axioms IChO2026T2A4.icho_2026_t2_a4_unique_direction
#print axioms IChO2026T2A4.icho_2026_t2_a4_supports_choice
#print axioms IChO2026T2A4.counterclockwise_traversal
