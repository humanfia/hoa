# IChO 2026, Problem T2 (Belousov–Zhabotinsky kinetics), part 2.4 (target icho_2026_t2_a4)

## Question (from `T2_page-3.png` / `theory_problem.pdf`, printed page Q2-3)

> **2.4** In which direction in the phase portrait of [HBrO₂] vs [Br⁻] will the
> concentrations of [HBrO₂] and [Br⁻] change over time? **Tick** the correct
> box. (2.0 pt)

The phase portrait sketched in the problem is a closed loop with:

- horizontal axis **[Br⁻]**, with marked values [Br⁻]critical < [Br⁻]max;
- vertical axis **[HBrO₂]**, with marked values [HBrO₂]B < [HBrO₂]A;
- a bottom horizontal edge at [HBrO₂] = [HBrO₂]B running between [Br⁻]critical and [Br⁻]max;
- a top horizontal edge at [HBrO₂] = [HBrO₂]A running between the same endpoints;
- a steep edge at [Br⁻] = [Br⁻]critical connecting [HBrO₂]B up to [HBrO₂]A;
- a steep edge at [Br⁻] = [Br⁻]max connecting [HBrO₂]A down to [HBrO₂]B.

The blank student answer sheet (A2-3, PDF page 21) offers four versions of this
loop, identical except for the directions of the four red arrowheads; the
student must tick the box under the correct one.

## Answer

**Counterclockwise.** The correct option is the diagram in which:

- along the **bottom edge** (at [HBrO₂] = [HBrO₂]B, Process B) the system moves
  **right → left**, i.e. [Br⁻] **decreases** from [Br⁻]max to [Br⁻]critical;
- on the **left edge** (at [Br⁻] = [Br⁻]critical) the system jumps **upward**,
  i.e. [HBrO₂] jumps from [HBrO₂]B to [HBrO₂]A and the system switches to Process A;
- along the **top edge** (at [HBrO₂] = [HBrO₂]A, Process A) the system moves
  **left → right**, i.e. [Br⁻] **increases** from [Br⁻]critical to [Br⁻]max;
- on the **right edge** (at [Br⁻] = [Br⁻]max) the system drops **downward**,
  i.e. [HBrO₂] falls from [HBrO₂]A to [HBrO₂]B and the system switches back to Process B.

On the answer sheet A2-3 this is the **bottom-left** of the four tick-box
diagrams (bottom-edge arrow pointing left, left-edge arrow pointing up,
top-edge arrow pointing right, right-edge arrow pointing down).

## Reasoning (from problem-stated material only)

1. **During Process B ([HBrO₂] = [HBrO₂]B):** elementary steps (4) and (5) of
   Process B consume Br⁻ (Br⁻ appears on the reactant side of both). Hence
   [Br⁻] falls while Process B runs — motion along the bottom edge from
   [Br⁻]max towards [Br⁻]critical (right → left). The problem itself states
   this verbatim in the text directly below item 2.4 (input to 2.5):
   *"the concentration of [Br⁻] slowly **decreases** from
   [Br⁻]max = 7.0 × 10⁻⁴ M to [Br⁻]critical, and then almost immediately
   reaches [Br⁻]max again."* This fixes the bottom-edge direction
   unambiguously.
2. **At [Br⁻]critical (B → A switch):** the problem states that the B → A
   switch occurs when the rate of step (1) exceeds that of step (4), which
   happens when [Br⁻] has fallen to [Br⁻]critical. Process A is autocatalytic
   in HBrO₂ (the net of steps (1)–(3) amplifies HBrO₂), so [HBrO₂] jumps
   almost immediately from [HBrO₂]B up to [HBrO₂]A at (nearly) constant
   [Br⁻] — upward motion on the left edge. This matches the printed phrase
   "almost immediately reaches [Br⁻]max again", whose quick legs are the
   vertical switch edges.
3. **During Process A ([HBrO₂] = [HBrO₂]A):** Process C occurs
   **continuously** (problem statement) and step (7),
   Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products, **produces** Br⁻. Since Process B
   "practically does not occur" while Process A runs, the bromide sink is
   switched off and [Br⁻] rises from [Br⁻]critical back towards [Br⁻]max at
   the Process-A steady-state level [HBrO₂]A — left → right motion along the
   top edge.
4. **At [Br⁻]max (A → B switch):** when [Br⁻] is large enough that
   rate(4) = k₄[H⁺][Br⁻][HBrO₂] exceeds rate(1) = k₁[H⁺][BrO₃⁻][HBrO₂], the
   problem states the system switches from Process A to Process B. The high
   Process-A level of HBrO₂ is then immediately quenched by step (4), so
   [HBrO₂] falls from [HBrO₂]A to [HBrO₂]B at (nearly) constant [Br⁻]max —
   downward motion on the right edge.

Steps 1–4 give a **counterclockwise** traversal (bottom ←, left ↑, top →,
right ↓). The geometry is consistent with part 2.3, where the switch criterion
rate(4) = rate(1) at [HBrO₂] = [HBrO₂]A gives
[Br⁻]critical = k₁[BrO₃⁻]/k₄ = 1.0×10⁴ × 0.06 / (2.0×10⁹) = 3×10⁻⁷ M, well
below the printed [Br⁻]max = 7.0 × 10⁻⁴ M — matching the portrait, in which
[Br⁻]critical lies strictly to the left of [Br⁻]max.

## Source grounding

- Question text and portrait: `T2_page-3.png` (= `theory_problem.pdf` page 17,
  printed page Q2-3).
- Mechanism, rate constants, alternation/continuity assumptions ("Processes A
  and B alternate… Process C occurs continuously", step (7) producing Br⁻,
  steps (4), (5) consuming Br⁻, the switch criterion rate(4) ≷ rate(1)):
  `theory_problem.pdf` pages 15–17 (Q2-1 to Q2-3) and `T2_page-2.png`.
- Tick-box options and their arrow directions: blank student answer sheet,
  `theory_problem.pdf` page 21 (A2-3), section "2.4 (2.0 pt)".
- The directional sentence "[Br⁻] slowly decreases from [Br⁻]max … to
  [Br⁻]critical, and then almost immediately reaches [Br⁻]max again" appears in
  the problem statement itself between items 2.4 and 2.5 on printed page Q2-3.

## Lean formalization

`IChO2026Problems/problem_icho_2026_t2_a4.lean` models the portrait as a
four-leg directed loop, encodes the problem-stated constraints on each edge
(Br⁻ decreases along Process B; HBrO₂ jumps up at the B→A switch; Br⁻
increases during Process A because the continuous Process C regenerates Br⁻;
HBrO₂ falls at the A→B switch), and proves:

- `IChO2026T2A4.icho_2026_t2_a4_answer` — the unique direction satisfying the
  problem-stated constraints is the counterclockwise one, and the clockwise
  option is excluded;
- `IChO2026T2A4.icho_2026_t2_a4_phase_direction_checks` — componentwise signs
  of the four edge directions (bottom leftward, left upward, top rightward,
  right downward);
- `IChO2026T2A4.icho_2026_t2_a4_unique_direction` — uniqueness of the
  compatible direction;
- `IChO2026T2A4.icho_2026_t2_a4_supports_choice` — an answer-sheet option is
  correct iff it satisfies the problem constraints (i.e. iff it is the
  counterclockwise / bottom-left diagram).

No `sorry`/`admit`, no custom axioms; `#print axioms` output is recorded in
`verification.md`.
