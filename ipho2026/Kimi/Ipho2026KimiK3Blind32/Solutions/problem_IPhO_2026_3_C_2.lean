import Mathlib

/-!
# IPhO 2026, Problem 3 (T3), Part C.2 — Carnot refrigerator of the Pm-T

Answer-blind formalization of subquestion T3-C2 (1.5 pts):

> The paramagnetic torus (Pm-T) executes the Carnot refrigeration cycle
> `1 → 2 → 3 → 4 → 1` shown in Figure 3b in the `H`-versus-`T` plane
> (`H` vertical, `T` horizontal).  `M₁, M₂, M₃, M₄` are the magnitudes of
> the magnetization `M` at the four labelled vertices.  The equation of
> state is `T * M * V = n * K * H` and the isothermal heat relation of
> part B may be reused.  **Write `M₁` in terms of `M₂, M₃, and M₄`.**

## Figure 3b geometry (read from the official page `T3_page-3.png`)

Vertex `1` is top-right, `4` bottom-right, `2` top-left, `3` bottom-left.
The legs `2 → 3` (left) and `4 → 1` (right) are drawn **vertical** — with
the `T` axis horizontal they are constant-`T` legs, i.e. the isothermal
heat legs; the legs `1 → 2` (upper) and `3 → 4` (lower) are drawn
**slanted**, connecting the two temperature levels — they are the
adiabatic connectors.  Accordingly the reservoir marking is

* `T₁ = T₄ = T_h` (vertices on the right, hot vertical), and
* `T₂ = T₃ = T_c` (vertices on the left, cold vertical),

so the hot isothermal leg is `4 → 1` (heat `Q_h` is rejected to the hot
reservoir there) and the cold isothermal leg is `2 → 3` (heat `Q_c` is
absorbed from the cold reservoir there).  Along each isothermal leg the
field varies with the traversal: `H₃ < H₂` on the cold leg `2 → 3`
(demagnetization, heat absorbed) and `H₄ < H₁` on the hot leg `4 → 1`
(the field rises from vertex `4` to vertex `1`, heat rejected).  Vertex
`3` (bottom left) sits at a nonzero lowest field (`0 < H₃`).  As drawn,
vertex `1` is the overall highest point and vertex `3` the lowest, and
the cold isotherm's upper endpoint `2` overtakes the hot isotherm's
lower endpoint `4` (`H₄ < H₂`), giving the full figure order
`0 < H₃ < H₄ < H₂ < H₁`; the contract keeps only the leg-orientation
inequalities that fix the refrigeration heat signs (`H₃ < H₂`,
`H₄ < H₁`) and the nonzero low-field endpoint (`0 < H₃`) — the
cross-isotherm comparisons are figure fidelity recorded here in the
documentation only.

This matches the reviewed sibling contracts of T3-C1
(`problem_IPhO_2026_3_C_1.lean`, same figure: vertical legs
`2 → 3, 4 → 1` isothermal, slanted legs adiabatic, `T₁=T₄=T_h`,
`T₂=T₃=T_c`) and T3-C3 (`problem_IPhO_2026_3_C_3.lean`: explicit
leg/heat assignment with the statement's numeric vertex fields
`H₃ = 204618 < H₄ = 240446 < H₂ = 311306 < H₁ = 411624`).

## Governing laws recorded

* Equation of state of the paramagnetic salt: `T * M * V = n * K * H`,
  at every vertex of the cycle (`EquationOfState`).
* Isothermal heat relation (part B.1, natural-language prerequisite,
  statement T3-B1): at fixed temperature `T`, when the field magnitude
  changes quasi-statically from `H_i` to `H_f`, the heat transferred
  **into** the torus is
  `Q = - μ₀ * V * n * K * (H_f² - H_i²) / (2 * T)`
  (first law with `dW_on = μ₀ V H dM` and the equation of state,
  `ΔU = 0` at fixed `T`; corroborated by the reviewed T3-B1 contract,
  where `IsHeatTransferred` sets the heat into the torus equal to the
  negative of the accumulated magnetic work).  Recorded as the
  deterministic law `isothermalHeatIntoTorus`; the sign convention
  `Q > 0` = heat into the Pm-T is kept verbatim from the reviewed
  contracts of T3-B1 and T3-C3.
* Reversible adiabatic legs `1 → 2` and `3 → 4`: no heat is exchanged.
* Carnot heat ratio for the reversible refrigeration cycle:
  `Q_h * T_c = Q_c * T_h` on the strictly positive heat magnitudes,
  with `Q_h` delivered **to** the hot reservoir and `Q_c` absorbed
  **from** the cold reservoir (`CarnotRatio`).

## Sign conventions for the heat magnitudes (refrigerator orientation)

* On the hot isothermal leg `4 → 1` the field *increases*
  (`H₄ < H₁`, magnetization at `T_h`): the torus expels heat to the hot
  reservoir, `isothermalHeatIntoTorus p T_h H₄ H₁ < 0`, so the magnitude
  rejected is `Q_h = - isothermalHeatIntoTorus p T_h H₄ H₁ > 0`.
* On the cold isothermal leg `2 → 3` the field *decreases*
  (`H₃ < H₂`, demagnetization at `T_c`): the torus absorbs heat from the
  cold reservoir, `isothermalHeatIntoTorus p T_c H₂ H₃ > 0`, so the
  magnitude absorbed is `Q_c = isothermalHeatIntoTorus p T_c H₂ H₃ > 0`.

## Permitted derivation route (iter-013 tenet)

Only the part-B.1 isothermal heat relation, the Carnot heat ratio and
the equation of state are permitted prerequisites for the constraint —
no part-B.2 result may be used.  From them:

* hot leg `4 → 1`:  `μ₀ V n K * (H₁² - H₄²) = 2 * T_h * Q_h`,
* cold leg `2 → 3`: `μ₀ V n K * (H₂² - H₃²) = 2 * T_c * Q_c`;
* Carnot `Q_h * T_c = Q_c * T_h` then forces
  `T_c² * (H₁² - H₄²) = T_h² * (H₂² - H₃²)`;
* the equation of state `H = V * T * M / (n * K)` with the isothermal
  pairings `T₁ = T₄ = T_h`, `T₂ = T₃ = T_c` collapses this to

  `M₁² + M₃² = M₂² + M₄²`

  — the answer-free square constraint carried by
  `vertex_magnetization_square_relation` and placed (with the candidate
  `m` in vertex 1's role) as the constraint conjunct of
  `VertexMagnetizationSolution`.  The requested closed form of `M₁`
  follows by taking the positive square root, using the cold-leg
  ordering `H₃ < H₂` (hence `M₃ < M₂` by the equation of state) for
  the strict positivity of `M₂² + M₄² - M₃²`; it appears in no
  signature, hypothesis, structure field, or local definition.

## Iter-013 redraft note (two repairs, history)

1. **Cycle-geometry repair** (fixed at iter-012, kept): the vertical
   legs `2 → 3`, `4 → 1` are the isothermal heat legs at `T_c`, `T_h`;
   the slanted legs `1 → 2`, `3 → 4` are the adiabats.  Reservoirs and
   heat magnitudes attach to the vertical legs.
2. **Rigid-witness repair** (iter-013 plan, kept): the solution
   predicate takes the realization witness `vs` as an external parameter
   and the main theorem quantifies over every realized cycle
   `∀ vs, IsCarnotRefrigerationCycle p R vs → ∃! m₁, …`; no existential
   over cycles hides inside the predicate whose uniqueness is asserted.
3. **Carrier repair** (iter-013 tenet): the previous constraint conjunct
   `m₁ * M₃ = M₂ * M₄` (the product relation the earlier
   inverted-geometry contract derived) is replaced by the square
   constraint the permitted B.1+Carnot+EOS derivation actually yields;
   the old product relation survives nowhere in this file.
-/

namespace IPhO_2026_3_C_2

/-- The four vertices of the cycle `1 → 2 → 3 → 4 → 1` of Figure 3b. -/
inductive Vertex : Type
  | v1 | v2 | v3 | v4
  deriving DecidableEq

/-- A thermodynamic state of the Pm-T at one vertex: magnetization
magnitude `M` (A/m), applied field magnitude `H` (A/m) and absolute
temperature `T` (K).  The torus volume `V` and the constants `μ₀, n, K`
are shared cycle parameters. -/
structure State where
  /-- Magnetization magnitude at the vertex. -/
  M : ℝ
  /-- Applied field magnitude at the vertex. -/
  H : ℝ
  /-- Absolute temperature at the vertex. -/
  T : ℝ

/-- Physical parameters of the Pm-T Carnot refrigerator: permeability of
free space `μ₀` (N/A²), amount of magnetic substance `n` (mol), torus
volume `V` (m³) and the material constant `K` (K·m³/mol) of the equation
of state.  All are genuinely positive — the physical regime of any
realized Pm-T. -/
structure Params where
  /-- Permeability of free space. -/
  μ₀ : ℝ
  /-- Amount of magnetic substance in the salt. -/
  n : ℝ
  /-- Volume of the torus. -/
  V : ℝ
  /-- Material constant of the salt (Curie-type). -/
  K : ℝ
  μ₀_pos : 0 < μ₀
  n_pos : 0 < n
  V_pos : 0 < V
  K_pos : 0 < K

/-- The reservoir temperatures `T_h > T_c > 0`, both strictly positive
(absolute temperatures). -/
structure Reservoirs where
  Th : ℝ
  Tc : ℝ
  hpos : 0 < Tc
  hlt : Tc < Th

/-- The hot reservoir temperature is positive. -/
theorem Reservoirs.Th_pos (R : Reservoirs) : 0 < R.Th :=
  lt_trans R.hpos R.hlt

/-- The thermodynamic state of the Pm-T at each vertex, together with the
two reservoir-temperature coincidences read from Figure 3b.

The legs drawn **vertical** in the `H`–`T` diagram (`2 → 3` on the left,
`4 → 1` on the right) are at constant `T` — they are the isothermal heat
legs — so the paired vertices share their temperatures: `T₂ = T₃ = T_c`
and `T₄ = T₁ = T_h`.  The slanted legs `1 → 2` and `3 → 4` are adiabatic
connectors that genuinely change the temperature (`T_h > T_c`).  All
states lie in the physical regime of positive absolute temperature and
nonnegative magnetization and field magnitudes. -/
structure VertexStates (R : Reservoirs) where
  states : Vertex → State
  /-- The cold (left) vertical leg is the cold isotherm: vertices `2`
  and `3` share their temperature (with `T_cold` below, `= T_c`). -/
  T_cold_pair : (states Vertex.v2).T = (states Vertex.v3).T
  /-- The hot (right) vertical leg is the hot isotherm: vertices `4`
  and `1` share their temperature (with `T_hot` below, `= T_h`). -/
  T_hot_pair : (states Vertex.v4).T = (states Vertex.v1).T
  /-- Physical regime: positive absolute temperatures at all vertices. -/
  T_pos : ∀ i, 0 < (states i).T
  /-- Magnetizations are magnitudes. -/
  M_nonneg : ∀ i, 0 ≤ (states i).M
  /-- Field strengths are magnitudes. -/
  H_nonneg : ∀ i, 0 ≤ (states i).H

/-- The equation of state of the paramagnetic salt,
`T * M * V = n * K * H`, valid at every vertex of the cycle. -/
def EquationOfState (p : Params) (st : Vertex → State) : Prop :=
  ∀ i, (st i).T * (st i).M * p.V = p.n * p.K * (st i).H

/-- Heat (J) transferred **into** the paramagnetic torus during a
quasi-static isothermal process at temperature `T` (K) in which the
applied field magnitude changes from `H_i` to `H_f` (A/m): the
isothermal heat relation of part B.1,

`Q = - μ₀ * V * n * K * (H_f² - H_i²) / (2 * T)`,

obtained in part B from the first law with the magnetic work
`dW_on = μ₀ V H dM` and the equation of state (`ΔU = 0` at fixed `T`).
Taken here as a governing law (natural-language prerequisite); the sign
convention is that of the problem — positive heat flows into the Pm-T,
so isothermal *magnetization* (`H_f > H_i`) expels heat and isothermal
*demagnetization* (`H_f < H_i`) absorbs it.  This sign and factorization
is kept verbatim from the reviewed T3-C3 contract and agrees with the
reviewed T3-B1 contract (heat into the torus equals the negative of the
accumulated magnetic work). -/
noncomputable def isothermalHeatIntoTorus
    (p : Params) (T H_i H_f : ℝ) : ℝ :=
  -p.μ₀ * p.V * p.n * p.K * (H_f ^ 2 - H_i ^ 2) / (2 * T)

/-- The heat magnitudes `Q_h`, `Q_c` of the cycle are the absolute
values delivered by the part-B.1 isothermal heat relation on the two
isothermal legs, with the signs fixed by the traversal direction of the
refrigeration cycle `1 → 2 → 3 → 4 → 1`:

* on the hot isothermal leg `4 → 1` the field increases (`H₄ < H₁`,
  magnetization at `T_h`), so heat is rejected to the hot reservoir and
  `Q_h = - isothermalHeatIntoTorus p T_h H₄ H₁` (strictly positive);
* on the cold isothermal leg `2 → 3` the field decreases (`H₃ < H₂`,
  demagnetization at `T_c`), so heat is absorbed from the cold reservoir
  and `Q_c = isothermalHeatIntoTorus p T_c H₂ H₃` (strictly positive). -/
def HeatMagnitudesFromPartB (p : Params) (st : Vertex → State)
    (Qh Qc : ℝ) : Prop :=
  Qh = - isothermalHeatIntoTorus p (st Vertex.v1).T
        (st Vertex.v4).H (st Vertex.v1).H ∧
  Qc = isothermalHeatIntoTorus p (st Vertex.v3).T
        (st Vertex.v2).H (st Vertex.v3).H

/-- Carnot heat ratio for the reversible refrigeration cycle:
`Q_h * T_c = Q_c * T_h`, i.e. `Q_h / Q_c = T_h / T_c` on the strictly
positive heat magnitudes. -/
def CarnotRatio (R : Reservoirs) (Qh Qc : ℝ) : Prop :=
  Qh * R.Tc = Qc * R.Th

/-- The slanted legs `1 → 2` and `3 → 4` of Figure 3b are the adiabatic
connectors: no heat is exchanged on them, so the heat transferred on
each isothermal leg is the *whole* heat exchanged with the corresponding
reservoir — this is what makes `Q_h`, `Q_c` (defined as the absolute
values of the heat transferred to the hot and from the cold reservoir)
coincide with the part-B.1 leg heats recorded in
`HeatMagnitudesFromPartB`.  The slanted legs connect the hot temperature
level `T_h` to the cold one `T_c`, with `T_c < T_h`, so neither is
itself isothermal. -/
def AdiabaticConnectors (R : Reservoirs) (st : Vertex → State) : Prop :=
  (st Vertex.v1).T = R.Th ∧ (st Vertex.v2).T = R.Tc ∧
  (st Vertex.v3).T = R.Tc ∧ (st Vertex.v4).T = R.Th

/-- **T3-C2, fully realized Carnot refrigeration cycle (answer-free).**

The Pm-T executes Figure 3b's Carnot refrigeration cycle: the equation
of state holds at all four vertices; the isothermal heat legs `2 → 3`
(cold) and `4 → 1` (hot) sit at the reservoir temperatures `T_c`, `T_h`
with the field orientations shown in the figure (`H₃ < H₂`, `H₄ < H₁`)
and a nonzero lowest field `0 < H₃`; the magnetizations are strict
magnitudes; the heat magnitudes `Q_h > 0`, `Q_c > 0` rejected on the hot
leg and absorbed on the cold leg are the absolute values of the part-B.1
isothermal heat relation, and they obey the Carnot heat ratio
`Q_h * T_c = Q_c * T_h`; the slanted legs `1 → 2`, `3 → 4` are the
adiabatic connectors joining the two temperature levels, so no heat is
exchanged on them.  No value of any vertex magnetization, and no
derived combination of them, is asserted — the witness structure is a
parameter of the theorems, so quantifications over it are genuine. -/
structure IsCarnotRefrigerationCycle (p : Params) (R : Reservoirs)
    (vs : VertexStates R) : Prop where
  /-- The salt obeys its equation of state at every vertex. -/
  eos : EquationOfState p vs.states
  /-- Vertex 1 (top right of Figure 3b) sits at the hot temperature. -/
  T_hot : (vs.states Vertex.v1).T = R.Th
  /-- Vertex 3 (bottom left) sits at the cold temperature. -/
  T_cold : (vs.states Vertex.v3).T = R.Tc
  /-- Vertex 3 sits at the nonzero field shown in Figure 3b. -/
  H3_pos : 0 < (vs.states Vertex.v3).H
  /-- Vertex 3 lies below vertex 2 on the cold (left) isotherm. -/
  H3_lt_H2 : (vs.states Vertex.v3).H < (vs.states Vertex.v2).H
  /-- Vertex 4 lies below vertex 1 on the hot (right) isotherm. -/
  H4_lt_H1 : (vs.states Vertex.v4).H < (vs.states Vertex.v1).H
  /-- Magnetizations are genuine (strictly positive) magnitudes. -/
  M_pos : ∀ i, 0 < (vs.states i).M
  /-- The slanted legs `1 → 2` and `3 → 4` are the adiabatic connectors
  joining the hot and cold temperature levels (no heat exchanged on
  them): the connector endpoints sit exactly at the reservoir
  temperatures `T_h`, `T_c`. -/
  adiabatic_connectors : AdiabaticConnectors R vs.states
  /-- The heat ledger: strictly positive heat magnitude `Q_h` rejected
  on the hot isothermal leg `4 → 1` and strictly positive `Q_c` absorbed
  on the cold isothermal leg `2 → 3`, both delivered by the part-B.1
  isothermal heat relation, satisfying the Carnot heat ratio.  The
  strictly positive marginals pin `Q_h`, `Q_c` to the leg heats — the
  ledger is non-vacuous. -/
  heat_ledger :
    ∃ (Qh Qc : ℝ),
      0 < Qh ∧ 0 < Qc ∧
      HeatMagnitudesFromPartB p vs.states Qh Qc ∧
      CarnotRatio R Qh Qc

/-- **T3-C2, solution predicate (answer-free, rigid witness).**  `m₁` is
a magnetization magnitude at vertex 1 of the Pm-T Carnot refrigeration
cycle `1 → 2 → 3 → 4 → 1` of Figure 3b **for the fixed realization
`vs`** provided that `m₁` is a genuine (strictly positive) magnitude and
obeys the vertex-magnetization square constraint in vertex 1's role: the
part-B.1 isothermal heat relation on the two heat legs, the Carnot heat
ratio and the equation of state force `m₁² + M₃² = M₂² + M₄²`.

Nothing in this predicate asserts the requested closed form of `m₁` in
terms of `M₂, M₃, M₄`; the constraint is the governing-equation
characterization from which that closed form is obtained in the main
theorem (by the unique positive square root, legitimate since the
cold-leg ordering gives `M₃ < M₂` and hence `M₂² + M₄² - M₃² > 0`).
The realization witness `vs` is an external parameter — rigid-witness
discipline: no existential over cycle realizations hides inside the
predicate whose uniqueness is asserted. -/
def VertexMagnetizationSolution (p : Params) (R : Reservoirs)
    (vs : VertexStates R) (m₁ : ℝ) : Prop :=
  IsCarnotRefrigerationCycle p R vs ∧ 0 < m₁ ∧
    m₁ ^ 2 + (vs.states Vertex.v3).M ^ 2 =
      (vs.states Vertex.v2).M ^ 2 + (vs.states Vertex.v4).M ^ 2

/-- **Vertex-magnetization square constraint (the physical content of
T3-C2).**  For any fully realized Carnot refrigeration cycle of the
Pm-T, the vertex magnetizations satisfy `M₁² + M₃² = M₂² + M₄²`.  This
is the answer-free constraint equation from which the requested
expression of `M₁` in terms of `M₂, M₃, M₄` is read off by the positive
square root; it follows from the part-B.1 isothermal heat relation on
the two heat legs combined with the Carnot heat ratio and the equation
of state alone (no part-B.2 input). -/
theorem vertex_magnetization_square_relation (p : Params) (R : Reservoirs)
    (vs : VertexStates R) (h : IsCarnotRefrigerationCycle p R vs) :
    (vs.states Vertex.v1).M ^ 2 + (vs.states Vertex.v3).M ^ 2 =
    (vs.states Vertex.v2).M ^ 2 + (vs.states Vertex.v4).M ^ 2 := by
  obtain ⟨Qh, Qc, hQh, hQc, ⟨hQh_def, hQc_def⟩, hcar⟩ := h.heat_ledger
  -- The reservoir-temperature identifications at the four vertices.
  have hT₁ : (vs.states Vertex.v1).T = R.Th := h.adiabatic_connectors.1
  have hT₂ : (vs.states Vertex.v2).T = R.Tc := h.adiabatic_connectors.2.1
  have hT₃ : (vs.states Vertex.v3).T = R.Tc := h.adiabatic_connectors.2.2.1
  have hT₄ : (vs.states Vertex.v4).T = R.Th := h.adiabatic_connectors.2.2.2
  have hTh : 0 < R.Th := R.Th_pos
  have hTc : 0 < R.Tc := R.hpos
  have hT₁' : (vs.states Vertex.v1).T ≠ 0 := ne_of_gt (vs.T_pos Vertex.v1)
  have hT₃' : (vs.states Vertex.v3).T ≠ 0 := ne_of_gt (vs.T_pos Vertex.v3)
  have hnk : p.n * p.K ≠ 0 := ne_of_gt (mul_pos p.n_pos p.K_pos)
  -- The leg relations from the part-B.1 isothermal heat formula.
  have hlegA : 2 * (vs.states Vertex.v1).T * Qh =
      p.μ₀ * p.V * p.n * p.K *
        ((vs.states Vertex.v1).H ^ 2 - (vs.states Vertex.v4).H ^ 2) := by
    rw [hQh_def]; unfold isothermalHeatIntoTorus
    field_simp
  have hlegB : 2 * (vs.states Vertex.v3).T * Qc =
      p.μ₀ * p.V * p.n * p.K *
        ((vs.states Vertex.v2).H ^ 2 - (vs.states Vertex.v3).H ^ 2) := by
    rw [hQc_def]; unfold isothermalHeatIntoTorus
    field_simp; ring
  -- Uniform strict positivity of all vertex fields from EOS + `M > 0`.
  have hHg : ∀ i, 0 < (vs.states i).H := by
    intro i
    have hi := h.eos i
    have hTi : 0 < (vs.states i).T := vs.T_pos i
    have hMi : 0 < (vs.states i).M := h.M_pos i
    have hpos : 0 < p.n * p.K * (vs.states i).H := by
      have hrw : p.n * p.K * (vs.states i).H =
          (vs.states i).T * (vs.states i).M * p.V := by linarith [hi]
      rw [hrw]; exact mul_pos (mul_pos hTi hMi) p.V_pos
    nlinarith [hpos, mul_pos p.n_pos p.K_pos]
  -- The scaled Carnot collapse: cancel `μ₀VnK > 0` to get the divergence eq.
  -- The Carnot constraint from the B.1 legs: substituting
  -- `Q_h = μ₀VnK (H₁²-H₄²)/(2 T_h)`, `Q_c = μ₀VnK (H₂²-H₃²)/(2 T_c)`
  -- into `Q_h T_c = Q_c T_h` yields `(H₁²-H₄²) T_c² = (H₂²-H₃²) T_h²`.
  have hdiv :
      ((vs.states Vertex.v1).H ^ 2 - (vs.states Vertex.v4).H ^ 2) *
        (vs.states Vertex.v3).T ^ 2 =
      ((vs.states Vertex.v2).H ^ 2 - (vs.states Vertex.v3).H ^ 2) *
        (vs.states Vertex.v1).T ^ 2 := by
    have hcpos : (0:ℝ) < p.μ₀ * p.V * p.n * p.K :=
      mul_pos (mul_pos (mul_pos p.μ₀_pos p.V_pos) p.n_pos) p.K_pos
    have hTh' : R.Th ≠ 0 := ne_of_gt hTh
    have hTc' : R.Tc ≠ 0 := ne_of_gt hTc
    have eQh : Qh = p.μ₀ * p.V * p.n * p.K *
        ((vs.states Vertex.v1).H ^ 2 - (vs.states Vertex.v4).H ^ 2) /
        (2 * (vs.states Vertex.v1).T) := by
      field_simp; linear_combination hlegA
    have eQc : Qc = p.μ₀ * p.V * p.n * p.K *
        ((vs.states Vertex.v2).H ^ 2 - (vs.states Vertex.v3).H ^ 2) /
        (2 * (vs.states Vertex.v3).T) := by
      field_simp; linear_combination hlegB
    unfold CarnotRatio at hcar
    rw [eQh, eQc, ← hT₁, ← hT₃] at hcar
    field_simp at hcar
    have hscaled : p.μ₀ * p.V * p.n * p.K *
          (((vs.states Vertex.v1).H ^ 2 - (vs.states Vertex.v4).H ^ 2) *
            (vs.states Vertex.v3).T ^ 2) =
        p.μ₀ * p.V * p.n * p.K *
          (((vs.states Vertex.v2).H ^ 2 - (vs.states Vertex.v3).H ^ 2) *
            (vs.states Vertex.v1).T ^ 2) := by
      ring_nf at hcar ⊢
      linarith [hcar]
    exact mul_left_cancel₀ hcpos.ne' hscaled
  -- EOS-expressed fields: `Hᵢ = Tᵢ Mᵢ V / (nK)` at each vertex.
  have hHe : ∀ i, (vs.states i).H =
      (vs.states i).T * (vs.states i).M * p.V / (p.n * p.K) := by
    intro i
    have hi := h.eos i
    have hcomm : p.n * p.K * (vs.states i).H = (vs.states i).H * (p.n * p.K) :=
      mul_comm _ _
    rw [eq_div_iff hnk, ← hcomm]
    exact hi.symm
  rw [hHe Vertex.v1, hHe Vertex.v2, hHe Vertex.v3, hHe Vertex.v4] at hdiv
  -- Collapse the temperature pairs: `T₂ = T₃ = T_c` and `T₄ = T₁ = T_h`.
  have hT₂' : (vs.states Vertex.v2).T = (vs.states Vertex.v3).T := by
    rw [hT₂, hT₃]
  have hT₄' : (vs.states Vertex.v4).T = (vs.states Vertex.v1).T := by
    rw [hT₄, hT₁]
  rw [hT₂', hT₄'] at hdiv
  -- Clear the `(nK)²` denominators by scaling `hdiv` by `(nK)²` and
  -- distributing; `field_simp` then discharges every division proof
  -- obligation since `n K ≠ 0`.  The resulting polynomial identity is
  -- exactly `(M₁² - M₄²) - (M₂² - M₃²) = 0` up to the common
  -- (now-cancelled) scale `T_h² T_c² V²` inside `hd2`.
  have hd2 := congrArg (fun x => x * (p.n * p.K) ^ 2) hdiv
  rw [sub_mul, sub_mul] at hd2
  field_simp at hd2
  -- Clear the one remaining `/ (p.n * p.K)` by scaling by `(p.n * p.K)`.
  have hn : p.n ≠ 0 := ne_of_gt p.n_pos
  have hK : p.K ≠ 0 := ne_of_gt p.K_pos
  have hd3 := congrArg (fun x => x * (p.n * p.K)) hd2
  field_simp at hd3
  -- `hd3 : V² (m₁² − m₄²) = V² (m₂² − m₃²)`; cancel the positive `V²`
  -- and read off the magnetization-square relation.
  have hV2 : p.V ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt p.V_pos)
  have hdiff : (vs.states Vertex.v1).M ^ 2 - (vs.states Vertex.v4).M ^ 2 =
      (vs.states Vertex.v2).M ^ 2 - (vs.states Vertex.v3).M ^ 2 :=
    mul_left_cancel₀ hV2 hd3
  linarith [hdiff]

/-- **T3-C2, main theorem: the vertex-1 magnetization is characterized.**
For **every** fully realized Carnot refrigeration cycle `vs` of the
Pm-T (equation of state `T * M * V = n * K * H`, isothermal legs of
Figure 3b at the reservoir temperatures with the part-B heat magnitudes,
adiabatic connectors, Carnot heat ratio, positive regime), there exists
a unique value `m₁` of the magnetization magnitude at vertex 1
consistent with that cycle.  Existence is realized by the strictly
positive square root of `M₂² + M₄² - M₃²` — legitimate because the
cold-leg ordering and the equation of state give `M₃ < M₂` — and
uniqueness follows from the strict positivity of `m₁`; the closed form
of this witness, in terms of `M₂, M₃, M₄`, is the requested answer and
is intentionally absent from this statement. -/
theorem vertex1_magnetization_exists_unique (p : Params) (R : Reservoirs) :
    ∀ vs : VertexStates R, IsCarnotRefrigerationCycle p R vs →
      ∃! m₁, VertexMagnetizationSolution p R vs m₁ := by
  intro vs h
  have hrel : (vs.states Vertex.v1).M ^ 2 + (vs.states Vertex.v3).M ^ 2 =
      (vs.states Vertex.v2).M ^ 2 + (vs.states Vertex.v4).M ^ 2 :=
    vertex_magnetization_square_relation p R vs h
  -- `M₃ < M₂`: the cold leg has `H₃ < H₂` at the common temperature,
  -- and the equation of state `M = n K H / (T V)` is strictly monotone
  -- in `H` with the positive factor `nK/(Tc·V)`.
  have hM3M2 : (vs.states Vertex.v3).M < (vs.states Vertex.v2).M := by
    have hT₃ : (vs.states Vertex.v3).T = R.Tc := h.adiabatic_connectors.2.2.1
    have hT₂ : (vs.states Vertex.v2).T = R.Tc := h.adiabatic_connectors.2.1
    have h3 := h.eos Vertex.v3
    have h2 := h.eos Vertex.v2
    have hTV : (0:ℝ) < (vs.states Vertex.v3).T * p.V :=
      mul_pos (vs.T_pos Vertex.v3) p.V_pos
    have hTV' : (vs.states Vertex.v3).T * p.V ≠ 0 := ne_of_gt hTV
    have e3 : (vs.states Vertex.v3).M =
        p.n * p.K * (vs.states Vertex.v3).H / ((vs.states Vertex.v3).T * p.V) := by
      rw [eq_div_iff hTV']
      linear_combination h3
    have e2 : (vs.states Vertex.v2).M =
        p.n * p.K * (vs.states Vertex.v2).H / ((vs.states Vertex.v3).T * p.V) := by
      have h2a : (vs.states Vertex.v2).T * (vs.states Vertex.v2).M * p.V =
          p.n * p.K * (vs.states Vertex.v2).H := h2
      rw [eq_div_iff hTV']
      rw [hT₂, ← hT₃] at h2a
      linear_combination h2a
    rw [e3, e2]
    exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left h.H3_lt_H2 (mul_pos p.n_pos p.K_pos)) hTV
  have hSpos : 0 < (vs.states Vertex.v2).M ^ 2 + (vs.states Vertex.v4).M ^ 2 -
      (vs.states Vertex.v3).M ^ 2 := by
    have h3nn : 0 ≤ (vs.states Vertex.v3).M := vs.M_nonneg Vertex.v3
    have h2pos : 0 < (vs.states Vertex.v2).M := h.M_pos Vertex.v2
    have hsq : (vs.states Vertex.v3).M ^ 2 < (vs.states Vertex.v2).M ^ 2 :=
      sq_lt_sq' (by linarith [h3nn, h2pos]) hM3M2
    have h4sq : 0 ≤ (vs.states Vertex.v4).M ^ 2 := sq_nonneg _
    nlinarith [hsq, h4sq]
  -- Existence: `m₁ = √(M₂² + M₄² - M₃²)` is positive and satisfies the
  -- constraint since `m₁² = M₂² + M₄² - M₃²` squares back by `Real.sq_sqrt`.
  refine ⟨Real.sqrt ((vs.states Vertex.v2).M ^ 2 + (vs.states Vertex.v4).M ^ 2 -
    (vs.states Vertex.v3).M ^ 2),
    ⟨h, Real.sqrt_pos_of_pos hSpos, ?_⟩, ?_⟩
  · rw [Real.sq_sqrt (le_of_lt hSpos)]; linarith [hrel]
  · -- Uniqueness: any positive `m₁` satisfying the constraint equals the
    -- positive square root, since `x² = y²` with `x, y > 0` forces `x = y`.
    intro m₁ hm₁
    obtain ⟨_, hm₁pos, hm₁eq⟩ := hm₁
    have hsq_eq : m₁ ^ 2 =
        (Real.sqrt ((vs.states Vertex.v2).M ^ 2 + (vs.states Vertex.v4).M ^ 2 -
          (vs.states Vertex.v3).M ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt hSpos)]; linarith [hm₁eq]
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq) with h | h
    · exact h
    · have hsqrtpos := Real.sqrt_pos_of_pos hSpos
      exfalso; nlinarith [hm₁pos, hsqrtpos]

end IPhO_2026_3_C_2
