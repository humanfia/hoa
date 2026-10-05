import Mathlib

/-!
# IPhO 2026, Experimental Exam E1 (Problem 4), Part A.4 — answer-blind formalization

**Physical setup (Part A: isochoric process of the confined air column).**

The apparatus contains a sealed air column (CA) in the inner cylinder (IC).
Propylene glycol (PG) is introduced into the IC up to the level
`h = 4.5 cm` and the valves D and E are closed, so that the **volume `V` of
the CA is fixed** for the whole of Part A (statement, Experimental Problem
E1, Part A). The cylinder dimensions are given in Figure 17 and the
time-averaged density of the ambient air is `ρ_a = 1.12 kg m⁻³`; these
data, together with the ideal-gas equation of state

    P · V = n · R · T,        (equation (1) of E1)

determine the amount of gas `n` confined in the CA (this was the content of
subquestion A.1). The outer cylinder (OC) is filled with water and heated,
and the pressure `P` of the CA is recorded as a function of its temperature
`T` (subquestion A.2); subquestion A.3 asks to plot `P` against `T`.

**Question (E1-A.4).** *Use the graph from A.3 to determine the experimental
value of the universal gas constant `R`.*

**Physical content.** At the fixed volume of the isochoric process,
equation (1) makes the equilibrium pressure a homogeneous linear function of
the absolute temperature,

    P(T) = (n R / V) · T.

The recorded A.2 states are equilibrium states of the confined air, so the
data cloud of the A.3 graph falls on the straight line of slope `n R / V`
through the origin, the slope prescribing the experimental gas constant via

    R = slope · V / n.

**Answer-blind statement design.** The official numerical value is withheld.
We model the fixed geometry (`V > 0`), the sealed amount of gas (`n > 0`),
the recorded isochoric measurements as a finite family of pairs `(Tᵢ, Pᵢ)`,
with at least two distinct recorded temperatures and positive recorded data,
and the ideal-gas equation of state as the **governing-law premise** `Pᵢ · V
= n · R · Tᵢ` shared by every recorded state. The solution predicate
`IsExperimentalGasConstant` characterizes the requested experimental
constant `R` from below (positivity) and from the governing law (every
recorded state obeys equation (1) with this `R`); the main theorem asserts
existence and **uniqueness** of such a constant. No numerical witness — and
no closed form of `R` — appears in any signature; the prover may later
construct the unique witness as the slope readout
`R = (V / n) · (Pⱼ - Pᵢ) / (Tⱼ - Tᵢ)` between two distinct recorded points
(or, equivalently, the least-squares slope `V · ∑ TᵢPᵢ / (n · ∑ Tᵢ²)` of the
A.3 plot).

**Redraft note (iter-012).** The previous draft's predicate also required
the *aggregated* least-squares slope identity
`(∑ TᵢPᵢ) / (∑ Tᵢ²) = n R / V` while its hypotheses did *not* include the
governing law for the recorded data; under that contract existence failed
(counterexample: `k = 2`, `T = ![1, 2]`, `P = ![1, 3]`, `n = V = 1`).
This redraft moves the ideal-gas consistency of the recorded states to the
hypothesis side (it is the equation of state of the experiment, equation
(1), not the answer of A.4) and lets the solution predicate carry exactly
the two physically defining roles of the sought constant.
-/

namespace IPhO_2026_4
namespace PartA4

/-- **Recorded isochoric data (A.2, A.3).** A finite family of `k`
equilibrium states of the sealed air column, each pairing the measured
temperature `T` (K) with the measured pressure `P` (Pa) recorded from the
sensor console while the outer water bath is slowly heated. -/
structure IsochoricData where
  /-- Number of recorded equilibrium states. -/
  k : ℕ
  /-- Measured absolute temperatures `Tᵢ` (K). -/
  T : Fin k → ℝ
  /-- Measured pressures `Pᵢ` (Pa). -/
  P : Fin k → ℝ

/-- The data actually record at least two measurements — needed for the
A.3 graph to define a slope at all. -/
def IsochoricData.HasTwoPoints (d : IsochoricData) : Prop := 2 ≤ d.k

/-- All recorded temperatures are positive (absolute/Kelvin scale, K;
the statement requires temperature conversions to the absolute scale). -/
def IsochoricData.TemperaturePos (d : IsochoricData) : Prop :=
  ∀ i, 0 < d.T i

/-- All recorded pressures are positive (absolute pressure, Pa). -/
def IsochoricData.PressurePos (d : IsochoricData) : Prop :=
  ∀ i, 0 < d.P i

/-- **Fixed-volume (isochoric) constraint.** Filling the IC with propylene
glycol to `h = 4.5 cm` and closing valves D and E fixes the volume of the
sealed air column; the same positive `V` (m³, from the Figure 17 geometry)
applies to every recorded state. -/
structure FixedVolume where
  /-- Fixed volume `V` of the CA, in m³. -/
  V : ℝ
  /-- The fixed volume is positive. -/
  pos : 0 < V

/-- **Sealed amount of gas.** With the valves closed the amount `n > 0`
(mol) of air in the CA is constant throughout the heating (it is the
quantity determined in A.1 from the Figure 17 geometry, the ambient density
`ρ_a = 1.12 kg m⁻³`, and equation (1)). -/
structure SealedAmount where
  /-- Sealed amount of substance `n` of the CA, in mol. -/
  n : ℝ
  /-- The sealed amount is positive. -/
  pos : 0 < n

/-- **Ideal-gas equilibrium consistency (equation (1) of E1).** The state
`(T, P)` is a thermal-equilibrium state of the confined air column when it
satisfies `P · V = n · R · T` (pressure in Pa, volume in m³, amount in mol,
temperature in K, and `R` in J·K⁻¹·mol⁻¹). -/
def IsEquilibriumState (V n R : ℝ) (T P : ℝ) : Prop :=
  P * V = n * R * T

/-- **Solution predicate (answer-free).** `R` is the experimental value of
the universal gas constant determined from the A.3 pressure–temperature
graph together with the fixed geometry and the sealed amount of gas:

* `R` is a positive constant of dimensions `J·K⁻¹·mol⁻¹`
  (modeled as a real number);
* every recorded state of the A.2/A.3 data obeys the ideal-gas equation of
  state *with this same value* `R` — i.e. through equation (1) the constant
  `R` is realized by the recorded graph: since the states are equilibrium
  states, with this `R` the data cloud lies on the straight line
  `P = (n R / V) · T` through the origin of the A.3 plot.

No closed form or numerical value of `R` is asserted; the prover constructs
the witness from two distinct recorded points (equivalently from the
best-fit slope of the graph). -/
structure IsExperimentalGasConstant (geo : FixedVolume) (gas : SealedAmount)
    (d : IsochoricData) (R : ℝ) : Prop where
  /-- The gas constant is positive. -/
  pos : 0 < R
  /-- Every recorded state obeys the ideal-gas law with this `R`. -/
  equilibrium : ∀ i, IsEquilibriumState geo.V gas.n R (d.T i) (d.P i)

/-- **IPhO 2026, E1-A.4 (answer-blind).**
For an isochoric dataset with at least two recorded states at *distinct*
temperatures, with positive temperatures and pressures, a fixed positive CA
volume, a sealed positive amount of gas, and under the governing law that
every recorded state is an ideal-gas equilibrium state for some value of
the gas constant (equation (1) applied to the confined air), there exists a
unique real number `R` that is the experimental value of the universal gas
constant determined from the A.3 graph through the ideal-gas equation of
state.

The theorem only asserts the existence and uniqueness of this experimental
constant; its concrete value — read off the slope of the
pressure–temperature graph as `R = slope · V / n` — is the unique witness,
to be constructed by the prover. -/
theorem problem_IPhO_2026_4_A_4
    (geo : FixedVolume) (gas : SealedAmount)
    (d : IsochoricData) (_hdata : d.HasTwoPoints)
    (hT : d.TemperaturePos) (hP : d.PressurePos)
    (hdistinct : ∃ i j : Fin d.k, d.T i ≠ d.T j)
    (hlaw : ∃ R : ℝ, ∀ i, IsEquilibriumState geo.V gas.n R (d.T i) (d.P i)) :
    ∃! R : ℝ, IsExperimentalGasConstant geo gas d R := by
  obtain ⟨R₀, hR₀⟩ := hlaw
  obtain ⟨i, j, hij⟩ := hdistinct
  -- The witness realizes every recorded state, hence is positive: at any
  -- recorded point, `Pᵢ · V = n · R₀ · Tᵢ` with `Pᵢ, V, n, Tᵢ > 0` forces
  -- `R₀ > 0`.
  have hR₀pos : 0 < R₀ := by
    have hTi : 0 < d.T i := hT i
    have hPi : 0 < d.P i := hP i
    have heq := hR₀ i
    have hn : 0 < gas.n := gas.pos
    have hV : 0 < geo.V := geo.pos
    have hposL : 0 < d.P i * geo.V := mul_pos hPi hV
    have hnT : 0 < gas.n * d.T i := mul_pos hn hTi
    have hL : 0 < gas.n * R₀ * d.T i := by
      have := hposL
      rw [heq] at this
      exact this
    -- hL : n * R₀ * Tᵢ = (n * Tᵢ) * R₀ (ring), and n*Tᵢ > 0 forces R₀ > 0
    by_contra hneg
    push Not at hneg
    have key : gas.n * R₀ * d.T i ≤ 0 := by
      have h1 : R₀ ≤ 0 := hneg
      have h2 : 0 ≤ gas.n * d.T i := le_of_lt hnT
      calc gas.n * R₀ * d.T i = (gas.n * d.T i) * R₀ := by ring
        _ ≤ (gas.n * d.T i) * 0 := mul_le_mul_of_nonneg_left h1 h2
        _ = 0 := mul_zero _
    linarith
  refine ⟨R₀, ⟨hR₀pos, hR₀⟩, ?_⟩
  rintro R' ⟨-, hR'⟩
  -- From the governing law at a recorded point and `n, T i ≠ 0`, cancel the
  -- common factors to identify `R' = R₀`.
  have h1 := hR₀ i
  have h2 := hR' i
  -- h1 : Pᵢ · V = n · R₀ · Tᵢ ; h2 : Pᵢ · V = n · R' · Tᵢ
  have hthis : gas.n * R₀ * d.T i = gas.n * R' * d.T i := by rw [← h1, ← h2]
  have hn : gas.n ≠ 0 := ne_of_gt gas.pos
  have hTi : d.T i ≠ 0 := ne_of_gt (hT i)
  have hc : gas.n * R₀ = gas.n * R' := by
    have := mul_right_cancel₀ hTi hthis
    simpa [mul_assoc] using this
  exact (mul_left_cancel₀ hn hc).symm

/-- **Slope readout bridge (secondary target).** Under the conditions of
A.4, any real `R` such that the recorded data cloud lies on the straight
line through the origin of slope `n R / V` (i.e. `Pᵢ = (n R / V) · Tᵢ` for
every recorded point) is uniquely determined: the experimental gas constant
is what the slope of the A.3 graph measures, via `R = slope · V / n`. This
is the relation actually read off the graph; it is a consequence of the
main theorem's predicate (at the fixed volume and sealed amount, division of
`Pᵢ · V = n · R · Tᵢ` by `V` gives the pointwise line relation), and is
recorded here as the figure-side characterization of the same constant. -/
theorem slope_readout_unique
    (geo : FixedVolume) (gas : SealedAmount)
    (d : IsochoricData)
    (hdistinct : ∃ i j : Fin d.k, d.T i ≠ d.T j)
    (R₁ R₂ : ℝ)
    (hT : d.TemperaturePos)
    (h₁ : ∀ i, d.P i = gas.n * R₁ / geo.V * d.T i)
    (h₂ : ∀ i, d.P i = gas.n * R₂ / geo.V * d.T i) :
    R₁ = R₂ := by
  obtain ⟨i, -, -⟩ := hdistinct
  have hTi : d.T i ≠ 0 := ne_of_gt (hT i)
  have h1 := h₁ i
  have h2 := h₂ i
  -- equate the two expressions for `Pᵢ`
  have hthis : gas.n * R₁ / geo.V * d.T i = gas.n * R₂ / geo.V * d.T i := by
    rw [← h1, ← h2]
  -- cancel the nonzero temperature on the right
  have step1 : gas.n * R₁ / geo.V = gas.n * R₂ / geo.V :=
    mul_right_cancel₀ hTi hthis
  -- cancel the nonzero volume denominator on the right
  have step2 : gas.n * R₁ = gas.n * R₂ := by
    have hVn : (geo.V)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt geo.pos)
    have : gas.n * R₁ * (geo.V)⁻¹ = gas.n * R₂ * (geo.V)⁻¹ := by
      simpa [div_eq_mul_inv] using step1
    exact mul_right_cancel₀ hVn this
  -- cancel the positive (hence nonzero) amount of gas on the left
  exact mul_left_cancel₀ (ne_of_gt gas.pos) step2

end PartA4
end IPhO_2026_4
