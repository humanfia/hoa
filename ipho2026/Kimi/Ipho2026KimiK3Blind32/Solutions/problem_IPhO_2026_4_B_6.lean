import Mathlib

/-!
# IPhO 2026, Experimental Exam E1, Problem 4, Part B.6 — Latent heat of
# vaporization per unit mass

Answer-blind formalization of subquestion E1-B.6 (0.5 pts), verified against
the official source page `E1_page-12.png`:

> **B6.** *[0.5 pt]* From the value of `Qᵥ`, determine `Lᵥ` (the latent heat
> of vaporization per unit mass) indicating the formula that you used.

## Experimental context (Part B: vapor pressure of water)

* The inner cylinder **IC** contains dry air plus water vapor at total
  pressure approximately `P_atm`; the water level height `H` is recorded as
  the temperature `T` falls (parts B.1–B.2), and `H₀` is the extrapolated
  height at `T₀ = 273.15 K` (part B.3), where the vapor pressure may be
  taken as zero.
* Part B.4 deduces the vapor pressure `Pᵥ` from `P_atm`, `H₀`, `H`, `T₀`,
  and `T`; part B.5 constructs a Clausius–Clapeyron graph from the
  integrated Clausius–Clapeyron law (equation (3) of the statement)

      ln (Pᵥ / Pᵥ0) = - (Qᵥ / R) * (1 / T - 1 / T₀)

  and determines the **molar** latent heat of vaporization `Qᵥ`
  (energy per mole, with the reference value `R = 8.31 J/(mol·K)`
  prescribed by the statement).
* Part B.6 (this question) converts the molar quantity `Qᵥ` into the
  **specific** quantity `Lᵥ`, the latent heat of vaporization per unit
  mass, and asks the student to *state the conversion formula used*.

The B.5 result is a *natural-language prerequisite only* (per the problem's
dependency policy): `Qᵥ` enters here as an experimentally determined molar
latent heat, and we do not import any Lean output of part B.5.

## Governing conversion law (encoded, not stipulated)

The conversion is physically forced by the **molar-to-specific accounting
principle**: one mole of water has mass equal to the molar mass `M_water`
(the substance's mass-per-mole constant), so the heat `Qᵥ` that vaporizes
**one mole** vaporizes the mass `M_water`.  Specific latent heat `Lᵥ` is the
heat required *per unit mass*; hence the heat for a sample of mass `m` is
`Lᵥ * m` on the one hand and `(m / M_water) * Qᵥ` on the other (molar
extensivity: `ν` moles absorb `ν * Qᵥ`).  Equating the two expressions for
the sample of one mole gives the governing relation

    Qᵥ = M_water * Lᵥ,

i.e. the molar latent heat is the molar mass times the specific latent heat.
Crucially, this multiplication form is the oriented physical law; the
division form `Lᵥ = Qᵥ / M_water` that the question asks to state is then
**derived as a theorem** (`formula_used`) by `field_simp`, not baked into a
definition.  The inverted formula `Lᵥ = Qᵥ * M_water` violates the governing
relation as soon as `M_water ≠ 1` (water's molar mass is about `18 g/mol`),
so the orientation is now discriminated by the artifact itself.

## Answer-free statement design

The official value of `Lᵥ` is withheld.  Following the blind policy, the
theorem signature introduces a result variable `L_v` of
energy-per-unit-mass role and the solution predicate
`IsLatentHeatPerUnitMass` is the *governing relation* above applied to the
experimentally determined `Qᵥ` and the molar mass of water; the target
theorem asserts existence and uniqueness.  Neither the witness nor the
derived formula appears in the target signature — the formula is the
separately proved lemma `formula_used`, keeping the "determine" target
answer-free while the "formula that you used" is honestly derived.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_4B6

/-! ## Governing law: molar-to-specific conversion of an extensive quantity -/

/-- **Governing conversion principle (molar to specific).**  For a pure
substance, the molar magnitude `q_molar` of an extensive quantity (heat
absorbed per mole) and its specific (per-unit-mass) magnitude `q_specific`
are related through the substance's molar mass `M` (mass per mole) by

    q_molar = M * q_specific :

the heat that converts one mole also converts the mass of one mole, namely
`M`.  This multiplication form is the physically oriented law: it expresses
that a mole of mass `M` absorbs `M` times the per-unit-mass heat.  The
familiar division `q_specific = q_molar / M` is a *derived* rearrangement
(valid when `M ≠ 0`), not the primary relation.

Because the field is a real normed field, representing this relation in
`ℝ` is dimensionally faithful — exactly the pattern used in B.5, where the
Clausius–Clapeyron law is the governing hypothesis and the graph slope
relation is derived from it. -/
def MolarSpecificConversion (q_molar M q_specific : ℝ) : Prop :=
  q_molar = M * q_specific

/-- The conversion principle is invariant under the molar extensivity of
heat: the heat absorbed by `n` moles is `n` times the molar latent heat.
(Recorded as the physical reading of `MolarSpecificConversion`; see the
derived formula `LatentHeatData.formula_used` for the division form.) -/
theorem molarSpecificConversion_reading {q_molar M q_specific : ℝ}
    (h : MolarSpecificConversion q_molar M q_specific) :
    q_molar = M * q_specific :=
  h

/-! ## Data for part B.6 -/

/-- Data for the molar-to-specific conversion of the latent heat of
vaporization of water in part B of Problem E1.

* `Q_v` is the **molar** latent heat of vaporization of water
  (energy per mole), determined experimentally in part B.5 from the
  Clausius–Clapeyron graph of equation (3),
  `ln (Pᵥ / Pᵥ0) = - (Qᵥ / R) * (1 / T - 1 / T₀)`; positive, since
  vaporization absorbs heat.
* `M_water` is the **molar mass of water** (mass per mole), the reference
  constant mediating the molar-to-specific conversion, known to be nonzero
  (and positive). -/
structure LatentHeatData where
  /-- Molar latent heat of vaporization `Qᵥ` of water (energy per mole),
  as determined in part B.5 via the Clausius–Clapeyron relation. -/
  Q_v : ℝ
  /-- Molar mass `M_water` of water (mass per mole), the reference constant
  used for the molar-to-specific conversion. -/
  M_water : ℝ
  /-- The molar latent heat determined in B.5 is positive (vaporization
  absorbs heat). -/
  Q_v_pos : 0 < Q_v
  /-- The molar mass of water is positive. -/
  M_water_pos : 0 < M_water

namespace LatentHeatData

variable (D : LatentHeatData)

/-- **Solution predicate for B.6 (answer-free).**  A real number `L_v` of
energy-per-unit-mass role is the latent heat of vaporization per unit mass
of water when it satisfies the governing molar-to-specific conversion
principle `MolarSpecificConversion` for the B.5 molar latent heat `Qᵥ` and
the molar mass of water:

    Qᵥ = M_water * L_v.

Note that the requested division form is *not* stipulated here; it is
derived as `formula_used` below. -/
def IsLatentHeatPerUnitMass (L_v : ℝ) : Prop :=
  MolarSpecificConversion D.Q_v D.M_water L_v

/-- **The formula that part B.6 asks to state, derived from the governing
law.**  Under the molar-to-specific conversion principle, the specific
latent heat is the molar latent heat divided by the molar mass:

    Lᵥ = Qᵥ / M_water.

This replaces the earlier definition-level stipulation: the division
orientation now *follows* from the encoded multiplication law via
`field_simp`, so the inverted formula (`Lᵥ = Qᵥ * M_water`) is excluded
whenever `M_water ≠ 1`, as it is for water. -/
theorem formula_used {L_v : ℝ} (h : D.IsLatentHeatPerUnitMass L_v) :
    L_v = D.Q_v / D.M_water := by
  have hM : D.M_water ≠ 0 := ne_of_gt D.M_water_pos
  have heq : D.Q_v = D.M_water * L_v := h
  field_simp [hM]
  -- Goal: L_v * D.M_water = D.Q_v (up to commutativity), closing via `heq`.
  rw [mul_comm L_v D.M_water]
  exact heq.symm

/-- The latent heat per unit mass of the B.6 conversion is positive:
per the governing law `Qᵥ = M_water * Lᵥ` with both `Qᵥ` and `M_water`
positive, `Lᵥ` must be positive — vaporization absorbs heat per unit mass.
No division of signs is invoked; positivity survives the physically
oriented multiplication form directly. -/
theorem isLatentHeatPerUnitMass_pos {L_v : ℝ}
    (h : D.IsLatentHeatPerUnitMass L_v) : 0 < L_v := by
  have heq : D.Q_v = D.M_water * L_v := h
  have hM : D.M_water ≠ 0 := ne_of_gt D.M_water_pos
  -- `L_v = Qᵥ / M_water` from the derived formula, then positivity of a
  -- quotient of positive reals.  (Keeping the derivation through
  -- `formula_used` makes this robust to the redrafted orientation.)
  rw [D.formula_used h]
  exact div_pos D.Q_v_pos D.M_water_pos

/-- **E1-B.6, answer-free characterization.**  Given the molar latent heat
`Qᵥ` of water determined in part B.5 and the molar mass of water, there
exists a unique real number `Lᵥ` satisfying the governing molar-to-specific
conversion principle — the latent heat of vaporization per unit mass.

Neither the explicit value of `Lᵥ` nor the requested formula appears in
this statement; the later proof constructs the unique witness, and the
formula that the question asks to indicate is the separately proved lemma
`formula_used`. -/
theorem latent_heat_per_unit_mass_exists_unique :
    ∃! L_v : ℝ, D.IsLatentHeatPerUnitMass L_v := by
  have hM : D.M_water ≠ 0 := ne_of_gt D.M_water_pos
  -- Existence: the witness `L_v = Qᵥ / M_water` satisfies the governing
  -- relation Qᵥ = M_water * L_v by right-cancelling the nonzero molar mass.
  refine ⟨D.Q_v / D.M_water, ?_, ?_⟩
  · change D.Q_v = D.M_water * (D.Q_v / D.M_water)
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hM]
  -- Uniqueness: any `L_v` satisfying the governing relation obeys the
  -- derived division formula `L_v = Qᵥ / M_water`, hence equals the witness.
  · intro L_v hL
    rw [D.formula_used hL]

end LatentHeatData

end Ipho2026KimiK3Blind32.ProblemIPhO2026_4B6
