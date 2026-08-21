import Mathlib

/-
# IPhO 2026, Theoretical Question 3 ("Chasing the absolute zero"), Part T3-A1

## Physical setup (official statement, figure 3a)

A torus of mean radius `R` and inner radius `r`, made of a homogeneous,
isotropic paramagnetic material, has an insulated conducting wire wound
densely around it (`N` turns in total) carrying an instantaneous current `I`.
The winding ends are connected to an external voltage source.  It is assumed
that `r ≪ R`, so that the magnetic field intensity `H`, the flux density `B`
and the magnetization `M` have approximately constant magnitudes throughout
the torus.  `V` and `A` denote the volume and the cross-sectional area of the
torus.  The constitutive relation `B = μ₀ H + μ₀ M` holds with `M ∥ H`, and
the energy-transfer sign convention takes work and heat entering the
paramagnetic torus (Pm-T) to be positive.

## Subquestion T3-A1

Let `H` be the magnitude of the magnetic field intensity inside the torus.
Express `H` in terms of `N`, the instantaneous current `I`, the cross-section
area `A` and the volume `V`, using Ampère's law for magnetic materials as
printed on the official sheet: `∮_C H · dl = I_C`, where `I_C` is the net free
current passing through the area bounded by the closed curve `C`.

## Formalization notes (answer-blind)

The requested expression is deliberately *not* part of the theorem signature:
we introduce a candidate scalar `H` and state that the parametrized physical
model `ParamagneticTorusA1` admits a unique such magnitude.  A later prover
may construct the explicit witness.

* The Amperian loop `C` is taken along the mean field line of the torus; its
  length `ℓ` is therefore the mean circumference, a condition recorded by
  `thin_torus_path` (`ℓ = 2 * π * R`).
* Because `r ≪ R` the field magnitude is assumed uniform over the loop, so
  the circulation is `∮_C H · dl = ℓ * H`; this appears directly as the
  left-hand side of `ampere_law`.
* The dense `N`-turn winding carries the net free current `N * I` through the
  area bounded by `C`; this is the right-hand side of `ampere_law`.
* A thin toroidal tube of constant cross-section sweeps its area `A` along
  the mean line, giving the geometric constraint `V = A * ℓ`
  (`torus_volume_cross_section`), expressed through the loop data rather than
  directly through `R`, so that its statement never presumes the derived
  target formula.
-/

open Real

/-- Parametrized physical data of subquestion T3-A1 (figure 3a): the Pm-T
geometry, the winding, and the Amperian loop `C` along the mean field line. -/
structure ParamagneticTorusA1 where
  /-- Mean radius `R` of the torus. -/
  meanRadius : ℝ
  /-- Inner (tube) radius `r` of the torus. -/
  innerRadius : ℝ
  /-- Cross-sectional area `A` of the torus. -/
  crossSection : ℝ
  /-- Volume `V` of the torus. -/
  volume : ℝ
  /-- Number of turns `N` of the dense winding. -/
  turns : ℕ
  /-- Instantaneous current `I` in the wire. -/
  current : ℝ
  /-- Length `ℓ` of the closed Amperian loop `C` (the mean field line). -/
  pathLength : ℝ
  meanRadius_pos : 0 < meanRadius
  innerRadius_pos : 0 < innerRadius
  crossSection_pos : 0 < crossSection
  volume_pos : 0 < volume
  /-- The thin-torus regime `r ≪ R`, recorded as strict smallness `r < R`;
  this licenses the uniformity of the fields throughout the torus. -/
  thin_regime : innerRadius < meanRadius
  /-- Sign convention for the winding and the current: the instantaneous
  current `I` is measured positively along the wire direction drawn in
  figure 3a, for which the field intensity `H ⃗` circulates along the chosen
  Amperian loop orientation. -/
  current_nonneg : 0 ≤ current
  /-- The Amperian loop is the mean field line of the torus, so its length is
  the mean circumference `ℓ = 2 π R`. -/
  thin_torus_path : pathLength = 2 * π * meanRadius
  /-- Thin toroidal tube of constant cross-section: its volume is the
  cross-section swept along the mean line, `V = A * ℓ` (equivalently
  `V = 2 π R A`), linking the requested quantities `V`, `A` to the loop. -/
  torus_volume_cross_section : volume = crossSection * pathLength

/-- Ampère's law for magnetic materials, exactly as printed on the official
sheet (`∮_C H · dl = I_C`), evaluated for subquestion T3-A1: under the
`r ≪ R` uniformity approximation the circulation of the field intensity of
magnitude `H` along the mean field line is `ℓ * H`, while the net free
current through the area bounded by `C` is `N * I`, since every one of the
`N` densely wound turns carries the instantaneous current `I` through that
surface. -/
def ParamagneticTorusA1.AmpereLaw (t : ParamagneticTorusA1) (H : ℝ) : Prop :=
  t.pathLength * H = t.turns * t.current

/-- Solution predicate for subquestion T3-A1: `H` is the non-negative
magnitude of the magnetic field intensity inside the torus fixed by Ampère's
law for the given winding and loop geometry. -/
def ParamagneticTorusA1.FieldMagnitudeSolution (t : ParamagneticTorusA1)
    (H : ℝ) : Prop :=
  0 ≤ H ∧ t.AmpereLaw H

/-- **T3-A1 target (answer-blind).**  For every physical configuration of the
Pm-T there is a unique field magnitude `H` inside the torus determined by
Ampère's law; the requested expression of `H` through `N`, `I`, `A` and `V`
is the content of the (later) construction of this witness. -/
theorem ParamagneticTorusA1.exists_unique_fieldMagnitude (t : ParamagneticTorusA1) :
    ∃! H : ℝ, t.FieldMagnitudeSolution H := by
  have hR := t.meanRadius_pos
  have hI := t.current_nonneg
  have hℓ : 0 < t.pathLength := by
    rw [t.thin_torus_path]
    positivity
  refine ⟨t.turns * t.current / t.pathLength, ⟨?_, ?_⟩, fun y hy ↦ ?_⟩
  · positivity
  · show t.pathLength * (t.turns * t.current / t.pathLength) = t.turns * t.current
    field_simp
  · rw [eq_div_iff hℓ.ne', mul_comm]
    exact hy.2
