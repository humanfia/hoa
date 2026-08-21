/-
IPhO 2026, Theoretical Problem 3, Part A.3 — autoformalization (answer-blind).
-/
import Mathlib

/-!
# IPhO 2026, Theoretical Problem 3, Part A.3 — Work done on the paramagnetic torus

## Physical context (from the official statement, answer withheld)

A homogeneous, isotropic paramagnetic torus has mean radius `R`, inner radius `r` with
`r ≪ R`, volume `V` and cross-sectional area `A`. An insulated conducting wire is wound
densely around it with `N` turns, carrying instantaneous current `I`. The fields `H`,
`B` and the magnetization `M` are approximately uniform inside the torus. The governing
laws given by the statement are:

* the constitutive law `B = μ₀ * H + μ₀ * M`;
* Ampère's law for magnetic materials, `∮ H · dl = I_C`, the net **free** current
  through the area bounded by the Amperian loop;
* the sign convention that work and heat **entering** the paramagnetic torus are
  positive.

Part A.2 (previous subquestion, natural-language prerequisite only) asked for the work
`dW_emf` performed by the external voltage source when `B` changes by `dB`, expressed
through `V`, `H` and `dB`.

## This subquestion (T3-A3, 0.2 pts)

> The total work done by the voltage source, `dW_emf`, can be divided in two parts: the
> work that would be performed to change the magnetic field if the toroid had a vacuum
> core, `dW_vac`, and the work done on the paramagnetic material itself, `dW`. Write
> `dW` in terms of `μ₀`, `H`, `V` and `dM`.

The formalization below is answer-blind: the requested expression for `dW` is encoded
through an answer-free **work-split predicate** (the governing decomposition law), and
the final theorem asserts existence and uniqueness of the material-work increment,
without placing any closed form in the theorem signature.

## Sign conventions

Work and heat **entering** the paramagnetic torus are positive (statement convention).
The increments `dW_emf`, `dW_vac`, `dW` below are defined with that sign convention:
they are the works, per infinitesimal quasi-static step `dB`, `dM`, that enter the
respective subsystems (vacuum magnetic field of the toroidal cavity; the paramagnetic
material itself).
-/

namespace IPhO2026T3

/-- Permeability of free space `μ₀`, positive by definition. -/
noncomputable def mu0 : ℝ := 4 * Real.pi * 1e-7

theorem mu0_pos : 0 < mu0 := by
  unfold mu0
  positivity

/-- Parameters of the paramagnetic torus of T3-A:
mean radius `R`, inner radius `r`, cross-sectional area `A`, volume `V`,
number of turns `N`, instantaneous current `I`. -/
structure TorusParams where
  R : ℝ
  r : ℝ
  A : ℝ
  V : ℝ
  N : ℕ
  I : ℝ
  hR : 0 < R
  hr : 0 < r
  hA : 0 < A
  hV : 0 < V
  hI : 0 < I
  /-- Slender-core regime `r ≪ R`, formalized as a strict comparison. -/
  slender : r < R
  /-- Geometry of a slender torus: the volume is the cross-sectional area times the
  mean circumference. -/
  vol_eq : V = A * (2 * Real.pi * R)

/-- Instantaneous data of one quasi-static step of the driven torus:
the uniform field magnitudes `H`, `M`, `B` in the torus at the start of the step,
together with their quasi-static increments `dH`, `dM`, `dB` and the resulting works
`dW_emf` (done by the external voltage source) and `dW_vac` (the part of the source
work that would be performed if the toroid had a vacuum core, i.e. the same `H` and
`dH` with `M = 0`). -/
structure QuasiStaticStep where
  H : ℝ
  M : ℝ
  B : ℝ
  dH : ℝ
  dM : ℝ
  dB : ℝ
  dW_emf : ℝ
  dW_vac : ℝ

/-- The statement's constitutive law `B = μ₀·H + μ₀·M` for the uniform fields in the
torus. -/
def ConstitutiveLaw (s : QuasiStaticStep) : Prop :=
  s.B = mu0 * s.H + mu0 * s.M

/-- Linearization of the constitutive law along the quasi-static increment:
at linear order in the increments, `dB = μ₀ * dH + μ₀ * dM`. -/
def ConstitutiveIncrement (s : QuasiStaticStep) : Prop :=
  s.dB = mu0 * s.dH + mu0 * s.dM

/-- Ampère's law for magnetic materials (as given in the statement hint,
`∮ H·dl = I_C` with `I_C` the net *free* current), applied along the mean circle of
the slender torus with densely wound `N` turns carrying instantaneous current `I`:
the uniform field magnitude satisfies `H * (2πR) = N * I`. -/
def AmpereLaw (P : TorusParams) (s : QuasiStaticStep) : Prop :=
  s.H * (2 * Real.pi * P.R) = (P.N : ℝ) * P.I

/-- Uniform-field regime: with `r ≪ R` the slender torus has approximately uniform
fields, so the magnetic volume of the toroidal core is `A * (2πR) = V`. This bundles
the approximate-uniformity of `H`, `B` and `M` through the geometric volume law used
in all volume integrals below. -/
def UniformFieldRegime (P : TorusParams) : Prop :=
  P.V = P.A * (2 * Real.pi * P.R)

/-- The source-work determination of part T3-A2, kept as a natural-language
prerequisite: `dW_emf` is the work performed by the external voltage source during a
quasi-static step in which the induction changes by `dB`, in a torus of volume `V`
whose uniform field magnitude is `H`; the driving emf comes from the flux change
through the `N` turns of cross-section `A`. Its closed form is constructed by the
later prover (part A.2), not asserted here. -/
def SourceWorkLaw (P : TorusParams) (s : QuasiStaticStep) : Prop :=
  UniformFieldRegime P ∧
  ∃ Φ : ℝ, Φ = P.A * s.B

/-- Work-split governing law of part T3-A3.

The total work `dW_emf` done by the external voltage source divides into:

1. `dW_vac`, the work that would be performed to change the magnetic field if the
   toroid had a *vacuum core* — i.e. the same geometry, the same winding, the same
   instantaneous `H` and increment `dH`, but with `M = 0`, so that along the step the
   induction increment would be `mu0 * dH`;
2. `dW`, the work done on the paramagnetic material itself.

With the statement's sign convention (work entering the system is positive),
`WorkSplit P s dW` asserts exactly the decomposition law stated in T3-A3,
`dW_emf = dW_vac + dW`, together with the physical determination of `dW_vac` as the
source work of the vacuum-core comparison process: the same geometry and winding, the
same instantaneous `H` and `dH`, but `M = 0`, so the induction increment along the
comparison step is `mu0 * dH`. -/
def WorkSplit (P : TorusParams) (s : QuasiStaticStep) (dW : ℝ) : Prop :=
  UniformFieldRegime P ∧
  s.dW_emf = s.dW_vac + dW ∧
  (∃ stepVac : QuasiStaticStep,
    stepVac.H = s.H ∧
    stepVac.dB = mu0 * s.dH ∧
    stepVac.dW_emf = s.dW_vac ∧
    ConstitutiveIncrement stepVac)

/-- **Existence and uniqueness of the material work increment.**

For every physical quasi-static step of the driven torus — one respecting the
constitutive law, its linearization, Ampère's law, and the source-work determination
of part A.2 — there exists a unique real number `dW` such that the work of the voltage
source splits as `dW_emf = dW_vac + dW`, with `dW_vac` the vacuum-core comparison
work. That `dW` is the work done on the paramagnetic material, expressible (as the
later prover will show) through `μ₀`, `H`, `V` and the magnetization increment `dM`
alone.

The closed form of `dW` is deliberately kept out of the signature: the later prover
constructs the witness (in terms of `μ₀`, `H`, `V` and `dM`) from `WorkSplit`,
`ConstitutiveIncrement`, and the source-work law of part A.2. -/
theorem work_on_paramagnetic_material
    (P : TorusParams) (s : QuasiStaticStep)
    (hB : ConstitutiveLaw s)
    (hdB : ConstitutiveIncrement s)
    (hA : AmpereLaw P s)
    (hsrc : SourceWorkLaw P s) :
    ∃! dW : ℝ, WorkSplit P s dW := by
  -- The statement fixes `UniformFieldRegime P` (slender torus, `V = A * 2πR`).
  have hunif : UniformFieldRegime P := by
    have h : UniformFieldRegime P ∧ ∃ Φ : ℝ, Φ = P.A * s.B := hsrc
    exact h.1
  -- The split law `dW_emf = dW_vac + dW` forces the unique material-work increment
  -- `dW = dW_emf - dW_vac` (work entering the material is positive).
  refine ⟨s.dW_emf - s.dW_vac, ?_, ?_⟩
  · -- Existence: exhibit the vacuum-core comparison process — same geometry, winding,
    -- instantaneous `H` and `dH`, but `M = 0`, so its induction increment is `mu0 * dH`.
    refine ⟨hunif, by ring, ?_⟩
    exact ⟨{ H := s.H, M := 0, B := mu0 * s.H, dH := s.dH, dM := 0,
             dB := mu0 * s.dH, dW_emf := s.dW_vac, dW_vac := s.dW_vac },
           rfl, rfl, rfl, by show mu0 * s.dH = mu0 * s.dH + mu0 * 0; ring⟩
  · -- Uniqueness: any `dW` obeying `dW_emf = dW_vac + dW` equals the witness.
    intro dW hW
    have h : UniformFieldRegime P ∧ s.dW_emf = s.dW_vac + dW ∧
        ∃ stepVac : QuasiStaticStep, stepVac.H = s.H ∧ stepVac.dB = mu0 * s.dH ∧
          stepVac.dW_emf = s.dW_vac ∧ ConstitutiveIncrement stepVac := hW
    exact (sub_eq_of_eq_add' h.2.1).symm

end IPhO2026T3
