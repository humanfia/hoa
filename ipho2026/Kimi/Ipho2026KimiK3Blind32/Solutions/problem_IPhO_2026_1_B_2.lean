import Mathlib

/-!
# IPhO 2026, Problem 1, Part B.2 — answer-blind formalization

At a certain instant a positron $e^+$ and an electron $e^-$, each of mass
$m$ with charges of equal magnitude and opposite sign, are separated by
`100 a₀` (T1 page 5, Fig. 1b: the positron sits above the electron, both
velocities horizontal).  Their velocities are antiparallel and perpendicular
to their separation, and each particle has angular momentum `μ ħ` about the
centre of mass, with the prescribed `μ = 15/2`.  For this value the pair is
unbound.  The problem asks for the angle, in degrees, between the asymptotic
relative velocity `u∞` and the initial positron line of motion.

The statement below follows the route supplied by the two printed hints.  It
uses the conserved energy and angular momentum to determine the eccentricity
of the hyperbola, then characterises the outgoing asymptote using the polar
conic `r = a / (1 - ε cos φ)`.  The requested numerical angle is deliberately
absent from every definition and from the theorem signature.
-/

namespace IPhO_2026_1_B_2

/-- The dimensionless data fixed by the question.  Distances are measured in
Bohr radii and angular momenta in units of `ħ`. -/
structure RadialData where
  μ : ℝ
  r0 : ℝ
  μ_pos : 0 < μ
  r0_pos : 0 < r0

/-- The prescribed angular-momentum parameter `μ = 15/2`. -/
noncomputable def muValue : ℝ := 15 / 2

/-- The prescribed initial separation `100 a₀`, in Bohr radii. -/
noncomputable def initialSeparationInBohrRadii : ℝ := 100

/-- In Bohr units the relative speed at the observed transverse state is
`4 μ / r₀` (the velocities being perpendicular to the separation, Fig. 1b,
the linear momenta of the two equal-mass particles each have magnitude
`2 μ ħ/r₀`).  Hence the dimensionless conserved energy of the reduced-mass
`m/2` motion is `Ē = ‖v̄‖²/4 - 1/r₀ = 4 μ²/r₀² - 1/r₀`. -/
noncomputable def initialDimlessEnergy (D : RadialData) : ℝ :=
  4 * D.μ ^ 2 / D.r0 ^ 2 - 1 / D.r0

/-- The total angular momentum in units of `ħ` is `L/ħ = 2 μ`. -/
noncomputable def initialAngularMomentumRatio (D : RadialData) : ℝ :=
  2 * D.μ

/-- **Hint 1 in dimensionless Bohr units.**  Substituting
`E = (ħ²/(m a₀²)) Ē`, `L = ħ ℓ`, and
`a₀ = ħ²/(k m e²)` into
`ε² = 1 + 4 L² E/(k² e⁴ m)` gives `ε² = 1 + 4 ℓ² Ē`. -/
noncomputable def conicEccentricitySq (ell Ebar : ℝ) : ℝ :=
  1 + 4 * ell ^ 2 * Ebar

/-- **Hint 2.**  The polar equation of the conic trajectory is
`r = a / (1 - ε cos φ)`. -/
noncomputable def conicRadius (a ε φ : ℝ) : ℝ :=
  a / (1 - ε * Real.cos φ)

/-- Answer-free conserved/conic data for the outgoing hyperbolic orbit.

* `Ebar` and `ell` are the conserved dimensionless energy and angular
  momentum fixed by the initial state;
* positivity of `Ebar` records the stated unbound branch;
* `ε > 1` and its squared equation are Hint 1;
* `a > 0` and `r(π) = r₀` normalize Hint 2's scale so the observed transverse
  (zero-radial-velocity) state is placed at the periapsis point of the
  parametrisation;
* `φ∞ ∈ (0, π/2)` and `ε cos φ∞ = 1` select the outgoing asymptote, where
  Hint 2's denominator vanishes.

No derived value of the eccentricity, asymptote, or requested angle occurs
in this predicate. -/
def ConicScatteringData (D : RadialData)
    (Ebar ell a ε φInf : ℝ) : Prop :=
  Ebar = initialDimlessEnergy D ∧
  ell = initialAngularMomentumRatio D ∧
  0 < Ebar ∧
  1 < ε ∧
  ε ^ 2 = conicEccentricitySq ell Ebar ∧
  0 < a ∧
  conicRadius a ε Real.pi = D.r0 ∧
  φInf ∈ Set.Ioo 0 (Real.pi / 2) ∧
  ε * Real.cos φInf = 1

/-- `θ_deg` is the asked acute angle.  The polar axis in Hint 2 is the
separation line, perpendicular to the initial line of motion, so the angle
to that initial line is `π/2 - φ∞`. -/
def Solution (D : RadialData) (θ_deg : ℝ) : Prop :=
  ∃ Ebar ell a ε φInf : ℝ,
    ConicScatteringData D Ebar ell a ε φInf ∧
    θ_deg * (Real.pi / 180) + φInf = Real.pi / 2

/- USER: Preserve `Solution` and the exact theorem signature below.  Fill only
the theorem body; an explicit witness may appear inside the proof. -/

/-- **Target theorem (answer-free).**  The stated conserved data and the two
printed conic hints determine a unique angle in degrees.  Its concrete value
is constructed only inside the proof. -/
theorem problem_IPhO_2026_1_B_2 :
    ∃! θ_deg : ℝ,
      Solution
        ⟨muValue, initialSeparationInBohrRadii,
          by norm_num [muValue],
          by norm_num [initialSeparationInBohrRadii]⟩
        θ_deg := by
  let φ : ℝ := Real.arccos (2 / 7)
  let θ : ℝ := (Real.pi / 2 - φ) * (180 / Real.pi)
  refine ⟨θ, ?_, ?_⟩
  · refine ⟨1 / 80, 15, 450, 7 / 2, φ, ?_, ?_⟩
    · constructor
      · norm_num [initialDimlessEnergy, muValue,
          initialSeparationInBohrRadii]
      constructor
      · norm_num [initialAngularMomentumRatio, muValue]
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num [conicEccentricitySq]
      constructor
      · norm_num
      constructor
      · norm_num [conicRadius, Real.cos_pi,
          initialSeparationInBohrRadii]
      constructor
      · constructor
        · dsimp [φ]
          exact Real.arccos_pos.mpr (by norm_num)
        · dsimp [φ]
          exact Real.arccos_lt_pi_div_two.mpr (by norm_num)
      · dsimp [φ]
        rw [Real.cos_arccos (by norm_num) (by norm_num)]
        norm_num
    · dsimp [θ]
      field_simp [Real.pi_ne_zero]
      ring
  · intro θ' hθ'
    rcases hθ' with ⟨Ebar, ell, a, ε, φInf, hdata, hangle⟩
    rcases hdata with
      ⟨hE, hell, _hEpos, hεpos, hεsq, _hapos, _hperi,
        hφrange, hφcos⟩
    have hE' : Ebar = 1 / 80 := by
      calc
        Ebar = initialDimlessEnergy
            ⟨muValue, initialSeparationInBohrRadii,
              by norm_num [muValue],
              by norm_num [initialSeparationInBohrRadii]⟩ := hE
        _ = 1 / 80 := by
          norm_num [initialDimlessEnergy, muValue,
            initialSeparationInBohrRadii]
    have hell' : ell = 15 := by
      calc
        ell = initialAngularMomentumRatio
            ⟨muValue, initialSeparationInBohrRadii,
              by norm_num [muValue],
              by norm_num [initialSeparationInBohrRadii]⟩ := hell
        _ = 15 := by norm_num [initialAngularMomentumRatio, muValue]
    have hεsq' : ε ^ 2 = (7 / 2 : ℝ) ^ 2 := by
      rw [hεsq, hell', hE']
      norm_num [conicEccentricitySq]
    have hε : ε = 7 / 2 := by
      nlinarith
    have hcos : Real.cos φInf = 2 / 7 := by
      rw [hε] at hφcos
      nlinarith
    have hφlepi : φInf ≤ Real.pi := by
      have hp : 0 < Real.pi := Real.pi_pos
      linarith [hφrange.2]
    have hφ : φInf = φ := by
      dsimp [φ]
      calc
        φInf = Real.arccos (Real.cos φInf) :=
          (Real.arccos_cos (le_of_lt hφrange.1) hφlepi).symm
        _ = Real.arccos (2 / 7) := by rw [hcos]
    rw [hφ] at hangle
    dsimp [θ]
    have hpi : 0 < Real.pi := Real.pi_pos
    field_simp [Real.pi_ne_zero] at hangle ⊢
    nlinarith

end IPhO_2026_1_B_2
