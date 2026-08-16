import Ipho2026Gpt56solBlind.Shared.CausticOptics

/-!
# IPhO 2026 Problem 2 C.2: first-order data for a neighboring reflected ray

This answer-blind model builds the reflected rays in Figure 2g from a typed
positive-radius circular mirror and the shared specular-reflection
construction.  The requested first-order result is represented by a unique
derivative jet of the canonical slope and intercept functions.  Its value is
not placed in any declaration signature.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_2_C_2

open Ipho2026Gpt56solBlind.Shared
open Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-- The one coherent SI chart used for every physical length in Figure 2g. -/
def figure2gUnitChoices : SIUnitChoices :=
  SIUnitChoices.SI

/-- The origin-centered typed circular mirror of physical radius `R`. -/
def figure2gPhysicalMirror (R : ISQDimensions.Length)
    (hR : 0 < ISQDimensions.coordinateInSI figure2gUnitChoices R) :
    PhysicalCircle figure2gUnitChoices :=
  { center := { x := 0, y := 0 }
    radius := R
    radius_pos := hR }

/-- The upper-semicycle axial specular family fixed by Figure 2g. -/
def figure2gReflectedFamily (R : ISQDimensions.Length)
    (hR : 0 < ISQDimensions.coordinateInSI figure2gUnitChoices R) :
    ReflectedRayFamily :=
  axialReflectedRayFamily
    (physicalCircleCoordinateInSI figure2gUnitChoices
      (figure2gPhysicalMirror R hR))
    .upper

/-- Admissible physical radius and base incidence parameter for Figure 2g. -/
structure Figure2gSourceData where
  radius : ISQDimensions.Length
  radius_pos : 0 < ISQDimensions.coordinateInSI figure2gUnitChoices radius
  theta : ℝ
  theta_mem_incidence :
    theta ∈ (figure2gReflectedFamily radius radius_pos).domain
  base_outgoing_nonvertical :
    ((figure2gReflectedFamily radius radius_pos).outgoing theta).1.x ≠ 0

/-- Parameters at which the reflected ray is interior and nonvertical. -/
def figure2gCoefficientDomain (data : Figure2gSourceData) : Set ℝ :=
  {t | t ∈ (figure2gReflectedFamily data.radius data.radius_pos).domain ∧
    ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x ≠ 0}

/-- Canonical slope-intercept coordinates of the reflected supporting line. -/
def figure2gCanonicalLineCoefficients (data : Figure2gSourceData) (t : ℝ) :
    LineCoefficients :=
  nonverticalLineCoefficients
    ((figure2gReflectedFamily data.radius data.radius_pos).incidence t)
    ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1

/-- The slope component of the canonical reflected-line coordinates. -/
def figure2gSlope (data : Figure2gSourceData) (t : ℝ) : ℝ :=
  (figure2gCanonicalLineCoefficients data t).slope

/-- The coherent-SI intercept component of the canonical line coordinates. -/
def figure2gIntercept (data : Figure2gSourceData) (t : ℝ) : ℝ :=
  (figure2gCanonicalLineCoefficients data t).intercept

/-- A candidate derivative jet supported by exact local little-o expansions. -/
def IsFigure2gFirstOrderCoefficientJet (data : Figure2gSourceData)
    (jet : CoefficientDerivativeData) : Prop :=
  ∃ slopeRemainder interceptRemainder : ℝ → ℝ,
    HasCoefficientFirstOrderExpansion
      (figure2gCoefficientDomain data)
      (figure2gSlope data) (figure2gIntercept data) data.theta jet
      slopeRemainder interceptRemainder

/-- The family used in Figure 2g satisfies the component law of specular reflection. -/
lemma figure2gReflectedFamily_isSpecular (R : ISQDimensions.Length)
    (hR : 0 < ISQDimensions.coordinateInSI figure2gUnitChoices R)
    (t : ℝ) (ht : t ∈ (figure2gReflectedFamily R hR).domain) :
    IsSpecularReflection
      (figure2gReflectedFamily R hR).incoming
      ((figure2gReflectedFamily R hR).normal t)
      ((figure2gReflectedFamily R hR).outgoing t) := by
  exact (figure2gReflectedFamily R hR).outgoing_is_specular t ht

/-- The Figure 2g reflected family is differentiable on its strict incidence domain. -/
lemma figure2gReflectedFamily_differentiable (R : ISQDimensions.Length)
    (hR : 0 < ISQDimensions.coordinateInSI figure2gUnitChoices R) :
    DifferentiableReflectedRayFamily (figure2gReflectedFamily R hR) := by
  exact axialReflectedRayFamily_differentiable
    (physicalCircleCoordinateInSI figure2gUnitChoices
      (figure2gPhysicalMirror R hR)) .upper

/-- Interior, nonvertical incidence parameters form an open set. -/
lemma figure2gCoefficientDomain_isOpen (data : Figure2gSourceData) :
    IsOpen (figure2gCoefficientDomain data) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  rcases ht with ⟨htDomain, htNonvertical⟩
  have hDiff := figure2gReflectedFamily_differentiable
    data.radius data.radius_pos
  have hOutContinuous : ContinuousAt
      (fun s : ℝ =>
        ((figure2gReflectedFamily data.radius data.radius_pos).outgoing s).1.x) t :=
    (hDiff.2.2.2.1 t htDomain).differentiableAt
      (hDiff.1.mem_nhds htDomain) |>.continuousAt
  filter_upwards [hDiff.1.mem_nhds htDomain,
    hOutContinuous.eventually_ne htNonvertical] with s hsDomain hsNonvertical
  exact ⟨hsDomain, hsNonvertical⟩

/-- The source datum places its base parameter in the coefficient domain. -/
lemma figure2gTheta_mem_coefficientDomain (data : Figure2gSourceData) :
    data.theta ∈ figure2gCoefficientDomain data := by
  exact ⟨data.theta_mem_incidence, data.base_outgoing_nonvertical⟩

/-- All sufficiently close neighboring rays remain interior and nonvertical. -/
lemma exists_localNonverticalNeighborhood (data : Figure2gSourceData) :
    ∃ η : ℝ, 0 < η ∧
      ∀ Δθ : ℝ, |Δθ| < η →
        data.theta + Δθ ∈ figure2gCoefficientDomain data := by
  rcases Metric.mem_nhds_iff.mp
      ((figure2gCoefficientDomain_isOpen data).mem_nhds
        (figure2gTheta_mem_coefficientDomain data)) with
    ⟨η, hη, hball⟩
  refine ⟨η, hη, ?_⟩
  intro Δθ hΔθ
  apply hball
  change |data.theta + Δθ - data.theta| < η
  rw [add_sub_cancel_left]
  exact hΔθ

/-- On the coefficient domain, the canonical pair is the unique reflected-line pair. -/
lemma figure2gCanonicalLineCoefficients_unique (data : Figure2gSourceData)
    (t : ℝ) (ht : t ∈ figure2gCoefficientDomain data) :
    IsReflectedLineCoefficients
        (figure2gReflectedFamily data.radius data.radius_pos) t
        (figure2gCanonicalLineCoefficients data t) ∧
      ∀ c : LineCoefficients,
        IsReflectedLineCoefficients
            (figure2gReflectedFamily data.radius data.radius_pos) t c →
          c = figure2gCanonicalLineCoefficients data t := by
  have hCanonical : IsReflectedLineCoefficients
      (figure2gReflectedFamily data.radius data.radius_pos) t
      (figure2gCanonicalLineCoefficients data t) := by
    refine ⟨ht.1, ?_⟩
    refine ⟨ht.2, ?_, ?_⟩
    · exact (div_mul_cancel₀
        ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.y
        ht.2).symm
    · change
        ((figure2gReflectedFamily data.radius data.radius_pos).incidence t).y =
          ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.y /
              ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x *
              ((figure2gReflectedFamily data.radius data.radius_pos).incidence t).x +
            (((figure2gReflectedFamily data.radius data.radius_pos).incidence t).y -
              ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.y /
                ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x *
                ((figure2gReflectedFamily data.radius data.radius_pos).incidence t).x)
      ring
  refine ⟨hCanonical, ?_⟩
  intro c hc
  exact (existsUnique_reflectedLineCoefficients
    (figure2gReflectedFamily data.radius data.radius_pos) t ht.1 ht.2).unique
      hc hCanonical

/-- The canonical slope and intercept are differentiable on their open domain. -/
lemma figure2gCanonicalCoefficients_differentiableOn (data : Figure2gSourceData) :
    DifferentiableOn ℝ (figure2gSlope data) (figure2gCoefficientDomain data) ∧
      DifferentiableOn ℝ (figure2gIntercept data)
        (figure2gCoefficientDomain data) := by
  have hDiff := figure2gReflectedFamily_differentiable
    data.radius data.radius_pos
  have hSubset : figure2gCoefficientDomain data ⊆
      (figure2gReflectedFamily data.radius data.radius_pos).domain := by
    intro t ht
    exact ht.1
  have hNonzero : ∀ t ∈ figure2gCoefficientDomain data,
      ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x ≠ 0 := by
    intro t ht
    exact ht.2
  have hPx := hDiff.2.1.mono hSubset
  have hPy := hDiff.2.2.1.mono hSubset
  have hDx := hDiff.2.2.2.1.mono hSubset
  have hDy := hDiff.2.2.2.2.mono hSubset
  have hSlope : DifferentiableOn ℝ
      (fun t : ℝ =>
        ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.y /
          ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x)
      (figure2gCoefficientDomain data) :=
    hDy.div hDx hNonzero
  have hIntercept : DifferentiableOn ℝ
      (fun t : ℝ =>
        ((figure2gReflectedFamily data.radius data.radius_pos).incidence t).y -
          (((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.y /
            ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x) *
            ((figure2gReflectedFamily data.radius data.radius_pos).incidence t).x)
      (figure2gCoefficientDomain data) :=
    hPy.sub (hSlope.mul hPx)
  constructor
  · change DifferentiableOn ℝ
      (fun t : ℝ =>
        ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.y /
          ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x)
      (figure2gCoefficientDomain data)
    exact hSlope
  · change DifferentiableOn ℝ
      (fun t : ℝ =>
        ((figure2gReflectedFamily data.radius data.radius_pos).incidence t).y -
          (((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.y /
            ((figure2gReflectedFamily data.radius data.radius_pos).outgoing t).1.x) *
            ((figure2gReflectedFamily data.radius data.radius_pos).incidence t).x)
      (figure2gCoefficientDomain data)
    exact hIntercept

/-- The two canonical coefficient functions have a derivative jet at the base ray. -/
lemma exists_coefficientDerivativeData (data : Figure2gSourceData) :
    ∃ jet : CoefficientDerivativeData,
      HasCoefficientDerivativesAt
        (figure2gSlope data) (figure2gIntercept data) data.theta jet := by
  have hOpen := figure2gCoefficientDomain_isOpen data
  have hTheta := figure2gTheta_mem_coefficientDomain data
  rcases figure2gCanonicalCoefficients_differentiableOn data with
    ⟨hSlope, hIntercept⟩
  have hSlopeAt : DifferentiableAt ℝ (figure2gSlope data) data.theta :=
    (hSlope data.theta hTheta).differentiableAt (hOpen.mem_nhds hTheta)
  have hInterceptAt : DifferentiableAt ℝ (figure2gIntercept data) data.theta :=
    (hIntercept data.theta hTheta).differentiableAt (hOpen.mem_nhds hTheta)
  refine ⟨{
    slopeDerivative := deriv (figure2gSlope data) data.theta
    interceptDerivative := deriv (figure2gIntercept data) data.theta }, ?_⟩
  exact ⟨hSlopeAt.hasDerivAt, hInterceptAt.hasDerivAt⟩

/-- Derivatives of the two fixed canonical coefficient functions determine the jet. -/
lemma coefficientDerivativeData_unique (data : Figure2gSourceData)
    (jet₁ jet₂ : CoefficientDerivativeData)
    (h₁ : HasCoefficientDerivativesAt
      (figure2gSlope data) (figure2gIntercept data) data.theta jet₁)
    (h₂ : HasCoefficientDerivativesAt
      (figure2gSlope data) (figure2gIntercept data) data.theta jet₂) :
    jet₁ = jet₂ := by
  cases jet₁ with
  | mk slope₁ intercept₁ =>
      cases jet₂ with
      | mk slope₂ intercept₂ =>
          have hSlope : slope₁ = slope₂ := h₁.1.unique h₂.1
          have hIntercept : intercept₁ = intercept₂ := h₁.2.unique h₂.2
          cases hSlope
          cases hIntercept
          rfl

/-- A derivative jet supplies exact first-order identities with little-o remainders. -/
lemma exists_firstOrderCoefficientRemainders (data : Figure2gSourceData)
    (jet : CoefficientDerivativeData)
    (hjet : HasCoefficientDerivativesAt
      (figure2gSlope data) (figure2gIntercept data) data.theta jet) :
    ∃ slopeRemainder interceptRemainder : ℝ → ℝ,
      HasCoefficientFirstOrderExpansion
        (figure2gCoefficientDomain data)
        (figure2gSlope data) (figure2gIntercept data) data.theta jet
        slopeRemainder interceptRemainder := by
  exact hasFirstOrderExpansion_of_hasDeriv
    (figure2gCoefficientDomain data)
    (figure2gSlope data) (figure2gIntercept data) data.theta jet
    (figure2gCoefficientDomain_isOpen data)
    (figure2gTheta_mem_coefficientDomain data) hjet

/-- Every sufficiently close finite neighbor has the expanded canonical line coordinates. -/
theorem neighborLine_hasFirstOrderExpansion (data : Figure2gSourceData)
    (jet : CoefficientDerivativeData)
    (slopeRemainder interceptRemainder : ℝ → ℝ)
    (hexpansion : HasCoefficientFirstOrderExpansion
      (figure2gCoefficientDomain data)
      (figure2gSlope data) (figure2gIntercept data) data.theta jet
      slopeRemainder interceptRemainder) :
    ∃ δ : ℝ, 0 < δ ∧
      IsLittleOAtZero slopeRemainder ∧
      IsLittleOAtZero interceptRemainder ∧
      ∀ Δθ : ℝ, 0 < |Δθ| → |Δθ| < δ →
        let tB := data.theta + Δθ
        let cB := figure2gCanonicalLineCoefficients data tB
        tB ∈ figure2gCoefficientDomain data ∧
          IsReflectedLineCoefficients
            (figure2gReflectedFamily data.radius data.radius_pos) tB cB ∧
          (∀ c : LineCoefficients,
            IsReflectedLineCoefficients
                (figure2gReflectedFamily data.radius data.radius_pos) tB c →
              c = cB) ∧
          cB.slope = figure2gSlope data data.theta +
            jet.slopeDerivative * Δθ + slopeRemainder Δθ ∧
          cB.intercept = figure2gIntercept data data.theta +
            jet.interceptDerivative * Δθ + interceptRemainder Δθ := by
  rcases hexpansion with
    ⟨_hDeriv,
      ⟨δSlope, hδSlope, hSlopeDomain, hSlopeExpansion, hSlopeLittleO⟩,
      ⟨δIntercept, hδIntercept, hInterceptDomain,
        hInterceptExpansion, hInterceptLittleO⟩⟩
  refine ⟨min δSlope δIntercept, lt_min hδSlope hδIntercept,
    hSlopeLittleO, hInterceptLittleO, ?_⟩
  intro Δθ _hΔθPos hΔθSmall
  dsimp only
  have hSlopeSmall : |Δθ| < δSlope :=
    lt_of_lt_of_le hΔθSmall (min_le_left _ _)
  have hInterceptSmall : |Δθ| < δIntercept :=
    lt_of_lt_of_le hΔθSmall (min_le_right _ _)
  have htDomain := hSlopeDomain Δθ hSlopeSmall
  have hCanonical := figure2gCanonicalLineCoefficients_unique data
    (data.theta + Δθ) htDomain
  refine ⟨htDomain, hCanonical.1, hCanonical.2, ?_, ?_⟩
  · exact hSlopeExpansion Δθ hSlopeSmall
  · exact hInterceptExpansion Δθ hInterceptSmall

/-- The canonical reflected-line family has one and only one first-order jet. -/
theorem existsUnique_firstOrderCoefficientJet (data : Figure2gSourceData) :
    ∃! jet : CoefficientDerivativeData,
      IsFigure2gFirstOrderCoefficientJet data jet := by
  rcases exists_coefficientDerivativeData data with ⟨jet, hjet⟩
  rcases exists_firstOrderCoefficientRemainders data jet hjet with
    ⟨slopeRemainder, interceptRemainder, hexpansion⟩
  refine ⟨jet, ⟨slopeRemainder, interceptRemainder, hexpansion⟩, ?_⟩
  intro other hother
  rcases hother with ⟨otherSlopeRemainder, otherInterceptRemainder,
    hotherExpansion⟩
  exact coefficientDerivativeData_unique data other jet hotherExpansion.1 hjet

end Ipho2026Gpt56solBlind.ProblemIPhO2026_2_C_2
