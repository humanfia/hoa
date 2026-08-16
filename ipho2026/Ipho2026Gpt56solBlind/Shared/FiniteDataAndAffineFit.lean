import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic
import Ipho2026Gpt56solBlind.Shared.FiniteObservations
import Ipho2026Gpt56solBlind.Shared.ExactGraph

/-!
# Finite data and affine-fit protocols

This aggregate module re-exports the finite-observation and exact-graph
constructions and adds answer-free affine fitting.  An `AffineData n` retains
the full ordered `Fin n` coordinate families.  A `FitProtocol n` declares a
finite system of residual equations, while a `FitCertificate` keeps the
candidate intercept and slope explicit.

Unweighted ordinary least squares with an intercept is provided as one
particular two-equation protocol.  It is not built into the generic notion of
fitting.
-/

namespace Ipho2026Gpt56solBlind.Shared.AffineFit

open scoped BigOperators

noncomputable section

/-- An ordered finite family of real predictor coordinates. -/
abbrev PredictorCoordinates (n : ℕ) := Fin n → ℝ

/-- An ordered finite family of real response coordinates. -/
abbrev ResponseCoordinates (n : ℕ) := Fin n → ℝ

/--
Nonempty ordered affine data.  Indexing by `Fin n` preserves sampling order
and multiplicity; the structure contains no fitted parameter.
-/
structure AffineData (n : ℕ) where
  nonempty : 0 < n
  predictor : PredictorCoordinates n
  response : ResponseCoordinates n

namespace AffineData

/-- Ordered affine data are determined by their two coordinate families. -/
theorem ext_coordinates {n : ℕ} {data data' : AffineData n}
    (hPredictor : ∀ i, data.predictor i = data'.predictor i)
    (hResponse : ∀ i, data.response i = data'.response i) :
    data = data' := by
  cases data with
  | mk hNonempty predictor response =>
      cases data' with
      | mk hNonempty' predictor' response' =>
          have hp : predictor = predictor' := funext hPredictor
          have hr : response = response' := funext hResponse
          subst predictor'
          subst response'
          rfl

/-- Extract affine data from an ordered family of real pairs. -/
def ofGraph {n : ℕ} (nonempty : 0 < n) (graph : Fin n → ℝ × ℝ) :
    AffineData n where
  nonempty := nonempty
  predictor := fun i ↦ (graph i).1
  response := fun i ↦ (graph i).2

end AffineData

/--
A data-only affine-fit protocol declares a finite family of residual
equations in a candidate intercept and slope.
-/
structure FitProtocol (n : ℕ) where
  equationCount : ℕ
  equationResidual : AffineData n → Fin equationCount → ℝ → ℝ → ℝ

/-- A candidate pair is certified when it solves every protocol equation. -/
def FitCertificate {n : ℕ} (protocol : FitProtocol n) (data : AffineData n)
    (intercept slope : ℝ) : Prop :=
  ∀ equation,
    protocol.equationResidual data equation intercept slope = 0

namespace FitCertificate

/-- For a fixed protocol, certificates depend extensionally on ordered data. -/
theorem ext_data {n : ℕ} (protocol : FitProtocol n)
    {data data' : AffineData n}
    (hPredictor : ∀ i, data.predictor i = data'.predictor i)
    (hResponse : ∀ i, data.response i = data'.response i)
    (intercept slope : ℝ) :
    FitCertificate protocol data intercept slope ↔
      FitCertificate protocol data' intercept slope := by
  have hData : data = data' :=
    AffineData.ext_coordinates hPredictor hResponse
  subst data'
  rfl

end FitCertificate

namespace FitProtocol

/--
A protocol is well posed for supplied data when it accepts a pair and any two
accepted pairs coincide.
-/
def WellPosed {n : ℕ} (protocol : FitProtocol n) (data : AffineData n) : Prop :=
  (∃ pair : ℝ × ℝ, FitCertificate protocol data pair.1 pair.2) ∧
    ∀ pair pair' : ℝ × ℝ,
      FitCertificate protocol data pair.1 pair.2 ∧
          FitCertificate protocol data pair'.1 pair'.2 →
        pair = pair'

/-- A well-posed protocol has exactly one certificate-bearing pair. -/
theorem existsUnique_fitCertificate {n : ℕ} (protocol : FitProtocol n)
    (data : AffineData n) (wellPosed : protocol.WellPosed data) :
    ∃! pair : ℝ × ℝ, FitCertificate protocol data pair.1 pair.2 := by
  rcases wellPosed with ⟨⟨pair, hPair⟩, hUnique⟩
  refine ⟨pair, hPair, ?_⟩
  intro pair' hPair'
  exact hUnique pair' pair ⟨hPair', hPair⟩

end FitProtocol

/-- Sum of the ordered predictor coordinates. -/
def predictorSum {n : ℕ} (data : AffineData n) : ℝ :=
  ∑ i : Fin n, data.predictor i

/-- Sum of the ordered response coordinates. -/
def responseSum {n : ℕ} (data : AffineData n) : ℝ :=
  ∑ i : Fin n, data.response i

/-- Arithmetic mean of the predictor coordinates. -/
def predictorMean {n : ℕ} (data : AffineData n) : ℝ :=
  predictorSum data / (n : ℝ)

/-- Arithmetic mean of the response coordinates. -/
def responseMean {n : ℕ} (data : AffineData n) : ℝ :=
  responseSum data / (n : ℝ)

/-- Centered predictor sum of squares. -/
def centeredPredictorSumSquares {n : ℕ} (data : AffineData n) : ℝ :=
  ∑ i : Fin n, (data.predictor i - predictorMean data) ^ 2

/-- Population centered predictor variance. -/
def centeredPredictorVariance {n : ℕ} (data : AffineData n) : ℝ :=
  centeredPredictorSumSquares data / (n : ℝ)

/-- Centered predictor--response cross-sum. -/
def centeredPredictorResponseSum {n : ℕ} (data : AffineData n) : ℝ :=
  ∑ i : Fin n,
    (data.predictor i - predictorMean data) *
      (data.response i - responseMean data)

/-- The predictor is nondegenerate when its centered sum of squares is positive. -/
def NondegeneratePredictor {n : ℕ} (data : AffineData n) : Prop :=
  0 < centeredPredictorSumSquares data

/-- Positive centered variance is exactly predictor nondegeneracy. -/
lemma positive_centeredPredictorVariance_iff_nondegeneratePredictor
    {n : ℕ} (data : AffineData n) :
    0 < centeredPredictorVariance data ↔ NondegeneratePredictor data := by
  change
    0 < centeredPredictorSumSquares data / (n : ℝ) ↔
      0 < centeredPredictorSumSquares data
  apply div_pos_iff_of_pos_right
  exact_mod_cast data.nonempty

/-- Nondegeneracy is equivalent to the occurrence of two distinct predictors. -/
lemma nondegeneratePredictor_iff_exists_ne {n : ℕ} (data : AffineData n) :
    NondegeneratePredictor data ↔
      ∃ i j : Fin n, data.predictor i ≠ data.predictor j := by
  constructor
  · intro hNondegenerate
    by_contra hNoDistinct
    have hAllEqual :
        ∀ i j : Fin n, data.predictor i = data.predictor j := by
      intro i j
      by_contra hij
      exact hNoDistinct ⟨i, j, hij⟩
    let i₀ : Fin n := ⟨0, data.nonempty⟩
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt data.nonempty)
    have hPredictorSum :
        predictorSum data = (n : ℝ) * data.predictor i₀ := by
      unfold predictorSum
      calc
        (∑ i : Fin n, data.predictor i) =
            ∑ _i : Fin n, data.predictor i₀ := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hAllEqual i i₀
        _ = (n : ℝ) * data.predictor i₀ := by simp
    have hPredictorMean : predictorMean data = data.predictor i₀ := by
      unfold predictorMean
      rw [hPredictorSum]
      field_simp [hn]
    have hSquaresZero : centeredPredictorSumSquares data = 0 := by
      unfold centeredPredictorSumSquares
      apply Finset.sum_eq_zero
      intro i hi
      rw [hAllEqual i i₀, hPredictorMean]
      ring
    unfold NondegeneratePredictor at hNondegenerate
    rw [hSquaresZero] at hNondegenerate
    linarith
  · rintro ⟨i, j, hij⟩
    unfold NondegeneratePredictor centeredPredictorSumSquares
    apply Finset.sum_pos'
    · intro k hk
      positivity
    · by_cases hi : data.predictor i = predictorMean data
      · have hj : data.predictor j ≠ predictorMean data := by
          intro hj
          apply hij
          exact hi.trans hj.symm
        exact
          ⟨j, Finset.mem_univ j,
            sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
      · exact
          ⟨i, Finset.mem_univ i,
            sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩

/-- Basic centered finite-sum identities for nonempty affine data. -/
lemma centeredIdentities {n : ℕ} (data : AffineData n) :
    (∑ i : Fin n, (data.predictor i - predictorMean data)) = 0 ∧
      (∑ i : Fin n, (data.response i - responseMean data)) = 0 ∧
      centeredPredictorSumSquares data =
        (∑ i : Fin n, (data.predictor i) ^ 2) -
          (predictorSum data) ^ 2 / (n : ℝ) ∧
      centeredPredictorResponseSum data =
        (∑ i : Fin n, data.predictor i * data.response i) -
          predictorSum data * responseSum data / (n : ℝ) ∧
      (∑ i : Fin n, (data.predictor i) ^ 2) =
        centeredPredictorSumSquares data +
          (n : ℝ) * (predictorMean data) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt data.nonempty)
  have hPredictorMean :
      (n : ℝ) * predictorMean data = predictorSum data := by
    unfold predictorMean
    field_simp [hn]
  have hResponseMean :
      (n : ℝ) * responseMean data = responseSum data := by
    unfold responseMean
    field_simp [hn]
  have hCenteredPredictor :
      (∑ i : Fin n, (data.predictor i - predictorMean data)) = 0 := by
    calc
      (∑ i : Fin n, (data.predictor i - predictorMean data)) =
          predictorSum data - (n : ℝ) * predictorMean data := by
            rw [Finset.sum_sub_distrib]
            simp [predictorSum]
      _ = 0 := by rw [hPredictorMean]; ring
  have hCenteredResponse :
      (∑ i : Fin n, (data.response i - responseMean data)) = 0 := by
    calc
      (∑ i : Fin n, (data.response i - responseMean data)) =
          responseSum data - (n : ℝ) * responseMean data := by
            rw [Finset.sum_sub_distrib]
            simp [responseSum]
      _ = 0 := by rw [hResponseMean]; ring
  have hPredictorExpansion :
      centeredPredictorSumSquares data =
        (∑ i : Fin n, (data.predictor i) ^ 2) -
          2 * predictorMean data * predictorSum data +
            (n : ℝ) * (predictorMean data) ^ 2 := by
    unfold centeredPredictorSumSquares
    calc
      (∑ i : Fin n, (data.predictor i - predictorMean data) ^ 2) =
          ∑ i : Fin n,
            ((data.predictor i) ^ 2 -
                2 * predictorMean data * data.predictor i +
              (predictorMean data) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin n, (data.predictor i) ^ 2) -
            (∑ i : Fin n,
              2 * predictorMean data * data.predictor i) +
            (∑ _i : Fin n, (predictorMean data) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ i : Fin n, (data.predictor i) ^ 2) -
            2 * predictorMean data * predictorSum data +
              (n : ℝ) * (predictorMean data) ^ 2 := by
            have hCross :
                (∑ i : Fin n,
                    2 * predictorMean data * data.predictor i) =
                  2 * predictorMean data * predictorSum data := by
              change
                (∑ i : Fin n,
                    (2 * predictorMean data) * data.predictor i) =
                  (2 * predictorMean data) *
                    (∑ i : Fin n, data.predictor i)
              rw [Finset.mul_sum]
            rw [hCross]
            simp
  have hPredictorSquares :
      centeredPredictorSumSquares data =
        (∑ i : Fin n, (data.predictor i) ^ 2) -
          (predictorSum data) ^ 2 / (n : ℝ) := by
    rw [hPredictorExpansion]
    rw [← hPredictorMean]
    field_simp [hn]
    ring
  have hCrossExpansion :
      centeredPredictorResponseSum data =
        (∑ i : Fin n, data.predictor i * data.response i) -
          predictorMean data * responseSum data -
          responseMean data * predictorSum data +
          (n : ℝ) * predictorMean data * responseMean data := by
    unfold centeredPredictorResponseSum
    calc
      (∑ i : Fin n,
          (data.predictor i - predictorMean data) *
            (data.response i - responseMean data)) =
          ∑ i : Fin n,
            (data.predictor i * data.response i -
                predictorMean data * data.response i -
              responseMean data * data.predictor i +
              predictorMean data * responseMean data) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin n, data.predictor i * data.response i) -
            predictorMean data * responseSum data -
            responseMean data * predictorSum data +
            (n : ℝ) * predictorMean data * responseMean data := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            have hMeanResponse :
                (∑ i : Fin n, predictorMean data * data.response i) =
                  predictorMean data * responseSum data := by
              change
                (∑ i : Fin n, predictorMean data * data.response i) =
                  predictorMean data *
                    (∑ i : Fin n, data.response i)
              rw [Finset.mul_sum]
            have hMeanPredictor :
                (∑ i : Fin n, responseMean data * data.predictor i) =
                  responseMean data * predictorSum data := by
              change
                (∑ i : Fin n, responseMean data * data.predictor i) =
                  responseMean data *
                    (∑ i : Fin n, data.predictor i)
              rw [Finset.mul_sum]
            rw [hMeanResponse, hMeanPredictor]
            simp
            ring
  have hPredictorResponse :
      centeredPredictorResponseSum data =
        (∑ i : Fin n, data.predictor i * data.response i) -
          predictorSum data * responseSum data / (n : ℝ) := by
    rw [hCrossExpansion]
    rw [← hPredictorMean, ← hResponseMean]
    field_simp [hn]
    ring
  have hFinal :
      (∑ i : Fin n, (data.predictor i) ^ 2) =
        centeredPredictorSumSquares data +
          (n : ℝ) * (predictorMean data) ^ 2 := by
    rw [hPredictorExpansion, ← hPredictorMean]
    ring
  exact
    ⟨hCenteredPredictor, hCenteredResponse, hPredictorSquares,
      hPredictorResponse, hFinal⟩

/-- Residual of an affine candidate at one indexed occurrence. -/
def residual {n : ℕ} (data : AffineData n) (intercept slope : ℝ)
    (i : Fin n) : ℝ :=
  data.response i - (intercept + slope * data.predictor i)

/-- Sum of squared affine residuals. -/
def residualSumSquares {n : ℕ} (data : AffineData n)
    (intercept slope : ℝ) : ℝ :=
  ∑ i : Fin n, (residual data intercept slope i) ^ 2

/-- The two normal equations for an affine model with an intercept. -/
def AffineNormalEquations {n : ℕ} (data : AffineData n)
    (intercept slope : ℝ) : Prop :=
  (∑ i : Fin n, residual data intercept slope i) = 0 ∧
    (∑ i : Fin n,
      data.predictor i * residual data intercept slope i) = 0

/-- The ordinary affine-fit relation specified by the two normal equations. -/
def IsAffineFit {n : ℕ} (data : AffineData n)
    (intercept slope : ℝ) : Prop :=
  AffineNormalEquations data intercept slope

/-- A candidate has globally least residual sum of squares. -/
def IsLeastResidual {n : ℕ} (data : AffineData n)
    (intercept slope : ℝ) : Prop :=
  ∀ intercept' slope' : ℝ,
    residualSumSquares data intercept slope ≤
      residualSumSquares data intercept' slope'

/-- The explicit two-equation ordinary-least-squares protocol. -/
def ordinaryLeastSquaresProtocol (n : ℕ) : FitProtocol n where
  equationCount := 2
  equationResidual := fun data equation intercept slope ↦
    if equation = (0 : Fin 2) then
      ∑ i : Fin n, residual data intercept slope i
    else
      ∑ i : Fin n,
        data.predictor i * residual data intercept slope i

/-- Certificates for the selected OLS protocol are exactly affine fits. -/
theorem fitCertificate_ordinaryLeastSquaresProtocol_iff
    {n : ℕ} (data : AffineData n) (intercept slope : ℝ) :
    FitCertificate (ordinaryLeastSquaresProtocol n) data intercept slope ↔
      IsAffineFit data intercept slope := by
  change
    (∀ equation : Fin 2,
      (if equation = (0 : Fin 2) then
        ∑ i : Fin n, residual data intercept slope i
      else
        ∑ i : Fin n,
          data.predictor i * residual data intercept slope i) = 0) ↔
      (∑ i : Fin n, residual data intercept slope i) = 0 ∧
        (∑ i : Fin n,
          data.predictor i * residual data intercept slope i) = 0
  constructor
  · intro h
    constructor
    · simpa using h (0 : Fin 2)
    · simpa using h (1 : Fin 2)
  · rintro ⟨hZero, hOne⟩ equation
    have hCases : equation = (0 : Fin 2) ∨ equation = (1 : Fin 2) := by
      omega
    rcases hCases with hEquation | hEquation <;>
      subst equation <;> simp_all

/-- Centered form of the two affine normal equations. -/
lemma normalEquations_iff_centered {n : ℕ} (data : AffineData n)
    (intercept slope : ℝ) :
    AffineNormalEquations data intercept slope ↔
      intercept + slope * predictorMean data = responseMean data ∧
        slope * centeredPredictorSumSquares data =
          centeredPredictorResponseSum data := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt data.nonempty)
  have hPredictorMean :
      (n : ℝ) * predictorMean data = predictorSum data := by
    unfold predictorMean
    field_simp [hn]
  have hResponseMean :
      (n : ℝ) * responseMean data = responseSum data := by
    unfold responseMean
    field_simp [hn]
  rcases centeredIdentities data with
    ⟨hCenteredPredictor, hCenteredResponse, hPredictorSquares,
      hPredictorResponse, hSquaresExpansion⟩
  have hResponseProductExpansion :
      (∑ i : Fin n, data.predictor i * data.response i) =
        centeredPredictorResponseSum data +
          (n : ℝ) * predictorMean data * responseMean data := by
    rw [hPredictorResponse, ← hPredictorMean, ← hResponseMean]
    field_simp [hn]
    ring
  have hResidualExpansion :
      (∑ i : Fin n, residual data intercept slope i) =
        responseSum data - (n : ℝ) * intercept -
          slope * predictorSum data := by
    have hSlopeSum :
        (∑ i : Fin n, slope * data.predictor i) =
          slope * predictorSum data := by
      change
        (∑ i : Fin n, slope * data.predictor i) =
          slope * (∑ i : Fin n, data.predictor i)
      rw [Finset.mul_sum]
    unfold residual
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hSlopeSum]
    simp [predictorSum, responseSum]
    ring
  have hWeightedResidualExpansion :
      (∑ i : Fin n,
          data.predictor i * residual data intercept slope i) =
        (∑ i : Fin n, data.predictor i * data.response i) -
          intercept * predictorSum data -
          slope * (∑ i : Fin n, (data.predictor i) ^ 2) := by
    have hInterceptSum :
        (∑ i : Fin n, intercept * data.predictor i) =
          intercept * predictorSum data := by
      change
        (∑ i : Fin n, intercept * data.predictor i) =
          intercept * (∑ i : Fin n, data.predictor i)
      rw [Finset.mul_sum]
    have hSlopeSquares :
        (∑ i : Fin n, slope * (data.predictor i) ^ 2) =
          slope * (∑ i : Fin n, (data.predictor i) ^ 2) := by
      rw [Finset.mul_sum]
    calc
      (∑ i : Fin n,
          data.predictor i * residual data intercept slope i) =
          ∑ i : Fin n,
            (data.predictor i * data.response i -
              intercept * data.predictor i -
              slope * (data.predictor i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            unfold residual
            ring
      _ = (∑ i : Fin n, data.predictor i * data.response i) -
            (∑ i : Fin n, intercept * data.predictor i) -
            (∑ i : Fin n, slope * (data.predictor i) ^ 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = (∑ i : Fin n, data.predictor i * data.response i) -
            intercept * predictorSum data -
            slope * (∑ i : Fin n, (data.predictor i) ^ 2) := by
            rw [hInterceptSum, hSlopeSquares]
  change
    ((∑ i : Fin n, residual data intercept slope i) = 0 ∧
      (∑ i : Fin n,
        data.predictor i * residual data intercept slope i) = 0) ↔ _
  constructor
  · rintro ⟨hResidual, hWeightedResidual⟩
    rw [hResidualExpansion] at hResidual
    rw [hWeightedResidualExpansion] at hWeightedResidual
    have hFirst :
        intercept + slope * predictorMean data = responseMean data := by
      have hFactor :
          (n : ℝ) *
              (responseMean data -
                (intercept + slope * predictorMean data)) = 0 := by
        calc
          (n : ℝ) *
                (responseMean data -
                  (intercept + slope * predictorMean data)) =
              responseSum data - (n : ℝ) * intercept -
                slope * predictorSum data := by
                  rw [← hResponseMean, ← hPredictorMean]
                  ring
          _ = 0 := hResidual
      have hCenteredZero :
          responseMean data -
              (intercept + slope * predictorMean data) = 0 :=
        (mul_eq_zero.mp hFactor).resolve_left hn
      linarith
    refine ⟨hFirst, ?_⟩
    have hCenteredWeighted :
        centeredPredictorResponseSum data -
            slope * centeredPredictorSumSquares data = 0 := by
      calc
        centeredPredictorResponseSum data -
              slope * centeredPredictorSumSquares data =
            (∑ i : Fin n, data.predictor i * data.response i) -
              intercept * predictorSum data -
              slope * (∑ i : Fin n, (data.predictor i) ^ 2) := by
                rw [hResponseProductExpansion, ← hPredictorMean,
                  hSquaresExpansion, ← hFirst]
                ring
        _ = 0 := hWeightedResidual
    linarith
  · rintro ⟨hFirst, hSlope⟩
    constructor
    · rw [hResidualExpansion]
      calc
        responseSum data - (n : ℝ) * intercept -
              slope * predictorSum data =
            (n : ℝ) *
              (responseMean data -
                (intercept + slope * predictorMean data)) := by
                  rw [← hResponseMean, ← hPredictorMean]
                  ring
        _ = 0 := by rw [← hFirst]; ring
    · rw [hWeightedResidualExpansion]
      calc
        (∑ i : Fin n, data.predictor i * data.response i) -
              intercept * predictorSum data -
              slope * (∑ i : Fin n, (data.predictor i) ^ 2) =
            centeredPredictorResponseSum data -
              slope * centeredPredictorSumSquares data := by
                rw [hResponseProductExpansion, ← hPredictorMean,
                  hSquaresExpansion, ← hFirst]
                ring
        _ = 0 := by linarith

/-- Nondegenerate affine data have exactly one normal-equation fit. -/
theorem existsUnique_isAffineFit {n : ℕ} (data : AffineData n)
    (nondegenerate : NondegeneratePredictor data) :
    ∃! pair : ℝ × ℝ, IsAffineFit data pair.1 pair.2 := by
  have hSquaresNe : centeredPredictorSumSquares data ≠ 0 :=
    ne_of_gt nondegenerate
  let candidateSlope : ℝ :=
    centeredPredictorResponseSum data /
      centeredPredictorSumSquares data
  let candidateIntercept : ℝ :=
    responseMean data - candidateSlope * predictorMean data
  have hCandidateSlope :
      candidateSlope * centeredPredictorSumSquares data =
        centeredPredictorResponseSum data := by
    dsimp [candidateSlope]
    exact div_mul_cancel₀ _ hSquaresNe
  refine ⟨(candidateIntercept, candidateSlope), ?_, ?_⟩
  · change AffineNormalEquations data candidateIntercept candidateSlope
    apply (normalEquations_iff_centered data candidateIntercept candidateSlope).2
    constructor
    · dsimp [candidateIntercept]
      ring
    · exact hCandidateSlope
  · intro pair hPair
    change AffineNormalEquations data pair.1 pair.2 at hPair
    rcases (normalEquations_iff_centered data pair.1 pair.2).1 hPair with
      ⟨hFirst, hSlope⟩
    have hPairSlope : pair.2 = candidateSlope := by
      apply (mul_left_inj' hSquaresNe).mp
      exact hSlope.trans hCandidateSlope.symm
    have hPairIntercept : pair.1 = candidateIntercept := by
      dsimp [candidateIntercept]
      rw [← hPairSlope]
      linarith
    apply Prod.ext
    · simpa using hPairIntercept
    · simpa using hPairSlope

/-- Positive predictor variance makes the selected OLS protocol well posed. -/
theorem ordinaryLeastSquaresProtocol_wellPosed {n : ℕ}
    (data : AffineData n) (positiveVariance : 0 < centeredPredictorVariance data) :
    (ordinaryLeastSquaresProtocol n).WellPosed data := by
  have hNondegenerate : NondegeneratePredictor data :=
    (positive_centeredPredictorVariance_iff_nondegeneratePredictor data).1
      positiveVariance
  rcases existsUnique_isAffineFit data hNondegenerate with
    ⟨pair, hPair, hUnique⟩
  constructor
  · exact
      ⟨pair,
        (fitCertificate_ordinaryLeastSquaresProtocol_iff
          data pair.1 pair.2).2 hPair⟩
  · intro pair' pair'' hCertificates
    have hPair' : IsAffineFit data pair'.1 pair'.2 :=
      (fitCertificate_ordinaryLeastSquaresProtocol_iff
        data pair'.1 pair'.2).1 hCertificates.1
    have hPair'' : IsAffineFit data pair''.1 pair''.2 :=
      (fitCertificate_ordinaryLeastSquaresProtocol_iff
        data pair''.1 pair''.2).1 hCertificates.2
    exact (hUnique pair' hPair').trans (hUnique pair'' hPair'').symm

/-- Positive predictor variance gives a unique selected-protocol certificate. -/
theorem existsUnique_ordinaryLeastSquaresFitCertificate {n : ℕ}
    (data : AffineData n) (positiveVariance : 0 < centeredPredictorVariance data) :
    ∃! pair : ℝ × ℝ,
      FitCertificate (ordinaryLeastSquaresProtocol n) data pair.1 pair.2 := by
  exact
    FitProtocol.existsUnique_fitCertificate
      (ordinaryLeastSquaresProtocol n) data
      (ordinaryLeastSquaresProtocol_wellPosed data positiveVariance)

/-- Change in residual sum of squares under an affine perturbation. -/
lemma residualSumSquares_perturbation {n : ℕ} (data : AffineData n)
    (intercept slope interceptPerturbation slopePerturbation : ℝ) :
    residualSumSquares data (intercept + interceptPerturbation)
          (slope + slopePerturbation) -
        residualSumSquares data intercept slope =
      (∑ i : Fin n,
          (interceptPerturbation +
            slopePerturbation * data.predictor i) ^ 2) -
        2 * interceptPerturbation *
          (∑ i : Fin n, residual data intercept slope i) -
        2 * slopePerturbation *
          (∑ i : Fin n,
            data.predictor i * residual data intercept slope i) := by
  unfold residualSumSquares
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i : Fin n,
        ((residual data (intercept + interceptPerturbation)
              (slope + slopePerturbation) i) ^ 2 -
          (residual data intercept slope i) ^ 2)) =
        ∑ i : Fin n,
          ((interceptPerturbation +
                slopePerturbation * data.predictor i) ^ 2 -
            2 * interceptPerturbation *
              residual data intercept slope i -
            2 * slopePerturbation *
              (data.predictor i * residual data intercept slope i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold residual
          ring
    _ = (∑ i : Fin n,
          (interceptPerturbation +
            slopePerturbation * data.predictor i) ^ 2) -
        2 * interceptPerturbation *
          (∑ i : Fin n, residual data intercept slope i) -
        2 * slopePerturbation *
          (∑ i : Fin n,
            data.predictor i * residual data intercept slope i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      have hInterceptCross :
          (∑ i : Fin n,
              2 * interceptPerturbation *
                residual data intercept slope i) =
            2 * interceptPerturbation *
              (∑ i : Fin n, residual data intercept slope i) := by
        rw [Finset.mul_sum]
      have hSlopeCross :
          (∑ i : Fin n,
              2 * slopePerturbation *
                (data.predictor i * residual data intercept slope i)) =
            2 * slopePerturbation *
              (∑ i : Fin n,
                data.predictor i * residual data intercept slope i) := by
        rw [Finset.mul_sum]
      rw [hInterceptCross, hSlopeCross]

/-- Under nondegeneracy, normal equations characterize global RSS minimizers. -/
theorem isAffineFit_iff_isLeastResidual {n : ℕ} (data : AffineData n)
    (nondegenerate : NondegeneratePredictor data) (intercept slope : ℝ) :
    IsAffineFit data intercept slope ↔
      IsLeastResidual data intercept slope := by
  constructor
  · intro hFit
    change AffineNormalEquations data intercept slope at hFit
    rcases hFit with ⟨hResidual, hWeightedResidual⟩
    change ∀ intercept' slope' : ℝ,
      residualSumSquares data intercept slope ≤
        residualSumSquares data intercept' slope'
    intro intercept' slope'
    have hDifference :=
      residualSumSquares_perturbation data intercept slope
        (intercept' - intercept) (slope' - slope)
    rw [hResidual, hWeightedResidual] at hDifference
    simp only [mul_zero, sub_zero] at hDifference
    have hIntercept :
        intercept + (intercept' - intercept) = intercept' := by
      ring
    have hSlope : slope + (slope' - slope) = slope' := by
      ring
    rw [hIntercept, hSlope] at hDifference
    have hSquaresNonnegative :
        0 ≤ ∑ i : Fin n,
          ((intercept' - intercept) +
            (slope' - slope) * data.predictor i) ^ 2 := by
      apply Finset.sum_nonneg
      intro i hi
      positivity
    linarith
  · intro hLeast
    change ∀ intercept' slope' : ℝ,
      residualSumSquares data intercept slope ≤
        residualSumSquares data intercept' slope' at hLeast
    change AffineNormalEquations data intercept slope
    have hNPos : (0 : ℝ) < n := by
      exact_mod_cast data.nonempty
    have hn : (n : ℝ) ≠ 0 := ne_of_gt hNPos
    let residualTotal : ℝ :=
      ∑ i : Fin n, residual data intercept slope i
    have hInterceptMinimal :=
      hLeast (intercept + residualTotal / (n : ℝ)) slope
    have hInterceptDifferenceNonnegative :
        0 ≤
          residualSumSquares data
              (intercept + residualTotal / (n : ℝ)) slope -
            residualSumSquares data intercept slope :=
      sub_nonneg.mpr hInterceptMinimal
    have hInterceptDifference :
        residualSumSquares data
              (intercept + residualTotal / (n : ℝ)) slope -
            residualSumSquares data intercept slope =
          -(residualTotal ^ 2 / (n : ℝ)) := by
      calc
        residualSumSquares data
                (intercept + residualTotal / (n : ℝ)) slope -
              residualSumSquares data intercept slope =
            (∑ i : Fin n,
                (residualTotal / (n : ℝ) +
                  0 * data.predictor i) ^ 2) -
              2 * (residualTotal / (n : ℝ)) *
                (∑ i : Fin n, residual data intercept slope i) -
              2 * 0 *
                (∑ i : Fin n,
                  data.predictor i * residual data intercept slope i) :=
            by
              simpa only [add_zero] using
                residualSumSquares_perturbation data intercept slope
                  (residualTotal / (n : ℝ)) 0
        _ = -(residualTotal ^ 2 / (n : ℝ)) := by
          simp [residualTotal]
          field_simp [hn]
          ring
    have hResidualTotal : residualTotal = 0 := by
      by_contra hResidualTotalNe
      have hNegative :
          -(residualTotal ^ 2 / (n : ℝ)) < 0 := by
        exact neg_lt_zero.mpr
          (div_pos (sq_pos_of_ne_zero hResidualTotalNe) hNPos)
      linarith
    constructor
    · change residualTotal = 0
      exact hResidualTotal
    · let weightedResidualTotal : ℝ :=
        ∑ i : Fin n,
          data.predictor i * residual data intercept slope i
      let predictorSquareTotal : ℝ :=
        ∑ i : Fin n, (data.predictor i) ^ 2
      rcases centeredIdentities data with
        ⟨hCenteredPredictor, hCenteredResponse, hPredictorSquares,
          hPredictorResponse, hSquareExpansion⟩
      have hSquareTotalExpansion :
          predictorSquareTotal =
            centeredPredictorSumSquares data +
              (n : ℝ) * (predictorMean data) ^ 2 := by
        exact hSquareExpansion
      have hSquareTotalPos : 0 < predictorSquareTotal := by
        rw [hSquareTotalExpansion]
        apply add_pos_of_pos_of_nonneg nondegenerate
        exact mul_nonneg (le_of_lt hNPos) (sq_nonneg _)
      have hSquareTotalNe : predictorSquareTotal ≠ 0 :=
        ne_of_gt hSquareTotalPos
      have hScaledSquares :
          (∑ i : Fin n,
              ((weightedResidualTotal / predictorSquareTotal) *
                data.predictor i) ^ 2) =
            (weightedResidualTotal / predictorSquareTotal) ^ 2 *
              predictorSquareTotal := by
        calc
          (∑ i : Fin n,
              ((weightedResidualTotal / predictorSquareTotal) *
                data.predictor i) ^ 2) =
              ∑ i : Fin n,
                (weightedResidualTotal / predictorSquareTotal) ^ 2 *
                  (data.predictor i) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
          _ = (weightedResidualTotal / predictorSquareTotal) ^ 2 *
                predictorSquareTotal := by
                  change
                    (∑ i : Fin n,
                        (weightedResidualTotal / predictorSquareTotal) ^ 2 *
                          (data.predictor i) ^ 2) =
                      (weightedResidualTotal / predictorSquareTotal) ^ 2 *
                        (∑ i : Fin n, (data.predictor i) ^ 2)
                  rw [Finset.mul_sum]
      have hSlopeMinimal :=
        hLeast intercept
          (slope + weightedResidualTotal / predictorSquareTotal)
      have hSlopeDifferenceNonnegative :
          0 ≤
            residualSumSquares data intercept
                (slope + weightedResidualTotal / predictorSquareTotal) -
              residualSumSquares data intercept slope :=
        sub_nonneg.mpr hSlopeMinimal
      have hSlopeDifference :
          residualSumSquares data intercept
                (slope + weightedResidualTotal / predictorSquareTotal) -
              residualSumSquares data intercept slope =
            -(weightedResidualTotal ^ 2 / predictorSquareTotal) := by
        calc
          residualSumSquares data intercept
                  (slope + weightedResidualTotal / predictorSquareTotal) -
                residualSumSquares data intercept slope =
              (∑ i : Fin n,
                  (0 + (weightedResidualTotal / predictorSquareTotal) *
                    data.predictor i) ^ 2) -
                2 * 0 *
                  (∑ i : Fin n, residual data intercept slope i) -
                2 * (weightedResidualTotal / predictorSquareTotal) *
                  (∑ i : Fin n,
                    data.predictor i * residual data intercept slope i) :=
              by
                simpa only [zero_add, add_zero] using
                  residualSumSquares_perturbation data intercept slope 0
                    (weightedResidualTotal / predictorSquareTotal)
          _ = -(weightedResidualTotal ^ 2 / predictorSquareTotal) := by
            simp only [zero_add, zero_mul, mul_zero, sub_zero]
            rw [hScaledSquares]
            change
              (weightedResidualTotal / predictorSquareTotal) ^ 2 *
                    predictorSquareTotal -
                  2 * (weightedResidualTotal / predictorSquareTotal) *
                    weightedResidualTotal =
                -(weightedResidualTotal ^ 2 / predictorSquareTotal)
            field_simp [hSquareTotalNe]
            ring
      have hWeightedResidualTotal : weightedResidualTotal = 0 := by
        by_contra hWeightedResidualTotalNe
        have hNegative :
            -(weightedResidualTotal ^ 2 / predictorSquareTotal) < 0 := by
          exact neg_lt_zero.mpr
            (div_pos (sq_pos_of_ne_zero hWeightedResidualTotalNe)
              hSquareTotalPos)
        linarith
      change weightedResidualTotal = 0
      exact hWeightedResidualTotal

/-- Selected OLS certificates are exactly global RSS minimizers. -/
theorem fitCertificate_ordinaryLeastSquaresProtocol_iff_isLeastResidual
    {n : ℕ} (data : AffineData n)
    (nondegenerate : NondegeneratePredictor data) (intercept slope : ℝ) :
    FitCertificate (ordinaryLeastSquaresProtocol n) data intercept slope ↔
      IsLeastResidual data intercept slope := by
  exact
    (fitCertificate_ordinaryLeastSquaresProtocol_iff
      data intercept slope).trans
      (isAffineFit_iff_isLeastResidual
        data nondegenerate intercept slope)

end

end Ipho2026Gpt56solBlind.Shared.AffineFit
