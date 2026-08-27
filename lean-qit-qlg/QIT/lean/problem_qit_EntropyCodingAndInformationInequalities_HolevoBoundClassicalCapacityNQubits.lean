import QITBench.Base.OneShot
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITFormalized.HolevoBoundClassicalCapacityNQubits

open QITBench

universe uX uY uH

noncomputable section

/-- A finite ensemble of density states with normalized real probabilities. -/
structure QuantumEnsemble (X : Type uX) (H : Type uH)
    [Fintype X] [Fintype H] [DecidableEq H] where
  probability : X → ℝ
  states : X → State H
  isProbability : OneShot.IsProbabilityDistribution probability

namespace QuantumEnsemble

variable {X : Type uX} {Y : Type uY} {H : Type uH}
variable [Fintype X] [Fintype Y] [DecidableEq Y]
variable [Fintype H] [DecidableEq H]

/-- The average density state `ρ = ∑ x, p_x ρ_x` of an ensemble. -/
noncomputable def averageState (E : QuantumEnsemble X H) : State H where
  matrix := ∑ x, E.probability x • (E.states x).matrix
  pos := by
    apply Matrix.posSemidef_sum Finset.univ
    intro x _
    rw [← Matrix.nonneg_iff_posSemidef]
    exact smul_nonneg (E.isProbability.1 x) (E.states x).pos.nonneg
  trace_eq_one := by
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, State.trace_eq_one, Complex.real_smul, mul_one]
    exact_mod_cast E.isProbability.2

@[simp]
theorem averageState_matrix (E : QuantumEnsemble X H) :
    E.averageState.matrix = ∑ x, E.probability x • (E.states x).matrix :=
  rfl

/-- The joint law of Alice's label and Bob's outcome under a POVM. -/
noncomputable def jointProbability (E : QuantumEnsemble X H) (M : POVM Y H) :
    X × Y → ℝ :=
  fun xy => E.probability xy.1 * (M.prob (E.states xy.1) xy.2 : ℝ)

/-- The ensemble and Born rule induce a normalized joint probability distribution. -/
theorem jointProbability_isProbability (E : QuantumEnsemble X H) (M : POVM Y H) :
    OneShot.IsProbabilityDistribution (E.jointProbability M) := by
  constructor
  · intro xy
    exact mul_nonneg (E.isProbability.1 xy.1) (NNReal.coe_nonneg _)
  · rw [show (∑ xy, E.jointProbability M xy) =
        ∑ x, ∑ y, E.jointProbability M (x, y) by
          exact Fintype.sum_prod_type _]
    simp only [jointProbability]
    calc
      (∑ x, ∑ y, E.probability x * (M.prob (E.states x) y : ℝ)) =
          ∑ x, E.probability x * ∑ y, (M.prob (E.states x) y : ℝ) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
      _ = ∑ x, E.probability x * 1 := by
            apply Finset.sum_congr rfl
            intro x _
            congr 1
            exact_mod_cast M.sum_prob (E.states x)
      _ = 1 := by simpa using E.isProbability.2

end QuantumEnsemble

/-- Shannon entropy in bits of a finite real distribution. -/
noncomputable def shannonEntropy {Z : Type*} [Fintype Z] (p : Z → ℝ) : ℝ :=
  OneShot.schmidtEntropy p

/-- First marginal of a finite joint law. -/
noncomputable def firstMarginal {X : Type*} {Y : Type*}
    [Fintype X] [Fintype Y] (q : X × Y → ℝ) : X → ℝ :=
  fun x => ∑ y, q (x, y)

/-- Second marginal of a finite joint law. -/
noncomputable def secondMarginal {X : Type*} {Y : Type*}
    [Fintype X] [Fintype Y] (q : X × Y → ℝ) : Y → ℝ :=
  fun y => ∑ x, q (x, y)

/-- Classical mutual information `H(X) + H(Y) - H(X,Y)`, measured in bits. -/
noncomputable def classicalMutualInformation {X : Type*} {Y : Type*}
    [Fintype X] [Fintype Y] (q : X × Y → ℝ) : ℝ :=
  shannonEntropy (firstMarginal q) + shannonEntropy (secondMarginal q) -
    shannonEntropy q

/-- Base-2 von Neumann entropy, defined as the Shannon entropy of the eigenvalues. -/
noncomputable def vonNeumannEntropy {H : Type*} [Fintype H] [DecidableEq H]
    (rho : State H) : ℝ :=
  shannonEntropy rho.pos.1.eigenvalues

/-- A finite probability distribution has nonnegative base-2 Shannon entropy. -/
theorem shannonEntropy_nonneg
    {Z : Type*} [Fintype Z] (p : Z → ℝ)
    (hp : OneShot.IsProbabilityDistribution p) :
    0 ≤ shannonEntropy p := by
  have hp_le_one (z : Z) : p z ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun z _ => hp.1 z) (Finset.mem_univ z)
  have hnat : 0 ≤ ∑ z, Real.negMulLog (p z) :=
    Finset.sum_nonneg fun z _ =>
      Real.negMulLog_nonneg (hp.1 z) (hp_le_one z)
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  unfold shannonEntropy OneShot.schmidtEntropy OneShot.log2
  rw [← Finset.sum_neg_distrib]
  calc
    0 ≤ (∑ z, Real.negMulLog (p z)) / Real.log 2 :=
      div_nonneg hnat hlog
    _ = ∑ z, -(p z * (Real.log (p z) / Real.log 2)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      rw [Real.negMulLog]
      ring

/-- The base-2 Shannon entropy of a finite probability distribution is at
most the base-2 logarithm of the size of its alphabet. -/
theorem shannonEntropy_le_log2_card
    {Z : Type*} [Fintype Z] (p : Z → ℝ)
    (hp : OneShot.IsProbabilityDistribution p) :
    shannonEntropy p ≤ OneShot.log2 (Fintype.card Z) := by
  classical
  have hcard : 0 < Fintype.card Z := by
    by_contra h
    have hcard_zero : Fintype.card Z = 0 :=
      Nat.eq_zero_of_not_pos h
    haveI : IsEmpty Z := Fintype.card_eq_zero_iff.mp hcard_zero
    simpa using hp.2
  let c : ℝ := (Fintype.card Z : ℝ)⁻¹
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hw : ∑ _z : Z, c = 1 := by
    simp [c, ne_of_gt hcard]
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _z : Z => c) (p := p)
    (fun _z _ => hc.le) hw (fun z _ => hp.1 z)
  have hnat :
      ∑ z, Real.negMulLog (p z) ≤ Real.log (Fintype.card Z) := by
    have hjensen' :
        c * (∑ z, Real.negMulLog (p z)) ≤ Real.negMulLog c := by
      simpa [← Finset.mul_sum, hp.2] using hjensen
    have hc_log :
        Real.negMulLog c = c * Real.log (Fintype.card Z) := by
      dsimp [c]
      rw [Real.negMulLog, Real.log_inv]
      ring
    rw [hc_log] at hjensen'
    exact le_of_mul_le_mul_left hjensen' hc
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  unfold shannonEntropy OneShot.schmidtEntropy OneShot.log2
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ z, -(p z * (Real.log (p z) / Real.log 2))) =
        (∑ z, Real.negMulLog (p z)) / Real.log 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      rw [Real.negMulLog]
      ring
    _ ≤ Real.log (Fintype.card Z) / Real.log 2 :=
      div_le_div_of_nonneg_right hnat hlog

/-- The eigenvalues of a density state are a finite probability
distribution. -/
theorem stateEigenvalues_isProbability
    {H : Type*} [Fintype H] [DecidableEq H] (rho : State H) :
    OneShot.IsProbabilityDistribution rho.pos.1.eigenvalues := by
  constructor
  · exact rho.pos.eigenvalues_nonneg
  · have htrace := rho.pos.1.trace_eq_sum_eigenvalues
    rw [rho.trace_eq_one] at htrace
    have hre := congrArg Complex.re htrace
    simpa using hre.symm

/-- Von Neumann entropy is nonnegative. -/
theorem vonNeumannEntropy_nonneg
    {H : Type*} [Fintype H] [DecidableEq H] (rho : State H) :
    0 ≤ vonNeumannEntropy rho :=
  shannonEntropy_nonneg _ (stateEigenvalues_isProbability rho)

/-- The entropy of a density state is at most the logarithm of the Hilbert
space dimension. -/
theorem vonNeumannEntropy_le_log2_card
    {H : Type*} [Fintype H] [DecidableEq H] (rho : State H) :
    vonNeumannEntropy rho ≤ OneShot.log2 (Fintype.card H) :=
  shannonEntropy_le_log2_card _ (stateEigenvalues_isProbability rho)

/-- Bob's mutual information with Alice's label for the chosen POVM. -/
noncomputable def measuredMutualInformation
    {X : Type*} {Y : Type*} {H : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype H] [DecidableEq H]
    (E : QuantumEnsemble X H) (M : POVM Y H) : ℝ :=
  classicalMutualInformation (E.jointProbability M)

/-- The Holevo quantity `S(ρ) - ∑ x, p_x S(ρ_x)` of an ensemble. -/
noncomputable def holevoInformation
    {X : Type*} {H : Type*} [Fintype X] [Fintype H] [DecidableEq H]
    (E : QuantumEnsemble X H) : ℝ :=
  vonNeumannEntropy E.averageState -
    ∑ x, E.probability x * vonNeumannEntropy (E.states x)

/-- For any encoding into a system of dimension `2^n` and any POVM, the
Holevo bound implies that Bob obtains at most `n` classical bits. -/
theorem measuredMutualInformation_le_n_of_holevo
    {X : Type uX} {Y : Type uY} {H : Type uH}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype H] [DecidableEq H]
    (n : ℕ) (h_dimension : Fintype.card H = 2 ^ n)
    (E : QuantumEnsemble X H) (M : POVM Y H)
    (h_holevo : measuredMutualInformation E M ≤ holevoInformation E) :
    measuredMutualInformation E M ≤ (n : ℝ) := by
  calc
    measuredMutualInformation E M ≤ holevoInformation E := h_holevo
    _ ≤ vonNeumannEntropy E.averageState := by
      unfold holevoInformation
      exact sub_le_self _ <|
        Finset.sum_nonneg fun x _ =>
          mul_nonneg (E.isProbability.1 x)
            (vonNeumannEntropy_nonneg (E.states x))
    _ ≤ OneShot.log2 (Fintype.card H) :=
      vonNeumannEntropy_le_log2_card E.averageState
    _ = (n : ℝ) := by
      rw [h_dimension]
      unfold OneShot.log2
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      have hlog : Real.log (2 : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_num))
      field_simp

end

end QITFormalized.HolevoBoundClassicalCapacityNQubits
