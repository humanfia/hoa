module

public import QITBench.Base

/-!
# One-shot entanglement-conversion primitives

Shared finite-dimensional surfaces for the OneShot benchmark statements.  The
previous problem files quantified over arbitrary `applyChannel`, `fidelity`, and
LOCC predicates; these definitions pin those notions to concrete `State`,
`Channel`, matrix-fidelity, tensor-power, and Schmidt-vector objects from
`QITBench.Base`.  A full finite-round LOCC syntax is outside the current Base
seed, so `LOCCProtocol` uses the concrete product-Kraus/separable-operation
surface that LOCC protocols induce, rather than caller-supplied behavior.
-/

@[expose] public section

namespace QITBench.OneShot

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- A finite real probability distribution. -/
def IsProbabilityDistribution
    {X : Type*} [Fintype X]
    (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1

/-- Base-2 logarithm. -/
noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Shannon entropy of a Schmidt-coefficient distribution. -/
noncomputable def schmidtEntropy
    {X : Type*} [Fintype X]
    (p : X → ℝ) : ℝ :=
  -∑ x, p x * log2 (p x)

/-- A pure bipartite vector has Schmidt coefficients `p` in the common basis `X`. -/
def HasSchmidtCoefficients
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : PureVector (X × X)) (p : X → ℝ) : Prop :=
  ∀ x y : X,
    psi.amp (x, y) = if x = y then ((Real.sqrt (p x) : ℝ) : ℂ) else 0

/-- Concrete finite-dimensional LOCC/separable protocol surface used by OneShot problems.

Finite-round LOCC channels admit product-Kraus descriptions after expanding the
classical transcript.  This structure stores exactly such local Kraus factors
and a trace-preservation proof, so it cannot wrap an arbitrary global entangling
CPTP map. -/
structure LOCCProtocol
    (A B A' B' : Type*)
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] where
  KrausIndex : Type*
  [fintypeKrausIndex : Fintype KrausIndex]
  leftKraus : KrausIndex → Matrix A' A ℂ
  rightKraus : KrausIndex → Matrix B' B ℂ
  tracePreserving :
    MatrixMap.IsTracePreserving
      (MatrixMap.ofKraus fun k : KrausIndex =>
        Matrix.kronecker (leftKraus k) (rightKraus k))

namespace LOCCProtocol

variable {A B A' B' : Type*}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype A'] [DecidableEq A']
variable [Fintype B'] [DecidableEq B']

/-- The product Kraus operator associated with one classical transcript branch. -/
noncomputable def productKraus (P : LOCCProtocol A B A' B')
    (k : P.KrausIndex) : Matrix (A' × B') (A × B) ℂ :=
  Matrix.kronecker (P.leftKraus k) (P.rightKraus k)

/-- The concrete CPTP channel implemented by the protocol. -/
noncomputable def channel (P : LOCCProtocol A B A' B') : Channel (A × B) (A' × B') := by
  letI := P.fintypeKrausIndex
  exact {
    map := MatrixMap.ofKraus P.productKraus
    completelyPositive := MatrixMap.ofKraus_completelyPositive P.productKraus
    tracePreserving := by
      simpa [productKraus] using P.tracePreserving
    mapsPositive := MatrixMap.ofKraus_mapsPositive P.productKraus
  }

end LOCCProtocol

/-- Matrix square root used in finite-dimensional fidelity. -/
noncomputable def matrixSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : CMatrix d :=
  CFC.sqrt A

/-- Trace norm through the matrix-CFC square root. -/
noncomputable def traceNorm
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (A.conjTranspose * A)))

/-- Unsquared quantum fidelity `Tr sqrt(sqrt(ρ) σ sqrt(ρ))`. -/
noncomputable def quantumFidelity
    {d : Type*} [Fintype d] [DecidableEq d]
    (rho sigma : CMatrix d) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (matrixSqrt rho * sigma * matrixSqrt rho)))

/-- The rate-`R` target Schmidt rank `⌊2^(nR)⌋`. -/
noncomputable def targetRankAtRate (R : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (Real.rpow (2 : ℝ) ((n : ℝ) * R))

/-- Standard maximally entangled vector of Schmidt rank `M`. -/
noncomputable def maximallyEntangledVector (M : ℕ) : (Fin M × Fin M) → ℂ :=
  fun ij => if ij.1 = ij.2 then (((1 : ℝ) / Real.sqrt (M : ℝ)) : ℂ) else 0

/-- Density matrix of the standard rank-`M` maximally entangled state. -/
noncomputable def maximallyEntangledDensity (M : ℕ) : CMatrix (Fin M × Fin M) :=
  rankOneMatrix (maximallyEntangledVector M)

/-- Normalized log-rank of the target maximally entangled state. -/
noncomputable def concentrationRate
    (M : ℕ → ℕ)
    (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * log2 (M n)

/-- `limsup_n (1/n) log₂ M_n ≤ entropy`, written with eventual upper bounds. -/
def AsymptoticRateAtMost
    (entropy : ℝ)
    (M : ℕ → ℕ) : Prop :=
  ∀ R : ℝ,
    entropy < R →
      ∀ᶠ n in Filter.atTop, concentrationRate M n ≤ R

/-- Schmidt coefficients sorted in descending order. -/
def SchmidtCoefficientsSorted
    {d : ℕ}
    (mu : Fin d → ℝ) : Prop :=
  ∀ i j : Fin d, (i : ℕ) ≤ (j : ℕ) → mu j ≤ mu i

/-- Strictly positive normalized Schmidt vector. -/
def IsSchmidtProbabilityVector
    {d : ℕ}
    (mu : Fin d → ℝ) : Prop :=
  SchmidtCoefficientsSorted mu ∧
    (∀ i, 0 < mu i) ∧
      (∑ i, mu i) = 1

/-- The largest Schmidt coefficient of a nonempty sorted vector. -/
def largestSchmidtCoefficient
    {d : ℕ}
    (mu : Fin d → ℝ) (hd : 0 < d) : ℝ :=
  mu ⟨0, hd⟩

/-- The rank-`M` maximally entangled Schmidt vector, padded in an ambient `d`. -/
noncomputable def maximallyEntangledSchmidtCoefficients
    {d : ℕ}
    (M : ℕ) : Fin d → ℝ :=
  fun i => if (i : ℕ) < M then (1 : ℝ) / (M : ℝ) else 0

/-- Sum of the first `k` entries of a vector indexed by `Fin d`. -/
noncomputable def sumFirst
    {d : ℕ}
    (k : ℕ) (v : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, if (i : ℕ) < k then v i else 0

/-- Majorization of descending finite probability vectors. -/
def MajorizedBy
    {d : ℕ}
    (p q : Fin d → ℝ) : Prop :=
  (∀ k : ℕ, k ≤ d → sumFirst k p ≤ sumFirst k q) ∧
    (∑ i, p i) = ∑ i, q i

/-- Nielsen pure-state deterministic LOCC criterion in Schmidt-vector form.

Here `d` is the exact Schmidt rank of the source, so coefficients are strictly
positive; the rank-`M` maximally entangled target is represented in the same
ambient list and therefore requires `M ≤ d`. -/
noncomputable def CanTransformDeterministicallyByLOCC
    {d : ℕ}
    (mu : Fin d → ℝ) (M : ℕ) : Prop :=
  IsSchmidtProbabilityVector mu ∧
    0 < M ∧
      M ≤ d ∧
        MajorizedBy mu (maximallyEntangledSchmidtCoefficients (d := d) M)

end

end QITBench.OneShot
