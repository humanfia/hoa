import QITBench.Base.OneShot
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Achievability of entanglement concentration

A bipartite pure state with Schmidt distribution `p` can be converted by LOCC
to maximally entangled states at every nonnegative rate strictly below the
Schmidt entropy, with fidelity tending to one.
-/

namespace QITFormalized

open Filter QITBench QITBench.OneShot
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

universe uA uB uA' uB'

/-- The party that performs the next local instrument in a finite-round LOCC
protocol. -/
inductive LOCCParty
  | alice
  | bob
  deriving DecidableEq

/-- Operational data for a finite-round LOCC protocol.

At each round, the acting party and its local instrument may depend on the
entire classical transcript of earlier outcomes. The two fixed workspace types
can contain all finite local ancillas used during the protocol. Local
isometries initialize those workspaces, and local channels perform the final
readout into the requested output systems.

The common outcome type is harmless: outcome sets that vary by round and
history can be embedded into one finite tagged outcome type, with zero Kraus
operators on unused tags. -/
structure FiniteRoundLOCCData
    (A : Type uA) (B : Type uB) (A' : Type uA') (B' : Type uB')
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] where
  rounds : ℕ
  Outcome : Type
  [fintypeOutcome : Fintype Outcome]
  AliceWorkspace : Type uA
  [fintypeAliceWorkspace : Fintype AliceWorkspace]
  [decidableEqAliceWorkspace : DecidableEq AliceWorkspace]
  BobWorkspace : Type uB
  [fintypeBobWorkspace : Fintype BobWorkspace]
  [decidableEqBobWorkspace : DecidableEq BobWorkspace]
  aliceInitial : Matrix AliceWorkspace A ℂ
  bobInitial : Matrix BobWorkspace B ℂ
  aliceInitial_isometry :
    Matrix.conjTranspose aliceInitial * aliceInitial = (1 : CMatrix A)
  bobInitial_isometry :
    Matrix.conjTranspose bobInitial * bobInitial = (1 : CMatrix B)
  activeParty :
    (r : Fin rounds) → (Fin r.val → Outcome) → LOCCParty
  aliceRoundKraus :
    (r : Fin rounds) →
      (history : Fin r.val → Outcome) →
        Outcome → CMatrix AliceWorkspace
  bobRoundKraus :
    (r : Fin rounds) →
      (history : Fin r.val → Outcome) →
        Outcome → CMatrix BobWorkspace
  round_complete :
    ∀ (r : Fin rounds) (history : Fin r.val → Outcome),
      match activeParty r history with
      | .alice =>
          ∑ o : Outcome,
              Matrix.conjTranspose (aliceRoundKraus r history o) *
                aliceRoundKraus r history o =
            (1 : CMatrix AliceWorkspace)
      | .bob =>
          ∑ o : Outcome,
              Matrix.conjTranspose (bobRoundKraus r history o) *
                bobRoundKraus r history o =
            (1 : CMatrix BobWorkspace)
  AliceFinalIndex : Type
  [fintypeAliceFinalIndex : Fintype AliceFinalIndex]
  BobFinalIndex : Type
  [fintypeBobFinalIndex : Fintype BobFinalIndex]
  aliceFinal : AliceFinalIndex → Matrix A' AliceWorkspace ℂ
  bobFinal : BobFinalIndex → Matrix B' BobWorkspace ℂ
  aliceFinal_complete :
    ∑ i : AliceFinalIndex,
        Matrix.conjTranspose (aliceFinal i) * aliceFinal i =
      (1 : CMatrix AliceWorkspace)
  bobFinal_complete :
    ∑ i : BobFinalIndex,
        Matrix.conjTranspose (bobFinal i) * bobFinal i =
      (1 : CMatrix BobWorkspace)

namespace FiniteRoundLOCCData

variable {A B A' B' : Type*}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype A'] [DecidableEq A']
variable [Fintype B'] [DecidableEq B']

/-- The prefix of a full transcript visible immediately before round `r`. -/
def history (P : FiniteRoundLOCCData A B A' B')
    (transcript : Fin P.rounds → P.Outcome) (r : Fin P.rounds) :
    Fin r.val → P.Outcome :=
  fun i => transcript ⟨i.val, Nat.lt_trans i.isLt r.isLt⟩

/-- Alice's accumulated local Kraus operator along a complete transcript. -/
noncomputable def aliceAccumulated
    (P : FiniteRoundLOCCData A B A' B')
    (transcript : Fin P.rounds → P.Outcome) :
    Matrix P.AliceWorkspace A ℂ := by
  letI := P.fintypeAliceWorkspace
  letI := P.decidableEqAliceWorkspace
  exact
    (List.ofFn fun r : Fin P.rounds =>
      match P.activeParty r (P.history transcript r) with
      | .alice => P.aliceRoundKraus r (P.history transcript r) (transcript r)
      | .bob => (1 : CMatrix P.AliceWorkspace)).foldl
        (fun accumulated step => step * accumulated) P.aliceInitial

/-- Bob's accumulated local Kraus operator along a complete transcript. -/
noncomputable def bobAccumulated
    (P : FiniteRoundLOCCData A B A' B')
    (transcript : Fin P.rounds → P.Outcome) :
    Matrix P.BobWorkspace B ℂ := by
  letI := P.fintypeBobWorkspace
  letI := P.decidableEqBobWorkspace
  exact
    (List.ofFn fun r : Fin P.rounds =>
      match P.activeParty r (P.history transcript r) with
      | .alice => (1 : CMatrix P.BobWorkspace)
      | .bob => P.bobRoundKraus r (P.history transcript r) (transcript r)).foldl
        (fun accumulated step => step * accumulated) P.bobInitial

/-- A leaf is a full classical transcript together with the two outcomes of
the final local channels. -/
abbrev BranchIndex (P : FiniteRoundLOCCData A B A' B') :=
  (Fin P.rounds → P.Outcome) × (P.AliceFinalIndex × P.BobFinalIndex)

/-- Alice's local Kraus factor at a protocol leaf. -/
noncomputable def leftKraus (P : FiniteRoundLOCCData A B A' B')
    (k : P.BranchIndex) : Matrix A' A ℂ := by
  letI := P.fintypeAliceWorkspace
  exact P.aliceFinal k.2.1 * P.aliceAccumulated k.1

/-- Bob's local Kraus factor at a protocol leaf. -/
noncomputable def rightKraus (P : FiniteRoundLOCCData A B A' B')
    (k : P.BranchIndex) : Matrix B' B ℂ := by
  letI := P.fintypeBobWorkspace
  exact P.bobFinal k.2.2 * P.bobAccumulated k.1

/-- The global product Kraus operator for one transcript leaf. -/
noncomputable def productKraus (P : FiniteRoundLOCCData A B A' B')
    (k : P.BranchIndex) : Matrix (A' × B') (A × B) ℂ :=
  Matrix.kronecker (P.leftKraus k) (P.rightKraus k)

/-- Trace preservation of the transcript-expanded Kraus map. This is
mathematically implied by the local completeness fields; retaining it as
explicit data makes the induced `Channel` available without first developing
that compositional proof. -/
def IsTracePreserving (P : FiniteRoundLOCCData A B A' B') : Prop := by
  letI := P.fintypeOutcome
  letI := P.fintypeAliceFinalIndex
  letI := P.fintypeBobFinalIndex
  exact MatrixMap.IsTracePreserving (MatrixMap.ofKraus P.productKraus)

end FiniteRoundLOCCData

/-- A genuine finite-round LOCC protocol together with trace preservation of
its transcript-expanded channel. Unlike `QITBench.OneShot.LOCCProtocol`, the
local instrument tree and its classical feed-forward data are part of the
witness. -/
structure FiniteRoundLOCCProtocol
    (A : Type uA) (B : Type uB) (A' : Type uA') (B' : Type uB')
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] where
  data : FiniteRoundLOCCData A B A' B'
  tracePreserving : data.IsTracePreserving

namespace FiniteRoundLOCCProtocol

variable {A B A' B' : Type*}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype A'] [DecidableEq A']
variable [Fintype B'] [DecidableEq B']

/-- The CPTP channel implemented by a finite-round adaptive LOCC protocol. -/
noncomputable def channel (P : FiniteRoundLOCCProtocol A B A' B') :
    Channel (A × B) (A' × B') := by
  letI := P.data.fintypeOutcome
  letI := P.data.fintypeAliceFinalIndex
  letI := P.data.fintypeBobFinalIndex
  exact {
    map := MatrixMap.ofKraus P.data.productKraus
    completelyPositive :=
      MatrixMap.ofKraus_completelyPositive P.data.productKraus
    tracePreserving := by
      simpa [FiniteRoundLOCCData.IsTracePreserving] using P.tracePreserving
    mapsPositive :=
      MatrixMap.ofKraus_mapsPositive P.data.productKraus
  }

end FiniteRoundLOCCProtocol

/-- The local Kraus family which discards a finite system into its unique
one-dimensional output. -/
noncomputable def discardToOneKraus
    {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) : Matrix (Fin 1) A ℂ :=
  Matrix.single 0 a 1

private theorem discardToOneKraus_complete
    {A : Type*} [Fintype A] [DecidableEq A] :
    ∑ a : A,
        Matrix.conjTranspose (discardToOneKraus a) *
          discardToOneKraus a =
      (1 : CMatrix A) := by
  ext i j
  simp [discardToOneKraus, Matrix.sum_single_one]

/-- A zero-round LOCC protocol which locally discards both input systems. -/
noncomputable def discardToOneData
    (A : Type*) (B : Type*)
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] :
    FiniteRoundLOCCData A B (Fin 1) (Fin 1) where
  rounds := 0
  Outcome := PUnit
  AliceWorkspace := A
  BobWorkspace := B
  aliceInitial := 1
  bobInitial := 1
  aliceInitial_isometry := by simp
  bobInitial_isometry := by simp
  activeParty := fun r => Fin.elim0 r
  aliceRoundKraus := fun r => Fin.elim0 r
  bobRoundKraus := fun r => Fin.elim0 r
  round_complete := fun r => Fin.elim0 r
  AliceFinalIndex := Fin (Fintype.card A)
  BobFinalIndex := Fin (Fintype.card B)
  aliceFinal := fun i => discardToOneKraus ((Fintype.equivFin A).symm i)
  bobFinal := fun i => discardToOneKraus ((Fintype.equivFin B).symm i)
  aliceFinal_complete := by
    calc
      ∑ i : Fin (Fintype.card A),
          Matrix.conjTranspose
              (discardToOneKraus ((Fintype.equivFin A).symm i)) *
            discardToOneKraus ((Fintype.equivFin A).symm i) =
          ∑ a : A,
            Matrix.conjTranspose (discardToOneKraus a) *
              discardToOneKraus a := by
                apply Fintype.sum_equiv (Fintype.equivFin A).symm
                intro i
                rfl
      _ = 1 := discardToOneKraus_complete
  bobFinal_complete := by
    calc
      ∑ i : Fin (Fintype.card B),
          Matrix.conjTranspose
              (discardToOneKraus ((Fintype.equivFin B).symm i)) *
            discardToOneKraus ((Fintype.equivFin B).symm i) =
          ∑ b : B,
            Matrix.conjTranspose (discardToOneKraus b) *
              discardToOneKraus b := by
                apply Fintype.sum_equiv (Fintype.equivFin B).symm
                intro i
                rfl
      _ = 1 := discardToOneKraus_complete

private theorem discardToOneData_productKraus
    {A : Type*} {B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (k : (discardToOneData A B).BranchIndex) :
    (discardToOneData A B).productKraus k =
      Matrix.kronecker
        (discardToOneKraus ((Fintype.equivFin A).symm k.2.1))
        (discardToOneKraus ((Fintype.equivFin B).symm k.2.2)) := by
  simp only [FiniteRoundLOCCData.productKraus, FiniteRoundLOCCData.leftKraus,
    FiniteRoundLOCCData.rightKraus, FiniteRoundLOCCData.aliceAccumulated,
    FiniteRoundLOCCData.bobAccumulated, discardToOneData, List.ofFn_zero,
    List.foldl_nil]
  congr 1 <;> exact Matrix.mul_one _

private theorem conjTranspose_kronecker_mul_self
    {A A' B B' : Type*}
    [Fintype A'] [Fintype B']
    (L : Matrix A' A ℂ) (R : Matrix B' B ℂ) :
    Matrix.conjTranspose (Matrix.kronecker L R) *
        Matrix.kronecker L R =
      Matrix.kronecker
        (Matrix.conjTranspose L * L)
        (Matrix.conjTranspose R * R) := by
  calc
    Matrix.conjTranspose (Matrix.kronecker L R) *
        Matrix.kronecker L R =
      Matrix.kronecker (Matrix.conjTranspose L) (Matrix.conjTranspose R) *
        Matrix.kronecker L R := by
          congr 1
          simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker L R
    _ = Matrix.kronecker
        (Matrix.conjTranspose L * L)
        (Matrix.conjTranspose R * R) := by
          exact (Matrix.mul_kronecker_mul
            (Matrix.conjTranspose L) L
            (Matrix.conjTranspose R) R).symm

private theorem discardToOneData_tracePreserving
    {A : Type*} {B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] :
    (discardToOneData A B).IsTracePreserving := by
  letI := (discardToOneData A B).fintypeOutcome
  letI := (discardToOneData A B).fintypeAliceFinalIndex
  letI := (discardToOneData A B).fintypeBobFinalIndex
  let K := (discardToOneData A B).productKraus
  apply MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one K
  dsimp [K]
  unfold MatrixMap.krausAdjoint
  simp_rw [discardToOneData_productKraus]
  simp only [Matrix.mul_one]
  simp_rw [conjTranspose_kronecker_mul_self]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  have hA := congrArg (fun M : CMatrix A => M ia ja)
    (discardToOneData A B).aliceFinal_complete
  dsimp only at hA
  simp only [discardToOneData] at hA
  have hA' :
      (∑ x : Fin (Fintype.card A),
        (Matrix.conjTranspose
              (discardToOneKraus ((Fintype.equivFin A).symm x)) *
            discardToOneKraus ((Fintype.equivFin A).symm x)) ia ja) =
        (1 : CMatrix A) ia ja := by
    rw [← Matrix.sum_apply]
    exact hA
  have hB := congrArg (fun M : CMatrix B => M ib jb)
    (discardToOneData A B).bobFinal_complete
  dsimp only at hB
  simp only [discardToOneData] at hB
  have hB' :
      (∑ x : Fin (Fintype.card B),
        (Matrix.conjTranspose
              (discardToOneKraus ((Fintype.equivFin B).symm x)) *
            discardToOneKraus ((Fintype.equivFin B).symm x)) ib jb) =
        (1 : CMatrix B) ib jb := by
    rw [← Matrix.sum_apply]
    exact hB
  rw [Fintype.sum_prod_type]
  letI :
      Unique
        (Fin (discardToOneData A B).rounds →
          (discardToOneData A B).Outcome) :=
    { default := fun i => Fin.elim0 i
      uniq := by
        intro f
        funext i
        exact Fin.elim0 i }
  rw [Fintype.sum_unique]
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [← Finset.sum_mul_sum]
  calc
    _ = (1 : CMatrix A) ia ja * (1 : CMatrix B) ib jb :=
      congrArg₂ (· * ·) hA' hB'
    _ = (1 : CMatrix (A × B)) (ia, ib) (ja, jb) := by
      simp only [Matrix.one_apply]
      by_cases ha : ia = ja <;> by_cases hb : ib = jb <;> simp [ha, hb]

/-- The finite-round LOCC protocol induced by `discardToOneData`. -/
noncomputable def discardToOneProtocol
    (A : Type*) (B : Type*)
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] :
    FiniteRoundLOCCProtocol A B (Fin 1) (Fin 1) where
  data := discardToOneData A B
  tracePreserving := discardToOneData_tracePreserving

private theorem state_matrix_eq_one_on_finOneProd
    (ρ : State (Fin 1 × Fin 1)) :
    ρ.matrix = 1 := by
  ext i j
  have hi : i = (0, 0) := Subsingleton.elim _ _
  have hj : j = (0, 0) := Subsingleton.elim _ _
  subst i
  subst j
  have htrace := ρ.trace_eq_one
  simpa [Matrix.trace, Fintype.sum_prod_type] using htrace

private theorem maximallyEntangledDensity_one :
    maximallyEntangledDensity 1 = (1 : CMatrix (Fin 1 × Fin 1)) := by
  ext i j
  have hi : i = (0, 0) := Subsingleton.elim _ _
  have hj : j = (0, 0) := Subsingleton.elim _ _
  subst i
  subst j
  rw [maximallyEntangledDensity, rankOneMatrix_apply]
  norm_num [maximallyEntangledVector]

private theorem quantumFidelity_one_finOneProd :
    quantumFidelity
        (1 : CMatrix (Fin 1 × Fin 1))
        (1 : CMatrix (Fin 1 × Fin 1)) =
      1 := by
  simp [quantumFidelity, matrixSqrt]

/-- The product probability of an IID Schmidt string. -/
private noncomputable def iidSchmidtWeight
    {X : Type*} (p : X → ℝ) :
    (n : ℕ) → QITBench.TensorPower X n → ℝ
  | 0, _ => 1
  | n + 1, xs => p xs.1 * iidSchmidtWeight p n xs.2

private theorem iidSchmidtWeight_nonneg
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ (n : ℕ) (xs : QITBench.TensorPower X n),
      0 ≤ iidSchmidtWeight p n xs := by
  intro n
  induction n with
  | zero =>
      intro xs
      simp [iidSchmidtWeight]
  | succ n ih =>
      intro xs
      exact mul_nonneg (hp.1 xs.1) (ih xs.2)

private theorem iidSchmidtWeight_sum
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ n : ℕ,
      ∑ xs : QITBench.TensorPower X n, iidSchmidtWeight p n xs = 1 := by
  intro n
  induction n with
  | zero =>
      simp [QITBench.TensorPower, iidSchmidtWeight]
  | succ n ih =>
      let e :
          QITBench.TensorPower X (n + 1) ≃
            X × QITBench.TensorPower X n :=
        Equiv.refl _
      calc
        ∑ xs : QITBench.TensorPower X (n + 1),
            iidSchmidtWeight p (n + 1) xs =
            ∑ xs : X × QITBench.TensorPower X n,
              p xs.1 * iidSchmidtWeight p n xs.2 := by
                apply Fintype.sum_equiv e
                intro xs
                rfl
        _ = ∑ x : X, ∑ xs : QITBench.TensorPower X n,
              p x * iidSchmidtWeight p n xs := by
                rw [Fintype.sum_prod_type]
        _ = 1 := by
          simp_rw [← Finset.mul_sum]
          rw [ih]
          simpa using hp.2

/-- The number of occurrences of one alphabet symbol in a tensor-power
string. -/
private def tensorPowerSymbolCount
    {X : Type*} [DecidableEq X] (a : X) :
    (n : ℕ) → QITBench.TensorPower X n → ℕ
  | 0, _ => 0
  | n + 1, xs =>
      (if xs.1 = a then 1 else 0) +
        tensorPowerSymbolCount a n xs.2

private theorem tensorPowerSymbolCount_le
    {X : Type*} [DecidableEq X] (a : X) :
    ∀ (n : ℕ) (xs : QITBench.TensorPower X n),
      tensorPowerSymbolCount a n xs ≤ n := by
  intro n
  induction n with
  | zero =>
      intro xs
      simp [tensorPowerSymbolCount]
  | succ n ih =>
      intro xs
      have htail := ih xs.2
      by_cases h : xs.1 = a <;>
        simp [tensorPowerSymbolCount, h] <;> omega

/-- An empirical type records every symbol count in a length-`n` string. -/
private abbrev TensorPowerEmpiricalType (X : Type*) (n : ℕ) :=
  X → Fin (n + 1)

private def tensorPowerEmpiricalType
    {X : Type*} [DecidableEq X] (n : ℕ)
    (xs : QITBench.TensorPower X n) :
    TensorPowerEmpiricalType X n :=
  fun a =>
    ⟨tensorPowerSymbolCount a n xs,
      Nat.lt_succ_of_le (tensorPowerSymbolCount_le a n xs)⟩

private theorem iidSchmidtWeight_eq_prod_pow_count
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) :
    ∀ (n : ℕ) (xs : QITBench.TensorPower X n),
      iidSchmidtWeight p n xs =
        ∏ a : X, p a ^ tensorPowerSymbolCount a n xs := by
  intro n
  induction n with
  | zero =>
      intro xs
      simp [iidSchmidtWeight, tensorPowerSymbolCount]
  | succ n ih =>
      intro xs
      calc
        iidSchmidtWeight p (n + 1) xs =
            p xs.1 * iidSchmidtWeight p n xs.2 := rfl
        _ = p xs.1 *
            ∏ a : X, p a ^ tensorPowerSymbolCount a n xs.2 := by
              rw [ih]
        _ = (∏ a : X, if xs.1 = a then p a else 1) *
            ∏ a : X, p a ^ tensorPowerSymbolCount a n xs.2 := by
              simp
        _ = ∏ a : X,
            (if xs.1 = a then p a else 1) *
              p a ^ tensorPowerSymbolCount a n xs.2 := by
                rw [Finset.prod_mul_distrib]
        _ = ∏ a : X,
            p a ^ tensorPowerSymbolCount a (n + 1) xs := by
              apply Finset.prod_congr rfl
              intro a ha
              by_cases h : xs.1 = a
              · subst a
                simp only [tensorPowerSymbolCount, if_pos]
                rw [pow_add]
                simp
              · simp [tensorPowerSymbolCount, h]

/-- IID strings of the same empirical type have exactly the same Schmidt
weight. -/
private theorem iidSchmidtWeight_eq_of_symbolCount_eq
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (n : ℕ)
    (xs ys : QITBench.TensorPower X n)
    (hcount :
      ∀ a : X,
        tensorPowerSymbolCount a n xs =
          tensorPowerSymbolCount a n ys) :
    iidSchmidtWeight p n xs = iidSchmidtWeight p n ys := by
  rw [iidSchmidtWeight_eq_prod_pow_count,
    iidSchmidtWeight_eq_prod_pow_count]
  apply Finset.prod_congr rfl
  intro a ha
  rw [hcount a]

/-- The finite empirical type class containing `xs`. -/
private def tensorPowerTypeClass
    {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (xs : QITBench.TensorPower X n) :
    Finset (QITBench.TensorPower X n) :=
  Finset.univ.filter fun ys =>
    ∀ a : X,
      tensorPowerSymbolCount a n ys =
        tensorPowerSymbolCount a n xs

private theorem mem_tensorPowerTypeClass_self
    {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (xs : QITBench.TensorPower X n) :
    xs ∈ tensorPowerTypeClass n xs := by
  simp [tensorPowerTypeClass]

private theorem iidSchmidtWeight_eq_of_mem_typeClass
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (n : ℕ)
    (xs ys : QITBench.TensorPower X n)
    (hys : ys ∈ tensorPowerTypeClass n xs) :
    iidSchmidtWeight p n ys = iidSchmidtWeight p n xs := by
  apply iidSchmidtWeight_eq_of_symbolCount_eq
  simpa [tensorPowerTypeClass] using hys

/-- Alice's orthogonal projector for one empirical type outcome. -/
private noncomputable def empiricalTypeProjector
    {X : Type*} [Fintype X] [DecidableEq X] (n : ℕ)
    (q : TensorPowerEmpiricalType X n) :
    CMatrix (QITBench.TensorPower X n) :=
  Matrix.diagonal fun xs =>
    if tensorPowerEmpiricalType n xs = q then 1 else 0

private theorem empiricalTypeProjector_selfAdjoint
    {X : Type*} [Fintype X] [DecidableEq X] (n : ℕ)
    (q : TensorPowerEmpiricalType X n) :
    Matrix.conjTranspose (empiricalTypeProjector n q) =
      empiricalTypeProjector n q := by
  ext xs ys
  by_cases hxy : xs = ys
  · subst ys
    simp [empiricalTypeProjector, Matrix.conjTranspose_apply]
  · have hyx : ys ≠ xs := Ne.symm hxy
    simp [empiricalTypeProjector, Matrix.conjTranspose_apply, hxy, hyx]

private theorem empiricalTypeProjector_mul_self
    {X : Type*} [Fintype X] [DecidableEq X] (n : ℕ)
    (q : TensorPowerEmpiricalType X n) :
    empiricalTypeProjector n q * empiricalTypeProjector n q =
      empiricalTypeProjector n q := by
  rw [empiricalTypeProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext xs
  by_cases h : tensorPowerEmpiricalType n xs = q <;> simp [h]

/-- The empirical-type projectors form a complete local measurement. -/
private theorem empiricalTypeProjector_complete
    {X : Type*} [Fintype X] [DecidableEq X] (n : ℕ) :
    ∑ q : TensorPowerEmpiricalType X n,
        Matrix.conjTranspose (empiricalTypeProjector n q) *
          empiricalTypeProjector n q =
      (1 : CMatrix (QITBench.TensorPower X n)) := by
  simp_rw [empiricalTypeProjector_selfAdjoint,
    empiricalTypeProjector_mul_self]
  ext xs ys
  by_cases hxy : xs = ys
  · subst ys
    simp [Matrix.sum_apply, empiricalTypeProjector]
  · simp [Matrix.sum_apply, empiricalTypeProjector, hxy]

/-- The diagonal Schmidt amplitude of an IID string pair. -/
private noncomputable def iidSchmidtAmplitude
    {X : Type*} [DecidableEq X] (p : X → ℝ) :
    (n : ℕ) →
      QITBench.TensorPower X n → QITBench.TensorPower X n → ℂ
  | 0, _, _ => 1
  | n + 1, xs, ys =>
      if xs.1 = ys.1 then
        ((Real.sqrt (p xs.1) : ℝ) : ℂ) *
          iidSchmidtAmplitude p n xs.2 ys.2
      else 0

private theorem iidSchmidtAmplitude_eq
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ (n : ℕ)
      (xs ys : QITBench.TensorPower X n),
      iidSchmidtAmplitude p n xs ys =
        if xs = ys then
          ((Real.sqrt (iidSchmidtWeight p n xs) : ℝ) : ℂ)
        else 0 := by
  intro n
  induction n with
  | zero =>
      intro xs ys
      cases xs
      cases ys
      simp [iidSchmidtAmplitude, iidSchmidtWeight]
  | succ n ih =>
      intro xs ys
      by_cases hhead : xs.1 = ys.1
      · by_cases htail : xs.2 = ys.2
        · have hxy : xs = ys := by
            cases xs
            cases ys
            simp_all
          simp only [iidSchmidtAmplitude, if_true, ih, iidSchmidtWeight, hxy]
          exact_mod_cast
            (Real.sqrt_mul (hp.1 ys.1)
              (iidSchmidtWeight p n ys.2)).symm
        · have hxy : xs ≠ ys := by
            intro h
            exact htail (congrArg Prod.snd h)
          simp [iidSchmidtAmplitude, hhead, ih, htail, hxy]
      · have hxy : xs ≠ ys := by
          intro h
          exact hhead (congrArg Prod.fst h)
        simp [iidSchmidtAmplitude, hhead, hxy]

/-- The recursively factored amplitude of a bipartite tensor power. -/
private noncomputable def tensorPowerBipartiteAmplitude
    {X : Type*} [Fintype X] [DecidableEq X]
    (ψ : PureVector (X × X)) :
    (n : ℕ) →
      QITBench.TensorPower X n → QITBench.TensorPower X n → ℂ
  | 0, _, _ => 1
  | n + 1, xs, ys =>
      ψ.amp (xs.1, ys.1) *
        tensorPowerBipartiteAmplitude ψ n xs.2 ys.2

private theorem tensorPowerBipartiteAmplitude_eq_iid
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (ψ : PureVector (X × X))
    (hψ : HasSchmidtCoefficients ψ p) :
    ∀ (n : ℕ)
      (xs ys : QITBench.TensorPower X n),
      tensorPowerBipartiteAmplitude ψ n xs ys =
        iidSchmidtAmplitude p n xs ys := by
  intro n
  induction n with
  | zero =>
      intro xs ys
      rfl
  | succ n ih =>
      intro xs ys
      rw [tensorPowerBipartiteAmplitude, iidSchmidtAmplitude, hψ, ih]
      by_cases h : xs.1 = ys.1 <;> simp [h]

private theorem tensorPowerBipartite_matrix_apply
    {X : Type*} [Fintype X] [DecidableEq X]
    (ψ : PureVector (X × X)) :
    ∀ (n : ℕ)
      (i j :
        QITBench.TensorPower X n × QITBench.TensorPower X n),
      (ψ.state.tensorPowerBipartite n).matrix i j =
        tensorPowerBipartiteAmplitude ψ n i.1 i.2 *
          star (tensorPowerBipartiteAmplitude ψ n j.1 j.2) := by
  intro n
  induction n with
  | zero =>
      intro i j
      rcases i with ⟨ia, ib⟩
      rcases j with ⟨ja, jb⟩
      cases ia
      cases ib
      cases ja
      cases jb
      simp [State.tensorPowerBipartite, State.tensorPower,
        QITBench.tensorPowerProdEquiv, State.reindex, State.unit,
        tensorPowerBipartiteAmplitude]
  | succ n ih =>
      intro i j
      rcases i with ⟨⟨ia, ias⟩, ⟨ib, ibs⟩⟩
      rcases j with ⟨⟨ja, jas⟩, ⟨jb, jbs⟩⟩
      change
        (ψ.state.tensorPower (n + 1)).matrix
            ((ia, ib), (QITBench.tensorPowerProdEquiv X X n).symm (ias, ibs))
            ((ja, jb), (QITBench.tensorPowerProdEquiv X X n).symm (jas, jbs)) =
          _
      simp only [State.tensorPower, State.prod, Matrix.kronecker,
        Matrix.kroneckerMap_apply, PureVector.state_matrix_apply,
        tensorPowerBipartiteAmplitude]
      have hrest := ih (ias, ibs) (jas, jbs)
      change
        (ψ.state.tensorPower n).matrix
            ((QITBench.tensorPowerProdEquiv X X n).symm (ias, ibs))
            ((QITBench.tensorPowerProdEquiv X X n).symm (jas, jbs)) =
          _ at hrest
      rw [hrest]
      rw [star_mul']
      ring

private theorem tensorPowerBipartite_matrix_eq_iid
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (ψ : PureVector (X × X))
    (hψ : HasSchmidtCoefficients ψ p) (n : ℕ) :
    (ψ.state.tensorPowerBipartite n).matrix =
      rankOneMatrix
        (fun i : QITBench.TensorPower X n × QITBench.TensorPower X n =>
          iidSchmidtAmplitude p n i.1 i.2) := by
  ext i j
  rw [tensorPowerBipartite_matrix_apply,
    tensorPowerBipartiteAmplitude_eq_iid p ψ hψ n i.1 i.2,
    tensorPowerBipartiteAmplitude_eq_iid p ψ hψ n j.1 j.2]
  simp only [rankOneMatrix_apply]

/-- The coordinates which are strictly between the two endpoints of the unit
interval. This is the termination measure for the finite dependent-rounding
argument below. -/
private noncomputable def fractionalIndices
    {D : Type*} [Fintype D] (r : D → ℝ) : Finset D := by
  classical
  exact Finset.univ.filter fun i => r i ≠ 0 ∧ r i ≠ 1

/-- The `0`-`1` vectors with exactly `M` nonzero coordinates. -/
private noncomputable def uniformSubsetVectors
    (D : Type*) [Fintype D] (M : ℕ) : Set (D → ℝ) :=
  {v | (∀ i, v i = 0 ∨ v i = 1) ∧ ∑ i, v i = (M : ℝ)}

private theorem exists_two_fractional_of_sum_nat
    {D : Type*} [Fintype D] [DecidableEq D]
    (r : D → ℝ) (M : ℕ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hsum : ∑ i, r i = (M : ℝ))
    (hne : ∃ i, r i ≠ 0 ∧ r i ≠ 1) :
    ∃ i j,
      i ≠ j ∧
        r i ≠ 0 ∧ r i ≠ 1 ∧ r j ≠ 0 ∧ r j ≠ 1 := by
  classical
  obtain ⟨i, hi0, hi1⟩ := hne
  by_contra hpair
  push Not at hpair
  have hother : ∀ j, j ≠ i → r j = 0 ∨ r j = 1 := by
    intro j hji
    by_cases hj0 : r j = 0
    · exact Or.inl hj0
    · by_cases hj1 : r j = 1
      · exact Or.inr hj1
      · exact (hj1 (hpair i j hji.symm hi0 hi1 hj0)).elim
  let S : Finset D :=
    (Finset.univ.erase i).filter fun j => r j = 1
  have hsumErase :
      ∑ j ∈ Finset.univ.erase i, r j = (S.card : ℝ) := by
    calc
      ∑ j ∈ Finset.univ.erase i, r j =
          ∑ j ∈ Finset.univ.erase i,
            if r j = 1 then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              have hji : j ≠ i := by simpa using hj
              rcases hother j hji with hj0 | hj1
              · simp [hj0]
              · simp [hj1]
      _ = (S.card : ℝ) := by simp [S]
  have hsplit : r i + (S.card : ℝ) = (M : ℝ) := by
    rw [← hsumErase, ← hsum]
    exact Finset.add_sum_erase Finset.univ
      (fun j => r j) (Finset.mem_univ i)
  have hriPos : 0 < r i :=
    lt_of_le_of_ne (hr0 i) (Ne.symm hi0)
  have hriLt : r i < 1 :=
    lt_of_le_of_ne (hr1 i) hi1
  have hcardLtReal : (S.card : ℝ) < (M : ℝ) := by
    linarith
  have hMLtReal : (M : ℝ) < (S.card : ℝ) + 1 := by
    linarith
  have hcardLt : S.card < M := by
    exact_mod_cast hcardLtReal
  have hMLt : M < S.card + 1 := by
    exact_mod_cast hMLtReal
  omega

private theorem sum_two_updates
    {D : Type*} [Fintype D] [DecidableEq D]
    (r : D → ℝ) (i j : D) (hij : i ≠ j) (a : ℝ) :
    ∑ k,
        Function.update
          (Function.update r i (r i + a)) j (r j - a) k =
      ∑ k, r k := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [Finset.sum_update_of_mem (s := Finset.univ.erase j)
    (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)]
  rw [Finset.sdiff_singleton_eq_erase]
  calc
    r j - a +
          (r i + a +
            ∑ x ∈ (Finset.univ.erase j).erase i, r x) =
        (∑ x ∈ (Finset.univ.erase j).erase i, r x) +
          r i + r j := by ring
    _ = (∑ x ∈ Finset.univ.erase j, r x) + r j := by
      rw [Finset.sum_erase_add (Finset.univ.erase j) r
        (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)]
    _ = ∑ k, r k :=
      Finset.sum_erase_add Finset.univ r (Finset.mem_univ j)

/-- A non-vertex point of the hypersimplex is a strict convex combination of
two points with fewer fractional coordinates. -/
private theorem exists_fractional_split
    {D : Type*} [Fintype D] [DecidableEq D]
    (r : D → ℝ) (M : ℕ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hsum : ∑ i, r i = (M : ℝ))
    (hne : (fractionalIndices r).Nonempty) :
    ∃ rplus rminus : D → ℝ, ∃ t : ℝ,
      0 < t ∧ t < 1 ∧
      (∀ i, 0 ≤ rplus i) ∧
      (∀ i, rplus i ≤ 1) ∧
      (∑ i, rplus i = (M : ℝ)) ∧
      (∀ i, 0 ≤ rminus i) ∧
      (∀ i, rminus i ≤ 1) ∧
      (∑ i, rminus i = (M : ℝ)) ∧
      (fractionalIndices rplus).card <
        (fractionalIndices r).card ∧
      (fractionalIndices rminus).card <
        (fractionalIndices r).card ∧
      r = (1 - t) • rminus + t • rplus := by
  classical
  have hex : ∃ i, r i ≠ 0 ∧ r i ≠ 1 := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  obtain ⟨i, j, hij, hi0, hi1, hj0, hj1⟩ :=
    exists_two_fractional_of_sum_nat r M hr0 hr1 hsum hex
  have hiPos : 0 < r i :=
    lt_of_le_of_ne (hr0 i) (Ne.symm hi0)
  have hiLt : r i < 1 :=
    lt_of_le_of_ne (hr1 i) hi1
  have hjPos : 0 < r j :=
    lt_of_le_of_ne (hr0 j) (Ne.symm hj0)
  have hjLt : r j < 1 :=
    lt_of_le_of_ne (hr1 j) hj1
  let a : ℝ := min (1 - r i) (r j)
  let b : ℝ := min (r i) (1 - r j)
  have haPos : 0 < a :=
    lt_min (sub_pos.mpr hiLt) hjPos
  have hbPos : 0 < b :=
    lt_min hiPos (sub_pos.mpr hjLt)
  have habPos : 0 < a + b :=
    add_pos haPos hbPos
  let rplus : D → ℝ :=
    Function.update
      (Function.update r i (r i + a)) j (r j - a)
  let rminus : D → ℝ :=
    Function.update
      (Function.update r i (r i - b)) j (r j + b)
  let t : ℝ := b / (a + b)
  have htPos : 0 < t :=
    div_pos hbPos habPos
  have htLt : t < 1 :=
    (div_lt_one habPos).mpr (by linarith)
  have ha_le_i : a ≤ 1 - r i :=
    min_le_left _ _
  have ha_le_j : a ≤ r j :=
    min_le_right _ _
  have hb_le_i : b ≤ r i :=
    min_le_left _ _
  have hb_le_j : b ≤ 1 - r j :=
    min_le_right _ _
  have hrplus0 : ∀ k, 0 ≤ rplus k := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa [rplus, Function.update_of_ne hij] using
        add_nonneg (hr0 i) haPos.le
    · by_cases hkj : k = j
      · subst k
        simp [rplus]
        linarith
      · simp [rplus, Function.update_of_ne hki,
          Function.update_of_ne hkj, hr0]
  have hrplus1 : ∀ k, rplus k ≤ 1 := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [rplus, Function.update_of_ne hij]
      linarith
    · by_cases hkj : k = j
      · subst k
        simp [rplus]
        linarith
      · simp [rplus, Function.update_of_ne hki,
          Function.update_of_ne hkj, hr1]
  have hrminus0 : ∀ k, 0 ≤ rminus k := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [rminus, Function.update_of_ne hij]
      linarith
    · by_cases hkj : k = j
      · subst k
        simpa [rminus] using
          add_nonneg (hr0 j) hbPos.le
      · simp [rminus, Function.update_of_ne hki,
          Function.update_of_ne hkj, hr0]
  have hrminus1 : ∀ k, rminus k ≤ 1 := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [rminus, Function.update_of_ne hij]
      linarith
    · by_cases hkj : k = j
      · subst k
        simp [rminus]
        linarith
      · simp [rminus, Function.update_of_ne hki,
          Function.update_of_ne hkj, hr1]
  have hsumPlus :
      ∑ k, rplus k = (M : ℝ) := by
    change
      ∑ k,
          Function.update
            (Function.update r i (r i + a)) j (r j - a) k =
        _
    rw [sum_two_updates r i j hij a, hsum]
  have hsumMinus :
      ∑ k, rminus k = (M : ℝ) := by
    change
      ∑ k,
          Function.update
            (Function.update r i (r i - b)) j (r j + b) k =
        _
    convert (sum_two_updates r i j hij (-b)).trans hsum using 1 <;>
      ring
  have hiFrac : i ∈ fractionalIndices r := by
    simp [fractionalIndices, hi0, hi1]
  have hjFrac : j ∈ fractionalIndices r := by
    simp [fractionalIndices, hj0, hj1]
  have hplusSubset :
      fractionalIndices rplus ⊆ fractionalIndices r := by
    intro k hk
    by_cases hki : k = i
    · simpa [hki] using hiFrac
    · by_cases hkj : k = j
      · simpa [hkj] using hjFrac
      · simpa [fractionalIndices, rplus,
          Function.update_of_ne hki,
          Function.update_of_ne hkj] using hk
  have hminusSubset :
      fractionalIndices rminus ⊆ fractionalIndices r := by
    intro k hk
    by_cases hki : k = i
    · simpa [hki] using hiFrac
    · by_cases hkj : k = j
      · simpa [hkj] using hjFrac
      · simpa [fractionalIndices, rminus,
          Function.update_of_ne hki,
          Function.update_of_ne hkj] using hk
  have hplusStrict :
      fractionalIndices rplus ⊂ fractionalIndices r := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hplusSubset, ?_⟩
    rcases min_choice (1 - r i) (r j) with ha | ha
    · intro heq
      have himem : i ∈ fractionalIndices rplus :=
        heq ▸ hiFrac
      have hi_ne_one : rplus i ≠ 1 :=
        (Finset.mem_filter.mp himem).2.2
      apply hi_ne_one
      simp [rplus, Function.update_of_ne hij, a, ha]
    · intro heq
      have hjmem : j ∈ fractionalIndices rplus :=
        heq ▸ hjFrac
      have hj_ne_zero : rplus j ≠ 0 :=
        (Finset.mem_filter.mp hjmem).2.1
      apply hj_ne_zero
      simp [rplus, a, ha]
  have hminusStrict :
      fractionalIndices rminus ⊂ fractionalIndices r := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hminusSubset, ?_⟩
    rcases min_choice (r i) (1 - r j) with hb | hb
    · intro heq
      have himem : i ∈ fractionalIndices rminus :=
        heq ▸ hiFrac
      have hi_ne_zero : rminus i ≠ 0 :=
        (Finset.mem_filter.mp himem).2.1
      apply hi_ne_zero
      simp [rminus, Function.update_of_ne hij, b, hb]
    · intro heq
      have hjmem : j ∈ fractionalIndices rminus :=
        heq ▸ hjFrac
      have hj_ne_one : rminus j ≠ 1 :=
        (Finset.mem_filter.mp hjmem).2.2
      apply hj_ne_one
      simp [rminus, b, hb]
  refine
    ⟨rplus, rminus, t, htPos, htLt,
      hrplus0, hrplus1, hsumPlus,
      hrminus0, hrminus1, hsumMinus,
      Finset.card_lt_card hplusStrict,
      Finset.card_lt_card hminusStrict, ?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [rplus, rminus, t, Function.update_of_ne hij]
    field_simp
    ring
  · by_cases hkj : k = j
    · subst k
      simp [rplus, rminus, t]
      field_simp
      ring
    · simp [rplus, rminus, t,
        Function.update_of_ne hki,
        Function.update_of_ne hkj]
      field_simp
      ring

/-- The hypersimplex is the convex hull of its fixed-cardinality `0`-`1`
vertices. This is the finite dependent-rounding lemma used by the one-way
Nielsen protocol below. -/
private theorem mem_convexHull_uniformSubsetVectors
    {D : Type*} [Fintype D] [DecidableEq D]
    (r : D → ℝ) (M : ℕ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hsum : ∑ i, r i = (M : ℝ)) :
    r ∈ convexHull ℝ (uniformSubsetVectors D M) := by
  classical
  generalize hN : (fractionalIndices r).card = N
  induction N using Nat.strong_induction_on generalizing r with
  | h N ih =>
      by_cases hfrac : (fractionalIndices r).Nonempty
      · obtain
          ⟨rplus, rminus, t, ht0, ht1,
            hp0, hp1, hpsum, hm0, hm1, hmsum,
            hpCount, hmCount, heq⟩ :=
          exists_fractional_split r M hr0 hr1 hsum hfrac
        have hp :
            rplus ∈
              convexHull ℝ (uniformSubsetVectors D M) :=
          ih (fractionalIndices rplus).card (by omega)
            rplus hp0 hp1 hpsum rfl
        have hm :
            rminus ∈
              convexHull ℝ (uniformSubsetVectors D M) :=
          ih (fractionalIndices rminus).card (by omega)
            rminus hm0 hm1 hmsum rfl
        apply
          (convex_convexHull ℝ
            (uniformSubsetVectors D M)).segment_subset hm hp
        rw [segment_eq_image]
        exact ⟨t, ⟨ht0.le, ht1.le⟩, heq.symm⟩
      · apply
          subset_convexHull ℝ (uniformSubsetVectors D M)
        refine ⟨?_, hsum⟩
        intro i
        by_cases hi0 : r i = 0
        · exact Or.inl hi0
        · right
          by_contra hi1
          exact hfrac
            ⟨i, by
              simp [fractionalIndices, hi0, hi1]⟩

/-- Encode a one-way protocol in the explicit two-round adaptive LOCC tree.
Alice performs the supplied complete instrument in round zero and Bob applies
the transcript-dependent unitary in round one. -/
private noncomputable def oneWayLOCCData
    {D A' B' : Type*} {O IA IB : Type}
    [Fintype D] [DecidableEq D]
    [Fintype O] [DecidableEq O]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    [Fintype IA] [Fintype IB]
    (aliceKraus : O → CMatrix D)
    (halice :
      ∑ o,
          Matrix.conjTranspose (aliceKraus o) *
            aliceKraus o =
        1)
    (bobUnitary : O → CMatrix D)
    (hbob :
      ∀ o,
        Matrix.conjTranspose (bobUnitary o) *
            bobUnitary o =
          1)
    (aliceFinal : IA → Matrix A' D ℂ)
    (haliceFinal :
      ∑ i,
          Matrix.conjTranspose (aliceFinal i) *
            aliceFinal i =
        1)
    (bobFinal : IB → Matrix B' D ℂ)
    (hbobFinal :
      ∑ i,
          Matrix.conjTranspose (bobFinal i) *
            bobFinal i =
        1) :
    FiniteRoundLOCCData D D A' B' where
  rounds := 2
  Outcome := Option O
  AliceWorkspace := D
  BobWorkspace := D
  aliceInitial := 1
  bobInitial := 1
  aliceInitial_isometry := by simp
  bobInitial_isometry := by simp
  activeParty := fun r _ =>
    if r.val = 0 then .alice else .bob
  aliceRoundKraus := fun r _ outcome =>
    if r.val = 0 then outcome.elim 0 aliceKraus else 0
  bobRoundKraus := fun r history outcome =>
    if hr : r.val = 1 then
      match outcome with
      | none =>
          match history ⟨0, by omega⟩ with
          | none => 1
          | some o => bobUnitary o
      | some _ => 0
    else 0
  round_complete := by
    intro r history
    fin_cases r
    · simp only [Fin.val_zero, ↓reduceIte, Option.elim]
      simpa using halice
    · simp only [Fin.val_one, one_ne_zero, ↓reduceIte]
      cases h : history 0 with
      | none => simp [h]
      | some o => simpa [h] using hbob o
  AliceFinalIndex := IA
  BobFinalIndex := IB
  aliceFinal := aliceFinal
  bobFinal := bobFinal
  aliceFinal_complete := haliceFinal
  bobFinal_complete := hbobFinal

private theorem oneWayLOCCData_productKraus
    {D A' B' : Type*} {O IA IB : Type}
    [Fintype D] [DecidableEq D]
    [Fintype O] [DecidableEq O]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    [Fintype IA] [Fintype IB]
    (aliceKraus : O → CMatrix D)
    (halice :
      ∑ o,
          Matrix.conjTranspose (aliceKraus o) *
            aliceKraus o =
        1)
    (bobUnitary : O → CMatrix D)
    (hbob :
      ∀ o,
        Matrix.conjTranspose (bobUnitary o) *
            bobUnitary o =
          1)
    (aliceFinal : IA → Matrix A' D ℂ)
    (haliceFinal :
      ∑ i,
          Matrix.conjTranspose (aliceFinal i) *
            aliceFinal i =
        1)
    (bobFinal : IB → Matrix B' D ℂ)
    (hbobFinal :
      ∑ i,
          Matrix.conjTranspose (bobFinal i) *
            bobFinal i =
        1)
    (k :
      (oneWayLOCCData aliceKraus halice bobUnitary hbob
        aliceFinal haliceFinal bobFinal hbobFinal).BranchIndex) :
    let P :=
      oneWayLOCCData aliceKraus halice bobUnitary hbob
        aliceFinal haliceFinal bobFinal hbobFinal
    P.productKraus k =
      match k.1 (0 : Fin 2), k.1 (1 : Fin 2) with
      | some o, none =>
          Matrix.kronecker
            (aliceFinal k.2.1 * aliceKraus o)
            (bobFinal k.2.2 * bobUnitary o)
      | _, _ => 0 := by
  classical
  dsimp
  simp only [FiniteRoundLOCCData.productKraus,
    FiniteRoundLOCCData.leftKraus,
    FiniteRoundLOCCData.rightKraus,
    FiniteRoundLOCCData.aliceAccumulated,
    FiniteRoundLOCCData.bobAccumulated,
    FiniteRoundLOCCData.history, oneWayLOCCData,
    List.ofFn_succ, List.ofFn_zero,
    List.foldl_cons, List.foldl_nil]
  have hAliceZero :
      (1 : CMatrix D) * ((0 : CMatrix D) * 1) = 0 := by
    rw [Matrix.zero_mul, Matrix.one_mul]
  have hAliceOne (K : CMatrix D) :
      (1 : CMatrix D) * (K * 1) = K := by
    rw [Matrix.mul_one, Matrix.one_mul]
  have hBobOne (U : CMatrix D) :
      U * ((1 : CMatrix D) * 1) = U := by
    rw [Matrix.one_mul, Matrix.mul_one]
  have hBobZero :
      (0 : CMatrix D) * ((1 : CMatrix D) * 1) = 0 := by
    rw [Matrix.zero_mul]
  cases h0 : k.1 ⟨0, by simp [oneWayLOCCData]⟩ with
  | none =>
      have h0' : k.1 (0 : Fin 2) = none := by
        convert h0
      cases h1 : k.1 ⟨1, by simp [oneWayLOCCData]⟩ with
      | none =>
          have h1' : k.1 (1 : Fin 2) = none := by
            convert h1
          simp [h0', h1', Matrix.zero_mul, Matrix.mul_zero,
            Matrix.mul_one, Matrix.one_mul]
          change Matrix.kronecker
            (aliceFinal k.2.1 *
              ((1 : CMatrix D) * ((0 : CMatrix D) * 1)))
            (bobFinal k.2.2 *
              ((1 : CMatrix D) * ((1 : CMatrix D) * 1))) = 0
          have hLeft :
              aliceFinal k.2.1 *
                  ((1 : CMatrix D) * ((0 : CMatrix D) * 1)) =
                0 := by
            calc
              _ = aliceFinal k.2.1 * 0 :=
                congrArg (fun K : CMatrix D => aliceFinal k.2.1 * K)
                  hAliceZero
              _ = 0 := Matrix.mul_zero _
          calc
            _ = Matrix.kronecker 0
                (bobFinal k.2.2 *
                  ((1 : CMatrix D) * ((1 : CMatrix D) * 1))) :=
              congrArg
                (fun K : Matrix A' D ℂ =>
                  Matrix.kronecker K
                    (bobFinal k.2.2 *
                      ((1 : CMatrix D) * ((1 : CMatrix D) * 1))))
                hLeft
            _ = 0 := by
              ext x y
              simp [Matrix.kronecker]
      | some o =>
          have h1' : k.1 (1 : Fin 2) = some o := by
            convert h1
          simp [h0', h1', Matrix.zero_mul, Matrix.mul_zero,
            Matrix.mul_one, Matrix.one_mul]
          change Matrix.kronecker
            (aliceFinal k.2.1 *
              ((1 : CMatrix D) * ((0 : CMatrix D) * 1)))
            (bobFinal k.2.2 *
              ((0 : CMatrix D) * ((1 : CMatrix D) * 1))) = 0
          have hLeft :
              aliceFinal k.2.1 *
                  ((1 : CMatrix D) * ((0 : CMatrix D) * 1)) =
                0 := by
            calc
              _ = aliceFinal k.2.1 * 0 :=
                congrArg (fun K : CMatrix D => aliceFinal k.2.1 * K)
                  hAliceZero
              _ = 0 := Matrix.mul_zero _
          calc
            _ = Matrix.kronecker 0
                (bobFinal k.2.2 *
                  ((0 : CMatrix D) * ((1 : CMatrix D) * 1))) :=
              congrArg
                (fun K : Matrix A' D ℂ =>
                  Matrix.kronecker K
                    (bobFinal k.2.2 *
                      ((0 : CMatrix D) * ((1 : CMatrix D) * 1))))
                hLeft
            _ = 0 := by
              ext x y
              simp [Matrix.kronecker]
  | some o =>
      have h0' : k.1 (0 : Fin 2) = some o := by
        convert h0
      cases h1 : k.1 ⟨1, by simp [oneWayLOCCData]⟩ with
      | none =>
          have h1' : k.1 (1 : Fin 2) = none := by
            convert h1
          simp [h0', h1', Matrix.zero_mul, Matrix.mul_zero,
            Matrix.mul_one, Matrix.one_mul]
          change Matrix.kronecker
            (aliceFinal k.2.1 *
              ((1 : CMatrix D) * (aliceKraus o * 1)))
            (bobFinal k.2.2 *
              (bobUnitary o * ((1 : CMatrix D) * 1))) =
            Matrix.kronecker
              (aliceFinal k.2.1 * aliceKraus o)
              (bobFinal k.2.2 * bobUnitary o)
          have hLeft :
              aliceFinal k.2.1 *
                  ((1 : CMatrix D) * (aliceKraus o * 1)) =
                aliceFinal k.2.1 * aliceKraus o :=
            congrArg (fun K : CMatrix D => aliceFinal k.2.1 * K)
              (hAliceOne (aliceKraus o))
          have hRight :
              bobFinal k.2.2 *
                  (bobUnitary o * ((1 : CMatrix D) * 1)) =
                bobFinal k.2.2 * bobUnitary o :=
            congrArg (fun K : CMatrix D => bobFinal k.2.2 * K)
              (hBobOne (bobUnitary o))
          calc
            _ = Matrix.kronecker
                (aliceFinal k.2.1 * aliceKraus o)
                (bobFinal k.2.2 *
                  (bobUnitary o * ((1 : CMatrix D) * 1))) :=
              congrArg
                (fun K : Matrix A' D ℂ =>
                  Matrix.kronecker K
                    (bobFinal k.2.2 *
                      (bobUnitary o * ((1 : CMatrix D) * 1))))
                hLeft
            _ = _ :=
              congrArg
                (fun K : Matrix B' D ℂ =>
                  Matrix.kronecker
                    (aliceFinal k.2.1 * aliceKraus o) K)
                hRight
      | some o' =>
          have h1' : k.1 (1 : Fin 2) = some o' := by
            convert h1
          simp [h0', h1', Matrix.zero_mul, Matrix.mul_zero,
            Matrix.mul_one, Matrix.one_mul]
          change Matrix.kronecker
            (aliceFinal k.2.1 *
              ((1 : CMatrix D) * (aliceKraus o * 1)))
            (bobFinal k.2.2 *
              ((0 : CMatrix D) * ((1 : CMatrix D) * 1))) = 0
          have hRight :
              bobFinal k.2.2 *
                  ((0 : CMatrix D) * ((1 : CMatrix D) * 1)) =
                0 := by
            calc
              _ = bobFinal k.2.2 * 0 :=
                congrArg (fun K : CMatrix D => bobFinal k.2.2 * K)
                  hBobZero
              _ = 0 := Matrix.mul_zero _
          calc
            _ = Matrix.kronecker
                (aliceFinal k.2.1 *
                  ((1 : CMatrix D) * (aliceKraus o * 1))) 0 :=
              congrArg
                (fun K : Matrix B' D ℂ =>
                  Matrix.kronecker
                    (aliceFinal k.2.1 *
                      ((1 : CMatrix D) * (aliceKraus o * 1))) K)
                hRight
            _ = 0 := by
              ext x y
              simp [Matrix.kronecker]

private def finTwoArrowEquiv (α : Type*) :
    (Fin 2 → α) ≃ α × α where
  toFun f := (f 0, f 1)
  invFun pair :=
    fun i => if i.val = 0 then pair.1 else pair.2
  left_inv f := by
    funext i
    fin_cases i <;> simp
  right_inv pair := by
    ext <;> simp

private theorem complete_after_kraus
    {D E I : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [Fintype I]
    (F : I → Matrix E D ℂ)
    (hF : ∑ i, Matrix.conjTranspose (F i) * F i = (1 : CMatrix D))
    (K : CMatrix D) :
    ∑ i,
        Matrix.conjTranspose (F i * K) *
          (F i * K) =
      Matrix.conjTranspose K * K := by
  simp_rw [Matrix.conjTranspose_mul]
  calc
    ∑ i, (Matrix.conjTranspose K * Matrix.conjTranspose (F i)) *
        (F i * K) =
        Matrix.conjTranspose K *
          ((∑ i, Matrix.conjTranspose (F i) * F i) * K) := by
            simp_rw [Matrix.mul_assoc]
            rw [Finset.sum_mul, Finset.mul_sum]
            simp_rw [Matrix.mul_assoc]
    _ = Matrix.conjTranspose K * K := by
      rw [hF, Matrix.one_mul]

private theorem oneWayLOCCData_tracePreserving
    {D A' B' : Type*} {O IA IB : Type}
    [Fintype D] [DecidableEq D]
    [Fintype O] [DecidableEq O]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    [Fintype IA] [Fintype IB]
    (aliceKraus : O → CMatrix D)
    (halice :
      ∑ o,
          Matrix.conjTranspose (aliceKraus o) *
            aliceKraus o =
        1)
    (bobUnitary : O → CMatrix D)
    (hbob :
      ∀ o,
        Matrix.conjTranspose (bobUnitary o) *
            bobUnitary o =
          1)
    (aliceFinal : IA → Matrix A' D ℂ)
    (haliceFinal :
      ∑ i,
          Matrix.conjTranspose (aliceFinal i) *
            aliceFinal i =
        1)
    (bobFinal : IB → Matrix B' D ℂ)
    (hbobFinal :
      ∑ i,
          Matrix.conjTranspose (bobFinal i) *
            bobFinal i =
        1) :
    (oneWayLOCCData aliceKraus halice bobUnitary hbob
      aliceFinal haliceFinal bobFinal hbobFinal).IsTracePreserving := by
  classical
  let P :=
    oneWayLOCCData aliceKraus halice bobUnitary hbob
      aliceFinal haliceFinal bobFinal hbobFinal
  letI := P.fintypeOutcome
  letI := P.fintypeAliceFinalIndex
  letI := P.fintypeBobFinalIndex
  let K := P.productKraus
  apply MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one K
  dsimp [K]
  unfold MatrixMap.krausAdjoint
  simp only [Matrix.mul_one]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  simp only [Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  calc
    ∑ t : Fin 2 → Option O, ∑ ij : IA × IB,
        (Matrix.conjTranspose
              (P.productKraus (t, ij)) *
            P.productKraus (t, ij)) (ia, ib) (ja, jb) =
      ∑ t : Option O × Option O, ∑ ij : IA × IB,
        (Matrix.conjTranspose
              (P.productKraus
                ((finTwoArrowEquiv (Option O)).symm t, ij)) *
            P.productKraus
              ((finTwoArrowEquiv (Option O)).symm t, ij))
          (ia, ib) (ja, jb) := by
            apply Fintype.sum_equiv (finTwoArrowEquiv (Option O))
            intro t
            simp
    _ =
      ∑ o : O, ∑ ij : IA × IB,
        (Matrix.conjTranspose
              (Matrix.kronecker
                (aliceFinal ij.1 * aliceKraus o)
                (bobFinal ij.2 * bobUnitary o)) *
            Matrix.kronecker
              (aliceFinal ij.1 * aliceKraus o)
              (bobFinal ij.2 * bobUnitary o))
          (ia, ib) (ja, jb) := by
            rw [Fintype.sum_prod_type]
            simp only [Fintype.sum_option]
            simp [P, finTwoArrowEquiv,
              oneWayLOCCData_productKraus]
    _ =
      ∑ o : O,
        (∑ ai : IA,
          (Matrix.conjTranspose
                (aliceFinal ai * aliceKraus o) *
              (aliceFinal ai * aliceKraus o)) ia ja) *
        (∑ bi : IB,
          (Matrix.conjTranspose
                (bobFinal bi * bobUnitary o) *
              (bobFinal bi * bobUnitary o)) ib jb) := by
            apply Finset.sum_congr rfl
            intro o ho
            rw [Fintype.sum_prod_type]
            simp_rw [conjTranspose_kronecker_mul_self]
            simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
            rw [← Finset.sum_mul_sum Finset.univ Finset.univ]
    _ =
      ∑ o : O,
        (Matrix.conjTranspose (aliceKraus o) *
            aliceKraus o) ia ja *
          (1 : CMatrix D) ib jb := by
            apply Finset.sum_congr rfl
            intro o ho
            rw [show
              (∑ ai : IA,
                (Matrix.conjTranspose
                      (aliceFinal ai * aliceKraus o) *
                    (aliceFinal ai * aliceKraus o)) ia ja) =
                (Matrix.conjTranspose (aliceKraus o) *
                    aliceKraus o) ia ja by
                  rw [← Matrix.sum_apply]
                  exact congrArg (fun L : CMatrix D => L ia ja)
                    (complete_after_kraus
                      aliceFinal haliceFinal (aliceKraus o))]
            rw [show
              (∑ bi : IB,
                (Matrix.conjTranspose
                      (bobFinal bi * bobUnitary o) *
                    (bobFinal bi * bobUnitary o)) ib jb) =
                (1 : CMatrix D) ib jb by
                  rw [← Matrix.sum_apply]
                  exact congrArg (fun L : CMatrix D => L ib jb)
                    ((complete_after_kraus
                      bobFinal hbobFinal (bobUnitary o)).trans
                        (hbob o))]
    _ =
      (1 : CMatrix D) ia ja * (1 : CMatrix D) ib jb := by
            rw [← Finset.sum_mul]
            congr 1
            rw [← Matrix.sum_apply]
            exact congrArg (fun L : CMatrix D => L ia ja) halice
    _ = (1 : CMatrix (D × D)) (ia, ib) (ja, jb) := by
      simp only [Matrix.one_apply]
      by_cases ha : ia = ja <;> by_cases hb : ib = jb <;> simp [ha, hb]

private noncomputable def oneWayLOCCProtocol
    {D A' B' : Type*} {O IA IB : Type}
    [Fintype D] [DecidableEq D]
    [Fintype O] [DecidableEq O]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    [Fintype IA] [Fintype IB]
    (aliceKraus : O → CMatrix D)
    (halice :
      ∑ o,
          Matrix.conjTranspose (aliceKraus o) *
            aliceKraus o =
        1)
    (bobUnitary : O → CMatrix D)
    (hbob :
      ∀ o,
        Matrix.conjTranspose (bobUnitary o) *
            bobUnitary o =
          1)
    (aliceFinal : IA → Matrix A' D ℂ)
    (haliceFinal :
      ∑ i,
          Matrix.conjTranspose (aliceFinal i) *
            aliceFinal i =
        1)
    (bobFinal : IB → Matrix B' D ℂ)
    (hbobFinal :
      ∑ i,
          Matrix.conjTranspose (bobFinal i) *
            bobFinal i =
        1) :
    FiniteRoundLOCCProtocol D D A' B' where
  data :=
    oneWayLOCCData aliceKraus halice bobUnitary hbob
      aliceFinal haliceFinal bobFinal hbobFinal
  tracePreserving :=
    oneWayLOCCData_tracePreserving
      aliceKraus halice bobUnitary hbob
      aliceFinal haliceFinal bobFinal hbobFinal

private theorem mul_rankOneMatrix_mul_conjTranspose
    {A B : Type*} [Fintype A] [Fintype B]
    (K : Matrix B A ℂ) (v : A → ℂ) :
    K * rankOneMatrix v * Matrix.conjTranspose K =
      rankOneMatrix (K.mulVec v) := by
  unfold rankOneMatrix
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  exact (Matrix.star_mulVec K v).symm

@[simp]
private theorem rankOneMatrix_zero
    {A : Type*} :
    rankOneMatrix (0 : A → ℂ) = (0 : CMatrix A) := by
  ext i j
  simp [rankOneMatrix_apply]

private theorem oneWayLOCCProtocol_apply_rankOneMatrix
    {D A' B' : Type*} {O IA IB : Type}
    [Fintype D] [DecidableEq D]
    [Fintype O] [DecidableEq O]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    [Fintype IA] [Fintype IB]
    (aliceKraus : O → CMatrix D)
    (halice :
      ∑ o,
          Matrix.conjTranspose (aliceKraus o) *
            aliceKraus o =
        1)
    (bobUnitary : O → CMatrix D)
    (hbob :
      ∀ o,
        Matrix.conjTranspose (bobUnitary o) *
            bobUnitary o =
          1)
    (aliceFinal : IA → Matrix A' D ℂ)
    (haliceFinal :
      ∑ i,
          Matrix.conjTranspose (aliceFinal i) *
            aliceFinal i =
        1)
    (bobFinal : IB → Matrix B' D ℂ)
    (hbobFinal :
      ∑ i,
          Matrix.conjTranspose (bobFinal i) *
            bobFinal i =
        1)
    (v : D × D → ℂ) :
    (oneWayLOCCProtocol
        aliceKraus halice bobUnitary hbob
        aliceFinal haliceFinal bobFinal hbobFinal).channel.map
        (rankOneMatrix v) =
      ∑ o : O, ∑ ai : IA, ∑ bi : IB,
        rankOneMatrix
          ((Matrix.kronecker
              (aliceFinal ai * aliceKraus o)
              (bobFinal bi * bobUnitary o)).mulVec v) := by
  classical
  let P :=
    oneWayLOCCData aliceKraus halice bobUnitary hbob
      aliceFinal haliceFinal bobFinal hbobFinal
  letI := P.fintypeOutcome
  letI := P.fintypeAliceFinalIndex
  letI := P.fintypeBobFinalIndex
  change
    (MatrixMap.ofKraus P.productKraus) (rankOneMatrix v) = _
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type]
  calc
    ∑ t : Fin 2 → Option O, ∑ ij : IA × IB,
        P.productKraus (t, ij) * rankOneMatrix v *
          Matrix.conjTranspose (P.productKraus (t, ij)) =
      ∑ t : Option O × Option O, ∑ ij : IA × IB,
        P.productKraus
              ((finTwoArrowEquiv (Option O)).symm t, ij) *
            rankOneMatrix v *
          Matrix.conjTranspose
            (P.productKraus
              ((finTwoArrowEquiv (Option O)).symm t, ij)) := by
        apply Fintype.sum_equiv (finTwoArrowEquiv (Option O))
        intro t
        simp
    _ =
      ∑ o : O, ∑ ij : IA × IB,
        Matrix.kronecker
              (aliceFinal ij.1 * aliceKraus o)
              (bobFinal ij.2 * bobUnitary o) *
            rankOneMatrix v *
          Matrix.conjTranspose
            (Matrix.kronecker
              (aliceFinal ij.1 * aliceKraus o)
              (bobFinal ij.2 * bobUnitary o)) := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_option]
        simp [P, finTwoArrowEquiv,
          oneWayLOCCData_productKraus]
    _ = _ := by
      simp_rw [Fintype.sum_prod_type,
        mul_rankOneMatrix_mul_conjTranspose]

private noncomputable def discardToFixedKraus
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) (i : D) :
    Matrix (Fin M) D ℂ :=
  Matrix.single ⟨0, hM⟩ i 1

private theorem discardToFixedKraus_complete
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) :
    ∑ i : D,
        Matrix.conjTranspose (discardToFixedKraus hM i) *
          discardToFixedKraus hM i =
      (1 : CMatrix D) := by
  ext i j
  simp [discardToFixedKraus, Matrix.sum_single_one]

private theorem discardToFixedKraus_complete_fin
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) :
    ∑ i : Fin (Fintype.card D),
        Matrix.conjTranspose
            (discardToFixedKraus hM
              ((Fintype.equivFin D).symm i)) *
          discardToFixedKraus hM
            ((Fintype.equivFin D).symm i) =
      (1 : CMatrix D) := by
  calc
    _ = ∑ i : D,
        Matrix.conjTranspose (discardToFixedKraus hM i) *
          discardToFixedKraus hM i := by
            apply Fintype.sum_equiv (Fintype.equivFin D).symm
            intro i
            rfl
    _ = 1 := discardToFixedKraus_complete hM

private noncomputable def discardToFixedProtocol
    (D : Type*) [Fintype D] [DecidableEq D]
    (M : ℕ) (hM : 0 < M) :
    FiniteRoundLOCCProtocol D D (Fin M) (Fin M) :=
  oneWayLOCCProtocol
    (fun _ : Unit => (1 : CMatrix D)) (by simp)
    (fun _ : Unit => (1 : CMatrix D)) (by simp)
    (fun i : Fin (Fintype.card D) =>
      discardToFixedKraus hM ((Fintype.equivFin D).symm i))
      (discardToFixedKraus_complete_fin hM)
    (fun i : Fin (Fintype.card D) =>
      discardToFixedKraus hM ((Fintype.equivFin D).symm i))
      (discardToFixedKraus_complete_fin hM)

/-- The final local channel coherently identifies the distinguished
`M`-element subspace with `Fin M` and sends every complementary basis vector
to the fixed output basis vector `0`. -/
private noncomputable def compressionKraus
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) (e : Fin M ↪ D) :
    Option (Fin (Fintype.card D)) → Matrix (Fin M) D ℂ
  | none => fun m i => if e m = i then 1 else 0
  | some k =>
      let i := (Fintype.equivFin D).symm k
      if i ∈ Set.range e then 0
      else Matrix.single ⟨0, hM⟩ i 1

private theorem compressionKraus_complete
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) (e : Fin M ↪ D) :
    ∑ k,
        Matrix.conjTranspose (compressionKraus hM e k) *
          compressionKraus hM e k =
      (1 : CMatrix D) := by
  classical
  let C0 := compressionKraus hM e none
  have hmain :
      Matrix.conjTranspose C0 * C0 =
        Matrix.diagonal
          (fun i =>
            if i ∈ Set.range e then (1 : ℂ) else 0) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      C0, compressionKraus, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ Set.range e
      · obtain ⟨m, rfl⟩ := hi
        simp [Set.mem_range]
      · rw [if_neg hi, if_pos rfl]
        apply Finset.sum_eq_zero
        intro m hm
        by_cases hemi : e m = i
        · exact (hi ⟨m, hemi⟩).elim
        · simp [hemi]
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro m hm
      by_cases hemj : e m = j
      · by_cases hemi : e m = i
        · exact (hij (hemi.symm.trans hemj)).elim
        · simp [hemj, Ne.symm hij]
      · simp [hemj]
  have hfail :
      (∑ k : Fin (Fintype.card D),
          Matrix.conjTranspose
              (compressionKraus hM e (some k)) *
            compressionKraus hM e (some k)) =
        Matrix.diagonal
          (fun i =>
            if i ∈ Set.range e then 0 else (1 : ℂ)) := by
    calc
      _ = ∑ x : D,
          Matrix.conjTranspose
              (if x ∈ Set.range e then 0 else
                (Matrix.single ⟨0, hM⟩ x 1 :
                  Matrix (Fin M) D ℂ)) *
            (if x ∈ Set.range e then 0 else
              (Matrix.single ⟨0, hM⟩ x 1 :
                Matrix (Fin M) D ℂ)) := by
                  apply Fintype.sum_equiv
                    (Fintype.equivFin D).symm
                  intro k
                  rfl
      _ = ∑ x : D,
          if x ∈ Set.range e then 0
          else Matrix.single x x (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxe : x ∈ Set.range e <;> simp [hxe]
      _ = _ := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.diagonal_apply]
        by_cases hij : i = j
        · subst j
          by_cases hi : i ∈ Set.range e
          · rw [if_pos hi, if_pos rfl]
            apply Finset.sum_eq_zero
            intro x hx
            by_cases hxi : x = i
            · subst x
              simp [hi]
            · split <;> simp [Matrix.single_apply, hxi]
          · rw [if_neg hi, if_pos rfl]
            rw [Finset.sum_eq_single i]
            · simp [hi, Matrix.single_apply]
            · intro x hx hxi
              split <;> simp [Matrix.single_apply, hxi]
            · simp
        · rw [if_neg hij]
          apply Finset.sum_eq_zero
          intro x hx
          split
          · rfl
          · simp only [Matrix.single_apply]
            split
            · rename_i h
              exact (hij (h.1.symm.trans h.2)).elim
            · rfl
  rw [Fintype.sum_option, hmain, hfail]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.diagonal_apply,
      Matrix.one_apply, ↓reduceIte]
    by_cases hi : i ∈ Set.range e
    · simp only [if_pos hi, add_zero]
    · simp only [if_neg hi, zero_add]
  · simp [Matrix.add_apply, hij]

private theorem diagonalSqrt_adjoint_mul
    {D : Type*} [Fintype D] [DecidableEq D]
    (a : D → ℝ) (ha : ∀ i, 0 ≤ a i) :
    let K : CMatrix D :=
      Matrix.diagonal fun i =>
        ((Real.sqrt (a i) : ℝ) : ℂ)
    Matrix.conjTranspose K * K =
      Matrix.diagonal fun i => ((a i : ℝ) : ℂ) := by
  dsimp
  rw [Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  change
    (starRingEnd ℂ) (Real.sqrt (a i)) *
        (Real.sqrt (a i) : ℂ) =
      (a i : ℂ)
  rw [Complex.conj_ofReal]
  norm_cast
  simpa [pow_two] using Real.sq_sqrt (ha i)

private theorem permMatrix_mul_diagonalSqrt_adjoint_mul
    {D : Type*} [Fintype D] [DecidableEq D]
    (σ : Equiv.Perm D) (a : D → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    let K : CMatrix D :=
      σ.permMatrix ℂ *
        Matrix.diagonal
          (fun i =>
            ((Real.sqrt (a i) : ℝ) : ℂ))
    Matrix.conjTranspose K * K =
      Matrix.diagonal fun i => ((a i : ℝ) : ℂ) := by
  dsimp
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
    (Matrix.conjTranspose (σ.permMatrix ℂ))]
  rw [Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp
  intro i
  norm_cast
  simpa [pow_two] using Real.sq_sqrt (ha i)

private noncomputable def successRatio
    {D : Type*} {ι : Type}
    (p : D → ℝ) (s : ℝ) (M : ℕ)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (k : ι) (i : D) : ℝ :=
  if p i = 0 then 0
  else s * w k * z k i / ((M : ℝ) * p i)

private noncomputable def leftoverRatio
    {D : Type*} (p q : D → ℝ) (i : D) : ℝ :=
  if p i = 0 then 1 else (p i - q i) / p i

/-- Alice's concentration instrument. A convex-decomposition branch performs
the diagonal Nielsen filter followed by its relabeling permutation. A
complementary branch records one input coordinate and one uniformly chosen
target coordinate; these branches prepare the correlated classical fallback
state. -/
private noncomputable def concentrationAliceKraus
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    (p q : D → ℝ) (s : ℝ) (M : ℕ) (_hM : 0 < M)
    (e : Fin M ↪ D)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (σ : ι → Equiv.Perm D) :
    (ι ⊕ (Fin (Fintype.card D) × Fin M)) → CMatrix D
  | .inl k =>
      (σ k).permMatrix ℂ *
        Matrix.diagonal
          (fun i =>
            ((Real.sqrt
                (successRatio p s M w z k i) : ℝ) : ℂ))
  | .inr pair =>
      let i := (Fintype.equivFin D).symm pair.1
      Matrix.single (e pair.2) i
        ((Real.sqrt
            (leftoverRatio p q i / (M : ℝ)) : ℝ) : ℂ)

set_option maxHeartbeats 800000 in
private theorem concentrationAliceKraus_complete
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    (p q : D → ℝ) (s : ℝ) (M : ℕ) (hM : 0 < M)
    (e : Fin M ↪ D)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (σ : ι → Equiv.Perm D)
    (hp0 : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 ≤ q i)
    (hqp : ∀ i, q i ≤ p i)
    (hs : 0 < s)
    (hw0 : ∀ k, 0 ≤ w k)
    (hz01 : ∀ k i, z k i = 0 ∨ z k i = 1)
    (hbar :
      ∀ i,
        ∑ k, w k * z k i = (M : ℝ) * q i / s) :
    ∑ o,
        Matrix.conjTranspose
            (concentrationAliceKraus
              p q s M hM e w z σ o) *
          concentrationAliceKraus
            p q s M hM e w z σ o =
      (1 : CMatrix D) := by
  classical
  have hMreal : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hM
  have hMC : (M : ℂ) ≠ 0 := by
    exact_mod_cast hM.ne'
  have hsuccess0 :
      ∀ k i, 0 ≤ successRatio p s M w z k i := by
    intro k i
    unfold successRatio
    split
    · exact le_rfl
    · apply div_nonneg
      · exact
          mul_nonneg
            (mul_nonneg hs.le (hw0 k))
            (by
              rcases hz01 k i with h | h <;> simp [h])
      · exact mul_nonneg hMreal.le (hp0 i)
  have hleft0 :
      ∀ i, 0 ≤ leftoverRatio p q i := by
    intro i
    unfold leftoverRatio
    split
    · norm_num
    · exact
        div_nonneg (sub_nonneg.mpr (hqp i)) (hp0 i)
  have hsuccess (k : ι) :
      Matrix.conjTranspose
            (concentrationAliceKraus
              p q s M hM e w z σ (.inl k)) *
          concentrationAliceKraus
            p q s M hM e w z σ (.inl k) =
        Matrix.diagonal
          fun i =>
            ((successRatio p s M w z k i : ℝ) : ℂ) := by
    exact
      permMatrix_mul_diagonalSqrt_adjoint_mul
        (σ k) _ (hsuccess0 k)
  have hfailure
      (ik : Fin (Fintype.card D)) (j : Fin M) :
      let i := (Fintype.equivFin D).symm ik
      Matrix.conjTranspose
            (concentrationAliceKraus
              p q s M hM e w z σ (.inr (ik, j))) *
          concentrationAliceKraus
            p q s M hM e w z σ (.inr (ik, j)) =
        Matrix.single i i
          ((leftoverRatio p q i / (M : ℝ) : ℝ) : ℂ) := by
    dsimp [concentrationAliceKraus]
    rw [Matrix.conjTranspose_single,
      Matrix.single_mul_single_same]
    congr 1
    change
      (starRingEnd ℂ)
            (Real.sqrt
              (leftoverRatio p q _ / (M : ℝ))) *
          (Real.sqrt
            (leftoverRatio p q _ / (M : ℝ)) : ℂ) =
        _
    rw [Complex.conj_ofReal]
    norm_cast
    simpa [pow_two] using
      Real.sq_sqrt
        (div_nonneg (hleft0 _) hMreal.le)
  rw [Fintype.sum_sum_type]
  simp_rw [hsuccess]
  rw [Fintype.sum_prod_type]
  simp_rw [hfailure]
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply,
    Matrix.diagonal_apply, Matrix.single_apply]
  by_cases hij : i = j
  · subst j
    simp only [if_true, Matrix.one_apply]
    have hsuccessSum :
        ∑ k, successRatio p s M w z k i =
          if p i = 0 then 0 else q i / p i := by
      by_cases hpi : p i = 0
      · simp [successRatio, hpi]
      · rw [if_neg hpi]
        simp_rw [successRatio, hpi]
        calc
          ∑ k,
              s * w k * z k i / ((M : ℝ) * p i) =
              s / ((M : ℝ) * p i) *
                ∑ k, w k * z k i := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro k hk
                  field_simp <;> ring
          _ =
              s / ((M : ℝ) * p i) *
                ((M : ℝ) * q i / s) := by
                  rw [hbar]
          _ = q i / p i := by
            field_simp <;> ring
    have hsuccessSumC :
        ∑ k,
            (successRatio p s M w z k i : ℂ) =
          ((if p i = 0 then 0 else q i / p i : ℝ) :
            ℂ) := by
      exact_mod_cast hsuccessSum
    rw [hsuccessSumC]
    have hfailureSum :
        ∑ x : Fin (Fintype.card D), ∑ _j : Fin M,
            (if
                (Fintype.equivFin D).symm x = i ∧
                  (Fintype.equivFin D).symm x = i
              then
                ((leftoverRatio p q
                    ((Fintype.equivFin D).symm x) /
                    (M : ℝ) : ℝ) : ℂ)
              else 0) =
          (leftoverRatio p q i : ℂ) := by
      calc
        _ = ∑ x : D, ∑ _j : Fin M,
            (if x = i ∧ x = i then
              ((leftoverRatio p q x / (M : ℝ) : ℝ) :
                ℂ)
            else 0) := by
              apply Fintype.sum_equiv
                (Fintype.equivFin D).symm
              intro x
              rfl
        _ = _ := by
          rw [Finset.sum_eq_single i]
          · simp only [and_self, if_true,
              Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            norm_cast
            have hMr : (M : ℝ) ≠ 0 := by
              exact_mod_cast hM.ne'
            field_simp
          · intro x hx hxi
            simp [hxi]
          · simp
    rw [hfailureSum]
    by_cases hpi : p i = 0
    · have hqi : q i = 0 :=
        le_antisymm (hpi ▸ hqp i) (hq0 i)
      simp [hpi, hqi, leftoverRatio]
    · simp [hpi, leftoverRatio]
      have hpC : (p i : ℂ) ≠ 0 := by
        exact_mod_cast hpi
      field_simp [hpC]
      ring
  · simp only [if_false, Matrix.one_apply, hij]
    have hf0 :
        (∑ ik, ∑ m : Fin M,
          if
              (Fintype.equivFin D).symm ik = i ∧
                (Fintype.equivFin D).symm ik = j
            then
              ((leftoverRatio p q
                  ((Fintype.equivFin D).symm ik) /
                  (M : ℝ) : ℝ) : ℂ)
            else 0) =
          0 := by
      apply Finset.sum_eq_zero
      intro ik hik
      apply Finset.sum_eq_zero
      intro m hm
      split
      · rename_i h
        exact (hij (h.1.symm.trans h.2)).elim
      · rfl
    simp only [Finset.sum_const_zero, zero_add]
    exact hf0

/-- Bob's feed-forward correction: the same relabeling permutation on a
successful convex-decomposition branch, and a transposition which brings the
recorded input coordinate to the recorded output coordinate on a fallback
branch. -/
private noncomputable def concentrationBobUnitary
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    {M : ℕ} (e : Fin M ↪ D)
    (σ : ι → Equiv.Perm D) :
    (ι ⊕ (Fin (Fintype.card D) × Fin M)) → CMatrix D
  | .inl k => (σ k).permMatrix ℂ
  | .inr pair =>
      (Equiv.swap (e pair.2)
        ((Fintype.equivFin D).symm pair.1)).permMatrix ℂ

private theorem concentrationBobUnitary_isometry
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    {M : ℕ} (e : Fin M ↪ D)
    (σ : ι → Equiv.Perm D) :
    ∀ o,
      Matrix.conjTranspose
            (concentrationBobUnitary e σ o) *
          concentrationBobUnitary e σ o =
        (1 : CMatrix D) := by
  intro o
  cases o <;>
    simp only [concentrationBobUnitary,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul] <;>
    simp

private theorem sqrt_mul_sqrt_successRatio
    {D : Type*} {ι : Type}
    (p : D → ℝ) (s : ℝ) (M : ℕ)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hs : 0 < s) (hM : 0 < M)
    (hw0 : ∀ k, 0 ≤ w k)
    (hz01 : ∀ k i, z k i = 0 ∨ z k i = 1)
    (hzero : ∀ k i, p i = 0 → w k * z k i = 0)
    (k : ι) (i : D) :
    Real.sqrt (p i) *
        Real.sqrt (successRatio p s M w z k i) =
      Real.sqrt (s * w k / (M : ℝ)) * z k i := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rcases hz01 k i with hzi | hzi
  · simp [hzi, successRatio]
  · rw [hzi]
    simp only [mul_one]
    by_cases hpi : p i = 0
    · have hwk : w k = 0 := by
        simpa [hzi] using hzero k i hpi
      simp [hpi, hwk, successRatio]
    · have hpipos : 0 < p i :=
        lt_of_le_of_ne (hp0 i) (Ne.symm hpi)
      have hratio0 :
          0 ≤ successRatio p s M w z k i := by
        rw [successRatio, if_neg hpi, hzi]
        exact
          div_nonneg
            (mul_nonneg (mul_nonneg hs.le (hw0 k)) zero_le_one)
            (mul_nonneg hMreal.le hpipos.le)
      have htarget0 : 0 ≤ s * w k / (M : ℝ) := by
        exact div_nonneg (mul_nonneg hs.le (hw0 k)) hMreal.le
      apply (sq_eq_sq₀
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt (hp0 i),
        Real.sq_sqrt hratio0, Real.sq_sqrt htarget0]
      rw [successRatio, if_neg hpi, hzi]
      field_simp

private noncomputable def diagonalSchmidtVector
    {D : Type*} [DecidableEq D] (p : D → ℝ) :
    D × D → ℂ :=
  fun ij =>
    if ij.1 = ij.2 then ((Real.sqrt (p ij.1) : ℝ) : ℂ) else 0

private theorem permMatrix_mul_diagonal_apply
    {D : Type*} [Fintype D] [DecidableEq D]
    (σ : Equiv.Perm D) (a : D → ℂ) (i j : D) :
    (σ.permMatrix ℂ * Matrix.diagonal a) i j =
      if σ i = j then a j else 0 := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

private theorem permuted_diagonal_filter_mulVec
    {D : Type*} [Fintype D] [DecidableEq D]
    (σ : Equiv.Perm D) (a : D → ℂ) (p : D → ℝ)
    (x y : D) :
    (Matrix.kronecker
        (σ.permMatrix ℂ * Matrix.diagonal a)
        (σ.permMatrix ℂ)).mulVec (diagonalSchmidtVector p) (x, y) =
      if x = y then
        a (σ x) * ((Real.sqrt (p (σ x)) : ℝ) : ℂ)
      else 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  simp only [permMatrix_mul_diagonal_apply]
  rw [Finset.sum_eq_single (σ x)]
  · rw [Finset.sum_eq_single (σ y)]
    · by_cases hxy : x = y
      · subst y
        simp [diagonalSchmidtVector]
      · have hsxy : σ x ≠ σ y := fun h => hxy (σ.injective h)
        simp [diagonalSchmidtVector, hxy, hsxy]
    · intro j hj hjne
      simp [Ne.symm hjne]
    · simp
  · intro i hi hine
    simp [Ne.symm hine]
  · simp

private noncomputable def embeddedUniformVector
    {D : Type*} [DecidableEq D] {M : ℕ}
    (e : Fin M ↪ D) (c : ℝ) : D × D → ℂ :=
  fun ij =>
    if ij.1 = ij.2 ∧ ij.1 ∈ Set.range e then (c : ℂ) else 0

private theorem concentration_success_preVector
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    (p : D → ℝ) (s : ℝ) (M : ℕ) (hM : 0 < M)
    (e : Fin M ↪ D)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (σ : ι → Equiv.Perm D)
    (hp0 : ∀ i, 0 ≤ p i) (hs : 0 < s)
    (hw0 : ∀ k, 0 ≤ w k)
    (hz01 : ∀ k i, z k i = 0 ∨ z k i = 1)
    (hzero : ∀ k i, p i = 0 → w k * z k i = 0)
    (hsupport :
      ∀ k i, z k (σ k i) = 1 ↔ i ∈ Set.range e)
    (k : ι) :
    (Matrix.kronecker
        (concentrationAliceKraus
          p p s M hM e w z σ (.inl k))
        (concentrationBobUnitary e σ (.inl k))).mulVec
          (diagonalSchmidtVector p) =
      embeddedUniformVector e
        (Real.sqrt (s * w k / (M : ℝ))) := by
  funext ij
  rcases ij with ⟨x, y⟩
  rw [concentrationAliceKraus, concentrationBobUnitary,
    permuted_diagonal_filter_mulVec]
  by_cases hxy : x = y
  · subst y
    simp only [if_pos, embeddedUniformVector]
    by_cases hx : x ∈ Set.range e
    · rw [if_pos (by simp [hx])]
      have hz : z k (σ k x) = 1 := (hsupport k x).2 hx
      have hsqrt :=
        sqrt_mul_sqrt_successRatio p s M w z hp0 hs hM
          hw0 hz01 hzero k (σ k x)
      rw [hz, mul_one] at hsqrt
      norm_cast
      simpa [mul_comm] using hsqrt
    · rw [if_neg (by simp [hx])]
      have hz : z k (σ k x) = 0 := by
        rcases hz01 k (σ k x) with hz | hz
        · exact hz
        · exact (hx ((hsupport k x).1 hz)).elim
      simp [successRatio, hz]
  · simp [hxy, embeddedUniformVector]

private theorem sqrt_mul_sqrt_leftoverRatio
    {D : Type*} (p q : D → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hqp : ∀ i, q i ≤ p i)
    (M : ℕ) (hM : 0 < M) (i : D) :
    Real.sqrt (p i) *
        Real.sqrt (leftoverRatio p q i / (M : ℝ)) =
      Real.sqrt ((p i - q i) / (M : ℝ)) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  by_cases hpi : p i = 0
  · have hqi : q i = 0 :=
      le_antisymm (hpi ▸ hqp i) (hq0 i)
    simp [hpi, hqi, leftoverRatio]
  · have hpipos : 0 < p i :=
      lt_of_le_of_ne (hp0 i) (Ne.symm hpi)
    have hleft0 : 0 ≤ leftoverRatio p q i / (M : ℝ) := by
      apply div_nonneg
      · rw [leftoverRatio, if_neg hpi]
        exact div_nonneg (sub_nonneg.mpr (hqp i)) hpipos.le
      · exact hMreal.le
    have htarget0 : 0 ≤ (p i - q i) / (M : ℝ) :=
      div_nonneg (sub_nonneg.mpr (hqp i)) hMreal.le
    apply (sq_eq_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt (hp0 i),
      Real.sq_sqrt hleft0, Real.sq_sqrt htarget0]
    rw [leftoverRatio, if_neg hpi]
    field_simp

private noncomputable def embeddedBasisVector
    {D : Type*} [DecidableEq D] (a : D) (c : ℂ) :
    D × D → ℂ :=
  fun ij => if ij = (a, a) then c else 0

private theorem single_swap_mulVec
    {D : Type*} [Fintype D] [DecidableEq D]
    (a i : D) (c : ℂ) (p : D → ℝ) :
    (Matrix.kronecker
        (Matrix.single a i c : CMatrix D)
        ((Equiv.swap a i).permMatrix ℂ)).mulVec
          (diagonalSchmidtVector p) =
      embeddedBasisVector a
        (c * ((Real.sqrt (p i) : ℝ) : ℂ)) := by
  funext xy
  rcases xy with ⟨x, y⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · by_cases hx : x = a
      · subst x
        by_cases hy : y = a
        · subst y
          simp [diagonalSchmidtVector, embeddedBasisVector]
        · simp [diagonalSchmidtVector, embeddedBasisVector, hy,
            Equiv.swap_apply_eq_iff]
      · simp [diagonalSchmidtVector, embeddedBasisVector, hx, Ne.symm hx]
    · intro j hj hji
      simp [diagonalSchmidtVector, Ne.symm hji]
    · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · simp

private theorem concentration_fallback_preVector
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    (p q : D → ℝ) (s : ℝ) (M : ℕ) (hM : 0 < M)
    (e : Fin M ↪ D)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (σ : ι → Equiv.Perm D)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hqp : ∀ i, q i ≤ p i)
    (ik : Fin (Fintype.card D)) (m : Fin M) :
    let i := (Fintype.equivFin D).symm ik
    (Matrix.kronecker
        (concentrationAliceKraus
          p q s M hM e w z σ (.inr (ik, m)))
        (concentrationBobUnitary e σ (.inr (ik, m)))).mulVec
          (diagonalSchmidtVector p) =
      embeddedBasisVector (e m)
        (((Real.sqrt ((p i - q i) / (M : ℝ)) : ℝ) : ℂ)) := by
  dsimp only
  rw [concentrationAliceKraus, concentrationBobUnitary,
    single_swap_mulVec]
  congr 1
  norm_cast
  simpa [mul_comm] using
    sqrt_mul_sqrt_leftoverRatio p q hp0 hq0 hqp M hM
      ((Fintype.equivFin D).symm ik)

private theorem compressionKraus_pair_mulVec_of_supported
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) (e : Fin M ↪ D)
    (v : D × D → ℂ)
    (hv :
      ∀ i j,
        i ∉ Set.range e ∨ j ∉ Set.range e →
          v (i, j) = 0)
    (a b : Option (Fin (Fintype.card D))) :
    (Matrix.kronecker
        (compressionKraus hM e a)
        (compressionKraus hM e b)).mulVec v =
      match a, b with
      | none, none =>
          fun mn : Fin M × Fin M => v (e mn.1, e mn.2)
      | _, _ => 0 := by
  classical
  funext mn
  rcases mn with ⟨m, n⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  cases a with
  | none =>
      cases b with
      | none =>
          simp only [compressionKraus]
          rw [Finset.sum_eq_single (e m)]
          · rw [Finset.sum_eq_single (e n)]
            · simp
            · intro j hj hjne
              simp [Ne.symm hjne]
            · simp
          · intro i hi hine
            simp [Ne.symm hine]
          · simp
      | some bk =>
          let j := (Fintype.equivFin D).symm bk
          by_cases hj : j ∈ Set.range e
          · simp [compressionKraus, j, hj]
          · simp only [compressionKraus, j, hj, if_false]
            rw [Finset.sum_eq_single (e m)]
            · rw [Finset.sum_eq_single j]
              · simp [hv (e m) j (Or.inr hj)]
              · intro x hx hxj
                simp [Matrix.single_apply, j, Ne.symm hxj]
              · simp
            · intro x hx hxm
              simp [Ne.symm hxm]
            · simp
  | some ak =>
      let i := (Fintype.equivFin D).symm ak
      by_cases hi : i ∈ Set.range e
      · simp [compressionKraus, i, hi]
      · simp only [compressionKraus, i, hi, if_false]
        rw [Finset.sum_eq_single i]
        · apply Finset.sum_eq_zero
          intro j hj
          simp [hv i j (Or.inl hi)]
        · intro x hx hxi
          simp [Matrix.single_apply, i, Ne.symm hxi]
        · simp

private noncomputable def uniformDiagonalVector
    (M : ℕ) (c : ℂ) : Fin M × Fin M → ℂ :=
  fun mn => if mn.1 = mn.2 then c else 0

private theorem compressionKraus_pair_mulVec_embeddedUniform
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) (e : Fin M ↪ D) (c : ℝ)
    (a b : Option (Fin (Fintype.card D))) :
    (Matrix.kronecker
        (compressionKraus hM e a)
        (compressionKraus hM e b)).mulVec
          (embeddedUniformVector e c) =
      match a, b with
      | none, none => uniformDiagonalVector M (c : ℂ)
      | _, _ => 0 := by
  rw [compressionKraus_pair_mulVec_of_supported]
  · cases a <;> cases b <;> funext mn <;>
      rcases mn with ⟨m, n⟩ <;>
      simp [embeddedUniformVector, uniformDiagonalVector, e.injective.eq_iff]
  · intro i j hij
    simp only [embeddedUniformVector]
    rw [if_neg]
    intro h
    rcases hij with hi | hj
    · exact hi h.2
    · exact hj (h.1 ▸ h.2)

private theorem compressionKraus_pair_mulVec_embeddedBasis
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : ℕ} (hM : 0 < M) (e : Fin M ↪ D)
    (m : Fin M) (c : ℂ)
    (a b : Option (Fin (Fintype.card D))) :
    (Matrix.kronecker
        (compressionKraus hM e a)
        (compressionKraus hM e b)).mulVec
          (embeddedBasisVector (e m) c) =
      match a, b with
      | none, none => embeddedBasisVector m c
      | _, _ => 0 := by
  rw [compressionKraus_pair_mulVec_of_supported]
  · cases a <;> cases b <;> funext mn <;>
      rcases mn with ⟨i, j⟩ <;>
      simp [embeddedBasisVector, Prod.ext_iff, e.injective.eq_iff]
  · intro i j hij
    simp only [embeddedBasisVector]
    rw [if_neg]
    intro h
    have hi : i = e m := congrArg Prod.fst h
    have hj : j = e m := congrArg Prod.snd h
    subst i
    subst j
    exact hij.elim
      (fun hi => hi (Set.mem_range_self m))
      (fun hj => hj (Set.mem_range_self m))

private theorem kronecker_composed_mulVec
    {A B C A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (LA : Matrix A' A ℂ) (KA : Matrix A C ℂ)
    (LB : Matrix B' B ℂ) (KB : Matrix B C ℂ)
    (v : C × C → ℂ) :
    (Matrix.kronecker (LA * KA) (LB * KB)).mulVec v =
      (Matrix.kronecker LA LB).mulVec
        ((Matrix.kronecker KA KB).mulVec v) := by
  rw [show
    Matrix.kronecker (LA * KA) (LB * KB) =
      Matrix.kronecker LA LB * Matrix.kronecker KA KB by
        simpa [Matrix.kronecker] using
          Matrix.mul_kronecker_mul LA KA LB KB]
  exact
    (Matrix.mulVec_mulVec v
      (Matrix.kronecker LA LB) (Matrix.kronecker KA KB)).symm

private theorem concentration_success_finalVector
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    (p : D → ℝ) (s : ℝ) (M : ℕ) (hM : 0 < M)
    (e : Fin M ↪ D)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (σ : ι → Equiv.Perm D)
    (hp0 : ∀ i, 0 ≤ p i) (hs : 0 < s)
    (hw0 : ∀ k, 0 ≤ w k)
    (hz01 : ∀ k i, z k i = 0 ∨ z k i = 1)
    (hzero : ∀ k i, p i = 0 → w k * z k i = 0)
    (hsupport :
      ∀ k i, z k (σ k i) = 1 ↔ i ∈ Set.range e)
    (k : ι) (a b : Option (Fin (Fintype.card D))) :
    (Matrix.kronecker
        (compressionKraus hM e a *
          concentrationAliceKraus
            p p s M hM e w z σ (.inl k))
        (compressionKraus hM e b *
          concentrationBobUnitary e σ (.inl k))).mulVec
          (diagonalSchmidtVector p) =
      match a, b with
      | none, none =>
          uniformDiagonalVector M
            (((Real.sqrt (s * w k / (M : ℝ)) : ℝ) : ℂ))
      | _, _ => 0 := by
  rw [kronecker_composed_mulVec,
    concentration_success_preVector p s M hM e w z σ
      hp0 hs hw0 hz01 hzero hsupport k,
    compressionKraus_pair_mulVec_embeddedUniform]

private theorem concentration_fallback_finalVector
    {D : Type*} [Fintype D] [DecidableEq D]
    {ι : Type} [Fintype ι]
    (p q : D → ℝ) (s : ℝ) (M : ℕ) (hM : 0 < M)
    (e : Fin M ↪ D)
    (w : ι → ℝ) (z : ι → D → ℝ)
    (σ : ι → Equiv.Perm D)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hqp : ∀ i, q i ≤ p i)
    (ik : Fin (Fintype.card D)) (m : Fin M)
    (a b : Option (Fin (Fintype.card D))) :
    let i := (Fintype.equivFin D).symm ik
    (Matrix.kronecker
        (compressionKraus hM e a *
          concentrationAliceKraus
            p q s M hM e w z σ (.inr (ik, m)))
        (compressionKraus hM e b *
          concentrationBobUnitary e σ (.inr (ik, m)))).mulVec
          (diagonalSchmidtVector p) =
      match a, b with
      | none, none =>
          embeddedBasisVector m
            (((Real.sqrt ((p i - q i) / (M : ℝ)) : ℝ) : ℂ))
      | _, _ => 0 := by
  dsimp only
  rw [kronecker_composed_mulVec,
    concentration_fallback_preVector
      p q s M hM e w z σ hp0 hq0 hqp ik m,
    compressionKraus_pair_mulVec_embeddedBasis]

/- Extract the finite convex decomposition used by the Nielsen instrument,
and simultaneously choose relabeling permutations which carry every support
to one fixed `M`-element coordinate subspace. -/
private theorem exists_uniform_decomposition_with_permutations
    {D : Type*} [Fintype D] [DecidableEq D]
    (r : D → ℝ) (M : ℕ)
    (hr :
      r ∈ convexHull ℝ (uniformSubsetVectors D M)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (e : Fin M ↪ D) (w : ι → ℝ) (z : ι → D → ℝ)
      (σ : ι → Equiv.Perm D),
      (∀ k, 0 ≤ w k) ∧
      (∑ k, w k = 1) ∧
      (∀ k i, z k i = 0 ∨ z k i = 1) ∧
      (∀ k i, z k (σ k i) = 1 ↔ i ∈ Set.range e) ∧
      (∀ i, ∑ k, w k * z k i = r i) := by
  classical
  rw [mem_convexHull_iff_exists_fintype] at hr
  obtain ⟨ι, hιFintype, w, z, hw0, hwsum, hz, hbar⟩ := hr
  letI : Fintype ι := hιFintype
  have hz01 : ∀ k i, z k i = 0 ∨ z k i = 1 :=
    fun k i => (hz k).1 i
  have hzsum : ∀ k, ∑ i, z k i = (M : ℝ) :=
    fun k => (hz k).2
  let support (k : ι) : Finset D :=
    Finset.univ.filter fun i => z k i = 1
  have hsupportCard (k : ι) : (support k).card = M := by
    have hsum :
        ∑ i : D, z k i = ((support k).card : ℝ) := by
      calc
        ∑ i : D, z k i =
            ∑ i : D, if z k i = 1 then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              rcases hz01 k i with hki | hki <;> simp [hki]
        _ = ((support k).card : ℝ) := by
          simp [support]
    have hcardReal : ((support k).card : ℝ) = (M : ℝ) :=
      hsum.symm.trans (hzsum k)
    exact_mod_cast hcardReal
  have hι : Nonempty ι := by
    by_contra hempty
    haveI : IsEmpty ι := not_nonempty_iff.mp hempty
    simpa using hwsum
  let f (k : ι) : Fin M ↪ D :=
    Classical.choose
      (Function.Embedding.exists_of_card_eq_finset
        (s := support k) (by simp [hsupportCard k]))
  have hf (k : ι) :
      Finset.map (f k) Finset.univ = support k :=
    Classical.choose_spec
      (Function.Embedding.exists_of_card_eq_finset
        (s := support k) (by simp [hsupportCard k]))
  let k₀ : ι := Classical.choice hι
  let e : Fin M ↪ D := f k₀
  have hperm (k : ι) :
      ∃ τ : Equiv.Perm D, ∀ m : Fin M, τ (e m) = f k m :=
    Equiv.Perm.exists_extending_pair e (f k) e.injective (f k).injective
  let σ (k : ι) : Equiv.Perm D := Classical.choose (hperm k)
  have hσ (k : ι) (m : Fin M) :
      σ k (e m) = f k m :=
    Classical.choose_spec (hperm k) m
  refine
    ⟨ι, inferInstance, e, w, z, σ, hw0, hwsum, hz01, ?_, ?_⟩
  · intro k i
    constructor
    · intro hzi
      have hmem : σ k i ∈ support k := by
        simp [support, hzi]
      rw [← hf k] at hmem
      obtain ⟨m, hm, hfm⟩ := Finset.mem_map.mp hmem
      have him : i = e m := by
        apply (σ k).injective
        rw [hσ k m]
        exact hfm.symm
      exact ⟨m, him.symm⟩
    · rintro ⟨m, rfl⟩
      rw [hσ k m]
      have hmem : f k m ∈ support k := by
        rw [← hf k]
        simp
      simpa [support] using hmem
  · intro i
    have hi := congrFun hbar i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hi

private noncomputable def correlatedDiagonalDensity (M : ℕ) :
    CMatrix (Fin M × Fin M) :=
  ((1 : ℂ) / (M : ℝ)) •
    ∑ m : Fin M, rankOneMatrix (embeddedBasisVector m 1)

private noncomputable def concentrationOutputMatrix
    (M : ℕ) (s : ℝ) : CMatrix (Fin M × Fin M) :=
  (s : ℂ) • maximallyEntangledDensity M +
    ((1 - s : ℝ) : ℂ) • correlatedDiagonalDensity M

private theorem correlatedDiagonalDensity_apply
    (M : ℕ) (i j : Fin M × Fin M) :
    correlatedDiagonalDensity M i j =
      if i = j ∧ i.1 = i.2 then ((1 : ℂ) / (M : ℝ)) else 0 := by
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  simp only [correlatedDiagonalDensity, Matrix.smul_apply,
    Matrix.sum_apply, rankOneMatrix_apply, embeddedBasisVector]
  by_cases hi : ia = ib
  · subst ib
    rw [Finset.sum_eq_single ia]
    · by_cases h : ja = ia ∧ jb = ia
      · have hjpair : (ja, jb) = (ia, ia) := Prod.ext h.1 h.2
        rw [if_pos rfl, if_pos hjpair,
          if_pos ⟨hjpair.symm, rfl⟩]
        simp
      · have hjpair : (ja, jb) ≠ (ia, ia) := by
          intro heq
          exact h ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
        have hrev : ¬((ia, ia) = (ja, jb) ∧ ia = ia) := by
          aesop
        rw [if_pos rfl, if_neg hjpair, if_neg hrev]
        simp
    · intro m hm hmi
      rw [if_neg]
      · simp
      · intro h
        exact hmi (congrArg Prod.fst h).symm
    · simp
  · rw [if_neg (by simp [Prod.ext_iff, hi])]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    · simp
    · intro h
      exact hi
        ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)

private theorem correlatedDiagonalDensity_mul_maximallyEntangledDensity
    (M : ℕ) :
    correlatedDiagonalDensity M * maximallyEntangledDensity M =
      ((1 : ℂ) / (M : ℝ)) • maximallyEntangledDensity M := by
  ext i j
  simp only [Matrix.mul_apply, correlatedDiagonalDensity_apply,
    Matrix.smul_apply]
  by_cases hi : i.1 = i.2
  · rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro k hk hki
      simp [Ne.symm hki]
    · simp
  · calc
      ∑ k,
          (if i = k ∧ i.1 = i.2 then (1 : ℂ) / (M : ℝ) else 0) *
            maximallyEntangledDensity M k j = 0 := by
              apply Finset.sum_eq_zero
              intro k hk
              simp [hi]
      _ = ((1 : ℂ) / (M : ℝ)) *
          maximallyEntangledDensity M i j := by
            simp [maximallyEntangledDensity, rankOneMatrix_apply,
              maximallyEntangledVector, hi]

private theorem maximallyEntangledDensity_mul_correlatedDiagonalDensity
    (M : ℕ) :
    maximallyEntangledDensity M * correlatedDiagonalDensity M =
      ((1 : ℂ) / (M : ℝ)) • maximallyEntangledDensity M := by
  have hτ :
      Matrix.conjTranspose (correlatedDiagonalDensity M) =
        correlatedDiagonalDensity M := by
    unfold correlatedDiagonalDensity
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
    simp
  have hΦ :
      Matrix.conjTranspose (maximallyEntangledDensity M) =
        maximallyEntangledDensity M := by
    simp [maximallyEntangledDensity]
  calc
    maximallyEntangledDensity M * correlatedDiagonalDensity M =
        Matrix.conjTranspose
          (correlatedDiagonalDensity M *
            maximallyEntangledDensity M) := by
              rw [Matrix.conjTranspose_mul, hΦ, hτ]
    _ = Matrix.conjTranspose
          (((1 : ℂ) / (M : ℝ)) •
            maximallyEntangledDensity M) := by
              rw [correlatedDiagonalDensity_mul_maximallyEntangledDensity]
    _ = ((1 : ℂ) / (M : ℝ)) •
          maximallyEntangledDensity M := by
            rw [Matrix.conjTranspose_smul, hΦ]
            simp

private theorem maximallyEntangledDensity_trace_eq_one_local
    (M : ℕ) (hM : 0 < M) :
    (maximallyEntangledDensity M).trace = 1 := by
  rw [maximallyEntangledDensity, rankOneMatrix_trace]
  simp only [dotProduct, maximallyEntangledVector]
  rw [Fintype.sum_prod_type]
  simp
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hM))
  field_simp
  norm_cast
  rw [Real.sq_sqrt (Nat.cast_nonneg M)]

private noncomputable def maximallyEntangledPureVectorLocal
    (M : ℕ) (hM : 0 < M) :
    PureVector (Fin M × Fin M) where
  amp := maximallyEntangledVector M
  trace_rankOne_eq_one := by
    simpa [maximallyEntangledDensity] using
      maximallyEntangledDensity_trace_eq_one_local M hM

private theorem concentrationOutputMatrix_mul_maximallyEntangledDensity
    (M : ℕ) (hM : 0 < M) (s : ℝ) :
    concentrationOutputMatrix M s * maximallyEntangledDensity M =
      ((s + (1 - s) / (M : ℝ) : ℝ) : ℂ) •
        maximallyEntangledDensity M := by
  have hΦid :
      maximallyEntangledDensity M * maximallyEntangledDensity M =
        maximallyEntangledDensity M := by
    simpa [maximallyEntangledPureVectorLocal,
      maximallyEntangledDensity] using
        (maximallyEntangledPureVectorLocal M hM).state_matrix_mul_self
  unfold concentrationOutputMatrix
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hΦid,
    correlatedDiagonalDensity_mul_maximallyEntangledDensity,
    smul_smul, ← add_smul]
  congr 1
  norm_cast
  ring

private theorem maximallyEntangledDensity_mul_concentrationOutputMatrix
    (M : ℕ) (hM : 0 < M) (s : ℝ) :
    maximallyEntangledDensity M * concentrationOutputMatrix M s =
      ((s + (1 - s) / (M : ℝ) : ℝ) : ℂ) •
        maximallyEntangledDensity M := by
  have hΦid :
      maximallyEntangledDensity M * maximallyEntangledDensity M =
        maximallyEntangledDensity M := by
    simpa [maximallyEntangledPureVectorLocal,
      maximallyEntangledDensity] using
        (maximallyEntangledPureVectorLocal M hM).state_matrix_mul_self
  unfold concentrationOutputMatrix
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hΦid,
    maximallyEntangledDensity_mul_correlatedDiagonalDensity,
    smul_smul, ← add_smul]
  congr 1
  norm_cast
  ring

private theorem quantumFidelity_concentrationOutputMatrix
    (M : ℕ) (hM : 0 < M) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ρ : State (Fin M × Fin M))
    (hρ : ρ.matrix = concentrationOutputMatrix M s) :
    quantumFidelity ρ.matrix (maximallyEntangledDensity M) =
      Real.sqrt (s + (1 - s) / (M : ℝ)) := by
  let Φ : CMatrix (Fin M × Fin M) :=
    maximallyEntangledDensity M
  let a : ℝ := s + (1 - s) / (M : ℝ)
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact add_nonneg hs0
      (div_nonneg (sub_nonneg.mpr hs1) hMreal.le)
  have hΦpos : Φ.PosSemidef := by
    dsimp [Φ]
    exact rankOneMatrix_pos _
  have hΦid : Φ * Φ = Φ := by
    simpa [Φ, maximallyEntangledPureVectorLocal,
      maximallyEntangledDensity] using
        (maximallyEntangledPureVectorLocal M hM).state_matrix_mul_self
  have hρΦ :
      ρ.matrix * Φ = (a : ℂ) • Φ := by
    rw [hρ]
    exact concentrationOutputMatrix_mul_maximallyEntangledDensity
      M hM s
  have hΦρ :
      Φ * ρ.matrix = (a : ℂ) • Φ := by
    rw [hρ]
    exact maximallyEntangledDensity_mul_concentrationOutputMatrix
      M hM s
  have hcomm : Commute ρ.matrix Φ := by
    exact hρΦ.trans hΦρ.symm
  let S : CMatrix (Fin M × Fin M) := CFC.sqrt ρ.matrix
  have hSsq : S * S = ρ.matrix := by
    dsimp [S]
    exact CFC.sqrt_mul_sqrt_self ρ.matrix (ha := ρ.pos.nonneg)
  have hScomm : Commute S Φ := by
    dsimp [S]
    rw [CFC.sqrt_eq_cfc]
    exact hcomm.cfc_nnreal NNReal.sqrt
  have hcore :
      S * Φ * S = (a : ℂ) • Φ := by
    calc
      S * Φ * S = S * (Φ * S) := by rw [Matrix.mul_assoc]
      _ = S * (S * Φ) := by rw [← hScomm.eq]
      _ = (S * S) * Φ := by rw [Matrix.mul_assoc]
      _ = ρ.matrix * Φ := by rw [hSsq]
      _ = (a : ℂ) • Φ := hρΦ
  let Q : CMatrix (Fin M × Fin M) :=
    (Real.sqrt a : ℝ) • Φ
  have hQsq : Q * Q = (a : ℂ) • Φ := by
    calc
      Q * Q =
          ((Real.sqrt a * Real.sqrt a : ℝ)) • (Φ * Φ) := by
            simp [Q, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (a : ℝ) • Φ := by
        rw [hΦid, Real.mul_self_sqrt ha0]
      _ = (a : ℂ) • Φ := by
        ext i j
        simp [Algebra.smul_def]
  have hQnonneg : 0 ≤ Q := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact hΦpos.smul (Real.sqrt_nonneg a)
  have hsqrtCore : CFC.sqrt (S * Φ * S) = Q := by
    rw [hcore]
    exact CFC.sqrt_unique hQsq hQnonneg
  unfold quantumFidelity matrixSqrt
  change Complex.re (Matrix.trace (CFC.sqrt (S * Φ * S))) =
    Real.sqrt a
  rw [hsqrtCore]
  dsimp [Q, Φ]
  rw [Matrix.trace_smul,
    maximallyEntangledDensity_trace_eq_one_local M hM]
  simp

private theorem rankOne_uniformDiagonalVector
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t) :
    rankOneMatrix
        (uniformDiagonalVector M
          (((Real.sqrt (t / (M : ℝ)) : ℝ) : ℂ))) =
      (t : ℂ) • maximallyEntangledDensity M := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hdiv0 : 0 ≤ t / (M : ℝ) := div_nonneg ht hMreal.le
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  by_cases hi : ia = ib
  · subst ib
    by_cases hj : ja = jb
    · subst jb
      simp only [rankOneMatrix_apply, uniformDiagonalVector,
        if_pos, Matrix.smul_apply, maximallyEntangledDensity,
        maximallyEntangledVector]
      simp only [Complex.star_def, map_div, Complex.conj_ofReal, smul_eq_mul]
      norm_cast
      rw [← pow_two, Real.sq_sqrt hdiv0]
      rw [Complex.conj_ofReal]
      norm_cast
      rw [show
        (1 / Real.sqrt (M : ℝ)) *
            (1 / Real.sqrt (M : ℝ)) =
          1 / (M : ℝ) by
            field_simp [Real.sqrt_ne_zero'.mpr hMreal]
            exact (Real.sq_sqrt hMreal.le).symm]
      ring
    · simp [rankOneMatrix_apply, uniformDiagonalVector, hj,
        maximallyEntangledDensity, maximallyEntangledVector]
  · simp [rankOneMatrix_apply, uniformDiagonalVector, hi,
      maximallyEntangledDensity, maximallyEntangledVector]

private theorem rankOne_embeddedBasisVector_sqrt
    (M : ℕ) (hM : 0 < M) (m : Fin M)
    (t : ℝ) (ht : 0 ≤ t) :
    rankOneMatrix
        (embeddedBasisVector m
          (((Real.sqrt (t / (M : ℝ)) : ℝ) : ℂ))) =
      ((t / (M : ℝ) : ℝ) : ℂ) •
        rankOneMatrix (embeddedBasisVector m 1) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hdiv0 : 0 ≤ t / (M : ℝ) := div_nonneg ht hMreal.le
  ext i j
  by_cases hi : i = (m, m)
  · subst i
    by_cases hj : j = (m, m)
    · subst j
      simp [rankOneMatrix_apply, embeddedBasisVector,
        Real.sq_sqrt hdiv0, pow_two]
      norm_cast
      rw [← pow_two, div_pow, Real.sq_sqrt ht,
        Real.sq_sqrt hMreal.le]
    · simp [rankOneMatrix_apply, embeddedBasisVector, hj]
  · simp [rankOneMatrix_apply, embeddedBasisVector, hi]

set_option maxHeartbeats 1200000 in
private theorem exists_concentration_protocol
    {D : Type*} [Fintype D] [DecidableEq D]
    (p q : D → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hqp : ∀ i, q i ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (s : ℝ) (hs : 0 < s) (hqSum : ∑ i, q i = s)
    (M : ℕ) (hM : 0 < M)
    (hconvex :
      (fun i : D => (M : ℝ) * q i / s) ∈
        convexHull ℝ (uniformSubsetVectors D M)) :
    ∃ P : FiniteRoundLOCCProtocol D D (Fin M) (Fin M),
      P.channel.map (rankOneMatrix (diagonalSchmidtVector p)) =
        concentrationOutputMatrix M s := by
  classical
  obtain
    ⟨ι, hιFintype, e, w, z, σ,
      hw0, hwsum, hz01, hsupport, hbar⟩ :=
    exists_uniform_decomposition_with_permutations
      (fun i : D => (M : ℝ) * q i / s) M hconvex
  letI : Fintype ι := hιFintype
  have hzero :
      ∀ k i, p i = 0 → w k * z k i = 0 := by
    intro k i hpi
    have hqi : q i = 0 :=
      le_antisymm (hpi ▸ hqp i) (hq0 i)
    have hsum0 : ∑ l, w l * z l i = 0 := by
      rw [hbar i, hqi]
      simp
    have hall : ∀ l, 0 ≤ w l * z l i := by
      intro l
      rcases hz01 l i with hzi | hzi
      · simp [hzi]
      · simpa [hzi] using hw0 l
    have hterm0 : 0 ≤ w k * z k i := hall k
    have hterm_le :
        w k * z k i ≤ ∑ l, w l * z l i := by
      rw [← Finset.sum_erase_add Finset.univ
        (fun l => w l * z l i) (Finset.mem_univ k)]
      exact le_add_of_nonneg_left
        (Finset.sum_nonneg fun l hl => hall l)
    linarith
  let A :=
    concentrationAliceKraus p q s M hM e w z σ
  have hA :
      ∑ o, Matrix.conjTranspose (A o) * A o =
        (1 : CMatrix D) :=
    concentrationAliceKraus_complete
      p q s M hM e w z σ hp0 hq0 hqp hs hw0 hz01 hbar
  let B := concentrationBobUnitary e σ
  have hB :
      ∀ o, Matrix.conjTranspose (B o) * B o =
        (1 : CMatrix D) :=
    concentrationBobUnitary_isometry e σ
  let C := compressionKraus hM e
  have hC :
      ∑ k, Matrix.conjTranspose (C k) * C k =
        (1 : CMatrix D) :=
    compressionKraus_complete hM e
  let P : FiniteRoundLOCCProtocol D D (Fin M) (Fin M) :=
    oneWayLOCCProtocol A hA B hB C hC C hC
  refine ⟨P, ?_⟩
  rw [show
    P.channel.map (rankOneMatrix (diagonalSchmidtVector p)) =
      ∑ o, ∑ a, ∑ b,
        rankOneMatrix
          ((Matrix.kronecker
            (C a * A o) (C b * B o)).mulVec
              (diagonalSchmidtVector p)) by
        exact
          oneWayLOCCProtocol_apply_rankOneMatrix
            A hA B hB C hC C hC (diagonalSchmidtVector p)]
  rw [Fintype.sum_sum_type]
  simp_rw [show
    ∀ (k : ι) (a b : Option (Fin (Fintype.card D))),
      (Matrix.kronecker
        (C a * A (.inl k)) (C b * B (.inl k))).mulVec
          (diagonalSchmidtVector p) =
        match a, b with
        | none, none =>
            uniformDiagonalVector M
              (((Real.sqrt (s * w k / (M : ℝ)) : ℝ) : ℂ))
        | _, _ => 0 by
      exact concentration_success_finalVector
        p s M hM e w z σ hp0 hs hw0 hz01 hzero hsupport]
  simp_rw [show
    ∀ (pair : Fin (Fintype.card D) × Fin M)
      (a b : Option (Fin (Fintype.card D))),
      (Matrix.kronecker
        (C a * A (.inr pair)) (C b * B (.inr pair))).mulVec
          (diagonalSchmidtVector p) =
        match a, b with
        | none, none =>
            embeddedBasisVector pair.2
              (((Real.sqrt
                ((p ((Fintype.equivFin D).symm pair.1) -
                    q ((Fintype.equivFin D).symm pair.1)) /
                  (M : ℝ)) : ℝ) : ℂ))
        | _, _ => 0 by
      intro pair a b
      rcases pair with ⟨ik, m⟩
      exact concentration_fallback_finalVector
        p q s M hM e w z σ hp0 hq0 hqp ik m a b]
  simp only [Fintype.sum_option, rankOneMatrix_zero,
    Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  have hsuccess :
      (∑ k : ι,
        rankOneMatrix
          (uniformDiagonalVector M
            (((Real.sqrt (s * w k / (M : ℝ)) : ℝ) : ℂ)))) =
        (s : ℂ) • maximallyEntangledDensity M := by
    calc
      _ = ∑ k : ι,
          ((s * w k : ℝ) : ℂ) •
            maximallyEntangledDensity M := by
              apply Finset.sum_congr rfl
              intro k hk
              exact rankOne_uniformDiagonalVector M hM
                (s * w k) (mul_nonneg hs.le (hw0 k))
      _ = _ := by
        rw [← Finset.sum_smul]
        congr 1
        norm_cast
        rw [← Finset.mul_sum, hwsum, mul_one]
  have hfallback :
      (∑ ik : Fin (Fintype.card D), ∑ m : Fin M,
        rankOneMatrix
          (embeddedBasisVector m
            (((Real.sqrt
              ((p ((Fintype.equivFin D).symm ik) -
                  q ((Fintype.equivFin D).symm ik)) /
                (M : ℝ)) : ℝ) : ℂ)))) =
        ((1 - s : ℝ) : ℂ) • correlatedDiagonalDensity M := by
    calc
      _ = ∑ i : D, ∑ m : Fin M,
          rankOneMatrix
            (embeddedBasisVector m
              (((Real.sqrt
                ((p i - q i) / (M : ℝ)) : ℝ) : ℂ))) := by
                  apply Fintype.sum_equiv
                    (Fintype.equivFin D).symm
                  intro ik
                  rfl
      _ = ∑ i : D, ∑ m : Fin M,
          ((((p i - q i) / (M : ℝ) : ℝ) : ℂ)) •
            rankOneMatrix (embeddedBasisVector m 1) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro m hm
              exact rankOne_embeddedBasisVector_sqrt M hM m
                (p i - q i) (sub_nonneg.mpr (hqp i))
      _ = ∑ m : Fin M,
          (∑ i : D,
            ((((p i - q i) / (M : ℝ) : ℝ) : ℂ))) •
              rankOneMatrix (embeddedBasisVector m 1) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro m hm
                rw [Finset.sum_smul]
      _ =
          ((((1 - s : ℝ) / (M : ℝ) : ℝ) : ℂ)) •
            ∑ m : Fin M,
              rankOneMatrix (embeddedBasisVector m 1) := by
                have hcoeff :
                    ∑ i : D, (p i - q i) / (M : ℝ) =
                      (1 - s) / (M : ℝ) := by
                  rw [← Finset.sum_div]
                  congr 1
                  rw [Finset.sum_sub_distrib, hpSum, hqSum]
                have hcoeffC :
                    ∑ i : D,
                        ((((p i - q i) / (M : ℝ) : ℝ) : ℂ)) =
                      ((((1 - s) / (M : ℝ) : ℝ) : ℂ)) := by
                  exact_mod_cast hcoeff
                rw [hcoeffC, Finset.smul_sum]
      _ = ((1 - s : ℝ) : ℂ) • correlatedDiagonalDensity M := by
        unfold correlatedDiagonalDensity
        rw [smul_smul]
        congr 1
        norm_cast
        field_simp
  rw [hsuccess, hfallback]
  rfl

/-! ### A finite-alphabet weak AEP

The following elementary finite-sum argument supplies the asymptotic input
needed by the positive-rate protocol.  It is stated directly for the recursive
`TensorPower` coordinates used above, so no conversion to a separate
probability-space model is required.
-/

private noncomputable def schmidtInformation
    {X : Type*} (p : X → ℝ) (x : X) : ℝ :=
  -log2 (p x)

private noncomputable def centeredSchmidtInformation
    {X : Type*} [Fintype X] (p : X → ℝ) (x : X) : ℝ :=
  schmidtInformation p x - schmidtEntropy p

private noncomputable def iidCenteredInformation
    {X : Type*} [Fintype X] (p : X → ℝ) :
    (n : ℕ) → QITBench.TensorPower X n → ℝ
  | 0, _ => 0
  | n + 1, xs =>
      centeredSchmidtInformation p xs.1 +
        iidCenteredInformation p n xs.2

private noncomputable def schmidtInformationVariance
    {X : Type*} [Fintype X] (p : X → ℝ) : ℝ :=
  ∑ x, p x * (centeredSchmidtInformation p x) ^ 2

private theorem schmidtInformation_mean
    {X : Type*} [Fintype X]
    (p : X → ℝ) :
    ∑ x, p x * schmidtInformation p x =
      schmidtEntropy p := by
  simp only [schmidtInformation, schmidtEntropy]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem centeredSchmidtInformation_mean_zero
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∑ x, p x * centeredSchmidtInformation p x = 0 := by
  calc
    ∑ x, p x * centeredSchmidtInformation p x =
        (∑ x, p x * schmidtInformation p x) -
          schmidtEntropy p * ∑ x, p x := by
            simp only [centeredSchmidtInformation, mul_sub,
              Finset.sum_sub_distrib]
            apply congrArg₂ (· - ·) rfl
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = 0 := by
      rw [schmidtInformation_mean, hp.2]
      ring

private theorem schmidtInformationVariance_nonneg
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    0 ≤ schmidtInformationVariance p := by
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (hp.1 x) (sq_nonneg _)

private theorem iidCenteredInformation_mean_zero
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ n : ℕ,
      ∑ xs : QITBench.TensorPower X n,
          iidSchmidtWeight p n xs *
            iidCenteredInformation p n xs = 0 := by
  intro n
  induction n with
  | zero =>
      simp [QITBench.TensorPower, iidSchmidtWeight,
        iidCenteredInformation]
  | succ n ih =>
      change
        (∑ pair : X × QITBench.TensorPower X n,
          iidSchmidtWeight p (n + 1) pair *
            iidCenteredInformation p (n + 1) pair) = 0
      rw [Fintype.sum_prod_type]
      change
        (∑ x : X, ∑ xs : QITBench.TensorPower X n,
          (p x * iidSchmidtWeight p n xs) *
            (centeredSchmidtInformation p x +
              iidCenteredInformation p n xs)) = 0
      calc
        _ =
            (∑ x : X, p x * centeredSchmidtInformation p x) *
                (∑ xs : QITBench.TensorPower X n,
                  iidSchmidtWeight p n xs) +
              (∑ x : X, p x) *
                (∑ xs : QITBench.TensorPower X n,
            iidSchmidtWeight p n xs *
                    iidCenteredInformation p n xs) := by
              rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro xs hxs
              ring
        _ = 0 := by
          rw [centeredSchmidtInformation_mean_zero p hp,
            iidSchmidtWeight_sum p hp n, hp.2, ih]
          ring

set_option maxHeartbeats 800000 in
private theorem iidCenteredInformation_secondMoment
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ n : ℕ,
      ∑ xs : QITBench.TensorPower X n,
          iidSchmidtWeight p n xs *
            (iidCenteredInformation p n xs) ^ 2 =
        (n : ℝ) * schmidtInformationVariance p := by
  intro n
  induction n with
  | zero =>
      simp [QITBench.TensorPower, iidSchmidtWeight,
        iidCenteredInformation]
  | succ n ih =>
      change
        (∑ pair : X × QITBench.TensorPower X n,
          iidSchmidtWeight p (n + 1) pair *
            (iidCenteredInformation p (n + 1) pair) ^ 2) =
          ((n + 1 : ℕ) : ℝ) * schmidtInformationVariance p
      rw [Fintype.sum_prod_type]
      change
        (∑ x : X, ∑ xs : QITBench.TensorPower X n,
          (p x * iidSchmidtWeight p n xs) *
            (centeredSchmidtInformation p x +
              iidCenteredInformation p n xs) ^ 2) =
          ((n + 1 : ℕ) : ℝ) * schmidtInformationVariance p
      calc
        _ =
            (∑ x : X,
                p x * (centeredSchmidtInformation p x) ^ 2) *
                (∑ xs : QITBench.TensorPower X n,
                  iidSchmidtWeight p n xs) +
              2 *
                ((∑ x : X,
                    p x * centeredSchmidtInformation p x) *
                  (∑ xs : QITBench.TensorPower X n,
                    iidSchmidtWeight p n xs *
                      iidCenteredInformation p n xs)) +
              (∑ x : X, p x) *
                (∑ xs : QITBench.TensorPower X n,
                  iidSchmidtWeight p n xs *
                    (iidCenteredInformation p n xs) ^ 2) := by
              rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
                Finset.sum_mul_sum]
              simp only [Finset.mul_sum]
              rw [← Finset.sum_add_distrib,
                ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              rw [← Finset.sum_add_distrib,
                ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro xs hxs
              ring
        _ = ((n + 1 : ℕ) : ℝ) *
              schmidtInformationVariance p := by
          rw [show
              (∑ x : X,
                  p x * (centeredSchmidtInformation p x) ^ 2) =
                schmidtInformationVariance p by
                  rfl,
            iidSchmidtWeight_sum p hp n,
            centeredSchmidtInformation_mean_zero p hp,
            iidCenteredInformation_mean_zero p hp n,
            hp.2, ih]
          push_cast
          ring

private noncomputable def iidInformation
    {X : Type*} (p : X → ℝ) :
    (n : ℕ) → QITBench.TensorPower X n → ℝ
  | 0, _ => 0
  | n + 1, xs =>
      schmidtInformation p xs.1 + iidInformation p n xs.2

private theorem iidCenteredInformation_eq_sub
    {X : Type*} [Fintype X]
    (p : X → ℝ) :
    ∀ (n : ℕ) (xs : QITBench.TensorPower X n),
      iidCenteredInformation p n xs =
        iidInformation p n xs - (n : ℝ) * schmidtEntropy p := by
  intro n
  induction n with
  | zero =>
      intro xs
      simp [iidCenteredInformation, iidInformation]
  | succ n ih =>
      intro xs
      simp only [iidCenteredInformation, iidInformation]
      rw [ih]
      simp only [centeredSchmidtInformation]
      push_cast
      ring

private noncomputable def iidInformationGoodMass
    {X : Type*} [Fintype X]
    (p : X → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ xs : QITBench.TensorPower X n,
    if (n : ℝ) * T ≤ iidInformation p n xs
    then iidSchmidtWeight p n xs
    else 0

private theorem iidInformationGoodMass_nonneg
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    0 ≤ iidInformationGoodMass p T n := by
  apply Finset.sum_nonneg
  intro xs hxs
  split
  · exact iidSchmidtWeight_nonneg p hp n xs
  · exact le_rfl

private theorem iidInformationGoodMass_le_one
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    iidInformationGoodMass p T n ≤ 1 := by
  rw [← iidSchmidtWeight_sum p hp n]
  apply Finset.sum_le_sum
  intro xs hxs
  split
  · exact le_rfl
  · exact iidSchmidtWeight_nonneg p hp n xs

private noncomputable def iidInformationBadMass
    {X : Type*} [Fintype X]
    (p : X → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ xs : QITBench.TensorPower X n,
    if (n : ℝ) * T ≤ iidInformation p n xs
    then 0
    else iidSchmidtWeight p n xs

private theorem iidInformationGoodMass_add_badMass
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    iidInformationGoodMass p T n +
        iidInformationBadMass p T n =
      1 := by
  rw [← iidSchmidtWeight_sum p hp n]
  unfold iidInformationGoodMass iidInformationBadMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro xs hxs
  split <;> simp_all

private theorem iidInformationBadMass_nonneg
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) :
    0 ≤ iidInformationBadMass p T n := by
  apply Finset.sum_nonneg
  intro xs hxs
  split
  · exact le_rfl
  · exact iidSchmidtWeight_nonneg p hp n xs

set_option maxHeartbeats 800000 in
private theorem iidInformationBadMass_mul_gap_sq_le
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (hT : T < schmidtEntropy p)
    (n : ℕ) :
    iidInformationBadMass p T n *
          ((n : ℝ) * (schmidtEntropy p - T)) ^ 2 ≤
      (n : ℝ) * schmidtInformationVariance p := by
  rw [← iidCenteredInformation_secondMoment p hp n]
  unfold iidInformationBadMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro xs hxs
  split
  · simpa using
      mul_nonneg
        (iidSchmidtWeight_nonneg p hp n xs) (sq_nonneg _)
  · rename_i hbad
    have hinfo :
        iidInformation p n xs < (n : ℝ) * T :=
      lt_of_not_ge hbad
    have hcenter :=
      iidCenteredInformation_eq_sub p n xs
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hgap : 0 < schmidtEntropy p - T := sub_pos.mpr hT
    have hsquares :
        ((n : ℝ) * (schmidtEntropy p - T)) ^ 2 ≤
          (iidCenteredInformation p n xs) ^ 2 := by
      rw [hcenter]
      nlinarith [mul_nonneg hn hgap.le]
    exact
      mul_le_mul_of_nonneg_left hsquares
        (iidSchmidtWeight_nonneg p hp n xs)

private theorem iidInformationBadMass_le_variance_bound
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (hT : T < schmidtEntropy p)
    (n : ℕ) (hn : 0 < n) :
    iidInformationBadMass p T n ≤
      schmidtInformationVariance p /
        ((n : ℝ) * (schmidtEntropy p - T) ^ 2) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 < schmidtEntropy p - T := sub_pos.mpr hT
  have hbase :=
    iidInformationBadMass_mul_gap_sq_le p hp T hT n
  have hcancel :
      iidInformationBadMass p T n *
          ((n : ℝ) * (schmidtEntropy p - T) ^ 2) ≤
        schmidtInformationVariance p := by
    apply le_of_mul_le_mul_left _ hnR
    calc
      (n : ℝ) *
            (iidInformationBadMass p T n *
              ((n : ℝ) * (schmidtEntropy p - T) ^ 2)) =
          iidInformationBadMass p T n *
            ((n : ℝ) * (schmidtEntropy p - T)) ^ 2 := by
              ring
      _ ≤ (n : ℝ) * schmidtInformationVariance p := hbase
  exact
    (le_div_iff₀ (mul_pos hnR (sq_pos_of_pos hgap))).2 hcancel

private theorem iidInformationBadMass_tendsto_zero
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (hT : T < schmidtEntropy p) :
    Tendsto (iidInformationBadMass p T) atTop (nhds 0) := by
  let C : ℝ :=
    schmidtInformationVariance p /
      (schmidtEntropy p - T) ^ 2
  have hbound :
      Tendsto (fun n : ℕ => C * ((n : ℝ)⁻¹)) atTop (nhds 0) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      (iidInformationBadMass_nonneg p hp T)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    calc
      iidInformationBadMass p T n ≤
          schmidtInformationVariance p /
            ((n : ℝ) * (schmidtEntropy p - T) ^ 2) :=
        iidInformationBadMass_le_variance_bound
          p hp T hT n hnpos
      _ = C * ((n : ℝ)⁻¹) := by
        dsimp [C]
        field_simp
  · exact hbound

private theorem iidInformationGoodMass_tendsto_one
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (hT : T < schmidtEntropy p) :
    Tendsto (iidInformationGoodMass p T) atTop (nhds 1) := by
  have hbad := iidInformationBadMass_tendsto_zero p hp T hT
  have heq :
      iidInformationGoodMass p T =
        fun n => 1 - iidInformationBadMass p T n := by
    funext n
    linarith [iidInformationGoodMass_add_badMass p hp T n]
  rw [heq]
  simpa using tendsto_const_nhds.sub hbad

private theorem rpow_log2
    (x : ℝ) (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  change (2 : ℝ) ^ (log2 x) = x
  rw [Real.rpow_def_of_pos (by norm_num)]
  unfold log2
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [show
      Real.log 2 * (Real.log x / Real.log 2) =
        Real.log x by
          field_simp]
  exact Real.exp_log hx

private theorem rpow_neg_schmidtInformation
    {X : Type*} (p : X → ℝ) (x : X)
    (hx : 0 < p x) :
    Real.rpow 2 (-schmidtInformation p x) = p x := by
  simp only [schmidtInformation, neg_neg]
  exact rpow_log2 (p x) hx

private theorem rpow_neg_iidInformation
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p) :
    ∀ (n : ℕ) (xs : QITBench.TensorPower X n),
      0 < iidSchmidtWeight p n xs →
        Real.rpow 2 (-iidInformation p n xs) =
          iidSchmidtWeight p n xs := by
  intro n
  induction n with
  | zero =>
      intro xs hxs
      simp [iidInformation, iidSchmidtWeight]
  | succ n ih =>
      intro xs hxs
      have hhead0 : 0 ≤ p xs.1 := hp.1 xs.1
      have htail0 :
          0 ≤ iidSchmidtWeight p n xs.2 :=
        iidSchmidtWeight_nonneg p hp n xs.2
      have hprod :
          0 < p xs.1 * iidSchmidtWeight p n xs.2 := by
        exact hxs
      have hboth :
          0 < p xs.1 ∧
            0 < iidSchmidtWeight p n xs.2 := by
        rcases mul_pos_iff.mp hprod with h | h
        · exact h
        · exact (not_lt_of_ge hhead0 h.1).elim
      have hhead : 0 < p xs.1 := hboth.1
      have htail : 0 < iidSchmidtWeight p n xs.2 := hboth.2
      change
        (2 : ℝ) ^
            (-(schmidtInformation p xs.1 +
              iidInformation p n xs.2)) =
          p xs.1 * iidSchmidtWeight p n xs.2
      rw [neg_add, Real.rpow_add (by norm_num)]
      have hheadEq :
          (2 : ℝ) ^ (-schmidtInformation p xs.1) =
            p xs.1 := by
        exact rpow_neg_schmidtInformation p xs.1 hhead
      have htailEq :
          (2 : ℝ) ^ (-iidInformation p n xs.2) =
            iidSchmidtWeight p n xs.2 := by
        exact ih xs.2 htail
      rw [hheadEq, htailEq]

private theorem iidSchmidtWeight_le_information_cap
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (T : ℝ) (n : ℕ) (xs : QITBench.TensorPower X n)
    (hgood : (n : ℝ) * T ≤ iidInformation p n xs) :
    iidSchmidtWeight p n xs ≤
      Real.rpow 2 (-((n : ℝ) * T)) := by
  by_cases hzero : iidSchmidtWeight p n xs = 0
  · rw [hzero]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  · have hpos : 0 < iidSchmidtWeight p n xs :=
      lt_of_le_of_ne
        (iidSchmidtWeight_nonneg p hp n xs) (Ne.symm hzero)
    rw [← rpow_neg_iidInformation p hp n xs hpos]
    exact
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_le_neg hgood)

private theorem targetRankAtRate_cast_le_rpow
    (R : ℝ) (n : ℕ) :
    (targetRankAtRate R n : ℝ) ≤
      Real.rpow 2 ((n : ℝ) * R) := by
  unfold targetRankAtRate
  exact Nat.floor_le
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

private theorem targetRank_mul_good_weight_le_exponential
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (R T : ℝ) (n : ℕ) (xs : QITBench.TensorPower X n)
    (hgood : (n : ℝ) * T ≤ iidInformation p n xs) :
    (targetRankAtRate R n : ℝ) *
        iidSchmidtWeight p n xs ≤
      Real.rpow 2 (-((n : ℝ) * (T - R))) := by
  calc
    (targetRankAtRate R n : ℝ) *
          iidSchmidtWeight p n xs ≤
        Real.rpow 2 ((n : ℝ) * R) *
          Real.rpow 2 (-((n : ℝ) * T)) :=
      mul_le_mul
        (targetRankAtRate_cast_le_rpow R n)
        (iidSchmidtWeight_le_information_cap p hp T n xs hgood)
        (iidSchmidtWeight_nonneg p hp n xs)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    _ = Real.rpow 2 (-((n : ℝ) * (T - R))) := by
      change
        (2 : ℝ) ^ ((n : ℝ) * R) *
            (2 : ℝ) ^ (-((n : ℝ) * T)) =
          (2 : ℝ) ^ (-((n : ℝ) * (T - R)))
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring

private theorem informationSpectrum_exponential_tendsto_zero
    (R T : ℝ) (hRT : R < T) :
    Tendsto
      (fun n : ℕ =>
        Real.rpow 2 (-((n : ℝ) * (T - R))))
      atTop (nhds 0) := by
  have hgap : 0 < T - R := sub_pos.mpr hRT
  let a : ℝ := (2 : ℝ) ^ (-(T - R))
  have ha0 : 0 ≤ a :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have ha1 : a < 1 := by
    dsimp [a]
    exact
      (Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)).2
        (Or.inl ⟨by norm_num, neg_lt_zero.mpr hgap⟩)
  have hpow :
      Tendsto (fun n : ℕ => a ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  convert hpow using 1
  funext n
  dsimp [a]
  change
    (2 : ℝ) ^ (-((n : ℝ) * (T - R))) =
      ((2 : ℝ) ^ (-(T - R))) ^ n
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

private theorem eventually_targetRank_mul_good_weight_le_goodMass
    {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : IsProbabilityDistribution p)
    (R T : ℝ) (hRT : R < T)
    (hTentropy : T < schmidtEntropy p) :
    ∀ᶠ n : ℕ in atTop,
      ∀ xs : QITBench.TensorPower X n,
        (n : ℝ) * T ≤ iidInformation p n xs →
          (targetRankAtRate R n : ℝ) *
              iidSchmidtWeight p n xs ≤
            iidInformationGoodMass p T n := by
  have hexp :=
    informationSpectrum_exponential_tendsto_zero R T hRT
  have hmass :=
    iidInformationGoodMass_tendsto_one p hp T hTentropy
  have hexpHalf :
      ∀ᶠ n : ℕ in atTop,
        Real.rpow 2 (-((n : ℝ) * (T - R))) ≤ (1 : ℝ) / 2 :=
    hexp.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hmassHalf :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / 2 ≤ iidInformationGoodMass p T n :=
    hmass.eventually (Ici_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  filter_upwards [hexpHalf, hmassHalf] with n hnexp hnmass
  intro xs hgood
  exact
    (targetRank_mul_good_weight_le_exponential
      p hp R T n xs hgood).trans (hnexp.trans hnmass)

private theorem normalized_good_spectrum_mem_convexHull
    {D : Type*} [Fintype D] [DecidableEq D]
    (p : D → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (good : D → Prop) [DecidablePred good]
    (M : ℕ) (s : ℝ)
    (hs :
      (∑ i : D, if good i then p i else 0) = s)
    (hspos : 0 < s)
    (hcap : ∀ i, good i → (M : ℝ) * p i ≤ s) :
    (fun i : D =>
      (M : ℝ) * (if good i then p i else 0) / s) ∈
        convexHull ℝ (uniformSubsetVectors D M) := by
  apply mem_convexHull_uniformSubsetVectors
  · intro i
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg M)
        (by split <;> simp_all [hp0 i]))
      hspos.le
  · intro i
    by_cases hi : good i
    · simp only [if_pos hi]
      exact (div_le_one hspos).2 (hcap i hi)
    · simp [hi]
  · calc
      ∑ i : D,
          (M : ℝ) * (if good i then p i else 0) / s =
          (M : ℝ) / s *
            ∑ i : D, (if good i then p i else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              field_simp
      _ = (M : ℝ) := by
        rw [hs]
        field_simp

/-- Achievability of asymptotic entanglement concentration for a finite
Schmidt distribution. The protocol at blocklength `n` has output Schmidt rank
`M n`, so its codomain depends on `n`. -/
theorem achievability_entanglement_concentration
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (ψ : PureVector (X × X))
    (hp : IsProbabilityDistribution p)
    (hψ : HasSchmidtCoefficients ψ p) :
    ∀ R : ℝ,
      0 ≤ R →
      R < schmidtEntropy p →
      ∃ (M : ℕ → ℕ)
        (Λ : (n : ℕ) →
          FiniteRoundLOCCProtocol
            (QITBench.TensorPower X n) (QITBench.TensorPower X n)
            (Fin (M n)) (Fin (M n))),
        (∀ n : ℕ, 0 < M n) ∧
        (∀ n : ℕ, M n = targetRankAtRate R n) ∧
        Tendsto
          (fun n : ℕ =>
            quantumFidelity
              ((Λ n).channel.applyState
                (ψ.state.tensorPowerBipartite n)).matrix
              (maximallyEntangledDensity (M n)))
          atTop (nhds 1) := by
  intro R hR hRentropy
  by_cases hRzero : R = 0
  · subst R
    let M : ℕ → ℕ := fun _ => 1
    let Λ : (n : ℕ) →
        FiniteRoundLOCCProtocol
          (QITBench.TensorPower X n) (QITBench.TensorPower X n)
          (Fin (M n)) (Fin (M n)) :=
      fun n =>
        discardToOneProtocol
          (QITBench.TensorPower X n) (QITBench.TensorPower X n)
    refine ⟨M, Λ, ?_, ?_, ?_⟩
    · intro n
      simp [M]
    · intro n
      simp [M, targetRankAtRate]
    · have hconstant :
          (fun n : ℕ =>
            quantumFidelity
              ((Λ n).channel.applyState
                (ψ.state.tensorPowerBipartite n)).matrix
              (maximallyEntangledDensity (M n))) =
            fun _ : ℕ => (1 : ℝ) := by
          funext n
          rw [state_matrix_eq_one_on_finOneProd,
            maximallyEntangledDensity_one]
          exact quantumFidelity_one_finOneProd
      rw [hconstant]
      exact tendsto_const_nhds
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    let M : ℕ → ℕ := fun n => targetRankAtRate R n
    have hMpos : ∀ n : ℕ, 0 < M n := by
      intro n
      rw [show M n = targetRankAtRate R n by rfl]
      unfold targetRankAtRate
      rw [Nat.floor_pos]
      exact Real.one_le_rpow (by norm_num)
        (mul_nonneg (Nat.cast_nonneg n) hRpos.le)
    have hconcentration :
        ∃ Λ : (n : ℕ) →
            FiniteRoundLOCCProtocol
              (QITBench.TensorPower X n) (QITBench.TensorPower X n)
              (Fin (M n)) (Fin (M n)),
          Tendsto
            (fun n : ℕ =>
              quantumFidelity
                ((Λ n).channel.applyState
                  (ψ.state.tensorPowerBipartite n)).matrix
                (maximallyEntangledDensity (M n)))
            atTop (nhds 1) := by
      classical
      let T : ℝ := (R + schmidtEntropy p) / 2
      have hRT : R < T := by
        dsimp [T]
        linarith
      have hTentropy : T < schmidtEntropy p := by
        dsimp [T]
        linarith
      have hgoodMass :
          Tendsto (iidInformationGoodMass p T) atTop (nhds 1) :=
        iidInformationGoodMass_tendsto_one p hp T hTentropy
      have hcoefficientCap :
          ∀ᶠ n : ℕ in atTop,
            ∀ xs : QITBench.TensorPower X n,
              (n : ℝ) * T ≤ iidInformation p n xs →
                (M n : ℝ) * iidSchmidtWeight p n xs ≤
                  iidInformationGoodMass p T n := by
        simpa [M] using
          eventually_targetRank_mul_good_weight_le_goodMass
            p hp R T hRT hTentropy
      have hgoodMassPos :
          ∀ᶠ n : ℕ in atTop,
            0 < iidInformationGoodMass p T n :=
        hgoodMass.eventually
          (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
      have hconvexDecomposition :
          ∀ᶠ n : ℕ in atTop,
            (fun xs : QITBench.TensorPower X n =>
              (M n : ℝ) *
                  (if
                    (n : ℝ) * T ≤ iidInformation p n xs
                  then iidSchmidtWeight p n xs
                  else 0) /
                iidInformationGoodMass p T n) ∈
              convexHull ℝ
                (uniformSubsetVectors
                  (QITBench.TensorPower X n) (M n)) := by
        filter_upwards
          [hcoefficientCap, hgoodMassPos] with n hncap hnmass
        apply normalized_good_spectrum_mem_convexHull
        · exact iidSchmidtWeight_nonneg p hp n
        · rfl
        · exact hnmass
        · intro xs hxs
          exact hncap xs hxs
      have hiidMatrix :
          ∀ n : ℕ,
            (ψ.state.tensorPowerBipartite n).matrix =
              rankOneMatrix
                (fun i :
                    QITBench.TensorPower X n ×
                    QITBench.TensorPower X n =>
                  iidSchmidtAmplitude p n i.1 i.2) :=
        tensorPowerBipartite_matrix_eq_iid p ψ hψ
      let Ready (n : ℕ) : Prop :=
        0 < iidInformationGoodMass p T n ∧
          (fun xs : QITBench.TensorPower X n =>
            (M n : ℝ) *
                (if
                  (n : ℝ) * T ≤ iidInformation p n xs
                then iidSchmidtWeight p n xs
                else 0) /
              iidInformationGoodMass p T n) ∈
            convexHull ℝ
              (uniformSubsetVectors
                (QITBench.TensorPower X n) (M n))
      have hReady : ∀ᶠ n : ℕ in atTop, Ready n := by
        filter_upwards
          [hgoodMassPos, hconvexDecomposition] with n hnpos hnconvex
        exact ⟨hnpos, hnconvex⟩
      have hblockProtocol
          (n : ℕ) (hn : Ready n) :
          ∃ P :
              FiniteRoundLOCCProtocol
                (QITBench.TensorPower X n)
                (QITBench.TensorPower X n)
                (Fin (M n)) (Fin (M n)),
            P.channel.map
                (rankOneMatrix
                  (diagonalSchmidtVector
                    (iidSchmidtWeight p n))) =
              concentrationOutputMatrix (M n)
                (iidInformationGoodMass p T n) := by
        refine exists_concentration_protocol
          (iidSchmidtWeight p n)
          (fun xs =>
            if (n : ℝ) * T ≤ iidInformation p n xs
            then iidSchmidtWeight p n xs
            else 0)
          ?_ ?_ ?_ ?_
          (iidInformationGoodMass p T n) ?_ ?_
          (M n) ?_ ?_
        · exact iidSchmidtWeight_nonneg p hp n
        · intro xs
          dsimp
          by_cases hxs :
              (n : ℝ) * T ≤ iidInformation p n xs <;>
            simp [hxs, iidSchmidtWeight_nonneg p hp n xs]
        · intro xs
          dsimp
          by_cases hxs :
              (n : ℝ) * T ≤ iidInformation p n xs <;>
            simp [hxs, iidSchmidtWeight_nonneg p hp n xs]
        · exact iidSchmidtWeight_sum p hp n
        · exact hn.1
        · rfl
        · exact hMpos n
        · exact hn.2
      let Λ : (n : ℕ) →
          FiniteRoundLOCCProtocol
            (QITBench.TensorPower X n) (QITBench.TensorPower X n)
            (Fin (M n)) (Fin (M n)) :=
        fun n =>
          if hn : Ready n then
            Classical.choose (hblockProtocol n hn)
          else
            discardToFixedProtocol
              (QITBench.TensorPower X n) (M n) (hMpos n)
      refine ⟨Λ, ?_⟩
      have hΛmap
          (n : ℕ) (hn : Ready n) :
          (Λ n).channel.map
              (rankOneMatrix
                (diagonalSchmidtVector
                  (iidSchmidtWeight p n))) =
            concentrationOutputMatrix (M n)
              (iidInformationGoodMass p T n) := by
        rw [show Λ n =
          Classical.choose (hblockProtocol n hn) by
            simp [Λ, hn]]
        exact Classical.choose_spec (hblockProtocol n hn)
      have hiidAmplitude :
          ∀ n : ℕ,
            (fun i :
                QITBench.TensorPower X n ×
                  QITBench.TensorPower X n =>
              iidSchmidtAmplitude p n i.1 i.2) =
            diagonalSchmidtVector (iidSchmidtWeight p n) := by
        intro n
        funext i
        rcases i with ⟨xs, ys⟩
        simpa [diagonalSchmidtVector] using
          iidSchmidtAmplitude_eq p hp n xs ys
      have hfidelityEventually :
          ∀ᶠ n : ℕ in atTop,
            quantumFidelity
                ((Λ n).channel.applyState
                  (ψ.state.tensorPowerBipartite n)).matrix
                (maximallyEntangledDensity (M n)) =
              Real.sqrt
                (iidInformationGoodMass p T n +
                  (1 - iidInformationGoodMass p T n) /
                    (M n : ℝ)) := by
        filter_upwards [hReady] with n hn
        let ρout :=
          (Λ n).channel.applyState
            (ψ.state.tensorPowerBipartite n)
        have hρout :
            ρout.matrix =
              concentrationOutputMatrix (M n)
                (iidInformationGoodMass p T n) := by
          change
            (Λ n).channel.map
                (ψ.state.tensorPowerBipartite n).matrix =
              _
          rw [hiidMatrix n, hiidAmplitude n]
          exact hΛmap n hn
        exact
          quantumFidelity_concentrationOutputMatrix
            (M n) (hMpos n)
            (iidInformationGoodMass p T n)
            (iidInformationGoodMass_nonneg p hp T n)
            (iidInformationGoodMass_le_one p hp T n)
            ρout hρout
      let a : ℕ → ℝ :=
        fun n =>
          iidInformationGoodMass p T n +
            (1 - iidInformationGoodMass p T n) / (M n : ℝ)
      have ha : Tendsto a atTop (nhds 1) := by
        apply Filter.Tendsto.squeeze hgoodMass tendsto_const_nhds
        · intro n
          dsimp [a]
          exact le_add_of_nonneg_right
            (div_nonneg
              (sub_nonneg.mpr
                (iidInformationGoodMass_le_one p hp T n))
              (Nat.cast_nonneg (M n)))
        · intro n
          dsimp [a]
          have hMone : (1 : ℝ) ≤ (M n : ℝ) := by
            exact_mod_cast hMpos n
          have hdiv :=
            div_le_self
              (sub_nonneg.mpr
                (iidInformationGoodMass_le_one p hp T n))
              hMone
          linarith
      have hsqrt :
          Tendsto (fun n : ℕ => Real.sqrt (a n))
            atTop (nhds 1) := by
        have h :=
          Real.continuous_sqrt.continuousAt.tendsto.comp ha
        simpa using h
      have hfidelityEventuallySymm :
          (fun n : ℕ => Real.sqrt (a n)) =ᶠ[atTop]
            (fun n : ℕ =>
              quantumFidelity
                ((Λ n).channel.applyState
                  (ψ.state.tensorPowerBipartite n)).matrix
                (maximallyEntangledDensity (M n))) := by
        filter_upwards [hfidelityEventually] with n hn
        exact hn.symm
      exact Filter.Tendsto.congr' hfidelityEventuallySymm hsqrt
    obtain ⟨Λ, hΛ⟩ := hconcentration
    exact ⟨M, Λ, hMpos, fun n => rfl, hΛ⟩

end

end QITFormalized
