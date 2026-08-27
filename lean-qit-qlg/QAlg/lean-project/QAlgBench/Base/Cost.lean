/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Gate
public import QAlgBench.Base.Util.Asymptotics
public import Cslib.Algorithms.Lean.TimeM

/-!
# Trusted cost annotations

This module connects Lean-QAlgBench theorem endpoints to CSLib's `TimeM`
interface. A value of `Timed α` returns an object of type `α` and carries a
trusted natural-number cost annotation.

The cost annotation is intentionally not derived from the Lean evaluator or from
matrix dimensions. Following CSLib's `TimeM` convention, correctness is proved
on `.ret`, while `.time` records the selected model. In the current quantum
algorithm bridge, one unit means one oracle query for the single-query
Walsh-Hadamard algorithms, and one good/bad-plane iterate for amplitude
amplification and Grover.

This is an operator-level bridge over the existing pure-state and gate
semantics. Fuller quantum program logics, such as density-operator or
Hoare-style semantics for quantum while programs, are future extensions rather
than prerequisites for this TimeM layer.
-/

@[expose] public section

namespace QAlgBench

universe u

/-- A CSLib `TimeM` computation with natural-number cost. -/
abbrev Timed (α : Type u) := Cslib.Algorithms.Lean.TimeM ℕ α

namespace Timed

/-- Attach a trusted cost to a return value. -/
def trusted {α : Type u} (cost : ℕ) (ret : α) : Timed α := ⟨ret, cost⟩

@[simp]
theorem trusted_ret {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).ret = ret := rfl

@[simp]
theorem trusted_time {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).time = cost := rfl

end Timed

/-- A trusted resource profile for registered theorem endpoints.

The fields are intentionally lightweight counters. They record the resource
model claimed beside a correctness theorem, not a derivation from Lean
evaluation. -/
structure ResourceProfile where
  /-- Trusted oracle-query count in the selected endpoint model. -/
  oracleQueries : ℕ
  /-- Trusted Hadamard-gate count for circuit statements. -/
  hadamardGates : ℕ
  /-- Trusted count of elementary non-Hadamard gates. -/
  elementaryGates : ℕ
  /-- Trusted count of classical side computations. -/
  classicalOps : ℕ
deriving DecidableEq

namespace ResourceProfile

/-- The empty resource profile. -/
def zero : ResourceProfile where
  oracleQueries := 0
  hadamardGates := 0
  elementaryGates := 0
  classicalOps := 0

/-- Sequential composition adds every resource counter. -/
def sequential (left right : ResourceProfile) : ResourceProfile where
  oracleQueries := left.oracleQueries + right.oracleQueries
  hadamardGates := left.hadamardGates + right.hadamardGates
  elementaryGates := left.elementaryGates + right.elementaryGates
  classicalOps := left.classicalOps + right.classicalOps

/-- Tensor/parallel circuit composition uses the same additive counters. -/
def tensor (left right : ResourceProfile) : ResourceProfile :=
  sequential left right

/-- Repeat a resource profile `k` times. -/
def scale (k : ℕ) (profile : ResourceProfile) : ResourceProfile where
  oracleQueries := k * profile.oracleQueries
  hadamardGates := k * profile.hadamardGates
  elementaryGates := k * profile.elementaryGates
  classicalOps := k * profile.classicalOps

/-- Exact counter claim used by supporting public theorem statements. -/
def HasExactCounts (profile : ResourceProfile)
    (oracleQueries hadamardGates elementaryGates classicalOps : ℕ) : Prop :=
  profile.oracleQueries = oracleQueries ∧
    profile.hadamardGates = hadamardGates ∧
    profile.elementaryGates = elementaryGates ∧
    profile.classicalOps = classicalOps

@[simp]
theorem sequential_oracleQueries (left right : ResourceProfile) :
    (sequential left right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem sequential_hadamardGates (left right : ResourceProfile) :
    (sequential left right).hadamardGates =
      left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem sequential_elementaryGates (left right : ResourceProfile) :
    (sequential left right).elementaryGates =
      left.elementaryGates + right.elementaryGates := rfl

@[simp]
theorem sequential_classicalOps (left right : ResourceProfile) :
    (sequential left right).classicalOps =
      left.classicalOps + right.classicalOps := rfl

@[simp]
theorem tensor_oracleQueries (left right : ResourceProfile) :
    (tensor left right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl

@[simp]
theorem tensor_hadamardGates (left right : ResourceProfile) :
    (tensor left right).hadamardGates =
      left.hadamardGates + right.hadamardGates := rfl

@[simp]
theorem tensor_elementaryGates (left right : ResourceProfile) :
    (tensor left right).elementaryGates =
      left.elementaryGates + right.elementaryGates := rfl

@[simp]
theorem tensor_classicalOps (left right : ResourceProfile) :
    (tensor left right).classicalOps =
      left.classicalOps + right.classicalOps := rfl

@[simp]
theorem scale_oracleQueries (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).oracleQueries = k * profile.oracleQueries := rfl

@[simp]
theorem scale_hadamardGates (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).hadamardGates = k * profile.hadamardGates := rfl

@[simp]
theorem scale_elementaryGates (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).elementaryGates = k * profile.elementaryGates := rfl

@[simp]
theorem scale_classicalOps (k : ℕ) (profile : ResourceProfile) :
    (scale k profile).classicalOps = k * profile.classicalOps := rfl

end ResourceProfile

/-! ### Counted gate words -/

/-- A small circuit word boundary for endpoints whose correctness and resource
counts must refer to the same constructed unitary.  The word deliberately keeps
only its evaluated gate and derived resource profile; richer syntax can be
introduced later without changing public theorem statements. -/
structure CountedGateWord (R : Register) where
  /-- Evaluated gate represented by the counted word. -/
  matrix : Gate R
  /-- Trusted resource counters attached to the same word. -/
  resources : ResourceProfile

namespace CountedGateWord

/-- A counted word with explicit resources for an already-built gate. -/
def ofGate {R : Register} (gate : Gate R) (resources : ResourceProfile) :
    CountedGateWord R where
  matrix := gate
  resources := resources

/-- Sequential composition evaluates by multiplying the gates and adds the
resource counters from the same syntax boundary. -/
def sequential {R : Register} (left right : CountedGateWord R) : CountedGateWord R where
  matrix := left.matrix * right.matrix
  resources := ResourceProfile.sequential left.resources right.resources

@[simp]
theorem sequential_matrix {R : Register} (left right : CountedGateWord R) :
    (sequential left right).matrix = left.matrix * right.matrix := rfl

@[simp]
theorem sequential_resources {R : Register} (left right : CountedGateWord R) :
    (sequential left right).resources =
      ResourceProfile.sequential left.resources right.resources := rfl

end CountedGateWord

/-- Gate counts for fixed circuit statements with named gate families. -/
structure CircuitGateProfile where
  /-- Number of Hadamard gates. -/
  hadamardGates : ℕ
  /-- Number of controlled phase gates. -/
  controlledPhaseGates : ℕ
  /-- Number of swap gates. -/
  swapGates : ℕ
deriving DecidableEq

namespace CircuitGateProfile

/-- Exact fixed-circuit gate-count claim. -/
def HasExactCounts (profile : CircuitGateProfile)
    (hadamardGates controlledPhaseGates swapGates : ℕ) : Prop :=
  profile.hadamardGates = hadamardGates ∧
    profile.controlledPhaseGates = controlledPhaseGates ∧
    profile.swapGates = swapGates

end CircuitGateProfile

/-- A return value paired with a trusted resource profile. -/
structure Profiled (α : Type u) where
  /-- The profiled return value. -/
  ret : α
  /-- Trusted resources associated with the return value. -/
  resources : ResourceProfile

namespace Profiled

/-- Attach a trusted resource profile to a return value. -/
def trusted {α : Type u} (resources : ResourceProfile) (ret : α) : Profiled α :=
  ⟨ret, resources⟩

@[simp]
theorem trusted_ret {α : Type u} (resources : ResourceProfile) (ret : α) :
    (trusted resources ret).ret = ret := rfl

@[simp]
theorem trusted_resources {α : Type u} (resources : ResourceProfile) (ret : α) :
    (trusted resources ret).resources = resources := rfl

end Profiled

/-- Communication resources for protocol statements. -/
structure CommunicationProfile where
  /-- Classical bits communicated by the protocol. -/
  classicalBits : ℕ
  /-- Qubits transmitted by the protocol. -/
  transmittedQubits : ℕ
  /-- Shared Bell pairs consumed or produced by the protocol. -/
  bellPairs : ℕ
deriving DecidableEq

namespace CommunicationProfile

/-- Exact communication-resource claim for protocol supporting theorems. -/
def HasExactCounts (profile : CommunicationProfile)
    (classicalBits transmittedQubits bellPairs : ℕ) : Prop :=
  profile.classicalBits = classicalBits ∧
    profile.transmittedQubits = transmittedQubits ∧
    profile.bellPairs = bellPairs

@[simp]
theorem hasExactCounts_mk (classicalBits transmittedQubits bellPairs : ℕ) :
    HasExactCounts
      { classicalBits := classicalBits, transmittedQubits := transmittedQubits,
        bellPairs := bellPairs }
      classicalBits transmittedQubits bellPairs := by
  simp [HasExactCounts]

end CommunicationProfile

end QAlgBench
