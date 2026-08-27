/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Cost
public import QAlgBench.Base.Measurement
public import QAlgBench.Base.Tensor
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Typed circuit histories

`Circuit R` is a typed, finite-dimensional construction history over a register
`R`.  The same history is interpreted into a unitary `Gate R`, resource
counters, depth, query depth, and terminal PVM output probabilities.

Qubit-specific circuits use the register `Qubits n`; `Circuit` itself is not
where qubits, operators, or gates are defined.
-/

@[expose] public section

namespace QAlgBench

open Kronecker

/-- Syntactic operation history for a typed circuit. -/
inductive CircuitHistory where
  | id
  | atom (name : String)
  | seq (left right : CircuitHistory)
  | tensor (left right : CircuitHistory)
  | inverse (body : CircuitHistory)
  | controlled (controlLabel : String) (body : CircuitHistory)
  | iterate (count : Nat) (body : CircuitHistory)
  | indexedProduct (label : String) (count : Nat) (start : CircuitHistory)
      (step : Fin count → CircuitHistory)

/-- Typed circuit object. -/
structure Circuit (R : Register) where
  /-- Construction history. -/
  history : CircuitHistory
  /-- Mathematical unitary gate denoted by the history. -/
  matrix : Gate R
  /-- Resource counters derived when the history is constructed. -/
  resources : ResourceProfile
  /-- Circuit depth derived when the history is constructed. -/
  depth : Nat
  /-- Oracle/query depth derived when the history is constructed. -/
  queryDepth : Nat

namespace Circuit

noncomputable section

/-- Identity circuit. -/
def identity (R : Register) : Circuit R where
  history := CircuitHistory.id
  matrix := 1
  resources := ResourceProfile.zero
  depth := 0
  queryDepth := 0

/-- Primitive finite-dimensional unitary operation. -/
def atom {R : Register} (name : String) (op : HilbertOperator R)
    (hunitary : op ∈ Matrix.unitaryGroup R.Index ℂ)
    (resources : ResourceProfile) (depth queryDepth : Nat) : Circuit R where
  history := CircuitHistory.atom name
  matrix := Gate.ofUnitary op hunitary
  resources := resources
  depth := depth
  queryDepth := queryDepth

/-- Lift an existing gate into the circuit syntax. -/
def ofGate {R : Register} (name : String) (gate : Gate R)
    (resources : ResourceProfile) (depth queryDepth : Nat) : Circuit R :=
  atom name (gate : HilbertOperator R) gate.unitary resources depth queryDepth

@[simp]
theorem atom_matrix {R : Register} (name : String) (op : HilbertOperator R)
    (hunitary : op ∈ Matrix.unitaryGroup R.Index ℂ)
    (resources : ResourceProfile) (depth queryDepth : Nat) :
    ((atom name op hunitary resources depth queryDepth).matrix : HilbertOperator R) = op := rfl

@[simp]
theorem ofGate_matrix {R : Register} (name : String) (gate : Gate R)
    (resources : ResourceProfile) (depth queryDepth : Nat) :
    ((ofGate name gate resources depth queryDepth).matrix : HilbertOperator R) =
      (gate : HilbertOperator R) := rfl

@[simp]
theorem ofGate_resources {R : Register} (name : String) (gate : Gate R)
    (resources : ResourceProfile) (depth queryDepth : Nat) :
    (ofGate name gate resources depth queryDepth).resources = resources := rfl

/-- Abstract circuit boundary for algorithm statements whose fine-grained gate
history has not yet been expanded.  It is still a typed history node with one
semantic gate and one resource counter record. -/
def abstract (R : Register) (name : String) (resources : ResourceProfile)
    (depth queryDepth : Nat) : Circuit R :=
  atom name (1 : HilbertOperator R) (one_mem _) resources depth queryDepth

@[simp]
theorem abstract_resources (R : Register) (name : String) (resources : ResourceProfile)
    (depth queryDepth : Nat) :
    (abstract R name resources depth queryDepth).resources = resources := rfl

/-- Promote an existing counted gate word into the typed circuit layer. -/
def ofCountedGateWord {R : Register} (name : String) (word : CountedGateWord R)
    (depth queryDepth : Nat) : Circuit R :=
  ofGate name word.matrix word.resources depth queryDepth

@[simp]
theorem ofCountedGateWord_resources {R : Register} (name : String) (word : CountedGateWord R)
    (depth queryDepth : Nat) :
    (ofCountedGateWord name word depth queryDepth).resources = word.resources := rfl

/-- Sequential circuit composition. -/
def seq {R : Register} (left right : Circuit R) : Circuit R where
  history := CircuitHistory.seq left.history right.history
  matrix := (left.matrix * right.matrix)
  resources := ResourceProfile.sequential left.resources right.resources
  depth := left.depth + right.depth
  queryDepth := left.queryDepth + right.queryDepth

/-- Tensor/parallel circuit composition over product registers. -/
def tensor {R S : Register} (left : Circuit R) (right : Circuit S) :
    Circuit (Register.prod R S) where
  history := CircuitHistory.tensor left.history right.history
  matrix := Gate.ofUnitary
    ((left.matrix : HilbertOperator R) ⊗ₖ (right.matrix : HilbertOperator S))
    (Matrix.kronecker_mem_unitary left.matrix.unitary right.matrix.unitary)
  resources := ResourceProfile.tensor left.resources right.resources
  depth := max left.depth right.depth
  queryDepth := max left.queryDepth right.queryDepth

/-- Inverse circuit. -/
def inverse {R : Register} (body : Circuit R) : Circuit R where
  history := CircuitHistory.inverse body.history
  matrix := body.matrix.conjTranspose
  resources := body.resources
  depth := body.depth
  queryDepth := body.queryDepth

/-- Matrix of a finite-register controlled circuit. -/
def controlledMatrix {T : Register} (control : Register) (controlValue : control.Index)
    (body : Circuit T) : HilbertOperator (Register.prod control T) :=
  fun i j =>
    if i.1 = j.1 then
      if i.1 = controlValue then
        body.matrix i.2 j.2
      else if i.2 = j.2 then 1 else 0
    else 0

/-- Controlled circuit over a finite-dimensional control register. -/
def controlled {T : Register} (control : Register) (controlValue : control.Index)
    (body : Circuit T)
    (hunitary :
      controlledMatrix control controlValue body ∈
        Matrix.unitaryGroup (Register.prod control T).Index ℂ) :
    Circuit (Register.prod control T) where
  history := CircuitHistory.controlled "finite-control" body.history
  matrix := Gate.ofUnitary (controlledMatrix control controlValue body) hunitary
  resources := body.resources
  depth := body.depth
  queryDepth := body.queryDepth

/-- Symbolic repetition of one circuit block. -/
def iterate {R : Register} (count : Nat) (body : Circuit R) : Circuit R where
  history := CircuitHistory.iterate count body.history
  matrix := body.matrix ^ count
  resources := ResourceProfile.scale count body.resources
  depth := count * body.depth
  queryDepth := count * body.queryDepth

/-- Sequential product of a finite list of circuit blocks. -/
def sequenceList {R : Register} (start : Circuit R) (steps : List (Circuit R)) :
    Circuit R :=
  steps.foldl seq start

/-- Indexed finite product of circuit blocks. -/
def indexedProduct {R : Register} (count : Nat) (start : Circuit R)
    (step : Fin count → Circuit R) : Circuit R :=
  let product := sequenceList start (List.ofFn step)
  { product with history := (
      CircuitHistory.indexedProduct "indexed-product" count start.history
        (fun j => (step j).history)) }

/-- Named version of `indexedProduct` for algorithm-specific product histories. -/
def indexedProductNamed {R : Register} (name : String) (count : Nat) (start : Circuit R)
    (step : Fin count → Circuit R) : Circuit R :=
  let product := sequenceList start (List.ofFn step)
  { product with history := (
      CircuitHistory.indexedProduct name count start.history
        (fun j => (step j).history)) }

/-- Indexed finite product over an explicit schedule. -/
def indexedProductList {R : Register} {α : Type} (name : String)
    (start : Circuit R) (schedule : List α) (step : α → Circuit R) : Circuit R :=
  let product := sequenceList start (schedule.map step)
  { product with history := (
      CircuitHistory.indexedProduct name schedule.length start.history
        (fun j => (step (schedule.get j)).history)) }

/-- Apply a circuit's interpreted gate to a finite-register state vector. -/
def apply {R : Register} (circuit : Circuit R) (state : StateVector R) : StateVector R :=
  circuit.matrix.applyVec state

@[simp]
theorem apply_ofGate {R : Register} (name : String) (gate : Gate R)
    (resources : ResourceProfile) (depth queryDepth : Nat) (state : StateVector R) :
    apply (ofGate name gate resources depth queryDepth) state = gate.applyVec state := rfl

theorem matrix_unitary {R : Register} (circuit : Circuit R) :
    (circuit.matrix : HilbertOperator R) ∈ Matrix.unitaryGroup R.Index ℂ :=
  circuit.matrix.unitary

/-- Terminal PVM output probability after running a circuit. -/
def outputProbability {R : Register} {outcome : Type} [Fintype outcome]
    (circuit : Circuit R) (pvm : TerminalPVM R outcome)
    (state : StateVector R) (x : outcome) : ℝ :=
  StateVector.probPVM (Circuit.apply circuit state) pvm x

@[simp]
theorem identity_matrix (R : Register) :
    ((identity R).matrix : HilbertOperator R) = (1 : HilbertOperator R) := rfl

@[simp]
theorem identity_resources (R : Register) :
    (identity R).resources = ResourceProfile.zero := rfl

@[simp]
theorem seq_matrix {R : Register} (left right : Circuit R) :
    ((seq left right).matrix : HilbertOperator R) =
      (left.matrix : HilbertOperator R) * (right.matrix : HilbertOperator R) := rfl

@[simp]
theorem seq_resources {R : Register} (left right : Circuit R) :
    (seq left right).resources =
      ResourceProfile.sequential left.resources right.resources := rfl

@[simp]
theorem seq_depth {R : Register} (left right : Circuit R) :
    (seq left right).depth = left.depth + right.depth := rfl

@[simp]
theorem seq_queryDepth {R : Register} (left right : Circuit R) :
    (seq left right).queryDepth = left.queryDepth + right.queryDepth := rfl

@[simp]
theorem iterate_matrix {R : Register} (count : Nat) (body : Circuit R) :
    ((iterate count body).matrix : HilbertOperator R) =
      (body.matrix : HilbertOperator R) ^ count := by
  change ((body.matrix ^ count : Gate R) : HilbertOperator R) =
    (body.matrix : HilbertOperator R) ^ count
  rw [Gate.coe_pow]

@[simp]
theorem iterate_resources {R : Register} (count : Nat) (body : Circuit R) :
    (iterate count body).resources = ResourceProfile.scale count body.resources := rfl

@[simp]
theorem iterate_depth {R : Register} (count : Nat) (body : Circuit R) :
    (iterate count body).depth = count * body.depth := rfl

@[simp]
theorem iterate_queryDepth {R : Register} (count : Nat) (body : Circuit R) :
    (iterate count body).queryDepth = count * body.queryDepth := rfl

@[simp]
theorem sequenceList_nil {R : Register} (start : Circuit R) :
    sequenceList start [] = start := rfl

@[simp]
theorem sequenceList_cons {R : Register} (start step : Circuit R)
    (steps : List (Circuit R)) :
    sequenceList start (step :: steps) = sequenceList (seq start step) steps := rfl

@[simp]
theorem sequenceList_append_singleton {R : Register} (start : Circuit R)
    (steps : List (Circuit R)) (step : Circuit R) :
    sequenceList start (steps ++ [step]) = seq (sequenceList start steps) step := by
  simp [sequenceList, List.foldl_append]

@[simp]
theorem sequenceList_map_matrix {R : Register} {α : Type} (start : Circuit R)
    (schedule : List α) (step : α → Circuit R) :
    ((sequenceList start (schedule.map step)).matrix : HilbertOperator R) =
      schedule.foldl
        (fun op a => op * ((step a).matrix : HilbertOperator R))
        (start.matrix : HilbertOperator R) := by
  induction schedule generalizing start with
  | nil => rfl
  | cons a schedule ih =>
      simp [sequenceList_cons, ih]

@[simp]
theorem foldl_gate_matrix {R : Register} {α : Type} (start : Gate R)
    (schedule : List α) (step : α → Gate R) :
    ((schedule.foldl (fun gate a => gate * step a) start : Gate R) :
        HilbertOperator R) =
      schedule.foldl
        (fun op a => op * ((step a) : HilbertOperator R))
        (start : HilbertOperator R) := by
  induction schedule generalizing start with
  | nil => rfl
  | cons a schedule ih =>
      change ((schedule.foldl (fun gate a => gate * step a) (start * step a) :
          Gate R) : HilbertOperator R) =
        schedule.foldl
          (fun op a => op * ((step a) : HilbertOperator R))
          (((start * step a : Gate R) : HilbertOperator R))
      rw [ih (start := start * step a)]

@[simp]
theorem indexedProductNamed_matrix {R : Register} (name : String) (count : Nat)
    (start : Circuit R) (step : Fin count → Circuit R) :
    ((indexedProductNamed name count start step).matrix : HilbertOperator R) =
      ((sequenceList start (List.ofFn step)).matrix : HilbertOperator R) := rfl

@[simp]
theorem indexedProductNamed_resources {R : Register} (name : String) (count : Nat)
    (start : Circuit R) (step : Fin count → Circuit R) :
    (indexedProductNamed name count start step).resources =
      (sequenceList start (List.ofFn step)).resources := rfl

@[simp]
theorem indexedProductList_matrix {R : Register} {α : Type} (name : String)
    (start : Circuit R) (schedule : List α) (step : α → Circuit R) :
    ((indexedProductList name start schedule step).matrix : HilbertOperator R) =
      ((sequenceList start (schedule.map step)).matrix : HilbertOperator R) := rfl

@[simp]
theorem indexedProductList_resources {R : Register} {α : Type} (name : String)
    (start : Circuit R) (schedule : List α) (step : α → Circuit R) :
    (indexedProductList name start schedule step).resources =
      (sequenceList start (schedule.map step)).resources := rfl

end

end Circuit

/-- A public theorem proof package whose correctness and resource evidence come
from one typed circuit witness. -/
structure ResourceCorrectWitness {R : Register} (correctness resourceClaim : Prop) where
  /-- The single circuit whose semantics and counters are used. -/
  circuit : Circuit R
  /-- Correctness proof for the theorem endpoint. -/
  correctness : correctness
  /-- Resource proof for the same circuit. -/
  resources : resourceClaim

end QAlgBench
