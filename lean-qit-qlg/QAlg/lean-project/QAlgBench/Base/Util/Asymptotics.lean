/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Quantum-free asymptotic helpers

This module contains small asymptotic wrappers that do not depend on the
quantum `Gate` or `HilbertOperator` layers.
-/

@[expose] public section

namespace QAlgBench

/-- Natural-number resource functions compared by Mathlib's real-valued
`Asymptotics.IsBigO` relation at infinity. -/
def NatBigO (f g : ℕ → ℕ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (f n : ℝ))
    (fun n : ℕ => (g n : ℝ))

namespace NatBigO

theorem refl (f : ℕ → ℕ) : NatBigO f f := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with n
  simp

/-- Multiplying a natural-number resource function by a fixed constant preserves
its `NatBigO` class. -/
theorem const_mul_left (c : ℕ) (f : ℕ → ℕ) :
    NatBigO (fun n : ℕ => c * f n) f := by
  refine Asymptotics.IsBigO.of_bound (c : ℝ) ?_
  filter_upwards with n
  simp [norm_mul]

end NatBigO

end QAlgBench

