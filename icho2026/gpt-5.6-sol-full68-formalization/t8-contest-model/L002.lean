import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

structure Experiment where
  category_to_condition : Fin 4 → Fin 4
  stack_present : Fin 4 → Bool
  h2_mole_percent : Fin 4 → ℝ
  photon_energy : Fin 4 → ℝ
  total_product_amount : Fin 4 → ℝ

axiom experiment : Experiment

axiom src_L002_A01 : experiment.stack_present 0 = false

axiom src_L002_A02 : experiment.stack_present 1 = true

axiom src_L002_A03 : experiment.stack_present 2 = true

axiom src_L002_A04 : experiment.stack_present 3 = true

theorem L002 : experiment.stack_present 0 = false ∧ experiment.stack_present 1 = true ∧ experiment.stack_present 2 = true ∧ experiment.stack_present 3 = true :=
by
  constructor
  · exact src_L002_A01
  constructor
  · exact src_L002_A02
  constructor
  · exact src_L002_A03
  · exact src_L002_A04
