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

axiom model_M001 : ∀ i : Fin 4, experiment.category_to_condition i = (0 : Fin 4) → experiment.stack_present i = false

theorem L005 : ∀ k : Fin 4, experiment.category_to_condition k = 0 → experiment.stack_present k = false :=
by
  intro k hk
  exact model_M001 k hk
