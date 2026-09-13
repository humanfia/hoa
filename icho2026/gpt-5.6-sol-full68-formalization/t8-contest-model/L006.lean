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

axiom model_M002 : ∀ i j : Fin 4, experiment.category_to_condition i ≠ (0 : Fin 4) → experiment.category_to_condition j ≠ (0 : Fin 4) → experiment.photon_energy (experiment.category_to_condition i) < experiment.photon_energy (experiment.category_to_condition j) → experiment.h2_mole_percent i < experiment.h2_mole_percent j

theorem L006 : ∀ i j : Fin 4, experiment.category_to_condition i ≠ 0 → experiment.category_to_condition j ≠ 0 → experiment.photon_energy (experiment.category_to_condition i) > experiment.photon_energy (experiment.category_to_condition j) → experiment.h2_mole_percent i > experiment.h2_mole_percent j :=
by
  intro i j hi hj hE
  exact model_M002 j i hj hi hE
