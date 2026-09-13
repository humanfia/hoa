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

axiom src_L003_A01 : experiment.h2_mole_percent 1 > experiment.h2_mole_percent 2

axiom src_L003_A02 : experiment.h2_mole_percent 2 > experiment.h2_mole_percent 3

theorem L003 : experiment.h2_mole_percent 1 > experiment.h2_mole_percent 2 ∧ experiment.h2_mole_percent 2 > experiment.h2_mole_percent 3 :=
⟨src_L003_A01, src_L003_A02⟩
