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

axiom src_L004_A01 : experiment.photon_energy 3 > experiment.photon_energy 2

axiom src_L004_A02 : experiment.photon_energy 2 > experiment.photon_energy 1

theorem L004 : experiment.photon_energy 3 > experiment.photon_energy 2 ∧ experiment.photon_energy 2 > experiment.photon_energy 1 :=
⟨src_L004_A01, src_L004_A02⟩
