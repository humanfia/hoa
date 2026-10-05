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

theorem L007 : experiment.stack_present 0 = false ∧ ∃ alt : Experiment, alt.stack_present = experiment.stack_present ∧ alt.h2_mole_percent = experiment.h2_mole_percent ∧ alt.photon_energy = experiment.photon_energy ∧ Function.Bijective alt.category_to_condition ∧ alt.category_to_condition 0 ≠ 0 ∧ alt.total_product_amount 0 > 0 :=
by
  refine ⟨L002.1, ?_⟩
  let alt : Experiment :=
    { category_to_condition := Equiv.swap (0 : Fin 4) (1 : Fin 4)
      stack_present := experiment.stack_present
      h2_mole_percent := experiment.h2_mole_percent
      photon_energy := experiment.photon_energy
      total_product_amount := fun _ => 1 }
  refine ⟨alt, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact (Equiv.swap (0 : Fin 4) (1 : Fin 4)).bijective
  · norm_num [alt]
  · norm_num [alt]
