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

axiom src_L004_A01 : experiment.photon_energy 3 > experiment.photon_energy 2

axiom src_L004_A02 : experiment.photon_energy 2 > experiment.photon_energy 1

theorem L004 : experiment.photon_energy 3 > experiment.photon_energy 2 ∧ experiment.photon_energy 2 > experiment.photon_energy 1 :=
⟨src_L004_A01, src_L004_A02⟩

theorem L008 : ∃ alt : Experiment, alt.stack_present = experiment.stack_present ∧ alt.h2_mole_percent = experiment.h2_mole_percent ∧ alt.photon_energy = experiment.photon_energy ∧ alt.total_product_amount = experiment.total_product_amount ∧ Function.Bijective alt.category_to_condition ∧ alt.category_to_condition 0 = 0 ∧ ∃ i j : Fin 4, alt.category_to_condition i ≠ 0 ∧ alt.category_to_condition j ≠ 0 ∧ alt.photon_energy (alt.category_to_condition i) > alt.photon_energy (alt.category_to_condition j) ∧ ¬ (alt.h2_mole_percent i > alt.h2_mole_percent j) :=
by
  let alt : Experiment :=
    { category_to_condition := fun k => k
      stack_present := experiment.stack_present
      h2_mole_percent := experiment.h2_mole_percent
      photon_energy := experiment.photon_energy
      total_product_amount := experiment.total_product_amount }
  refine ⟨alt, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
  · constructor
    · intro x y h
      simpa [alt] using h
    · intro y
      exact ⟨y, by simp [alt]⟩
  · refine ⟨3, 2, ?_, ?_, ?_, ?_⟩
    · exact by decide
    · exact by decide
    · simpa [alt] using L004.1
    · intro h
      have h32 : experiment.h2_mole_percent 3 > experiment.h2_mole_percent 2 := by
        simpa [alt] using h
      linarith [L003.2]
