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

axiom src_L001_A01 : Function.Bijective experiment.category_to_condition

theorem L001 : Function.Bijective experiment.category_to_condition :=
src_L001_A01

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

axiom model_M001 : ∀ i : Fin 4, experiment.category_to_condition i = (0 : Fin 4) → experiment.stack_present i = false

theorem L005 : ∀ k : Fin 4, experiment.category_to_condition k = 0 → experiment.stack_present k = false :=
by
  intro k hk
  exact model_M001 k hk

theorem L009 : ∀ k : Fin 4, experiment.category_to_condition k = 0 → experiment.stack_present k = false :=
L005

theorem L011 : experiment.category_to_condition 0 = 0 :=
by
  obtain ⟨k, hk⟩ := L001.2 (0 : Fin 4)
  have hs : experiment.stack_present k = false := L009 k hk
  rcases L002 with ⟨h0, h1, h2, h3⟩
  have hk0 : k = (0 : Fin 4) := by
    revert hs
    refine Fin.cases ?_ ?_ k
    · intro _
      rfl
    · intro k1
      refine Fin.cases ?_ ?_ k1
      · intro hs
        simp [h1] at hs
      · intro k2
        refine Fin.cases ?_ ?_ k2
        · intro hs
          simp [h2] at hs
        · intro k3
          refine Fin.cases ?_ ?_ k3
          · intro hs
            simp [h3] at hs
          · intro k4
            exact Fin.elim0 k4
  simpa [hk0] using hk
