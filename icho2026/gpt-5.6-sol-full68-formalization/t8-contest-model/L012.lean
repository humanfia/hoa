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

axiom src_L003_A01 : experiment.h2_mole_percent 1 > experiment.h2_mole_percent 2

axiom src_L003_A02 : experiment.h2_mole_percent 2 > experiment.h2_mole_percent 3

theorem L003 : experiment.h2_mole_percent 1 > experiment.h2_mole_percent 2 ∧ experiment.h2_mole_percent 2 > experiment.h2_mole_percent 3 :=
⟨src_L003_A01, src_L003_A02⟩

axiom src_L004_A01 : experiment.photon_energy 3 > experiment.photon_energy 2

axiom src_L004_A02 : experiment.photon_energy 2 > experiment.photon_energy 1

theorem L004 : experiment.photon_energy 3 > experiment.photon_energy 2 ∧ experiment.photon_energy 2 > experiment.photon_energy 1 :=
⟨src_L004_A01, src_L004_A02⟩

axiom model_M001 : ∀ i : Fin 4, experiment.category_to_condition i = (0 : Fin 4) → experiment.stack_present i = false

theorem L005 : ∀ k : Fin 4, experiment.category_to_condition k = 0 → experiment.stack_present k = false :=
by
  intro k hk
  exact model_M001 k hk

axiom model_M002 : ∀ i j : Fin 4, experiment.category_to_condition i ≠ (0 : Fin 4) → experiment.category_to_condition j ≠ (0 : Fin 4) → experiment.photon_energy (experiment.category_to_condition i) < experiment.photon_energy (experiment.category_to_condition j) → experiment.h2_mole_percent i < experiment.h2_mole_percent j

theorem L006 : ∀ i j : Fin 4, experiment.category_to_condition i ≠ 0 → experiment.category_to_condition j ≠ 0 → experiment.photon_energy (experiment.category_to_condition i) > experiment.photon_energy (experiment.category_to_condition j) → experiment.h2_mole_percent i > experiment.h2_mole_percent j :=
by
  intro i j hi hj hE
  exact model_M002 j i hj hi hE

theorem L009 : ∀ k : Fin 4, experiment.category_to_condition k = 0 → experiment.stack_present k = false :=
L005

theorem L010 : ∀ i j : Fin 4, experiment.category_to_condition i ≠ 0 → experiment.category_to_condition j ≠ 0 → experiment.photon_energy (experiment.category_to_condition i) > experiment.photon_energy (experiment.category_to_condition j) → experiment.h2_mole_percent i > experiment.h2_mole_percent j :=
L006

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

theorem L012 : experiment.category_to_condition 1 = 3 ∧ experiment.category_to_condition 2 = 2 ∧ experiment.category_to_condition 3 = 1 :=
by
  rcases L003 with ⟨hh12, hh23⟩
  rcases L004 with ⟨he32, he21⟩
  have he31 : experiment.photon_energy 3 > experiment.photon_energy 1 :=
    lt_trans he21 he32
  have hh13 : experiment.h2_mole_percent 1 > experiment.h2_mole_percent 3 :=
    lt_trans hh23 hh12
  have hfin : ∀ x : Fin 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x
    refine Fin.cases ?_ ?_ x
    · exact Or.inl rfl
    · intro x1
      refine Fin.cases ?_ ?_ x1
      · exact Or.inr (Or.inl rfl)
      · intro x2
        refine Fin.cases ?_ ?_ x2
        · exact Or.inr (Or.inr (Or.inl rfl))
        · intro x3
          refine Fin.cases ?_ ?_ x3
          · exact Or.inr (Or.inr (Or.inr rfl))
          · intro x4
            exact Fin.elim0 x4
  have hnonzero : ∀ i : Fin 4, i ≠ 0 → experiment.category_to_condition i ≠ 0 := by
    intro i hi hfi
    apply hi
    apply L001.1
    exact hfi.trans L011.symm
  have h1n0 : experiment.category_to_condition 1 ≠ 0 :=
    hnonzero 1 (by decide)
  have h2n0 : experiment.category_to_condition 2 ≠ 0 :=
    hnonzero 2 (by decide)
  have h3n0 : experiment.category_to_condition 3 ≠ 0 :=
    hnonzero 3 (by decide)
  have h12ne : experiment.category_to_condition 1 ≠ experiment.category_to_condition 2 := by
    intro h
    have h' : (1 : Fin 4) = 2 := L001.1 h
    exact (by decide : (1 : Fin 4) ≠ 2) h'
  have h13ne : experiment.category_to_condition 1 ≠ experiment.category_to_condition 3 := by
    intro h
    have h' : (1 : Fin 4) = 3 := L001.1 h
    exact (by decide : (1 : Fin 4) ≠ 3) h'
  have h23ne : experiment.category_to_condition 2 ≠ experiment.category_to_condition 3 := by
    intro h
    have h' : (2 : Fin 4) = 3 := L001.1 h
    exact (by decide : (2 : Fin 4) ≠ 3) h'
  have hf1 : experiment.category_to_condition 1 = 3 := by
    rcases hfin (experiment.category_to_condition 1) with hf1_zero | hf1_one | hf1_two | hf1_three
    · exact (h1n0 hf1_zero).elim
    · rcases hfin (experiment.category_to_condition 2) with hf2_zero | hf2_one | hf2_two | hf2_three
      · exact (h2n0 hf2_zero).elim
      · exact (h12ne (hf1_one.trans hf2_one.symm)).elim
      · have hbad : experiment.h2_mole_percent 2 > experiment.h2_mole_percent 1 :=
          L010 2 1 h2n0 h1n0 (by
            simpa [hf2_two, hf1_one] using he21)
        exfalso
        exact lt_asymm hh12 hbad
      · have hbad : experiment.h2_mole_percent 2 > experiment.h2_mole_percent 1 :=
          L010 2 1 h2n0 h1n0 (by
            simpa [hf2_three, hf1_one] using he31)
        exfalso
        exact lt_asymm hh12 hbad
    · rcases hfin (experiment.category_to_condition 2) with hf2_zero | hf2_one | hf2_two | hf2_three
      · exact (h2n0 hf2_zero).elim
      · rcases hfin (experiment.category_to_condition 3) with hf3_zero | hf3_one | hf3_two | hf3_three
        · exact (h3n0 hf3_zero).elim
        · exact (h23ne (hf2_one.trans hf3_one.symm)).elim
        · exact (h13ne (hf1_two.trans hf3_two.symm)).elim
        · have hbad : experiment.h2_mole_percent 3 > experiment.h2_mole_percent 1 :=
            L010 3 1 h3n0 h1n0 (by
              simpa [hf3_three, hf1_two] using he32)
          exfalso
          exact lt_asymm hh13 hbad
      · exact (h12ne (hf1_two.trans hf2_two.symm)).elim
      · have hbad : experiment.h2_mole_percent 2 > experiment.h2_mole_percent 1 :=
          L010 2 1 h2n0 h1n0 (by
            simpa [hf2_three, hf1_two] using he32)
        exfalso
        exact lt_asymm hh12 hbad
    · exact hf1_three
  have hf2 : experiment.category_to_condition 2 = 2 := by
    rcases hfin (experiment.category_to_condition 2) with hf2_zero | hf2_one | hf2_two | hf2_three
    · exact (h2n0 hf2_zero).elim
    · rcases hfin (experiment.category_to_condition 3) with hf3_zero | hf3_one | hf3_two | hf3_three
      · exact (h3n0 hf3_zero).elim
      · exact (h23ne (hf2_one.trans hf3_one.symm)).elim
      · have hbad : experiment.h2_mole_percent 3 > experiment.h2_mole_percent 2 :=
          L010 3 2 h3n0 h2n0 (by
            simpa [hf3_two, hf2_one] using he21)
        exfalso
        exact lt_asymm hh23 hbad
      · exact (h13ne (hf1.trans hf3_three.symm)).elim
    · exact hf2_two
    · exact (h12ne (hf1.trans hf2_three.symm)).elim
  have hf3 : experiment.category_to_condition 3 = 1 := by
    rcases hfin (experiment.category_to_condition 3) with hf3_zero | hf3_one | hf3_two | hf3_three
    · exact (h3n0 hf3_zero).elim
    · exact hf3_one
    · exact (h23ne (hf2.trans hf3_two.symm)).elim
    · exact (h13ne (hf1.trans hf3_three.symm)).elim
  exact ⟨hf1, hf2, hf3⟩
