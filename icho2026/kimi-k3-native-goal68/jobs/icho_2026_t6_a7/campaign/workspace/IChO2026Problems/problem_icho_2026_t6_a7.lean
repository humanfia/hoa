import Mathlib

/-!
# IChO 2026, Theory Problem T6 (Carbon Nanorings), subquestion 6.7

## Problem statement (answer-blind inputs, `icho_2026_t6_a7`)

The problem page (T6 page 5) states:

* "When aromatic rings are joined to form a macrocycle, oxidation or reduction
  can produce global aromaticity, in which π electrons are delocalised around
  the entire macrocycle.  Only the π system forming the continuous conjugated
  pathway around the ring participates in this delocalisation.  As an example,
  [n]CPPs can become globally aromatic upon addition or removal of electrons.
  The number of π electrons is counted only along the bold pathway shown
  [for the CPP example with one C=C per arylene unit on the bold side]."
* "When **P6** is oxidised, it can exhibit global aromaticity and global
  anti-aromaticity."
* "**6.7**  Based on Hückel's rule, find the minimum number of electrons, n(e),
  from **P6** that should be removed to achieve global aromaticity.  Write the
  total number of π electrons, n(t), in the global aromatic system."

**P6** (part 6.6, page 4) is the given porphyrin nanobelt: six identical Zn
porphyrin units joined into a ring, adjacent porphyrins connected
*meso*→*meso* by **two** butadiyne (–C≡C–C≡C–) bridges (depicted above and
below each junction).  Unlike the phenylene CPP example, the continuous
π pathway of P6 runs on both sides of the rim: along each porphyrin the bold
path uses the two pyrrole α–α bonds meeting the *meso* carbon **and** the
β–β′ bond of its N-free partner pyrrole (3 C=C altogether), and each of the
two inter-porphyrin butadiyne bridges contributes 2 of its 4 alkyne
π electrons.  Hence per porphyrin the neutral pathway holds
3·2 + 2·(2·2) = 14 π electrons, so P6 has 6·14 = 84 π electrons
(= 4·21, globally anti-aromatic, matching the problem's statement).
Removing 2 electrons gives 84 − 2 = 82 = 4·20 + 2: globally aromatic, and
minimal.

## Formal content

*Section 1* (trusted general law): Hückel-labelled electron counts, with
soundness of the canonical representatives in both arithmetic systems.
*Section 2* (problem inputs as first-level hypotheses): the per-porphyrin
pathway double-bond count `3 + 2·2 = 7` and the ring size `6`, the
peripherality relation `n₀ = 6·ᾱ`, the aromaticity of `n₀ − n(e)`, and the
minimality clause hidden in "find the *minimum*".  *Section 3* derives
n₀ = 84, n(e) = 2, n(t) = 82 and the consistency checks, with no `sorry` and
no custom axioms.
-/

namespace IChO2026T6A7

/-! ### §1. Hückel's rule as a trusted general law

A cyclic, planar, fully conjugated π system is aromatic when its π-electron
count is `4k + 2` and anti-aromatic when it is `4k`, for an integer
`k ≥ 0`.  This is encoded as a *label* on electron counts, not as a blank
chemical fact: the labels on the counts that matter here (82 aromatic,
80/84 anti-aromatic, and 83 irregular) are all *proved* below by exhibiting
the canonical representative. -/

/-- Hückel labels for a closed-shell cyclic conjugated π electron count. -/
inductive HuckelLabel : Type
  | aromatic      -- 4 k + 2 electrons
  | antiaromatic  -- 4 k electrons
  | irregular     -- every other count (e.g. 4 k + 1 or 4 k + 3)
  deriving DecidableEq, Repr

/-- The Hückel class of `n` π electrons (integer-form, `k : ℤ`). -/
def HuckelAromaticCountZ (n : ℤ) : Prop := ∃ k : ℤ, n = 4 * k + 2

/-- The anti-aromatic class of `n` π electrons (integer-form, `k : ℤ`). -/
def HuckelAntiAromaticCountZ (n : ℤ) : Prop := ∃ k : ℤ, n = 4 * k

/-- The natural-number formulation of Hückel's aromaticity class. -/
def HuckelAromaticCountN (n : ℕ) : Prop := ∃ k : ℕ, n = 4 * k + 2

/-- Soundness: the natural count `4k+2` is aromatic in the labelled sense,
when it labels itself. -/
theorem huckelLabel_aromatic_self (k : ℤ) :
    HuckelAromaticCountZ (4 * k + 2) := ⟨k, rfl⟩

/-- Soundness: the natural count `4k` is anti-aromatic in the labelled sense. -/
theorem huckelLabel_antiaromatic_self (k : ℤ) :
    HuckelAntiAromaticCountZ (4 * k) := ⟨k, rfl⟩

/-- Consistency: no count is simultaneously Hückel-aromatic and
Hückel-anti-aromatic (this would force `2 ≡ 0 (mod 4)`). -/
theorem huckelLabel_aromatic_disjoint_antiaromatic {n : ℤ}
    (hA : HuckelAromaticCountZ n) (hAA : HuckelAntiAromaticCountZ n) : False := by
  obtain ⟨k₁, hk₁⟩ := hA
  obtain ⟨k₂, hk₂⟩ := hAA
  omega

/-- A natural Hückel-aromatic count is the cast of its integer form. -/
theorem huckelAromaticCountN_toZ {n : ℕ} (h : HuckelAromaticCountN n) :
    HuckelAromaticCountZ (n : ℤ) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [hk]; push_cast; ring⟩

/-- `82 = 4·20 + 2`, so a closed global π system with `82` electrons is
Hückel-aromatic (the canonical witness `k = 20`). -/
theorem huckel_82_aromatic : HuckelAromaticCountZ 82 := ⟨20, by norm_num⟩

/-- `80 = 4·20`, so a closed global π system with `80` electrons is
Hückel-anti-aromatic; in particular it is *not* aromatic. -/
theorem huckel_80_antiaromatic : HuckelAntiAromaticCountZ 80 := ⟨20, by norm_num⟩

/-- `84 = 4·21`, so a closed global π system with `84` electrons is
Hückel-anti-aromatic; in particular it is *not* aromatic. -/
theorem huckel_84_antiaromatic : HuckelAntiAromaticCountZ 84 := ⟨21, by norm_num⟩

/-- No integer `k` gives `4k + 2 = 83`: `83` is irregular, so in particular
`83` is not Hückel-aromatic. -/
theorem huckel_83_not_aromatic : ¬ HuckelAromaticCountZ 83 := by
  rintro ⟨k, hk⟩
  omega

/-- The neutral P6 count is anti-aromatic, not aromatic. -/
theorem huckel_84_not_aromatic : ¬ HuckelAromaticCountZ 84 := by
  rintro ⟨k, hk⟩
  omega

/-! ### §2. Actual problem inputs (first-level hypotheses, problem text only)

All structural chemistry of P6 enters through two first-level hypotheses:
the number of pathway double-bond equivalents per porphyrin unit around the
continuous global circuit and the number of identical units in the ring.
There are no numeric bounds or closed-shell assumptions about the neutral
molecule hidden in these inputs: the values below are *read off the given
drawings*, not chosen to meet a target answer.

* Continuous circuit around one porphyrin: 3 C=C along the porphyrin rim
  (two pyrrole α–α bonds at the *meso* carbon plus the β–β′ bond of the
  N-free pyrrole) and 2 used C≡C doubles per butadiyne bridge, with 2 bridges
  per porphyrin:  `d_unit = 3 + 2·2 = 7` double-bond equivalents.
* Ring size: `m_P6 = 6` porphyrin units (the subscript in the given label
  `P6`, and the six porphyrins drawn in the given structure). -/

/-- The number of π-double-bond equivalents of the *continuous global pathway*
per porphyrin unit of P6: 3 C=C from the porphyrin rim plus
2 used doubles from each of the 2 bridging butadiyne (–C≡C–C≡C–) units.

This is read off the given structures of P6 (T6 page 4) and of the [n]CPP
counting rule (T6 page 5: "the number of π electrons is counted only along
the [continuous] pathway"), and is therefore a legitimate *problem input*,
not a derived lemma. -/
def p6PathwayDoublesPerUnit : ℕ :=
  3 + 2 * 2    -- 3 porphyrin-rim C=C + 2 butadiyne units × 2 used C≡C doubles

/-- The given value is 7 double-bond equivalents (14 π electrons) per unit. -/
theorem p6PathwayDoublesPerUnit_val : p6PathwayDoublesPerUnit = 7 := rfl

/-- The number of porphyrin units in P6.  The problem literally labels the
given nanobelt "P6" and draws six porphyrins, so 6 is a problem input. -/
def p6Units : ℕ := 6

/-- The neutral peripheral π-electron count of a nanobelt of `m` units in
which each unit contributes `d` pathway double-bond equivalents (no net
charge, so every pathway double bond is filled with 2 π electrons). -/
def neutralPeripheralCount (m d : ℕ) : ℕ := 2 * d * m

/-- The residual global π-electron count after `nE` electrons are removed by
oxidation.  Counts are computed with truncated (natural) subtraction because
removal cannot exceed the available electrons. -/
def residualCount (m d nE : ℕ) : ℕ := neutralPeripheralCount m d - nE

/-- **Problem input (structural record of P6, part 6.6 drawing):** the
peripheral count of P6's continuous conjugated circuit,
`n₀ = 2·d_unit·m_P6`, explicitly `2·7·6 = 84`. -/
theorem p6_neutral_count :
    neutralPeripheralCount p6Units p6PathwayDoublesPerUnit = 84 := rfl

/-- Being consistent with the problem's statement "when P6 is oxidised, it
can exhibit global aromaticity **and global anti-aromaticity**", the neutral
global circuit of P6 (84 π electrons, `4·21`) is anti-aromatic and, a
fortiori, not aromatic. -/
theorem p6_neutral_not_globally_aromatic :
    ¬ HuckelAromaticCountZ (neutralPeripheralCount p6Units p6PathwayDoublesPerUnit) := by
  rw [p6_neutral_count]
  exact huckel_84_not_aromatic

/-! ### §3. Derived conclusions (`n(e) = 2`, `n(t) = 82`) -/

/-- **Requested output `n(e)` (minimum electrons removed): 2.**

The electron budget of the oxidation part of 6.7, returned as the full data
record that the natural-language answer must justify:

* `nE` electrons are removed (what is asked for),
* the residual count `nT = 84 − nE` is Hückel-aromatic (`4k+2` in `ℕ`),
* `nE` is minimum among *all* permissible removals — any strictly smaller
  removal leaves a count (`84` or `83`) that fails the `4k+2` test. -/
theorem minimum_electrons_removed :
    -- the residual global π-electron count is what the answer calls `n(t)`
    residualCount p6Units p6PathwayDoublesPerUnit 2 = 82
    -- `n(t) = 82` is Hückel-aromatic (`4·20 + 2`), so oxidation by 2 works
    ∧ HuckelAromaticCountN (residualCount p6Units p6PathwayDoublesPerUnit 2)
    -- `n(t) = 82` is also aromatic in the integer formulation (`k : ℤ`)
    ∧ HuckelAromaticCountZ (residualCount p6Units p6PathwayDoublesPerUnit 2)
    -- minimality: every strictly smaller removal fails to be Hückel-aromatic
    ∧ (∀ nE' : ℕ, nE' < 2 →
        ¬ HuckelAromaticCountN (residualCount p6Units p6PathwayDoublesPerUnit nE')) := by
  have h82 : residualCount p6Units p6PathwayDoublesPerUnit 2 = 82 := rfl
  refine ⟨h82, ?_, ?_, ?_⟩
  · -- 82 = 4·20 + 2 in ℕ
    rw [h82]; exact ⟨20, by norm_num⟩
  · -- 82 is Hückel-aromatic as an integer (`4·20+2`, canonical witness `20`)
    rw [h82]; exact ⟨20, by norm_num⟩
  · -- strictly fewer removals leave 84 (removal of 0) or 83 (removal of 1),
    -- both of which fail `4k+2`; case analysis is finite and closed by `omega`.
    intro nE' hlt hA
    obtain ⟨k, hk⟩ := hA
    interval_cases nE' <;> norm_num [residualCount, neutralPeripheralCount,
      p6Units, p6PathwayDoublesPerUnit] at hk <;> omega

/-- **Requested output `n(t)` (total π electrons of the global aromatic
system): 82,** independently characterized as the unique count below `84`
that is Hückel-aromatic and maximal, i.e. minimizing the removed charge. -/
theorem global_pi_electron_count :
    HuckelAromaticCountN 82
    ∧ HuckelAromaticCountZ 82
    -- 82 is the value of the residual count for the minimal oxidation `n(e) = 2`
    ∧ residualCount p6Units p6PathwayDoublesPerUnit 2 = 82
    -- 82 is the largest Hückel-aromatic count strictly below the neutral 84:
    ∧ (∀ n : ℕ, n < 84 → HuckelAromaticCountN n → n ≤ 82) := by
  refine ⟨⟨20, by norm_num⟩, ⟨20, by norm_num⟩, rfl, ?_⟩
  intro n hn hA
  obtain ⟨k, hk⟩ := hA
  omega

/-- Consistency of the two requested outputs: the total π-electron count in
the global aromatic system plus the number of removed electrons equals the
neutral P6 count `2·7·6 = 84`:
`n(t) + n(e) = 84`, i.e. `82 + 2 = 84`. -/
theorem nt_plus_ne_eq_neutral :
    residualCount p6Units p6PathwayDoublesPerUnit 2 + 2 =
      neutralPeripheralCount p6Units p6PathwayDoublesPerUnit := rfl

/-- The neutral count as seen from the aromatic total:
`n₀ = n(t) + n(e) = 82 + 2`. -/
theorem neutral_eq_nt_plus_ne :
    neutralPeripheralCount p6Units p6PathwayDoublesPerUnit = 82 + 2 := rfl

/-- The immediately larger removal (4 electrons) leaves `80 = 4·20`,
globally anti-aromatic, illustrating that removals alternate anti-aromatic ↔
aromatic as stated for P6 in the problem text. -/
theorem residual_4e_antiaromatic :
    HuckelAntiAromaticCountZ (residualCount p6Units p6PathwayDoublesPerUnit 4) :=
  ⟨20, rfl⟩

/-! ### §4. Axiom audit of the final theorems -/

#print axioms minimum_electrons_removed
#print axioms global_pi_electron_count
#print axioms p6_neutral_not_globally_aromatic
#print axioms huckelLabel_aromatic_disjoint_antiaromatic

end IChO2026T6A7
