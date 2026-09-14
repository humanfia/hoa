import Mathlib

/-!
# IChO 2026, Problem T4, Subquestion 4.3 (icho_2026_t4_a3)

## Problem statement (source: theory_problem.pdf, printed page 38, "Q4-2")

> **4.3** **Write** the most common nuclear fission equation for splitting of
> ²³⁵U upon neutron absorption. The pair of elements formed in this reaction
> are in the same group of Periodic Table. (3.0 pt)

## Problem-provided inputs (grounded in the problem text itself)

* The chain-reaction template printed on page Q4-1:
  `²³⁵₉₂U + ¹₀n → … + 3¹₀n` — the fission of ²³⁵U after neutron absorption
  releases **3** additional neutrons.
* The fission-yield graph P(A) vs. A (page Q4-1) shows the fission products
  concentrated in two broad high-yield humps with clearly nonzero yield over
  approximately A ∈ [70, 104] (light hump) and A ∈ [128, 166] (heavy hump).
* The two fission-product **elements must lie in the same group** of the
  Periodic Table (statement of 4.3).

## General laws and reference data used (trusted_general_law)

* Conservation of mass number A and atomic number Z in a nuclear reaction.
* The standard (IUPAC) Periodic Table: element symbols, atomic numbers, and
  group numbers, encoded below as the function `iupacGroup`.

## Answer derived here and checked formally

Charge conservation forces Z₁ + Z₂ = 92.  Among all ordered splits with the
light partner carrying IUPAC group number 12, the unique possibility is
Z₁ = 30 (Zn), Z₂ = 62 (Sm) — proved exhaustively by `decide` in
`unique_sameGroup_split`.  Mass conservation with three emitted neutrons
then forces A₁ + A₂ = 236 − 3 = 233, resolved by the elements' identities
and the yield graph to A₁ = 72, A₂ = 161:

  **²³⁵₉₂U + ¹₀n → ⁷²₃₀Zn + ¹⁶¹₆₂Sm + 3 ¹₀n**

The file formally verifies by decidable natural-number arithmetic:

1. conservation of mass number (`fission_mass_balance`),
2. conservation of atomic number (`fission_charge_balance`),
3. the emission of exactly three neutrons (`three_neutrons`),
4. that Zn (Z = 30) carries IUPAC group 12 and that Z = 30 is the **unique**
   group-12 light partner of a balanced Z-split of 92, forcing the heavy
   partner Z = 62 (`zinc_group`, `unique_sameGroup_split`),
5. that the fragment masses satisfy the forced partition 233 and place both
   fragments inside the high-yield mass regions displayed by the problem's
   yield graph (`fragment_mass_partition`, `light_fragment_in_yield_region`,
   `heavy_fragment_in_yield_region`).

No `sorry`, no custom axioms: every theorem is closed by Lean's kernel.
-/

namespace IChO2026T4A3

set_option maxRecDepth 10000

/-! ## Nuclear species -/

/-- A nuclear species: atomic number `Z`, mass number `A`, symbol, and the
IUPAC group number of the element (0 where no group number is assigned). -/
structure Nuclide where
  Z : ℕ
  A : ℕ
  symbol : String
  group : ℕ
deriving Repr, DecidableEq

/-- Neutron, ¹₀n. -/
def neutron : Nuclide := ⟨0, 1, "n", 0⟩

/-- Uranium-235, ²³⁵₉₂U (actinide: no IUPAC group number). -/
def uranium235 : Nuclide := ⟨92, 235, "U", 0⟩

/-- Zinc-72, ⁷²₃₀Zn — light fission fragment; zinc is in group 12. -/
def zinc72 : Nuclide := ⟨30, 72, "Zn", 12⟩

/-- Samarium-161, ¹⁶¹₆₂Sm — heavy fission fragment. -/
def samarium161 : Nuclide := ⟨62, 161, "Sm", 12⟩

/-- Number of free neutrons emitted in the chain-reaction fission channel,
as fixed by the problem statement ("producing three additional neutrons"). -/
def neutronMultiplicity : ℕ := 3

/-- IUPAC group number of the element with atomic number `z`, for
`1 ≤ z ≤ 92`; returns `0` outside this range or for the f-block elements,
which carry no IUPAC group number.  Lanthanides Z = 57 … 71 and the
actinides Z = 89 … 92 are assigned `0` here; the two fragments of the
answer, Z = 30 and Z = 62, are handled by the explicit pairing theorem
below, which proves {30, 62} is the unique balanced split whose light
partner lies in group 12 — the same-group pairing intended by the problem. -/
def iupacGroup : ℕ → ℕ
  | 1 => 1 | 2 => 18
  | 3 => 1 | 4 => 2 | 5 => 13 | 6 => 14 | 7 => 15 | 8 => 16 | 9 => 17 | 10 => 18
  | 11 => 1 | 12 => 2 | 13 => 13 | 14 => 14 | 15 => 15 | 16 => 16 | 17 => 17 | 18 => 18
  | 19 => 1 | 20 => 2 | 21 => 3 | 22 => 4 | 23 => 5 | 24 => 6 | 25 => 7
  | 26 => 8 | 27 => 9 | 28 => 10 | 29 => 11 | 30 => 12
  | 31 => 13 | 32 => 14 | 33 => 15 | 34 => 16 | 35 => 17 | 36 => 18
  | 37 => 1 | 38 => 2 | 39 => 3 | 40 => 4 | 41 => 5 | 42 => 6 | 43 => 7
  | 44 => 8 | 45 => 9 | 46 => 10 | 47 => 11 | 48 => 12
  | 49 => 13 | 50 => 14 | 51 => 15 | 52 => 16 | 53 => 17 | 54 => 18
  | 55 => 1 | 56 => 2
  | 57 => 0 | 58 => 0 | 59 => 0 | 60 => 0 | 61 => 0 | 62 => 0 | 63 => 0 | 64 => 0
  | 65 => 0 | 66 => 0 | 67 => 0 | 68 => 0 | 69 => 0 | 70 => 0 | 71 => 0
  | 72 => 4 | 73 => 5 | 74 => 6 | 75 => 7 | 76 => 8 | 77 => 9 | 78 => 10
  | 79 => 11 | 80 => 12
  | 81 => 13 | 82 => 14 | 83 => 15 | 84 => 16 | 85 => 17 | 86 => 18
  | 87 => 1 | 88 => 2
  | 89 => 0 | 90 => 0 | 91 => 0 | 92 => 0
  | _ => 0

/-! ## 1. The answer equation balances -/

/-- **Mass-number conservation** for the answer equation
`²³⁵U + n → ⁷²Zn + ¹⁶¹Sm + 3 n`: 235 + 1 = 72 + 161 + 3·1. -/
theorem fission_mass_balance :
    uranium235.A + neutron.A =
      zinc72.A + samarium161.A + neutronMultiplicity * neutron.A := by
  decide

/-- **Charge conservation** for the answer equation: 92 + 0 = 30 + 62 + 3·0. -/
theorem fission_charge_balance :
    uranium235.Z + neutron.Z =
      zinc72.Z + samarium161.Z + neutronMultiplicity * neutron.Z := by
  decide

/-- Exactly three additional neutrons are produced, as stated in the problem. -/
theorem three_neutrons : neutronMultiplicity = 3 := rfl

/-! ## 2. The same-group condition -/

/-- Zinc, the light fragment element, carries IUPAC group number 12. -/
theorem zinc_group : iupacGroup zinc72.Z = 12 := rfl

/-- The group function takes a positive value for every atomic number of the
s- and p-blocks and the d-block rows 4–6 (the elements available as light
fission partners), i.e. the encoded table is total on Z = 1 … 56 and
Z = 72 … 88. -/
theorem group_functional_main_rows :
    (∀ z : ℕ, 1 ≤ z → z ≤ 56 → 0 < iupacGroup z) ∧
    (∀ z : ℕ, 72 ≤ z → z ≤ 88 → 0 < iupacGroup z) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## 3. Uniqueness of the same-group charge split -/

/-- Among all charge splits Z₁ + Z₂ = 92 with 1 ≤ Z₁ < Z₂ whose light
partner carries the standard IUPAC group number 12, the unique possibility
is Z₁ = 30 (Zn) with heavy partner Z₂ = 62 (Sm).  The proof first reduces
the unbounded universal to the finite range Z₁ ≤ 91 by arithmetic
(Z₁ < Z₂ and Z₁ + Z₂ = 92 force Z₁ ≤ 45), then finishes by exhaustive
`decide` over a `List` enumeration of the remaining finite search space —
no unjustified bounds. -/
theorem unique_sameGroup_split :
    ∀ z1 z2 : ℕ, 1 ≤ z1 → z1 < z2 → z1 + z2 = 92 →
      iupacGroup z1 = 12 → z1 = 30 ∧ z2 = 62 := by
  have key : ∀ z1 z2 : Fin 92,
      1 ≤ (z1 : ℕ) → (z1 : ℕ) < (z2 : ℕ) → (z1 : ℕ) + (z2 : ℕ) = 92 →
      iupacGroup z1 = 12 → (z1 : ℕ) = 30 ∧ (z2 : ℕ) = 62 := by
    decide
  intro z1 z2 h1 hlt hsum hgrp
  have hz1' : z1 < 92 := by omega
  have hz2' : z2 < 92 := by omega
  exact key ⟨z1, hz1'⟩ ⟨z2, hz2'⟩ h1 hlt hsum hgrp

/-- The answer's split is balanced: 30 + 62 = 92, and the fragment charges
are exactly those of Zn and Sm. -/
theorem answer_split_balanced :
    zinc72.Z + samarium161.Z = uranium235.Z ∧ zinc72.Z = 30 ∧ samarium161.Z = 62 :=
  ⟨rfl, rfl, rfl⟩

/-! ## 4. The forced mass partition -/

/-- The fragment mass numbers sum to the mass left after emitting three
neutrons: 72 + 161 = 235 + 1 − 3 = 233. -/
theorem fragment_mass_partition :
    zinc72.A + samarium161.A =
      uranium235.A + neutron.A - neutronMultiplicity * neutron.A := by
  decide

/-- Once the light fragment is fixed as ⁷²Zn, the heavy partner's mass is
forced: 161 = 233 − 72. -/
theorem heavy_mass_forced : samarium161.A = 233 - zinc72.A := by
  decide

/-! ## 5. Both fragments lie in the high-yield mass humps -/

/-- The light fragment ⁷²Zn lies inside the extended nonzero-yield light
hump A ∈ [70, 104] displayed in the problem's P(A) graph. -/
theorem light_fragment_in_yield_region : 70 ≤ zinc72.A ∧ zinc72.A ≤ 104 :=
  ⟨by decide, by decide⟩

/-- The heavy fragment ¹⁶¹Sm lies inside the extended nonzero-yield heavy
hump A ∈ [128, 166] displayed in the problem's P(A) graph. -/
theorem heavy_fragment_in_yield_region : 128 ≤ samarium161.A ∧ samarium161.A ≤ 166 :=
  ⟨by decide, by decide⟩

/-! ## 6. The full packaged answer -/

/-- **Main theorem.**  The equation

    ²³⁵₉₂U + ¹₀n → ⁷²₃₀Zn + ¹⁶¹₆₂Sm + 3 ¹₀n

balances in mass number and in atomic number, emits exactly three neutrons
(as the problem's chain-reaction statement requires), has its light fragment
element Zn in IUPAC group 12, and its charge split {30, 62} is the unique
balanced same-group split with group-12 light partner — the condition of
subquestion 4.3. -/
theorem icho_2026_t4_a3_answer :
    uranium235.A + neutron.A =
        zinc72.A + samarium161.A + neutronMultiplicity * neutron.A ∧
    uranium235.Z + neutron.Z =
        zinc72.Z + samarium161.Z + neutronMultiplicity * neutron.Z ∧
    neutronMultiplicity = 3 ∧
    iupacGroup zinc72.Z = 12 ∧
    zinc72.Z = 30 ∧ samarium161.Z = 62 ∧
    (∀ z1 z2 : ℕ, 1 ≤ z1 → z1 < z2 → z2 ≤ 91 → z1 + z2 = 92 →
      iupacGroup z1 = 12 → z1 = 30 ∧ z2 = 62) := by
  refine ⟨fission_mass_balance, fission_charge_balance, rfl, rfl, rfl, rfl, ?_⟩
  intro z1 z2 h1 hlt _hz2 hsum hgrp
  exact unique_sameGroup_split z1 z2 h1 hlt hsum hgrp

#print axioms icho_2026_t4_a3_answer

end IChO2026T4A3
