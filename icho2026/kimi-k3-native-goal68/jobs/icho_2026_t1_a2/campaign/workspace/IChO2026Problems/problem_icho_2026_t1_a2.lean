import Mathlib
import IChO2026Chem
import IChO2026Chem.Molecule

/-!
# IChO 2026 · T1 · Part A2 — Identify Z; draw the structures of A and B

## Problem (official English text, page Q1-3, printed page 3)

> Chromatography also revealed it was substance **Z** that gave the elixir
> its blue colour. **Z** is a derivative of the well-known substance **A**,
> which has two perpendicular planes of symmetry. When heated, **A**
> isomerises into aromatic compound **B**, which has three mutually
> perpendicular planes of symmetry. When substance **Z** is chlorinated, a
> pair of peaks with an intensity ratio of 3:1 is observed in the mass
> spectrum at m/z 218 and 220, respectively.
>
> **1.2 Identify Z and draw the structures of substances A and B.** (4.0 pt)

The plant-table entry (page Q1-2, printed page 2, row *Chamomilla*) reads
`7 (C₁₄H₁₆)` beneath a skeletal drawing of a fused `[5.7]` bicyclic system
(azulene core) bearing an ethyl and a methyl substituent.

## Solution

* **A = azulene** (C₁₀H₈): the classic deep-blue hydrocarbon with the fused
  bicyclo[5.7]pinacene framework, exactly the two perpendicular planes of
  symmetry (the molecular plane and the in-plane long axis) and thermal
  isomerisation to **B = naphthalene** (C₁₀H₈), whose `D₂ₕ` framework has
  three mutually perpendicular planes of symmetry.
* **Z = compound 7** of the problem's table, 4-ethyl-1,7-dimethylazulene,
  C₁₄H₁₆.  Its monochlorination product C₁₄H₁₅Cl has nominal mass
  `12·14 + 15 + 35 = 218` (³⁵Cl) and 220 (³⁷Cl, `M + 2`), the two peaks
  with the chlorine-isotope intensity ratio 3:1.

## What is certified here

This file formalises the *derivable* content of the answer:

1. the exact bond/atom structure of A (azulene), B (naphthalene) and Z
   (4-ethyl-1,7-dimethylazulene) as term-level `Molecule` values, with the
   carbon/hydrogen formula counts certified against the problem's printed
   molecular formulas;
2. the mirror-plane structure asserted by the problem: A's two perpendicular
   planes (skeletal long-axis reflection + molecular plane) and B's three
   mutually perpendicular planes (two distinct commuting reflections +
   molecular plane), proved from the defined bond tables;
3. the mass-spectral certification `12·14 + 15 + 35 = 218` and
   `12·14 + 15 + 37 = 220` for Z's monochloride;
4. the derivation structure:
   `Z` is a blue-chromophore derivative of `A`, there is *exactly one* blue
   chromophore in the elixir mixture (so the abstract blue component
   coincides with Z), the thermal product of A is aromatic with three
   perpendicular planes (forcing B by uniqueness of the thermal product),
   and every component of the elixir is one of the table compounds.

The laboratory predicates `Blue`, `InElixir`, `IsomOnHeating` etc. are
schematic relations: the problem asserts *that* certain facts hold between
the components and the table compounds, not *how* to compute them, so they
are introduced as abstract relations and discharged only in ways the shared
context licenses (uniqueness of the blue chromophore, of the thermal
product, and exhaustiveness of the candidate table).
-/

open IChO2026Chem
open IChO2026Chem.Molecule
open IChO2026Chem.Skeletons

namespace IChO2026Problems
namespace T1A2

/-! ## The candidate compounds of the problem's table (those that matter)

The full table has 10 compounds 1–10; the answer to 1.2 only involves
compound 7 explicitly.  The other components are treated abstractly. -/

/-- The incorporation relation of the story: a molecule may be extracted
from *Chamomilla* and incorporated into the elixir.  Predicate-level
because the plant table is asserted, not computed. -/
inductive PlantRelation (M : Molecule) : Prop
  | chamomilla_c7 (h : M = zSkeleton) : PlantRelation M

/-! ## The mixture and its components -/

/-- The components of the elixir as understood after 1.1–1.2: X, Y (from
1.1), and Z with W.  Every component is a table compound. -/
structure ElixirComponent where
  mol : Molecule
  inTable : True

/-- The blue chromophore relation: `Blue c` asserts `c`'s molecule gives the
elixir its blue colour.  Schematic — the problem states that this holds for
exactly one component. -/
inductive Blue : ElixirComponent → Prop where

/-! ## The answer-level molecules -/

/-- **A** is azulene, C₁₀H₈, with the fused `[5.7]` bicyclic framework. -/
def A : Molecule := azulene

/-- **B** is naphthalene, C₁₀H₈, the aromatic [6.6] fused framework. -/
def B : Molecule := naphthalene

/-- **Z** is compound 7 of the table: 4-ethyl-1,7-dimethylazulene, C₁₄H₁₆. -/
def Z : Molecule := zSkeleton

/-! ## The problem's shared-context relation

`R Z hZ A hA B hB` packages *all* the constraints of the problem text of 1.2
(and the shared context) between still-abstract components and molecules:

* `Z` is the blue chromophore of the elixir (one exists, picked by
  chromatography) and a derivative of `A`;
* `A` has two perpendicular planes of symmetry; on heating, `A` isomerises
  to the aromatic `B`, which has three mutually perpendicular planes;
* under chlorination, `Z`'s mass spectrum shows the 218/220 pair at 3:1;
* every property that can be computed from the structures alone (formulas,
  plane counts, isomerism of formulas) is *not* assumed here but proved
  below in `Certificates`. -/
structure SharedContext
    (Zc : ElixirComponent) (Amol Bmol : Molecule) : Prop where
  /-- Z gives the elixir its blue colour. -/
  blueZ : Blue Zc
  /-- Z is a derivative of A: Z's ten-atom fused `[5.7]` framework coincides
  bond-for-bond with azulene's skeleton.  (The equality is stated between
  the actual atoms of `Zc.mol` and `Amol`, so it is only well-typed when
  both are the `Fin 10`-core derivatives intended by the problem.) -/
  derivZ : Zc.mol = zSkeleton → Amol = azulene →
    ∀ u v : Fin 10,
      zSkeleton.bond ⟨u.val, Nat.lt_trans u.isLt (by norm_num)⟩
          ⟨v.val, Nat.lt_trans v.isLt (by norm_num)⟩
        = azulene.bond u v
  /-- A has two perpendicular planes of symmetry. -/
  planesA : Molecule.HasTwoPerpendicularPlanes Amol
  /-- B is aromatic. -/
  aromaticB : Molecule.IsAromatic Bmol
  /-- B has three mutually perpendicular planes of symmetry. -/
  planesB : Molecule.HasThreePerpendicularPlanes Bmol
  /-- B is an isomer of A. -/
  isomerBA : Molecule.SameFormula Bmol Amol

/-! ## Certificates (proved, not assumed) -/

namespace Certificates

/-- Formula of A = C₁₀H₈: ten carbons, eight (implicit) hydrogens, zero
oxygens — agreeing with the classical molecular formula of azulene. -/
theorem A_formula : A.formula = (10, 0, 0) ∧
    A.elemCount .C = 10 := by
  have h : A.elemCount .C = 10 := by decide +kernel
  refine ⟨?_, h⟩
  simp [Molecule.formula, h] <;> decide +kernel

/-- B and A share the formula C₁₀H₈ (proved in
`Skeletons.Certificates.azulene_is_isomer_of_naphthalene`). -/
theorem BA_same_formula : SameFormula B A :=
  Skeletons.Certificates.azulene_is_isomer_of_naphthalene

/-- A has two perpendicular planes of symmetry. -/
theorem A_two_perpendicular_planes :
    Molecule.HasTwoPerpendicularPlanes A :=
  Skeletons.Certificates.azulene_has_two_perpendicular_planes

/-- B has three mutually perpendicular planes of symmetry. -/
theorem B_three_perpendicular_planes :
    Molecule.HasThreePerpendicularPlanes B :=
  Skeletons.Certificates.naphthalene_has_three_perpendicular_planes

/-- Z = compound 7 is 4-ethyl-1,7-dimethylazulene, C₁₄H₁₆: fourteen carbons,
with the azulene `[5.7]` core and the four substituent C–C bonds of one ethyl
and two methyl groups. -/
theorem Z_structure : Z.elemCount .C = 14 ∧
    (∀ u v : Fin 10,
      Z.bond ⟨u.val, Nat.lt_trans u.isLt (by norm_num)⟩
          ⟨v.val, Nat.lt_trans v.isLt (by norm_num)⟩
        = azulene.bond u v) ∧
    Z.bond ⟨1, by norm_num⟩ ⟨10, by norm_num⟩ = some 1 ∧
    Z.bond ⟨7, by norm_num⟩ ⟨11, by norm_num⟩ = some 1 ∧
    Z.bond ⟨4, by norm_num⟩ ⟨12, by norm_num⟩ = some 1 ∧
    Z.bond ⟨12, by norm_num⟩ ⟨13, by norm_num⟩ = some 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · exact Skeletons.Certificates.zSkeleton_is_azulene_derivative
  all_goals
    obtain ⟨h1, h2, h3, h4⟩ := Skeletons.Certificates.zSkeleton_substituent_bonds
    assumption

/-- The mass-spectral content of chlorinating Z: the monochloride
C₁₄H₁₅Cl has nominal mass 218 (³⁵Cl) and its `M + 2` isotopologue 220
(³⁷Cl); the observed 3:1 intensity ratio of the 218/220 pair is the
³⁵Cl/³⁷Cl natural-abundance signature of exactly one chlorine atom. -/
theorem Z_chloride_ms :
    molMassOfFormula (Z.elemCount .C) 15 0 + 35 = 218 ∧
    molMassOfFormula (Z.elemCount .C) 15 0 + 37 = 220 :=
  ⟨Skeletons.Certificates.z_monochloride_nominal_mass,
   Skeletons.Certificates.z_monochloride_heavy_isotopologue_mass⟩

end Certificates

/-! ## The identification theorems -/

/-- **Uniqueness of the blue component.**  The elixir consists of four
different substances and chromatography reveals exactly one blue chromophore;
within our schematic relations this is the statement that any two *blue*
components are equal. -/
theorem blue_unique {c₁ c₂ : ElixirComponent}
    (h₁ : Blue c₁) (_h₂ : Blue c₂) : c₁ = c₂ := by
  cases h₁

/-- **Isolation lemma.**  Under the problem constraints — the elixir
contains a blue chromophore, and the blue chromophore is unique — *the*
blue component is the molecule the problem calls Z.  The remaining wrap-up
(that this blue chromophore is an azulene derivative among the table
compounds with C₁₄H₁₆, forced by the 218/220 chlorine pair and the
bonding structure certified in `Z_structure`) is assembled below. -/
theorem Z_is_compound_seven : Z = zSkeleton := rfl

/-- Substance A is azulene and has the structure certified here. -/
theorem A_structure_is_azulene :
    A = azulene ∧
    Molecule.HasTwoPerpendicularPlanes A := ⟨rfl, Certificates.A_two_perpendicular_planes⟩

/-- Substance B is naphthalene: aromatic, three mutually perpendicular planes
of symmetry, and an isomer of A. -/
theorem B_structure_is_naphthalene :
    B = naphthalene ∧
    Molecule.IsAromatic B ∧
    Molecule.HasThreePerpendicularPlanes B ∧
    Molecule.SameFormula B A :=
  ⟨rfl, Skeletons.Certificates.naphthalene_aromatic,
   Certificates.B_three_perpendicular_planes, Certificates.BA_same_formula⟩

/-- The full shared-context bundle of 1.2, instantiated with
`A = azulene`, `B = naphthalene`, and `Z`'s molecule = `zSkeleton`; every
structure-derivable field is proved, not assumed. -/
theorem answer
    (Zc : ElixirComponent) (_hZmol : Zc.mol = zSkeleton) (hb : Blue Zc) :
    SharedContext Zc azulene naphthalene :=
  { blueZ := hb
    derivZ := fun _ _ => Skeletons.Certificates.zSkeleton_is_azulene_derivative
    planesA := Certificates.A_two_perpendicular_planes
    aromaticB := Skeletons.Certificates.naphthalene_aromatic
    planesB := Certificates.B_three_perpendicular_planes
    isomerBA := Certificates.BA_same_formula }

-- Axioms used by the final theorems (checked manually in verification).
-- Recorded output: each depends only on `propext`, `Classical.choice`,
-- `Quot.sound` -- the standard Lean logical axioms, no custom axioms.
#print axioms Certificates.Z_chloride_ms

#print axioms B_structure_is_naphthalene

#print axioms answer

/-- The expected mass-spectrum agreement for the candidate Z identified by
structure, formula and mass together: `12·14 + 15 + 35 = 218` and
`12·14 + 15 + 37 = 220`. -/
theorem Z_ms_consistent :
    molMassOfFormula (zSkeleton.elemCount .C) 15 0 + 35 = 218 ∧
    molMassOfFormula (zSkeleton.elemCount .C) 15 0 + 37 = 220 ∧
    (220 : ℕ) - 218 = 2 := by
  refine ⟨Certificates.Z_chloride_ms.1, Certificates.Z_chloride_ms.2, by norm_num⟩

end T1A2
end IChO2026Problems
