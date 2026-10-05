import Mathlib
import CRNT.Basic.Reaction

/-!
# IChO 2026 T7-A4: CO₂ scrubbing with an aqueous solution of N-methyldiethanolamine (MDEA, 3)

## Source grounding (problem-only inputs, 58th IChO, Uzbekistan 2026, Theory Q7-2)

The shared problem context for T7 states (page Q7-2, directly above the 7.4 answer box):

> "An aqueous solution of **3** is being used to remove CO₂ from the mixture."
> "**7.4**  Write the equation for this reaction.  (3.0 pt)"

The structural formula printed for compound **3** (page Q7-2) is

  HO–CH₂–CH₂–N(CH₃)–CH₂–CH₂–OH

i.e. N-methyldiethanolamine (MDEA), molecular formula C₅H₁₃NO₂ (CH₃N(CH₂CH₂OH)₂):
a tertiary alkanolamine carrying no N–H proton.  MDEA is the standard industrial
"gas-treating" amine for CO₂ scrubbing: as a *tertiary* amine its Brønsted-base
reaction with CO₂ in *aqueous* solution is

  MeN(CH₂CH₂OH)₂ + CO₂ + H₂O → [MeNH(CH₂CH₂OH)₂]⁺ HCO₃⁻

i.e., at the molecular/formula level used below,

  C₅H₁₃NO₂ + CO₂ + H₂O → [C₅H₁₄NO₂]⁺ + [HCO₃]⁻

(MDEA protonates to the MDEAH⁺ ammonium ion and CO₂ is fixed as hydrogen carbonate.)
This is the reaction of the problem statement: the removal of CO₂ from the mixture by
the aqueous solution of 3.

## What is formalized here

Because a molecular-graph search formalization is out of scope for this model, we
formalize the answer at the level that the requested output type actually imposes: the
*balanced chemical equation*.  We introduce the species as their molecular formulas
(`Formula = String`, an actual input read off the printed structure of 3 and the
textually named CO₂/H₂O), give their elemental compositions, construct the CRNT
reaction  source = MDEA + CO₂ + H₂O ⟹ target = MDEAH⁺ + HCO₃⁻  and **prove**

1.  the exact stoichiometry of the CRNT reaction (coefficients 1, 1, 1 → 1, 1);
2.  element-by-element mass conservation across the reaction (C, H, N, O);
3.  overall charge conservation (0 → (+1) + (−1));
4.  the reaction is nontrivial (the target really differs from the source, i.e. a
    genuine chemical transformation, not a formal tautology).

No custom axioms are introduced; the only logical axioms used are Lean's standard
`propext` / `Classical.choice` / `Quot.sound` as reported by `#print axioms`.
-/

namespace IChO2026

/-- Chemical species of T7-A4 are given by their molecular formulas, as printed in the
problem (structure of 3 read off as C₅H₁₃NO₂; CO₂, H₂O, and the ionic products named in
the chemistry). -/
abbrev Formula := String

/-- N-methyldiethanolamine (compound 3), CH₃N(CH₂CH₂OH)₂ = C₅H₁₃NO₂. -/
def MDEA : Formula := "C5H13NO2"
/-- Carbon dioxide, the gas being scrubbed (problem text: "remove CO₂"). -/
def CO2 : Formula := "CO2"
/-- Water (problem text: "aqueous solution"). -/
def H2O : Formula := "H2O"
/-- Protonated MDEA (the MDEAH⁺ ammonium ion), C₅H₁₄NO₂⁺. -/
def MDEAH : Formula := "[C5H14NO2]+"
/-- Hydrogen carbonate (bicarbonate), HCO₃⁻. -/
def HCO3 : Formula := "[HCO3]-"

/-- Elemental composition of a chemical formula: number of atoms of each of the
elements relevant to T7-A4 (C, H, N, O).  These values are read off the printed
structure of compound 3 and the standard formulas of CO₂/H₂O; they are problem
inputs, not derived claims. -/
structure Composition where
  C : ℕ
  H : ℕ
  N : ℕ
  O : ℕ
deriving DecidableEq

namespace Composition

/-- MDEA = CH₃N(CH₂CH₂OH)₂: 5 C, 13 H, 1 N, 2 O. -/
def mdea : Composition := ⟨5, 13, 1, 2⟩
/-- CO₂. -/
def co2 : Composition := ⟨1, 0, 0, 2⟩
/-- H₂O. -/
def h2o : Composition := ⟨0, 2, 0, 1⟩
/-- MDEAH⁺ = protonated MDEA: one extra H. -/
def mdeaH : Composition := ⟨5, 14, 1, 2⟩
/-- HCO₃⁻. -/
def hco3 : Composition := ⟨1, 1, 0, 3⟩

/-- Elemental composition of each T7-A4 species. -/
def of : Formula → Composition
  | s =>
    if s = MDEA then mdea
    else if s = CO2 then co2
    else if s = H2O then h2o
    else if s = MDEAH then mdeaH
    else if s = HCO3 then hco3
    else ⟨0, 0, 0, 0⟩

end Composition

/-- Net electric charge of a T7-A4 species (in units of e).  The neutral reactants
carry charge 0; MDEAH⁺ carries +1 and HCO₃⁻ carries −1. -/
def charge : Formula → ℤ
  | s =>
    if s = MDEAH then 1
    else if s = HCO3 then -1
    else 0

/-- Net charge of a CRNT complex over the five T7-A4 species. -/
def chargeCount (c : CRNT.Complex Formula) : ℤ :=
  charge MDEA * c MDEA + charge CO2 * c CO2 + charge H2O * c H2O +
    charge MDEAH * c MDEAH + charge HCO3 * c HCO3

/-- The T7-A4 reaction: CO₂ scrubbing by the aqueous solution of 3 (MDEA),

    CH₃N(CH₂CH₂OH)₂ + CO₂ + H₂O → [CH₃NH(CH₂CH₂OH)₂]⁺ + HCO₃⁻

formalized as a CRNT reaction with source complex  1·MDEA + 1·CO₂ + 1·H₂O  and target
complex  1·MDEAH⁺ + 1·HCO₃⁻. -/
def mdeaCO2Reaction : CRNT.Reaction Formula where
  source := fun s =>
    if s = MDEA then 1 else if s = CO2 then 1 else if s = H2O then 1 else 0
  target := fun s =>
    if s = MDEAH then 1 else if s = HCO3 then 1 else 0

/-- Externally visible coefficient statement: the reactant stoichiometric coefficients
of MDEA, CO₂ and H₂O are all 1, and the product coefficients of MDEAH⁺ and HCO₃⁻ are
all 1 (all other coefficients 0).  This is the equation
  C₅H₁₃NO₂ + CO₂ + H₂O → C₅H₁₄NO₂⁺ + HCO₃⁻
made precise. -/
theorem mdeaCO2Reaction_stoichiometry :
    mdeaCO2Reaction.source MDEA = 1 ∧
    mdeaCO2Reaction.source CO2 = 1 ∧
    mdeaCO2Reaction.source H2O = 1 ∧
    mdeaCO2Reaction.source MDEAH = 0 ∧
    mdeaCO2Reaction.source HCO3 = 0 ∧
    mdeaCO2Reaction.target MDEAH = 1 ∧
    mdeaCO2Reaction.target HCO3 = 1 ∧
    mdeaCO2Reaction.target MDEA = 0 ∧
    mdeaCO2Reaction.target CO2 = 0 ∧
    mdeaCO2Reaction.target H2O = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The reaction is a genuine chemical transformation: the product complex differs from
the reactant complex (a proton has moved from water to MDEA and CO₂ has been fixed as
hydrogen carbonate). -/
theorem mdeaCO2Reaction_nontrivial : mdeaCO2Reaction.Nontrivial := by
  intro h
  have hs : mdeaCO2Reaction.source MDEA = 1 := rfl
  have ht : mdeaCO2Reaction.target MDEA = 0 := rfl
  have hc := congrFun h MDEA
  rw [hs, ht] at hc
  exact one_ne_zero hc

/-- Elementwise mass balance for C: reactants 5+1+0 = products 5+1. -/
theorem mdeaCO2Reaction_element_balance_C :
    (Composition.of MDEA).C + (Composition.of CO2).C + (Composition.of H2O).C =
      (Composition.of MDEAH).C + (Composition.of HCO3).C := by
  decide

/-- Elementwise mass balance for H: reactants 13+0+2 = products 14+1. -/
theorem mdeaCO2Reaction_element_balance_H :
    (Composition.of MDEA).H + (Composition.of CO2).H + (Composition.of H2O).H =
      (Composition.of MDEAH).H + (Composition.of HCO3).H := by
  decide

/-- Elementwise mass balance for N: reactants 1+0+0 = products 1+0. -/
theorem mdeaCO2Reaction_element_balance_N :
    (Composition.of MDEA).N + (Composition.of CO2).N + (Composition.of H2O).N =
      (Composition.of MDEAH).N + (Composition.of HCO3).N := by
  decide

/-- Elementwise mass balance for O: reactants 2+2+1 = products 2+3. -/
theorem mdeaCO2Reaction_element_balance_O :
    (Composition.of MDEA).O + (Composition.of CO2).O + (Composition.of H2O).O =
      (Composition.of MDEAH).O + (Composition.of HCO3).O := by
  decide

/-- Net electric charge is conserved: 0 = (+1) + (−1). -/
theorem mdeaCO2Reaction_charge_balance :
    chargeCount mdeaCO2Reaction.source = chargeCount mdeaCO2Reaction.target := by
  unfold chargeCount charge mdeaCO2Reaction MDEA CO2 H2O MDEAH HCO3
  decide

/-- The full chemical statement of T7-A4 bundled: nontriviality, elementwise mass
balance for all four elements, and charge balance — i.e. the equation is a genuine,
balanced chemical equation. -/
theorem mdeaCO2Reaction_answer :
    mdeaCO2Reaction.Nontrivial ∧
    (Composition.of MDEA).C + (Composition.of CO2).C + (Composition.of H2O).C =
      (Composition.of MDEAH).C + (Composition.of HCO3).C ∧
    (Composition.of MDEA).H + (Composition.of CO2).H + (Composition.of H2O).H =
      (Composition.of MDEAH).H + (Composition.of HCO3).H ∧
    (Composition.of MDEA).N + (Composition.of CO2).N + (Composition.of H2O).N =
      (Composition.of MDEAH).N + (Composition.of HCO3).N ∧
    (Composition.of MDEA).O + (Composition.of CO2).O + (Composition.of H2O).O =
      (Composition.of MDEAH).O + (Composition.of HCO3).O ∧
    chargeCount mdeaCO2Reaction.source = chargeCount mdeaCO2Reaction.target := by
  refine ⟨mdeaCO2Reaction_nontrivial,
    mdeaCO2Reaction_element_balance_C, mdeaCO2Reaction_element_balance_H,
    mdeaCO2Reaction_element_balance_N, mdeaCO2Reaction_element_balance_O,
    mdeaCO2Reaction_charge_balance⟩

end IChO2026

#print axioms IChO2026.mdeaCO2Reaction_answer
