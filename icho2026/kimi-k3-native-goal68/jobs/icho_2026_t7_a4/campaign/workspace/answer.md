# IChO 2026 (58th IChO, Uzbekistan) — Theory Q7, subquestion 7.4 (T7-A4)

## Question

From the official problem materials (English, Q7-2, 3.0 pt):

> "An aqueous solution of **3** is being used to remove CO₂ from the mixture."
> "**7.4**  Write the equation for this reaction."

Compound **3** is printed on page Q7-2 as the structure

  HO–CH₂–CH₂–N(CH₃)–CH₂–CH₂–OH

i.e. **N-methyldiethanolamine (MDEA)**, CH₃N(CH₂CH₂OH)₂, molecular formula C₅H₁₃NO₂.

## Answer

**R MeN(CH₂CH₂OH)₂ + CO₂ + H₂O → [MeNH(CH₂CH₂OH)₂]⁺ HCO₃⁻**

Written with molecular formulas:

**C₅H₁₃NO₂ + CO₂ + H₂O → [C₅H₁₄NO₂]⁺ + [HCO₃]⁻**

(MDEAH⁺ bicarbonate: protonated MDEA plus hydrogen carbonate.)

## Reasoning (source-grounded)

1. **What is being asked.** The sentence immediately above the 7.4 box introduces the
   *CO₂ scrubber* of Fig. 1 (box "Z − CO₂ scrubber" on page Q7-1): an aqueous solution
   of compound 3 is used to remove CO₂ from the mixture.  "This reaction" is therefore
   the reaction of 3 with CO₂ in water.
2. **What compound 3 is.** The printed structure shows a tertiary amine: a central
   nitrogen bearing one methyl group and two 2-hydroxyethyl groups —
   N-methyldiethanolamine, the classical alkanolamine gas-treating agent (an industrial
   CO₂ absorbent).  Counting atoms in the printed structure gives C₅H₁₃NO₂.
3. **Which products.** MDEA is a *tertiary* amine: its nitrogen has no N–H hydrogen, so
   it cannot form a carbamate (the R₂N–COO⁻ pathway open to primary/secondary amines).
   A tertiary amine in aqueous solution therefore acts as a Brønsted base toward the
   carbonic acid formed from CO₂ + H₂O, giving the ammonium–hydrogen-carbonate pair —
   this is the standard chemistry of industrial MDEA gas sweetening
   (R₃N + CO₂ + H₂O → R₃NH⁺ + HCO₃⁻), a trusted general chemical law.
4. **Balance check.**  Reactants: C 5+1 = 6, H 13+2 = 15, N 1, O 2+2+1 = 5.
   Products: C 5+1 = 6, H 14+1 = 15, N 1, O 2+3 = 5.  Charge: 0 = (+1) + (−1).  The
   equation balances atom-for-atom and in charge with all coefficients equal to 1.

## Faithfulness notes

* The identification "compound 3 = MDEA (C₅H₁₃NO₂)" is read directly off the structure
  printed on page Q7-2 of the official English problem paper; CO₂ and the *aqueous*
  medium are named in the problem text. No official solutions, marking schemes, or
  external answer repositories were used.
* The requested output is a single balanced equation with exact (1:1:1:1:1)
  stoichiometry; no numeric reporting policy applies beyond exact symbolic form.
* The Lean formalization constructs this equation as a CRNT reaction over
  molecular-formula species and proves its stoichiometry, nontriviality,
  element-by-element mass balance (C, H, N, O) and overall charge balance.
