import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T1-A6: thermogravimetric identification of the mysterious stone

This file formalizes the answer-blind source contract.  In particular, the
facts needed from T1-A4 and T1-A5 are rederived here from their printed data;
they are not imported as prior answers.

The thermogravimetric transformation is used quantitatively.  Its closed
contest-model species domain has six named roles and no catch-all stream:
hydrated salt, anhydrous salt core, water vapour, dioxygen, carbon dioxide,
and a primitive neutral aluminium oxide.  The two displayed mass plateaux are
interpreted through their mechanically fixed half-quantum intervals.
-/

namespace IChO2026Problems.T1A6

open scoped BigOperators

/-! ## Formulae, phases, and pinned conventional atomic weights -/

/-- The complete element domain needed by the A4/A5 derivations and the TGA
ledger.  This is a ledger domain, not a proposed exhaustive periodic table. -/
inductive Element where
  | H | C | O | F | Na | Al
  deriving DecidableEq, Fintype, Repr

/-- A molecular or formula-unit composition is its atom count for each element. -/
abbrev Formula := Element → ℕ

def zeroFormula : Formula := fun _ => 0

def addFormula (p q : Formula) : Formula := fun e => p e + q e

def scaleFormula (n : ℕ) (p : Formula) : Formula := fun e => n * p e

def singleElementFormula (wanted : Element) : Formula := fun e =>
  if e = wanted then 1 else 0

def formulaH2O : Formula := fun
  | .H => 2
  | .O => 1
  | _ => 0

def formulaO2 : Formula := fun
  | .O => 2
  | _ => 0

def formulaCO2 : Formula := fun
  | .C => 1
  | .O => 2
  | _ => 0

def hydrateFormula (core : Formula) (waters : ℕ) : Formula :=
  addFormula core (scaleFormula waters formulaH2O)

/-- Provenance carried by every finite domain or conventional datum used here. -/
inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

structure ConstraintOrigin where
  label : String
  origin : Provenance
  locator : String
  deriving Repr

def candidateDomainOrigins : List ConstraintOrigin :=
  [ { label := "stoichiometric stone and printed mass plateaux"
      origin := .problemText
      locator := "T1 page 3 final line and page 4 opening lines" },
    { label := "open-air atmosphere and named terminal plateau compound"
      origin := .problemImage
      locator := "T1_page-3.png and T1_page-4.png" },
    { label := "ordinary integral atom counts and common ionic charges"
      origin := .trustedGeneralLaw
      locator := "Al(III), Na(I), F(-I), and O(-II) charge balance" },
    { label := "A4 aluminium-fluoride and A5 mellitate compatibility checks"
      origin := .derivedTheorem
      locator := "previousPartA4Spec and previousPartA5Spec below" } ]

def atomicWeightDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def atomicWeightDatasetSha256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

/-- Exact olympiad-style nominal values returned by the pinned offline table. -/
def atomicWeight : Element → ℝ
  | .H => 1.0080
  | .C => 12.011
  | .O => 15.999
  | .F => 18.998
  | .Na => 22.990
  | .Al => 26.982

/-- An explicit enumeration bridge lets exact formula-mass calculations reduce
to six ordinary summands without relying on implementation details of the
derived `Fintype` instance. -/
def elementEquivFinSix : Element ≃ Fin 6 where
  toFun
    | .H => 0
    | .C => 1
    | .O => 2
    | .F => 3
    | .Na => 4
    | .Al => 5
  invFun i :=
    match i.val with
    | 0 => .H
    | 1 => .C
    | 2 => .O
    | 3 => .F
    | 4 => .Na
    | _ => .Al
  left_inv e := by cases e <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem sum_over_elements (f : Element → ℝ) :
    (∑ e : Element, f e) =
      f .H + f .C + f .O + f .F + f .Na + f .Al := by
  calc
    (∑ e : Element, f e) =
        ∑ i : Fin 6, f (elementEquivFinSix.symm i) := by
          apply Fintype.sum_equiv elementEquivFinSix
          intro e
          rw [Equiv.symm_apply_apply]
    _ = f .H + f .C + f .O + f .F + f .Na + f .Al := by
      rw [Fin.sum_univ_six]
      rfl

structure AtomicWeightReceipt where
  element : Element
  nominal : ℝ
  recordSha256 : String

def atomicWeightReceipts : List AtomicWeightReceipt :=
  [ ⟨.H, 1.0080, "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5"⟩,
    ⟨.C, 12.011, "0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a"⟩,
    ⟨.O, 15.999, "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588"⟩,
    ⟨.F, 18.998, "96f1d50213dac1410f593d656038a9faa513227e1fd342c16b54096aa2e3b1bb"⟩,
    ⟨.Na, 22.990, "14234e37d6ac93ded8d1d6f1883bd01f1855b92c90a61fb1370b0bb83f736417"⟩,
    ⟨.Al, 26.982, "bdb840d02b2eb42be07e27b58fc76501786c75d0a321d38f76dae129c84f5e7f"⟩ ]

def AtomicWeightReceiptsMatch : Prop :=
  ∀ r ∈ atomicWeightReceipts, atomicWeight r.element = r.nominal

theorem atomicWeightReceipts_match : AtomicWeightReceiptsMatch := by
  -- Each branch reduces to equality of the exact registry numeral recorded above.
  norm_num [AtomicWeightReceiptsMatch, atomicWeightReceipts, atomicWeight]

def molarMass (p : Formula) : ℝ :=
  ∑ e : Element, (p e : ℝ) * atomicWeight e

noncomputable def elementMassFraction (e : Element) (p : Formula) : ℝ :=
  (p e : ℝ) * atomicWeight e / molarMass p

noncomputable def waterMassFraction (p : Formula) (waters : ℕ) : ℝ :=
  (waters : ℝ) * molarMass formulaH2O / molarMass p

def percent (fraction : ℝ) : ℝ := 100 * fraction

inductive Phase where
  | solid | liquid | gas | aqueous | unspecified
  deriving DecidableEq, Repr

structure Species where
  label : String
  formula : Formula
  charge : ℤ
  phase : Phase

structure SpeciesAmount where
  coefficient : ℕ
  species : Species

def atomInventory (xs : List SpeciesAmount) : Formula :=
  xs.foldl (fun total x => addFormula total (scaleFormula x.coefficient x.species.formula))
    zeroFormula

def chargeInventory (xs : List SpeciesAmount) : ℤ :=
  xs.foldl (fun total x => total + (x.coefficient : ℤ) * x.species.charge) 0

def formulaMassInventory (xs : List SpeciesAmount) : ℝ :=
  xs.foldl (fun total x => total + (x.coefficient : ℝ) * molarMass x.species.formula) 0

def AtomBalanced (inputs outputs : List SpeciesAmount) : Prop :=
  atomInventory inputs = atomInventory outputs

def ChargeBalanced (inputs outputs : List SpeciesAmount) : Prop :=
  chargeInventory inputs = chargeInventory outputs

def FormulaMassBalanced (inputs outputs : List SpeciesAmount) : Prop :=
  formulaMassInventory inputs = formulaMassInventory outputs

/-! ## Inline derivation of the A4 information used by A6 -/

def formulaNaF : Formula := fun
  | .Na => 1
  | .F => 1
  | _ => 0

def formulaAlF3 : Formula := fun
  | .Al => 1
  | .F => 3
  | _ => 0

def formulaNa3AlF6 : Formula := fun
  | .Na => 3
  | .Al => 1
  | .F => 6
  | _ => 0

def a4AnhydrousC : Species :=
  ⟨"C: aluminium fluoride", formulaAlF3, 0, .solid⟩

def a4SodiumFluoride : Species :=
  ⟨"sodium fluoride", formulaNaF, 0, .solid⟩

def a4CompoundD : Species :=
  ⟨"D: sodium hexafluoroaluminate", formulaNa3AlF6, 0, .solid⟩

def a4ReactionInputs : List SpeciesAmount :=
  [⟨1, a4AnhydrousC⟩, ⟨3, a4SodiumFluoride⟩]

def a4ReactionOutputs : List SpeciesAmount :=
  [⟨1, a4CompoundD⟩]

/-- Candidate verification for A4.  The percentages are component mass divided
by total compound mass, and `0.01` is the printed percentage-point quantum. -/
def PreviousPartA4Spec : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
      (percent (waterMassFraction (hydrateFormula formulaAlF3 3) 3)) 39.16 0.01 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      (percent (elementMassFraction .Na formulaNa3AlF6)) 32.85 0.01 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      (percent (elementMassFraction .Al formulaNa3AlF6)) 12.85 0.01 ∧
  AtomBalanced a4ReactionInputs a4ReactionOutputs ∧
  ChargeBalanced a4ReactionInputs a4ReactionOutputs

theorem previousPartA4_derived : PreviousPartA4Spec := by
  -- Expand all three formula masses; the remaining goals are exact rational
  -- interval arithmetic and the AlF3 + 3 NaF atom ledger.
  norm_num [PreviousPartA4Spec, IChO2026Chem.Reporting.ConsistentMeasurement,
    percent, waterMassFraction, elementMassFraction, molarMass, hydrateFormula,
    formulaH2O, formulaAlF3, formulaNa3AlF6, atomicWeight, AtomBalanced,
    atomInventory, a4ReactionInputs, a4ReactionOutputs, a4AnhydrousC,
    a4SodiumFluoride, a4CompoundD, addFormula, scaleFormula, zeroFormula,
    ChargeBalanced, chargeInventory, sum_over_elements]
  funext e
  cases e <;>
    norm_num [addFormula, scaleFormula, zeroFormula, formulaAlF3, formulaNaF,
      formulaNa3AlF6]

/-- The source also gives pH ≈ 4, dilute nitric acid, precipitation by NaF, and
industrial use of D.  They are retained as source cues but are not free Boolean
filters and are not needed to force the TGA answer. -/
def a4SourceCues : List String :=
  [ "stone dissolved in dilute nitric acid",
    "pH adjusted to approximately 4 before NaF addition",
    "C·xH2O is a precipitate",
    "anhydrous C reacts with excess NaF to give D",
    "D is used in industrial production of Q" ]

/-! ## Inline derivation of the A5 information used by A6 -/

inductive StructuralComponent where
  | aromaticC6Core
  | methylGroup
  | carboxylGroup
  | anhydrideC2O3Fragment
  deriving DecidableEq, Repr

def componentFormula : StructuralComponent → Formula
  | .aromaticC6Core => fun
      | .C => 6
      | _ => 0
  | .methylGroup => fun
      | .C => 1
      | .H => 3
      | _ => 0
  | .carboxylGroup => fun
      | .C => 1
      | .H => 1
      | .O => 2
      | _ => 0
  | .anhydrideC2O3Fragment => fun
      | .C => 2
      | .O => 3
      | _ => 0

def assembleComponents (xs : List (ℕ × StructuralComponent)) : Formula :=
  xs.foldl
    (fun total x => addFormula total (scaleFormula x.1 (componentFormula x.2)))
    zeroFormula

def eComponentLedger : List (ℕ × StructuralComponent) :=
  [(1, .aromaticC6Core), (6, .methylGroup)]

def fComponentLedger : List (ℕ × StructuralComponent) :=
  [(1, .aromaticC6Core), (6, .carboxylGroup)]

def gComponentLedger : List (ℕ × StructuralComponent) :=
  [(1, .aromaticC6Core), (3, .anhydrideC2O3Fragment)]

def formulaE : Formula := assembleComponents eComponentLedger

def formulaF : Formula := assembleComponents fComponentLedger

def formulaG : Formula := assembleComponents gComponentLedger

inductive RingSubstituent where
  | methyl | carboxyl
  deriving DecidableEq, Repr

def rotateSite (step : ℕ) (i : Fin 6) : Fin 6 :=
  ⟨(i.val + step) % 6, Nat.mod_lt _ (by norm_num)⟩

def eSubstituent (_ : Fin 6) : RingSubstituent := .methyl

def fSubstituent (_ : Fin 6) : RingSubstituent := .carboxyl

def SixFoldInvariant (pattern : Fin 6 → RingSubstituent) : Prop :=
  ∀ i, pattern (rotateSite 1 i) = pattern i

/-- Three adjacent carboxyl pairs, encoded without hiding their topology. -/
def gAnhydridePair (i j : Fin 6) : Prop :=
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
  (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
  (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)

def ThreeFoldPairInvariant : Prop :=
  ∀ i j, gAnhydridePair i j ↔ gAnhydridePair (rotateSite 2 i) (rotateSite 2 j)

def formulaMellitateAnion : Formula := fun
  | .C => 12
  | .O => 12
  | _ => 0

inductive NamedTransformUse where
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

/-- Source-arrow data bind direction, named reagent, roles, formula carriers,
and image locator while leaving every omitted protocol detail unknown. -/
structure SourceArrow where
  reactantRole : String
  reagentLabel : String
  productRole : String
  reactantFormula : Formula
  productFormula : Formula
  locator : String
  useClass : NamedTransformUse

def a5PermanganateArrow : SourceArrow where
  reactantRole := "E"
  reagentLabel := "KMnO4 in acidic HNO3 solution"
  productRole := "F"
  reactantFormula := formulaE
  productFormula := formulaF
  locator := "T1_page-3.png: E --KMnO4/HNO3--> F"
  useClass := .qualitativeNamedTransformOnly

def a5PhosphorusPentoxideArrow : SourceArrow where
  reactantRole := "F"
  reagentLabel := "P2O5"
  productRole := "G"
  reactantFormula := formulaF
  productFormula := formulaG
  locator := "T1_page-3.png: F --P2O5--> G"
  useClass := .qualitativeNamedTransformOnly

/-- Both printed arrows are used only as qualitative named-transform
compatibility constraints.  No yield, completeness, phase, or byproduct claim
is made. -/
def A5NamedTransformCompatibility : Prop :=
  a5PermanganateArrow.reactantFormula = formulaE ∧
  a5PermanganateArrow.productFormula = formulaF ∧
  a5PhosphorusPentoxideArrow.reactantFormula = formulaF ∧
  a5PhosphorusPentoxideArrow.productFormula = formulaG ∧
  (∀ i, eSubstituent i = .methyl ∧ fSubstituent i = .carboxyl) ∧
  addFormula formulaG (scaleFormula 3 formulaH2O) = formulaF

def PreviousPartA5Spec : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
      (percent (elementMassFraction .H formulaE)) 11.18 0.01 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      (percent (elementMassFraction .O formulaG)) 49.98 0.01 ∧
  SixFoldInvariant eSubstituent ∧
  SixFoldInvariant fSubstituent ∧
  ThreeFoldPairInvariant ∧
  (∀ e, formulaG e > 0 → e = .C ∨ e = .O) ∧
  A5NamedTransformCompatibility ∧
  addFormula formulaMellitateAnion (scaleFormula 6 (singleElementFormula .H)) = formulaF

theorem previousPartA5_derived : PreviousPartA5Spec := by
  -- The ledgers give E = C12H18, F = C12H6O12, and G = C12O9.
  -- Exact registry arithmetic checks both percentages; the cyclic definitions
  -- discharge the two symmetry constraints and the two atom compatibilities.
  constructor
  · norm_num [IChO2026Chem.Reporting.ConsistentMeasurement, percent,
      elementMassFraction, molarMass, formulaE, eComponentLedger,
      assembleComponents, componentFormula, addFormula, scaleFormula,
      zeroFormula, atomicWeight, sum_over_elements]
  constructor
  · norm_num [IChO2026Chem.Reporting.ConsistentMeasurement, percent,
      elementMassFraction, molarMass, formulaG, gComponentLedger,
      assembleComponents, componentFormula, addFormula, scaleFormula,
      zeroFormula, atomicWeight, sum_over_elements]
  constructor
  · intro i
    rfl
  constructor
  · intro i
    rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gAnhydridePair, rotateSite]
  constructor
  · intro e he
    cases e <;>
      simp_all [formulaG, gComponentLedger, assembleComponents,
        componentFormula, addFormula, scaleFormula, zeroFormula]
  constructor
  · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro i
      exact ⟨rfl, rfl⟩
    · funext e
      cases e <;>
        simp [formulaG, gComponentLedger, formulaF, fComponentLedger,
          assembleComponents, componentFormula, addFormula, scaleFormula,
          formulaH2O, zeroFormula]
  · funext e
    cases e <;>
      simp [formulaMellitateAnion, singleElementFormula, formulaF,
        fComponentLedger, assembleComponents, componentFormula, addFormula,
        scaleFormula, zeroFormula]

/-! ## Salt-core assembly inherited by derivation, not by prior-answer import -/

def aluminumCation : Species :=
  ⟨"Al(III)", singleElementFormula .Al, 3, .aqueous⟩

def mellitateAnion : Species :=
  ⟨"mellitate", formulaMellitateAnion, -6, .aqueous⟩

def aluminumMellitateComponents : List SpeciesAmount :=
  [⟨2, aluminumCation⟩, ⟨1, mellitateAnion⟩]

def formulaAluminumMellitate : Formula :=
  addFormula (scaleFormula 2 (singleElementFormula .Al)) formulaMellitateAnion

def AluminumMellitateAssemblySpec : Prop :=
  atomInventory aluminumMellitateComponents = formulaAluminumMellitate ∧
  chargeInventory aluminumMellitateComponents = 0

theorem aluminumMellitateAssembly_derived : AluminumMellitateAssemblySpec := by
  -- Two Al(III) cations balance one six-negative mellitate anion.
  constructor
  · funext e
    cases e <;>
      norm_num [AluminumMellitateAssemblySpec, atomInventory,
        aluminumMellitateComponents, aluminumCation, mellitateAnion,
        formulaAluminumMellitate, formulaMellitateAnion,
        singleElementFormula, addFormula, scaleFormula, zeroFormula]
  · norm_num [AluminumMellitateAssemblySpec, chargeInventory,
      aluminumMellitateComponents, aluminumCation, mellitateAnion]

/-! ## Printed TGA data and its fixed measurement interpretation -/

structure DisplayedMass where
  shownGrams : ℝ
  quantumGrams : ℝ

def DisplayedMass.consistent (reading : DisplayedMass) (actualGrams : ℝ) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
    actualGrams reading.shownGrams reading.quantumGrams

inductive Atmosphere where
  | openAir
  deriving DecidableEq, Repr

inductive PlateauBehavior where
  | constantAtHigherTemperatures
  deriving DecidableEq, Repr

inductive TemperatureQualifier where
  | approximately | at
  deriving DecidableEq, Repr

structure TemperatureCue where
  celsius : ℝ
  qualifier : TemperatureQualifier

structure TgaSourceData where
  initial : DisplayedMass
  firstPlateau : DisplayedMass
  finalPlateau : DisplayedMass
  firstLossOnset : TemperatureCue
  firstPlateauTemperature : TemperatureCue
  secondDropTemperature : TemperatureCue
  atmosphere : Atmosphere
  terminalBehavior : PlateauBehavior

def sourceTga : TgaSourceData where
  initial := ⟨10.00, 0.01⟩
  firstPlateau := ⟨5.75, 0.01⟩
  finalPlateau := ⟨1.50, 0.01⟩
  firstLossOnset := ⟨100, .approximately⟩
  firstPlateauTemperature := ⟨200, .at⟩
  secondDropTemperature := ⟨400, .at⟩
  atmosphere := .openAir
  terminalBehavior := .constantAtHigherTemperatures

inductive StageClassification where
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

def tgaStageClassification : StageClassification := .quantitativeMaterialStage

/-- A primitive neutral oxide allowed by ordinary Al(+III)/O(-II) valence. -/
structure AluminumOxideStoichiometry where
  aluminumAtoms : ℕ
  oxygenAtoms : ℕ
  aluminumPositive : 0 < aluminumAtoms
  oxygenPositive : 0 < oxygenAtoms
  primitive : Nat.Coprime aluminumAtoms oxygenAtoms
  chargeNeutral : 3 * aluminumAtoms = 2 * oxygenAtoms

def aluminumOxideFormula (s : AluminumOxideStoichiometry) : Formula := fun
  | .Al => s.aluminumAtoms
  | .O => s.oxygenAtoms
  | _ => 0

/-- Role names form the complete source-bounded staged species domain. -/
inductive StageRole where
  | hydratedSalt
  | anhydrousSaltCore
  | waterVapor
  | dioxygen
  | carbonDioxide
  | terminalOxide
  deriving DecidableEq, Fintype, Repr

def stagedSpeciesDomain : Finset StageRole := Finset.univ

def roleSpecies (waters : ℕ) (oxide : AluminumOxideStoichiometry) : StageRole → Species
  | .hydratedSalt =>
      ⟨"hydrated stone", hydrateFormula formulaAluminumMellitate waters, 0, .solid⟩
  | .anhydrousSaltCore =>
      ⟨"anhydrous aluminium mellitate", formulaAluminumMellitate, 0, .solid⟩
  | .waterVapor => ⟨"water vapour", formulaH2O, 0, .gas⟩
  | .dioxygen => ⟨"dioxygen from open air", formulaO2, 0, .gas⟩
  | .carbonDioxide => ⟨"carbon dioxide", formulaCO2, 0, .gas⟩
  | .terminalOxide =>
      ⟨"primitive neutral aluminium oxide", aluminumOxideFormula oxide, 0, .solid⟩

def lowStageInputs (waters : ℕ) (oxide : AluminumOxideStoichiometry) :
    List SpeciesAmount :=
  [⟨1, roleSpecies waters oxide .hydratedSalt⟩]

def lowStageOutputs (waters : ℕ) (oxide : AluminumOxideStoichiometry) :
    List SpeciesAmount :=
  [ ⟨1, roleSpecies waters oxide .anhydrousSaltCore⟩,
    ⟨waters, roleSpecies waters oxide .waterVapor⟩ ]

/-- For generic `Al_a O_b`, `a` salt cores and `b+6a` O2 give two oxide
formula units and `12a` CO2.  This exposes every coefficient used later. -/
def highStageInputs (waters : ℕ) (oxide : AluminumOxideStoichiometry) :
    List SpeciesAmount :=
  [ ⟨oxide.aluminumAtoms, roleSpecies waters oxide .anhydrousSaltCore⟩,
    ⟨oxide.oxygenAtoms + 6 * oxide.aluminumAtoms,
      roleSpecies waters oxide .dioxygen⟩ ]

def highStageOutputs (waters : ℕ) (oxide : AluminumOxideStoichiometry) :
    List SpeciesAmount :=
  [ ⟨2, roleSpecies waters oxide .terminalOxide⟩,
    ⟨12 * oxide.aluminumAtoms, roleSpecies waters oxide .carbonDioxide⟩ ]

def LowStageAtomLedger (waters : ℕ) (oxide : AluminumOxideStoichiometry) : Prop :=
  AtomBalanced (lowStageInputs waters oxide) (lowStageOutputs waters oxide)

def HighStageAtomLedger (waters : ℕ) (oxide : AluminumOxideStoichiometry) : Prop :=
  AtomBalanced (highStageInputs waters oxide) (highStageOutputs waters oxide)

def TgaChargeLedgers (waters : ℕ) (oxide : AluminumOxideStoichiometry) : Prop :=
  ChargeBalanced (lowStageInputs waters oxide) (lowStageOutputs waters oxide) ∧
  ChargeBalanced (highStageInputs waters oxide) (highStageOutputs waters oxide)

def TgaFormulaMassLedgers (waters : ℕ) (oxide : AluminumOxideStoichiometry) : Prop :=
  FormulaMassBalanced (lowStageInputs waters oxide) (lowStageOutputs waters oxide) ∧
  FormulaMassBalanced (highStageInputs waters oxide) (highStageOutputs waters oxide)

def TgaPhaseLedger (waters : ℕ) (oxide : AluminumOxideStoichiometry) : Prop :=
  (roleSpecies waters oxide .hydratedSalt).phase = .solid ∧
  (roleSpecies waters oxide .anhydrousSaltCore).phase = .solid ∧
  (roleSpecies waters oxide .waterVapor).phase = .gas ∧
  (roleSpecies waters oxide .dioxygen).phase = .gas ∧
  (roleSpecies waters oxide .carbonDioxide).phase = .gas ∧
  (roleSpecies waters oxide .terminalOxide).phase = .solid

structure TgaIdentification where
  waterCount : ℕ
  oxide : AluminumOxideStoichiometry

/-- The numerator of each TGA fraction is the mass of the retained solid, and
the denominator is the total original sample (first stage) or retained
anhydrous core (second stage).  The same actual masses occur in both stages. -/
def TgaCompatible (candidate : TgaIdentification) : Prop :=
  0 < candidate.waterCount ∧
  LowStageAtomLedger candidate.waterCount candidate.oxide ∧
  HighStageAtomLedger candidate.waterCount candidate.oxide ∧
  TgaChargeLedgers candidate.waterCount candidate.oxide ∧
  TgaFormulaMassLedgers candidate.waterCount candidate.oxide ∧
  TgaPhaseLedger candidate.waterCount candidate.oxide ∧
  sourceTga.atmosphere = .openAir ∧
  sourceTga.terminalBehavior = .constantAtHigherTemperatures ∧
  ∃ initialMass firstPlateauMass finalMass : ℝ,
    sourceTga.initial.consistent initialMass ∧
    sourceTga.firstPlateau.consistent firstPlateauMass ∧
    sourceTga.finalPlateau.consistent finalMass ∧
    0 < finalMass ∧ finalMass < firstPlateauMass ∧ firstPlateauMass < initialMass ∧
    firstPlateauMass *
        molarMass (hydrateFormula formulaAluminumMellitate candidate.waterCount) =
      initialMass * molarMass formulaAluminumMellitate ∧
    finalMass *
        ((candidate.oxide.aluminumAtoms : ℝ) * molarMass formulaAluminumMellitate) =
      firstPlateauMass * (2 * molarMass (aluminumOxideFormula candidate.oxide))

def aluminumOxideTwoThree : AluminumOxideStoichiometry where
  aluminumAtoms := 2
  oxygenAtoms := 3
  aluminumPositive := by norm_num
  oxygenPositive := by norm_num
  primitive := by decide
  chargeNeutral := by norm_num

def canonicalTgaIdentification : TgaIdentification :=
  ⟨16, aluminumOxideTwoThree⟩

theorem canonicalTgaIdentification_compatible :
    TgaCompatible canonicalTgaIdentification := by
  -- Choose the common actual initial mass 10 g.  The exact registry masses
  -- predict 5.750703... g and 1.503131... g, respectively, both inside the
  -- fixed ±0.005 g display cells.  The remaining goals are the named ledgers.
  refine ⟨by norm_num [canonicalTgaIdentification], ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · funext e
    cases e <;>
      norm_num [LowStageAtomLedger, AtomBalanced, atomInventory,
        lowStageInputs, lowStageOutputs, roleSpecies,
        canonicalTgaIdentification, aluminumOxideTwoThree, hydrateFormula,
        formulaAluminumMellitate, formulaMellitateAnion, formulaH2O,
        singleElementFormula, addFormula, scaleFormula, zeroFormula]
  · funext e
    cases e <;>
      simp [atomInventory, highStageInputs, highStageOutputs, roleSpecies,
        canonicalTgaIdentification, aluminumOxideTwoThree,
        aluminumOxideFormula, formulaAluminumMellitate,
        formulaMellitateAnion, formulaO2, formulaCO2, singleElementFormula,
        addFormula, scaleFormula, zeroFormula]
  · norm_num [TgaChargeLedgers, ChargeBalanced, chargeInventory,
      lowStageInputs, lowStageOutputs, highStageInputs, highStageOutputs,
      roleSpecies, canonicalTgaIdentification, aluminumOxideTwoThree]
  · norm_num [TgaFormulaMassLedgers, FormulaMassBalanced,
      formulaMassInventory, lowStageInputs, lowStageOutputs, highStageInputs,
      highStageOutputs, roleSpecies, canonicalTgaIdentification,
      aluminumOxideTwoThree, molarMass, sum_over_elements, hydrateFormula,
      aluminumOxideFormula, formulaAluminumMellitate, formulaMellitateAnion,
      formulaH2O, formulaO2, formulaCO2, singleElementFormula, addFormula,
      scaleFormula, zeroFormula, atomicWeight]
  · norm_num [TgaPhaseLedger, roleSpecies, canonicalTgaIdentification]
  · refine ⟨10, (975210 / 169581 : ℝ), (1019610 / 678324 : ℝ), ?_⟩
    simp [DisplayedMass.consistent, IChO2026Chem.Reporting.ConsistentMeasurement,
      sourceTga, canonicalTgaIdentification, aluminumOxideTwoThree,
      molarMass, sum_over_elements, hydrateFormula, aluminumOxideFormula,
      formulaAluminumMellitate, formulaMellitateAnion, formulaH2O,
      singleElementFormula, addFormula, scaleFormula, atomicWeight]
    norm_num

theorem tgaIdentification_unique
    (candidate : TgaIdentification) (h : TgaCompatible candidate) :
    candidate = canonicalTgaIdentification := by
  -- The first interval isolates the integral hydrate count 16.  Primitive
  -- Al(+III)/O(-II) neutrality gives the oxide ratio 2:3; the final interval
  -- independently checks its solid-mass consequence.
  rcases h with
    ⟨hwaterPositive, _, _, _, _, _, _, _, initialMass, firstPlateauMass,
      finalMass, hInitial, hFirst, _, _, _, _, hLowMass, _⟩
  have hInitialCell := hInitial
  have hFirstCell := hFirst
  norm_num [DisplayedMass.consistent,
    IChO2026Chem.Reporting.ConsistentMeasurement, sourceTga] at hInitialCell hFirstCell
  rw [abs_le] at hInitialCell hFirstCell
  have hLowMass' := hLowMass
  simp [molarMass, sum_over_elements, hydrateFormula,
    formulaAluminumMellitate, formulaMellitateAnion, formulaH2O,
    singleElementFormula, addFormula, scaleFormula, atomicWeight] at hLowMass'
  have hwater : candidate.waterCount = 16 := by
    have hlt : candidate.waterCount < 17 := by
      by_contra hnot
      have hnNat : 17 ≤ candidate.waterCount := by omega
      have hnReal : (17 : ℝ) ≤ (candidate.waterCount : ℝ) := by
        exact_mod_cast hnNat
      have hfirstLower : (1149 / 200 : ℝ) ≤ firstPlateauMass := by
        nlinarith [hFirstCell.1]
      have hfirstNonnegative : 0 ≤ firstPlateauMass := by positivity
      have hproduct :
          (1149 / 200 : ℝ) * 17 ≤
            firstPlateauMass * (candidate.waterCount : ℝ) := by
        exact mul_le_mul hfirstLower hnReal (by norm_num) hfirstNonnegative
      nlinarith [hInitialCell.2]
    have hgt : 15 < candidate.waterCount := by
      by_contra hnot
      have hnNat : candidate.waterCount ≤ 15 := by omega
      have hnReal : (candidate.waterCount : ℝ) ≤ (15 : ℝ) := by
        exact_mod_cast hnNat
      have hnNonnegative : (0 : ℝ) ≤ candidate.waterCount := by positivity
      have hfirstUpper : firstPlateauMass ≤ (1151 / 200 : ℝ) := by
        nlinarith [hFirstCell.2]
      have hproduct :
          firstPlateauMass * (candidate.waterCount : ℝ) ≤
            (1151 / 200 : ℝ) * 15 := by
        exact mul_le_mul hfirstUpper hnReal hnNonnegative (by norm_num)
      nlinarith [hInitialCell.1]
    omega
  have hoxide : candidate.oxide = aluminumOxideTwoThree := by
    have htwo : 2 ∣ candidate.oxide.aluminumAtoms := by
      apply ((show Nat.Coprime 2 3 by decide).dvd_mul_left).mp
      exact ⟨candidate.oxide.oxygenAtoms, candidate.oxide.chargeNeutral⟩
    obtain ⟨k, hak⟩ := htwo
    have hbk : candidate.oxide.oxygenAtoms = 3 * k := by
      have hneutral := candidate.oxide.chargeNeutral
      omega
    have hkAl : k ∣ candidate.oxide.aluminumAtoms := by
      exact ⟨2, by omega⟩
    have hkO : k ∣ candidate.oxide.oxygenAtoms := by
      exact ⟨3, by omega⟩
    have hk : k = 1 :=
      Nat.eq_one_of_dvd_coprimes candidate.oxide.primitive hkAl hkO
    have ha : candidate.oxide.aluminumAtoms = 2 := by omega
    have hb : candidate.oxide.oxygenAtoms = 3 := by omega
    cases hox : candidate.oxide with
    | mk a b aluminumPositive oxygenPositive primitive chargeNeutral =>
        have ha' : a = 2 := by simpa [hox] using ha
        have hb' : b = 3 := by simpa [hox] using hb
        subst a
        subst b
        rfl
  cases hidentified : candidate with
  | mk waterCount oxide =>
      have hwater' : waterCount = 16 := by simpa [hidentified] using hwater
      have hoxide' : oxide = aluminumOxideTwoThree := by
        simpa [hidentified] using hoxide
      subst waterCount
      subst oxide
      rfl

theorem tgaIdentification_existsUnique :
    ∃! candidate : TgaIdentification, TgaCompatible candidate := by
  -- Existence is the preceding exact compatibility calculation; uniqueness
  -- applies all source intervals and both stage ledgers uniformly.
  refine ⟨canonicalTgaIdentification, canonicalTgaIdentification_compatible, ?_⟩
  intro candidate hcandidate
  exact tgaIdentification_unique candidate hcandidate

noncomputable def derivedTgaIdentification : TgaIdentification :=
  Classical.choose tgaIdentification_existsUnique

theorem derivedTgaIdentification_eq_canonical :
    derivedTgaIdentification = canonicalTgaIdentification := by
  -- Eliminate the source-derived unique witness.
  apply tgaIdentification_unique
  exact (Classical.choose_spec tgaIdentification_existsUnique).1

/-- Requested output carrier: selected from the unique source-compatible TGA
model, rather than defined to be a submitted formula. -/
noncomputable def stoneFormula : Formula :=
  hydrateFormula formulaAluminumMellitate derivedTgaIdentification.waterCount

/-- Requested output carrier for compound H, selected by the same model. -/
noncomputable def compoundHFormula : Formula :=
  aluminumOxideFormula derivedTgaIdentification.oxide

def expectedStoneFormula : Formula :=
  hydrateFormula formulaAluminumMellitate 16

def expectedCompoundHFormula : Formula :=
  aluminumOxideFormula aluminumOxideTwoThree

theorem stoneFormula_eq_expected : stoneFormula = expectedStoneFormula := by
  -- Substitute the unique TGA identification into the output carrier.
  unfold stoneFormula expectedStoneFormula
  rw [derivedTgaIdentification_eq_canonical]
  rfl

theorem compoundHFormula_eq_expected : compoundHFormula = expectedCompoundHFormula := by
  -- Substitute the primitive neutral terminal oxide selected above.
  unfold compoundHFormula expectedCompoundHFormula
  rw [derivedTgaIdentification_eq_canonical]
  rfl

/-- The raw symbolic result retains the A4/A5 derivations, all compatibility
constraints, and uniqueness before exposing either displayed formula. -/
def RawResultSpec : Prop :=
  AtomicWeightReceiptsMatch ∧
  PreviousPartA4Spec ∧
  PreviousPartA5Spec ∧
  AluminumMellitateAssemblySpec ∧
  TgaCompatible canonicalTgaIdentification ∧
  (∀ candidate, TgaCompatible candidate → candidate = canonicalTgaIdentification) ∧
  stoneFormula = expectedStoneFormula ∧
  compoundHFormula = expectedCompoundHFormula

/-- Exact-symbolic reporting expands both requested formulae into atom counts.
For the hydrate, this also preserves the decomposition into salt core plus
sixteen waters instead of reporting only the recombined empirical counts. -/
def ReportedResultSpec : Prop :=
  RawResultSpec ∧
  stoneFormula = hydrateFormula formulaAluminumMellitate 16 ∧
  stoneFormula .Al = 2 ∧ stoneFormula .C = 12 ∧
  stoneFormula .O = 28 ∧ stoneFormula .H = 32 ∧
  stoneFormula .Na = 0 ∧ stoneFormula .F = 0 ∧
  compoundHFormula .Al = 2 ∧ compoundHFormula .O = 3 ∧
  compoundHFormula .H = 0 ∧ compoundHFormula .C = 0 ∧
  compoundHFormula .Na = 0 ∧ compoundHFormula .F = 0

theorem rawResultSpec_proved : RawResultSpec := by
  -- Combine the independent prior-part checks with the source-derived unique
  -- TGA candidate and its two output projections.
  exact ⟨atomicWeightReceipts_match, previousPartA4_derived,
    previousPartA5_derived, aluminumMellitateAssembly_derived,
    canonicalTgaIdentification_compatible, tgaIdentification_unique,
    stoneFormula_eq_expected, compoundHFormula_eq_expected⟩

theorem reportedResultSpec_proved : ReportedResultSpec := by
  -- Expand Al2[C6(COO)6]·16H2O and Al2O3 element by element.
  refine ⟨rawResultSpec_proved, ?_⟩
  rw [stoneFormula_eq_expected, compoundHFormula_eq_expected]
  simp [expectedStoneFormula, expectedCompoundHFormula, hydrateFormula,
    formulaAluminumMellitate, formulaMellitateAnion, formulaH2O,
    aluminumOxideFormula, aluminumOxideTwoThree, singleElementFormula,
    addFormula, scaleFormula]

/-- Hash-bound raw symbolic solve artifact. -/
theorem blindRawResultContract :
    ("5b03479227290948f08b6e84402dcd7a728a97b0562f9cd8e3643be8e30dafee" : String) =
        "5b03479227290948f08b6e84402dcd7a728a97b0562f9cd8e3643be8e30dafee" ∧
      IChO2026Problems.T1A6.RawResultSpec := by
  constructor
  · rfl
  · exact rawResultSpec_proved

/-- Hash-bound exact-symbolic reported solve artifact. -/
theorem blindReportedResultContract :
    ("4c2f9f44a27a00f94cba058804b2e51aa54fe537438e0381d8319606be8ff899" : String) =
        "4c2f9f44a27a00f94cba058804b2e51aa54fe537438e0381d8319606be8ff899" ∧
      IChO2026Problems.T1A6.ReportedResultSpec := by
  constructor
  · rfl
  · exact reportedResultSpec_proved

end IChO2026Problems.T1A6
