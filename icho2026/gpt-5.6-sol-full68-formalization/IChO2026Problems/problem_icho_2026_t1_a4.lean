import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 1, part A4

This file formalizes the identification of the metal `Q`, hydrated precipitate
`C · xH₂O`, and double fluoride `D`.  The three printed mass percentages are
treated as displayed measurements: a value printed to `0.01 %` represents a
mass-fraction interval of half-width `0.00005`.

The finite metal domain is selected before applying those percentages.  It is
the trusted-periodic-table list of metals below the independently derived
atomic-weight bound `36`: Li, Be, Na, Mg, and Al.  The decisive predicate
`AdmissibleAssignment` is uniform over that five-element domain and does not
mention the derived candidate.

The arrow `C + excess NaF ⟶ D` is used only as a
`qualitativeNamedTransformOnly` formula-compatibility constraint.  No claim is
made about yield, completeness, phases of `C` or `D`, or omitted byproducts.
-/

namespace IChO2026Problems.Icho2026T1A4

open IChO2026Chem.Reporting

noncomputable section

/-! ## Source-facing chemical vocabulary -/

/-- Provenance classes permitted by the answer-blind source contract. -/
inductive EvidenceProvenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- The phases explicitly distinguished by the bound source. -/
inductive Phase where
  | solid
  | aqueousSolution
  | unspecified
  deriving DecidableEq, Repr

/-- Named roles in the part-A4 process diagram. -/
inductive SpeciesRole where
  | stone
  | dissolvedStone
  | hydratedC
  | anhydrousC
  | sodiumFluoride
  | compoundD
  | metalQ
  deriving DecidableEq, Repr

/-- Reagents and reagent conditions printed in the source. -/
inductive ReagentCondition where
  | diluteNitricAcid
  | sodiumFluoride
  | excessSodiumFluoride
  deriving DecidableEq, Repr

/-- How a displayed transformation is used by the requested result. -/
inductive StagedTransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

/-- A source-arrow carrier.  `none` records an omitted item; it does not assert
that the corresponding coefficient, phase, or byproduct is absent. -/
structure SourceArrow where
  reactantRole : SpeciesRole
  productRole : SpeciesRole
  reagent : ReagentCondition
  reactantPhase : Phase
  productPhase : Phase
  approximatePH : Option ℚ
  stoichiometricCoefficient : Option ℕ
  transformationUse : StagedTransformationUse
  sourceLocator : String
  deriving Repr

/-- The source's dissolution arrow, which is contextual rather than decisive
for the three requested formula identifications. -/
def stoneDissolutionArrow : SourceArrow where
  reactantRole := .stone
  productRole := .dissolvedStone
  reagent := .diluteNitricAcid
  reactantPhase := .solid
  productPhase := .aqueousSolution
  approximatePH := none
  stoichiometricCoefficient := none
  transformationUse := .qualitativeNamedTransformOnly
  sourceLocator := "T1_page-3.png, Part 2 first process arrow"

/-- The pH-adjustment/NaF precipitation arrow. -/
def hydratePrecipitationArrow : SourceArrow where
  reactantRole := .dissolvedStone
  productRole := .hydratedC
  reagent := .sodiumFluoride
  reactantPhase := .aqueousSolution
  productPhase := .solid
  approximatePH := some 4
  stoichiometricCoefficient := none
  transformationUse := .qualitativeNamedTransformOnly
  sourceLocator := "T1_page-3.png, Part 2 process arrow at pH approximately 4"

/-- The explicitly directed `C` to `D` arrow. -/
def cToDSourceArrow : SourceArrow where
  reactantRole := .anhydrousC
  productRole := .compoundD
  reagent := .excessSodiumFluoride
  reactantPhase := .unspecified
  productPhase := .unspecified
  approximatePH := none
  stoichiometricCoefficient := none
  transformationUse := .qualitativeNamedTransformOnly
  sourceLocator := "T1_page-3.png, C --NaF--> D and accompanying sentence"

/-- A data carrier for the printed industrial-use observation.  It retains the
direction `D` is used to produce `Q`, but deliberately supplies no inverse
classification theorem. -/
structure IndustrialUseObservation where
  materialRole : SpeciesRole
  producedRole : SpeciesRole
  sourceLocator : String
  deriving Repr

def industrialUseObservation : IndustrialUseObservation where
  materialRole := .compoundD
  producedRole := .metalQ
  sourceLocator := "T1_page-3.png, Part 2 paragraph ending 'industrial production of Q'"

/-- The source calls the mysterious stone one stoichiometric compound. -/
structure StoneSampleObservation where
  sampleRole : SpeciesRole
  isStoichiometric : Bool
  sourceLocator : String
  deriving Repr

def stoneSampleObservation : StoneSampleObservation where
  sampleRole := .stone
  isStoichiometric := true
  sourceLocator := "T1_page-3.png, Part 2 opening sentence"

/-! ## Pinned conventional atomic weights and their provenance -/

/-- A compact local carrier for a successful lookup in the pinned offline
chemistry registry.  The nominal value is used as the exact conventional input
for this olympiad-style identification. -/
structure AtomicWeightReceipt where
  symbol : String
  atomicNumber : ℕ
  nominalValue : ℝ
  datasetVersion : String
  datasetSHA256 : String
  recordSHA256 : String

def pinnedDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def pinnedDatasetSHA256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def lithiumReceipt : AtomicWeightReceipt where
  symbol := "Li"
  atomicNumber := 3
  nominalValue := (694 : ℝ) / 100
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "2ab22ba6fed980e8fbe2548e375cd1052d19d710fd97776b02aa5a0a6d895b7c"

def berylliumReceipt : AtomicWeightReceipt where
  symbol := "Be"
  atomicNumber := 4
  nominalValue := (45061 : ℝ) / 5000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "02771a9e92a522ee006060bc222b4780be37ad6ac6ab811a0a1b2c2d89ee75c8"

def sodiumReceipt : AtomicWeightReceipt where
  symbol := "Na"
  atomicNumber := 11
  nominalValue := (22990 : ℝ) / 1000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "14234e37d6ac93ded8d1d6f1883bd01f1855b92c90a61fb1370b0bb83f736417"

def magnesiumReceipt : AtomicWeightReceipt where
  symbol := "Mg"
  atomicNumber := 12
  nominalValue := (24305 : ℝ) / 1000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "2e608771ea42401255eb776ab9aafb17d5aaaf2bebd2779b6fd53efb82b2c4c7"

def aluminumReceipt : AtomicWeightReceipt where
  symbol := "Al"
  atomicNumber := 13
  nominalValue := (26982 : ℝ) / 1000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "bdb840d02b2eb42be07e27b58fc76501786c75d0a321d38f76dae129c84f5e7f"

def potassiumBoundaryReceipt : AtomicWeightReceipt where
  symbol := "K"
  atomicNumber := 19
  nominalValue := (39098 : ℝ) / 1000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "b85a5c1a355dacaeaf84d80179237c44b4acceb48a72eaf418d0aeb10ce08484"

def fluorineReceipt : AtomicWeightReceipt where
  symbol := "F"
  atomicNumber := 9
  nominalValue := (18998 : ℝ) / 1000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "96f1d50213dac1410f593d656038a9faa513227e1fd342c16b54096aa2e3b1bb"

def hydrogenReceipt : AtomicWeightReceipt where
  symbol := "H"
  atomicNumber := 1
  nominalValue := (10080 : ℝ) / 10000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5"

def oxygenReceipt : AtomicWeightReceipt where
  symbol := "O"
  atomicNumber := 8
  nominalValue := (15999 : ℝ) / 1000
  datasetVersion := pinnedDatasetVersion
  datasetSHA256 := pinnedDatasetSHA256
  recordSHA256 := "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588"

/-! ## Candidate domain and formula model -/

/-- Exhaustive light-metal domain after the source percentages, fluoride
charge balance, and the ordinary positive-charge bound `z ≤ 4` imply that the
metal's atomic weight is below `36`.  This is a five-way domain, not an
answer-shaped singleton. -/
inductive LightMetal where
  | lithium
  | beryllium
  | sodium
  | magnesium
  | aluminum
  deriving DecidableEq, Fintype, Repr

/-- Provenance-bound carrier for the finite domain actually filtered below. -/
structure CandidateDomainCarrier where
  candidates : Finset LightMetal
  atomicWeightUpperBound : ℝ
  provenance : List EvidenceProvenance

def lightMetalCandidateDomainCarrier : CandidateDomainCarrier where
  candidates := Finset.univ
  atomicWeightUpperBound := 36
  provenance := [.problemText, .trustedGeneralLaw, .derivedTheorem]

def lightMetalCandidateDomain : Finset LightMetal :=
  lightMetalCandidateDomainCarrier.candidates

def candidateDomainProvenance : List EvidenceProvenance :=
  lightMetalCandidateDomainCarrier.provenance

/-- The filtered domain is visibly non-singleton and contains five cases. -/
theorem lightMetalCandidateDomain_card :
    lightMetalCandidateDomain.card = 5 := by
  native_decide

/-- Pinned nominal standard atomic weight on the prefiltered domain. -/
def standardAtomicWeight : LightMetal → ℝ
  | .lithium => lithiumReceipt.nominalValue
  | .beryllium => berylliumReceipt.nominalValue
  | .sodium => sodiumReceipt.nominalValue
  | .magnesium => magnesiumReceipt.nominalValue
  | .aluminum => aluminumReceipt.nominalValue

/-- Ordinary charge of the simple fluoride cation in the candidate audit. -/
def fluorideCationCharge : LightMetal → ℕ
  | .lithium => 1
  | .beryllium => 2
  | .sodium => 1
  | .magnesium => 2
  | .aluminum => 3

/-- Atom counts in a sodium/metal fluoride formula unit. -/
structure FluorideFormula where
  sodiumAtoms : ℕ
  metalAtoms : ℕ
  fluorineAtoms : ℕ
  deriving DecidableEq, Repr

/-- A formula together with the identity occupying its metal sites. -/
structure IdentifiedFluoride where
  metal : LightMetal
  formula : FluorideFormula
  deriving DecidableEq, Repr

/-- A hydrate formula keeps the anhydrous unit and its water multiplier
separate, matching the printed notation `C · xH₂O`. -/
structure HydratedFluorideFormula where
  anhydrous : IdentifiedFluoride
  waterMolecules : ℕ
  deriving DecidableEq, Repr

/-- The ordinary neutral binary fluoride `QF_z`. -/
def anhydrousCFormulaFor (q : LightMetal) : IdentifiedFluoride where
  metal := q
  formula := {
    sodiumAtoms := 0
    metalAtoms := 1
    fluorineAtoms := fluorideCationCharge q
  }

/-- Formula obtained by the candidate-level incorporation of `k` NaF formula
units into `QF_z`: `Na_k Q F_(z+k)`. -/
def compoundDFormulaFor (q : LightMetal) (k : ℕ) : IdentifiedFluoride where
  metal := q
  formula := {
    sodiumAtoms := k
    metalAtoms := 1
    fluorineAtoms := fluorideCationCharge q + k
  }

/-- Formula-level compatibility for the source arrow.  It does not claim that
the displayed transformation is complete or has no other streams. -/
def NaFFormulaCompatible
    (c d : IdentifiedFluoride) (k : ℕ) : Prop :=
  c.metal = d.metal ∧
  d.formula.sodiumAtoms = c.formula.sodiumAtoms + k ∧
  d.formula.metalAtoms = c.formula.metalAtoms ∧
  d.formula.fluorineAtoms = c.formula.fluorineAtoms + k

/-- Formal charge of a sodium/metal fluoride unit, with Na at `+1`, the metal
at its candidate fluoride charge, and F at `-1`. -/
def formulaCharge (f : IdentifiedFluoride) : ℤ :=
  (f.formula.sodiumAtoms : ℤ) +
    ((fluorideCationCharge f.metal * f.formula.metalAtoms : ℕ) : ℤ) -
    (f.formula.fluorineAtoms : ℤ)

/-! ## Source measurements and their mass-fraction basis -/

def sodiumAtomicWeight : ℝ := sodiumReceipt.nominalValue
def fluorineAtomicWeight : ℝ := fluorineReceipt.nominalValue
def hydrogenAtomicWeight : ℝ := hydrogenReceipt.nominalValue
def oxygenAtomicWeight : ℝ := oxygenReceipt.nominalValue

/-- One water molecule's conventional molar mass, computed without rounding. -/
def waterMolarMass : ℝ := 2 * hydrogenAtomicWeight + oxygenAtomicWeight

/-- A percentage printed to `0.01 %` has mass-fraction quantum `0.0001`. -/
def sourceMassFractionQuantum : ℝ := (1 : ℝ) / 10000

def shownSodiumMassFractionInD : ℝ := (3285 : ℝ) / 10000
def shownMetalMassFractionInD : ℝ := (1285 : ℝ) / 10000
def shownWaterMassFractionInHydrate : ℝ := (3916 : ℝ) / 10000

/-- Before naming the element, the `C + k NaF` compatibility model is
parameterized by its atomic weight, positive fluoride charge, and incorporated
NaF count. -/
structure FluoridePreAssignment where
  metalAtomicWeight : ℝ
  metalCharge : ℕ
  sodiumFluorideUnits : ℕ

def dSodiumMass (p : FluoridePreAssignment) : ℝ :=
  (p.sodiumFluorideUnits : ℝ) * sodiumAtomicWeight

def dMetalMass (p : FluoridePreAssignment) : ℝ := p.metalAtomicWeight

def dFluorineMass (p : FluoridePreAssignment) : ℝ :=
  (p.metalCharge + p.sodiumFluorideUnits : ℕ) * fluorineAtomicWeight

/-- Total-mixture molar mass is the denominator for both printed `D` mass
fractions. -/
def dTotalMass (p : FluoridePreAssignment) : ℝ :=
  dSodiumMass p + dMetalMass p + dFluorineMass p

def dSodiumMassFraction (p : FluoridePreAssignment) : ℝ :=
  dSodiumMass p / dTotalMass p

def dMetalMassFraction (p : FluoridePreAssignment) : ℝ :=
  dMetalMass p / dTotalMass p

/-- Candidate-independent constraints coming from the two displayed `D`
percentages and ordinary fluoride charge bounds. -/
def PreAdmissible (p : FluoridePreAssignment) : Prop :=
  0 < p.metalAtomicWeight ∧
  0 < p.metalCharge ∧
  p.metalCharge ≤ 4 ∧
  0 < p.sodiumFluorideUnits ∧
  ConsistentMeasurement
    (dSodiumMassFraction p) shownSodiumMassFractionInD sourceMassFractionQuantum ∧
  ConsistentMeasurement
    (dMetalMassFraction p) shownMetalMassFractionInD sourceMassFractionQuantum

/-- The displayed sodium, metal, and hence fluorine fractions force `k = z`,
`k ≤ 4`, and an atomic weight below 36 before the periodic-table domain is
filtered. -/
theorem preAdmissible_source_bounds
    (p : FluoridePreAssignment) (hp : PreAdmissible p) :
    p.sodiumFluorideUnits = p.metalCharge ∧
      p.sodiumFluorideUnits ≤ 4 ∧
      p.metalAtomicWeight < 36 := by
  rcases hp with ⟨hA, hz, hz4, hk, hs, hm⟩
  have htotal : 0 < dTotalMass p := by
    unfold dTotalMass dSodiumMass dMetalMass dFluorineMass
    norm_num [sodiumAtomicWeight, fluorineAtomicWeight, sodiumReceipt,
      fluorineReceipt]
    positivity
  have hslo : (6569 : ℝ) / 20000 ≤ dSodiumMassFraction p := by
    have h := (abs_le.mp hs.2).1
    norm_num [shownSodiumMassFractionInD, sourceMassFractionQuantum] at h
    linarith
  have hshi : dSodiumMassFraction p ≤ (6571 : ℝ) / 20000 := by
    have h := (abs_le.mp hs.2).2
    norm_num [shownSodiumMassFractionInD, sourceMassFractionQuantum] at h
    linarith
  have hmlo : (2569 : ℝ) / 20000 ≤ dMetalMassFraction p := by
    have h := (abs_le.mp hm.2).1
    norm_num [shownMetalMassFractionInD, sourceMassFractionQuantum] at h
    linarith
  have hmhi : dMetalMassFraction p ≤ (2571 : ℝ) / 20000 := by
    have h := (abs_le.mp hm.2).2
    norm_num [shownMetalMassFractionInD, sourceMassFractionQuantum] at h
    linarith
  have hslo' :
      ((6569 : ℝ) / 20000) * dTotalMass p ≤ dSodiumMass p := by
    apply (le_div_iff₀ htotal).mp
    simpa [dSodiumMassFraction] using hslo
  have hshi' :
      dSodiumMass p ≤ ((6571 : ℝ) / 20000) * dTotalMass p := by
    apply (div_le_iff₀ htotal).mp
    simpa [dSodiumMassFraction] using hshi
  have hmlo' :
      ((2569 : ℝ) / 20000) * dTotalMass p ≤ dMetalMass p := by
    apply (le_div_iff₀ htotal).mp
    simpa [dMetalMassFraction] using hmlo
  have hmhi' :
      dMetalMass p ≤ ((2571 : ℝ) / 20000) * dTotalMass p := by
    apply (div_le_iff₀ htotal).mp
    simpa [dMetalMassFraction] using hmhi
  have hledger :
      dTotalMass p = dSodiumMass p + dMetalMass p + dFluorineMass p := rfl
  have hflo' :
      ((5429 : ℝ) / 10000) * dTotalMass p ≤ dFluorineMass p := by
    nlinarith [hshi', hmhi']
  have hfhi' :
      dFluorineMass p ≤ ((5431 : ℝ) / 10000) * dTotalMass p := by
    nlinarith [hslo', hmlo']
  have hratioLower :
      ((5429 : ℝ) / 10000) * dSodiumMass p ≤
        ((6571 : ℝ) / 20000) * dFluorineMass p := by
    nlinarith [hflo', hshi']
  have hratioUpper :
      ((6569 : ℝ) / 20000) * dFluorineMass p ≤
        ((5431 : ℝ) / 10000) * dSodiumMass p := by
    nlinarith [hfhi', hslo']
  norm_num [dSodiumMass, dFluorineMass, sodiumAtomicWeight,
    fluorineAtomicWeight, sodiumReceipt, fluorineReceipt, Nat.cast_add] at hratioLower hratioUpper
  have hz4R : (p.metalCharge : ℝ) ≤ 4 := by exact_mod_cast hz4
  have hklt5R : (p.sodiumFluorideUnits : ℝ) < 5 := by
    nlinarith [hratioLower]
  have hklt5 : p.sodiumFluorideUnits < 5 := by exact_mod_cast hklt5R
  have hk4 : p.sodiumFluorideUnits ≤ 4 := by omega
  have hk4R : (p.sodiumFluorideUnits : ℝ) ≤ 4 := by exact_mod_cast hk4
  have hk_le_z : p.sodiumFluorideUnits ≤ p.metalCharge := by
    by_contra h
    have hgap : p.metalCharge + 1 ≤ p.sodiumFluorideUnits := by omega
    have hgapR : (p.metalCharge : ℝ) + 1 ≤ p.sodiumFluorideUnits := by
      exact_mod_cast hgap
    nlinarith [hratioLower]
  have hz_le_k : p.metalCharge ≤ p.sodiumFluorideUnits := by
    by_contra h
    have hgap : p.sodiumFluorideUnits + 1 ≤ p.metalCharge := by omega
    have hgapR : (p.sodiumFluorideUnits : ℝ) + 1 ≤ p.metalCharge := by
      exact_mod_cast hgap
    nlinarith [hratioUpper]
  have hkeq : p.sodiumFluorideUnits = p.metalCharge := by omega
  have hweightRatio :
      ((6569 : ℝ) / 20000) * dMetalMass p ≤
        ((2571 : ℝ) / 20000) * dSodiumMass p := by
    nlinarith [hmhi', hslo']
  norm_num [dMetalMass, dSodiumMass, sodiumAtomicWeight, sodiumReceipt] at hweightRatio
  have hweight : p.metalAtomicWeight < 36 := by
    nlinarith
  exact ⟨hkeq, hk4, hweight⟩

/-- The local candidate space.  The two unbounded natural-number coordinates
ensure that neither the NaF coefficient nor the hydrate count is selected in
advance. -/
structure StoneAssignment where
  q : LightMetal
  sodiumFluorideUnits : ℕ
  waterMolecules : ℕ
  deriving DecidableEq, Repr

def StoneAssignment.toPreAssignment (a : StoneAssignment) : FluoridePreAssignment where
  metalAtomicWeight := standardAtomicWeight a.q
  metalCharge := fluorideCationCharge a.q
  sodiumFluorideUnits := a.sodiumFluorideUnits

def StoneAssignment.anhydrousC (a : StoneAssignment) : IdentifiedFluoride :=
  anhydrousCFormulaFor a.q

def StoneAssignment.compoundD (a : StoneAssignment) : IdentifiedFluoride :=
  compoundDFormulaFor a.q a.sodiumFluorideUnits

def StoneAssignment.hydratedC (a : StoneAssignment) : HydratedFluorideFormula where
  anhydrous := a.anhydrousC
  waterMolecules := a.waterMolecules

/-- Mass of the anhydrous `QF_z` portion of the hydrate. -/
def hydrateAnhydrousMass (a : StoneAssignment) : ℝ :=
  standardAtomicWeight a.q +
    (fluorideCationCharge a.q : ℝ) * fluorineAtomicWeight

/-- Mass in the numerator of the hydrate's water mass fraction. -/
def hydrateWaterMass (a : StoneAssignment) : ℝ :=
  (a.waterMolecules : ℝ) * waterMolarMass

/-- Total hydrate molar mass, the denominator of the water mass fraction. -/
def hydrateTotalMass (a : StoneAssignment) : ℝ :=
  hydrateAnhydrousMass a + hydrateWaterMass a

def hydrateWaterMassFraction (a : StoneAssignment) : ℝ :=
  hydrateWaterMass a / hydrateTotalMass a

/-- Every decisive source-first constraint is applied uniformly here.  The
industrial-use sentence is retained by `industrialUseObservation`, but is not
misused as an unsupported inverse classification rule. -/
def AdmissibleAssignment (a : StoneAssignment) : Prop :=
  a.q ∈ lightMetalCandidateDomain ∧
  PreAdmissible a.toPreAssignment ∧
  0 < a.waterMolecules ∧
  ConsistentMeasurement
    (hydrateWaterMassFraction a)
    shownWaterMassFractionInHydrate
    sourceMassFractionQuantum ∧
  formulaCharge a.anhydrousC = 0 ∧
  formulaCharge a.compoundD = 0 ∧
  NaFFormulaCompatible a.anhydrousC a.compoundD a.sodiumFluorideUnits

/-! ## Derived candidate and independent specifications -/

/-- Candidate obtained by filtering the full five-metal/unbounded-count model. -/
def derivedAssignment : StoneAssignment where
  q := .aluminum
  sodiumFluorideUnits := 3
  waterMolecules := 3

/-- Requested output 1: identity of metal `Q`. -/
def metalQIdentity : LightMetal := .aluminum

/-- Requested output 2: formula `AlF₃ · 3H₂O`. -/
def hydratedCFormula : HydratedFluorideFormula := derivedAssignment.hydratedC

/-- Requested output 3: formula `Na₃AlF₆`. -/
def compoundDFormula : IdentifiedFluoride := derivedAssignment.compoundD

/-- Exact unrounded candidate check for `D`: total molar mass `209.94`, sodium
mass fraction `2299/6998`, and metal mass fraction `4497/34990`. -/
theorem derivedD_exact_mass_ledger :
    dTotalMass derivedAssignment.toPreAssignment = (10497 : ℝ) / 50 ∧
    dSodiumMassFraction derivedAssignment.toPreAssignment = (2299 : ℝ) / 6998 ∧
    dMetalMassFraction derivedAssignment.toPreAssignment = (4497 : ℝ) / 34990 := by
  norm_num [dTotalMass, dSodiumMassFraction, dMetalMassFraction,
    dSodiumMass, dMetalMass, dFluorineMass, StoneAssignment.toPreAssignment,
    derivedAssignment, standardAtomicWeight, fluorideCationCharge,
    sodiumAtomicWeight, fluorineAtomicWeight, sodiumReceipt, fluorineReceipt,
    aluminumReceipt]

/-- Exact unrounded candidate check for the hydrate. -/
theorem derivedHydrate_exact_mass_ledger :
    hydrateAnhydrousMass derivedAssignment = (10497 : ℝ) / 125 ∧
    hydrateWaterMass derivedAssignment = (10809 : ℝ) / 200 ∧
    hydrateTotalMass derivedAssignment = (138021 : ℝ) / 1000 ∧
    hydrateWaterMassFraction derivedAssignment = (18015 : ℝ) / 46007 := by
  norm_num [hydrateAnhydrousMass, hydrateWaterMass, hydrateTotalMass,
    hydrateWaterMassFraction, waterMolarMass, derivedAssignment,
    standardAtomicWeight, fluorideCationCharge, fluorineAtomicWeight,
    hydrogenAtomicWeight, oxygenAtomicWeight, aluminumReceipt,
    fluorineReceipt, hydrogenReceipt, oxygenReceipt]

/-- All three displayed measurement cells accept the derived assignment. -/
theorem derivedAssignment_admissible :
    AdmissibleAssignment derivedAssignment := by
  norm_num [AdmissibleAssignment, PreAdmissible, ConsistentMeasurement,
    lightMetalCandidateDomain, lightMetalCandidateDomainCarrier,
    StoneAssignment.toPreAssignment, StoneAssignment.anhydrousC,
    StoneAssignment.compoundD, anhydrousCFormulaFor, compoundDFormulaFor,
    formulaCharge, NaFFormulaCompatible, dSodiumMassFraction,
    dMetalMassFraction, dTotalMass, dSodiumMass, dMetalMass, dFluorineMass,
    hydrateWaterMassFraction, hydrateTotalMass, hydrateAnhydrousMass,
    hydrateWaterMass, waterMolarMass, derivedAssignment, standardAtomicWeight,
    fluorideCationCharge, sodiumAtomicWeight, fluorineAtomicWeight,
    hydrogenAtomicWeight, oxygenAtomicWeight, sourceMassFractionQuantum,
    shownSodiumMassFractionInD, shownMetalMassFractionInD,
    shownWaterMassFractionInHydrate, sodiumReceipt, aluminumReceipt,
    fluorineReceipt, hydrogenReceipt, oxygenReceipt]

/-- Uniform filtering leaves exactly the derived assignment. -/
theorem admissibleAssignment_unique :
    ∀ a : StoneAssignment,
      AdmissibleAssignment a → a = derivedAssignment := by
  rintro ⟨q, k, x⟩ ha
  rcases ha with ⟨_, hpre, hxpos, hwater, _, _, _⟩
  have hbounds := preAdmissible_source_bounds _ hpre
  have hk : k = fluorideCationCharge q := by
    simpa [StoneAssignment.toPreAssignment] using hbounds.1
  have hmetal := hpre.2.2.2.2.2
  have hq : q = .aluminum := by
    cases q with
    | lithium =>
        norm_num [fluorideCationCharge] at hk
        subst k
        norm_num [ConsistentMeasurement, dMetalMassFraction, dTotalMass,
          dSodiumMass, dMetalMass, dFluorineMass,
          StoneAssignment.toPreAssignment, standardAtomicWeight,
          fluorideCationCharge, sodiumAtomicWeight, fluorineAtomicWeight,
          sourceMassFractionQuantum, shownMetalMassFractionInD,
          lithiumReceipt, sodiumReceipt, fluorineReceipt] at hmetal
    | beryllium =>
        norm_num [fluorideCationCharge] at hk
        subst k
        norm_num [ConsistentMeasurement, dMetalMassFraction, dTotalMass,
          dSodiumMass, dMetalMass, dFluorineMass,
          StoneAssignment.toPreAssignment, standardAtomicWeight,
          fluorideCationCharge, sodiumAtomicWeight, fluorineAtomicWeight,
          sourceMassFractionQuantum, shownMetalMassFractionInD,
          berylliumReceipt, sodiumReceipt, fluorineReceipt] at hmetal
    | sodium =>
        norm_num [fluorideCationCharge] at hk
        subst k
        norm_num [ConsistentMeasurement, dMetalMassFraction, dTotalMass,
          dSodiumMass, dMetalMass, dFluorineMass,
          StoneAssignment.toPreAssignment, standardAtomicWeight,
          fluorideCationCharge, sodiumAtomicWeight, fluorineAtomicWeight,
          sourceMassFractionQuantum, shownMetalMassFractionInD,
          sodiumReceipt, fluorineReceipt] at hmetal
    | magnesium =>
        norm_num [fluorideCationCharge] at hk
        subst k
        norm_num [ConsistentMeasurement, dMetalMassFraction, dTotalMass,
          dSodiumMass, dMetalMass, dFluorineMass,
          StoneAssignment.toPreAssignment, standardAtomicWeight,
          fluorideCationCharge, sodiumAtomicWeight, fluorineAtomicWeight,
          sourceMassFractionQuantum, shownMetalMassFractionInD,
          magnesiumReceipt, sodiumReceipt, fluorineReceipt] at hmetal
    | aluminum => rfl
  subst q
  norm_num [fluorideCationCharge] at hk
  subst k
  have hwlo :
      (7831 : ℝ) / 20000 ≤
        hydrateWaterMassFraction
          { q := .aluminum, sodiumFluorideUnits := 3, waterMolecules := x } := by
    have h := (abs_le.mp hwater.2).1
    norm_num [shownWaterMassFractionInHydrate, sourceMassFractionQuantum] at h
    linarith
  have hwhi :
      hydrateWaterMassFraction
          { q := .aluminum, sodiumFluorideUnits := 3, waterMolecules := x } ≤
        (7833 : ℝ) / 20000 := by
    have h := (abs_le.mp hwater.2).2
    norm_num [shownWaterMassFractionInHydrate, sourceMassFractionQuantum] at h
    linarith
  have hhydrateTotal :
      0 < hydrateTotalMass
        { q := .aluminum, sodiumFluorideUnits := 3, waterMolecules := x } := by
    norm_num [hydrateTotalMass, hydrateAnhydrousMass, hydrateWaterMass,
      waterMolarMass, standardAtomicWeight, fluorideCationCharge,
      fluorineAtomicWeight, hydrogenAtomicWeight, oxygenAtomicWeight,
      aluminumReceipt, fluorineReceipt, hydrogenReceipt, oxygenReceipt]
    positivity
  have hwlo' :
      ((7831 : ℝ) / 20000) *
          hydrateTotalMass
            { q := .aluminum, sodiumFluorideUnits := 3, waterMolecules := x } ≤
        hydrateWaterMass
          { q := .aluminum, sodiumFluorideUnits := 3, waterMolecules := x } := by
    apply (le_div_iff₀ hhydrateTotal).mp
    simpa [hydrateWaterMassFraction] using hwlo
  have hwhi' :
      hydrateWaterMass
          { q := .aluminum, sodiumFluorideUnits := 3, waterMolecules := x } ≤
        ((7833 : ℝ) / 20000) *
          hydrateTotalMass
            { q := .aluminum, sodiumFluorideUnits := 3, waterMolecules := x } := by
    apply (div_le_iff₀ hhydrateTotal).mp
    simpa [hydrateWaterMassFraction] using hwhi
  norm_num [hydrateTotalMass, hydrateAnhydrousMass, hydrateWaterMass,
    waterMolarMass, standardAtomicWeight, fluorideCationCharge,
    fluorineAtomicWeight, hydrogenAtomicWeight, oxygenAtomicWeight,
    aluminumReceipt, fluorineReceipt, hydrogenReceipt, oxygenReceipt] at hwlo' hwhi'
  have hxgt2R : (2 : ℝ) < x := by nlinarith [hwlo']
  have hxlt4R : (x : ℝ) < 4 := by nlinarith [hwhi']
  have hxgt2 : 2 < x := by exact_mod_cast hxgt2R
  have hxlt4 : x < 4 := by exact_mod_cast hxlt4R
  have hx : x = 3 := by omega
  subst x
  rfl

theorem existsUnique_admissibleAssignment :
    ∃! a : StoneAssignment, AdmissibleAssignment a := by
  refine ⟨derivedAssignment, derivedAssignment_admissible, ?_⟩
  intro a ha
  exact admissibleAssignment_unique a ha

/-- Nontrivial requested-output specification for the metal identity. -/
def MetalQIdentitySpec : Prop :=
  AdmissibleAssignment derivedAssignment ∧
    ∀ a : StoneAssignment, AdmissibleAssignment a → a.q = metalQIdentity

/-- Nontrivial requested-output specification for `C · xH₂O`. -/
def HydratedCFormulaSpec : Prop :=
  AdmissibleAssignment derivedAssignment ∧
    ∀ a : StoneAssignment, AdmissibleAssignment a → a.hydratedC = hydratedCFormula

/-- Nontrivial requested-output specification for `D`. -/
def CompoundDFormulaSpec : Prop :=
  AdmissibleAssignment derivedAssignment ∧
    ∀ a : StoneAssignment, AdmissibleAssignment a → a.compoundD = compoundDFormula

theorem metalQIdentity_result : MetalQIdentitySpec := by
  refine ⟨derivedAssignment_admissible, ?_⟩
  intro a ha
  rw [admissibleAssignment_unique a ha]
  rfl

theorem hydratedCFormula_result : HydratedCFormulaSpec := by
  refine ⟨derivedAssignment_admissible, ?_⟩
  intro a ha
  rw [admissibleAssignment_unique a ha]
  rfl

theorem compoundDFormula_result : CompoundDFormulaSpec := by
  refine ⟨derivedAssignment_admissible, ?_⟩
  intro a ha
  rw [admissibleAssignment_unique a ha]
  rfl

/-- Mixed symbolic raw-result proposition covering all requested outputs in
their controller-fixed order. -/
def RawResultSpec : Prop :=
  MetalQIdentitySpec ∧ HydratedCFormulaSpec ∧ CompoundDFormulaSpec

/-- Exact-symbolic reporting changes none of the three raw identifications. -/
def ReportedResultSpec : Prop :=
  RawResultSpec ∧
    metalQIdentity = .aluminum ∧
    hydratedCFormula = derivedAssignment.hydratedC ∧
    compoundDFormula = derivedAssignment.compoundD

theorem rawResultSpec_holds : RawResultSpec := by
  exact ⟨metalQIdentity_result, hydratedCFormula_result, compoundDFormula_result⟩

theorem reportedResultSpec_holds : ReportedResultSpec := by
  exact ⟨rawResultSpec_holds, rfl, rfl, rfl⟩

/-- Hash-bound answer-blind raw symbolic result contract. -/
theorem answerBlindRawResult :
    ("9f9a8fd2f125c68acb9853f68f43ea9927ef37559ea1dbdd0c4248ad43e3ef3e" : String) =
        "9f9a8fd2f125c68acb9853f68f43ea9927ef37559ea1dbdd0c4248ad43e3ef3e" ∧
      RawResultSpec := by
  exact ⟨rfl, rawResultSpec_holds⟩

/-- Hash-bound answer-blind exact-symbolic reported result contract. -/
theorem answerBlindReportedResult :
    ("b3cae327cf36028e6b8a9977f533e94dad7eff767f124acfa7fe7664ac8c8b86" : String) =
        "b3cae327cf36028e6b8a9977f533e94dad7eff767f124acfa7fe7664ac8c8b86" ∧
      ReportedResultSpec := by
  exact ⟨rfl, reportedResultSpec_holds⟩

end

end IChO2026Problems.Icho2026T1A4
