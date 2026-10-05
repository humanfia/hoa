import IChO2026Chem.Reporting

/-!
# IChO 2026, problem 3.7

This file formalizes both requested numerical outputs.  `Source` contains only
transcriptions of printed numerical data and direct atom/topology observations
from the problem figures.  Everything outside that namespace is derived.

The molar-mass calculation uses the atomic masses printed in the problem's
periodic table.  All computations are exact over `ℚ`; coercion to `ℝ` happens
only at the final reporting boundary.
-/

namespace IChO2026Problems.T3A7

open IChO2026Chem.Reporting

/-- Element counts needed for this subproblem. -/
structure AtomCounts where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace AtomCounts

def add (a b : AtomCounts) : AtomCounts :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen }

def scale (n : ℕ) (a : AtomCounts) : AtomCounts :=
  { carbon := n * a.carbon
    hydrogen := n * a.hydrogen
    nitrogen := n * a.nitrogen
    oxygen := n * a.oxygen }

/-- Remove `n` water molecules from a balanced precursor formula. -/
def removeWater (n : ℕ) (a : AtomCounts) : AtomCounts :=
  { carbon := a.carbon
    hydrogen := a.hydrogen - 2 * n
    nitrogen := a.nitrogen
    oxygen := a.oxygen - n }

end AtomCounts

namespace Source

/-! ## Printed experimental data on Q3-7 -/

def initialConcentrationMgPerDm3 : ℚ := 1990 / 100
def equilibriumConcentrationMgPerDm3 : ℚ := 9225 / 1000
def solutionVolumeMl : ℚ := 2000 / 10
def cof9MassMg : ℚ := 5000 / 1000

def mlPerDm3 : ℚ := 1000
def mgPerG : ℚ := 1000

/-! ## Atomic masses printed on general-data page G1-5 -/

def hydrogenMolarMass : ℚ := 1008 / 1000
def carbonMolarMass : ℚ := 1201 / 100
def nitrogenMolarMass : ℚ := 1401 / 100
def oxygenMolarMass : ℚ := 1600 / 100
def uraniumMolarMass : ℚ := 23803 / 100

/-!
## Direct transcription of the pictured structures

Atom counting gives D2 = C24H15N3O3 and E1 = C12H9N3.  The honeycomb pictured
around a pore has three vertices of each kind, while each tritopic vertex is
shared by three pores.  Thus there is one D2 and one E1 equivalent per pore.
The six pore edges are shared by two pores, giving three condensations per
pore.  The one E1 equivalent carries three nitrile groups.
-/

def d2 : AtomCounts := ⟨24, 15, 3, 3⟩
def e1 : AtomCounts := ⟨12, 9, 3, 0⟩
def hydroxylamine : AtomCounts := ⟨0, 3, 1, 1⟩

def d2VertexAppearances : ℚ := 3
def e1VertexAppearances : ℚ := 3
def poresSharingTritopicVertex : ℚ := 3
def edgesAroundPore : ℚ := 6
def poresSharingEdge : ℚ := 2

end Source

/-! ## Topological and formula derivation -/

def d2EquivalentsPerPore : ℚ :=
  Source.d2VertexAppearances / Source.poresSharingTritopicVertex

def e1EquivalentsPerPore : ℚ :=
  Source.e1VertexAppearances / Source.poresSharingTritopicVertex

def condensationsPerPore : ℚ :=
  Source.edgesAroundPore / Source.poresSharingEdge

theorem pore_stoichiometry :
    d2EquivalentsPerPore = 1 ∧
    e1EquivalentsPerPore = 1 ∧
    condensationsPerPore = 3 := by
  norm_num [d2EquivalentsPerPore, e1EquivalentsPerPore,
    condensationsPerPore, Source.d2VertexAppearances,
    Source.e1VertexAppearances, Source.poresSharingTritopicVertex,
    Source.edgesAroundPore, Source.poresSharingEdge]

/-- Formula per pore after the three water-eliminating condensations that form
COF-8 from one D2 and one E1 equivalent. -/
def cof8PerPore : AtomCounts :=
  AtomCounts.removeWater 3 (AtomCounts.add Source.d2 Source.e1)

/-- Each of the three nitrile groups adds one NH2OH to become an amidoxime. -/
def cof9PerPore : AtomCounts :=
  AtomCounts.add cof8PerPore (AtomCounts.scale 3 Source.hydroxylamine)

theorem cof8_formula_per_pore : cof8PerPore = ⟨36, 18, 6, 0⟩ := by
  rfl

theorem cof9_formula_per_pore : cof9PerPore = ⟨36, 27, 9, 3⟩ := by
  rfl

def molarMass (a : AtomCounts) : ℚ :=
  a.carbon * Source.carbonMolarMass +
  a.hydrogen * Source.hydrogenMolarMass +
  a.nitrogen * Source.nitrogenMolarMass +
  a.oxygen * Source.oxygenMolarMass

def cof9MolarMass : ℚ := molarMass cof9PerPore

/-- Chemical-convention molar mass of UO2^2+: U + 2 O. -/
def uranylMolarMass : ℚ :=
  Source.uraniumMolarMass + 2 * Source.oxygenMolarMass

theorem cof9_molar_mass : cof9MolarMass = 316833 / 500 := by
  norm_num [cof9MolarMass, molarMass, cof9PerPore, cof8PerPore,
    AtomCounts.add, AtomCounts.scale, AtomCounts.removeWater,
    Source.d2, Source.e1, Source.hydroxylamine,
    Source.carbonMolarMass, Source.hydrogenMolarMass,
    Source.nitrogenMolarMass, Source.oxygenMolarMass]

theorem uranyl_molar_mass : uranylMolarMass = 27003 / 100 := by
  norm_num [uranylMolarMass, Source.uraniumMolarMass,
    Source.oxygenMolarMass]

/-! ## Experimental mass balance and equilibrium capacity -/

def solutionVolumeDm3 : ℚ :=
  Source.solutionVolumeMl / Source.mlPerDm3

def cof9MassG : ℚ := Source.cof9MassMg / Source.mgPerG

def absorbedUranylMassMg : ℚ :=
  (Source.initialConcentrationMgPerDm3 -
    Source.equilibriumConcentrationMgPerDm3) * solutionVolumeDm3

/-- `q_e = (c_0 - c_e) V / m`, in mg of uranyl per g of COF-9. -/
def equilibriumCapacityMgPerG : ℚ := absorbedUranylMassMg / cof9MassG

theorem source_unit_conversions :
    solutionVolumeDm3 = 1 / 5 ∧ cof9MassG = 1 / 200 := by
  norm_num [solutionVolumeDm3, cof9MassG, Source.solutionVolumeMl,
    Source.mlPerDm3, Source.cof9MassMg, Source.mgPerG]

theorem absorbed_uranyl_mass : absorbedUranylMassMg = 427 / 200 := by
  norm_num [absorbedUranylMassMg, solutionVolumeDm3,
    Source.initialConcentrationMgPerDm3,
    Source.equilibriumConcentrationMgPerDm3,
    Source.solutionVolumeMl, Source.mlPerDm3]

theorem equilibrium_capacity_raw : equilibriumCapacityMgPerG = 427 := by
  norm_num [equilibriumCapacityMgPerG, absorbedUranylMassMg,
    solutionVolumeDm3, cof9MassG,
    Source.initialConcentrationMgPerDm3,
    Source.equilibriumConcentrationMgPerDm3,
    Source.solutionVolumeMl, Source.mlPerDm3,
    Source.cof9MassMg, Source.mgPerG]

/-! ## Uranyl entities per pore -/

/-- The mole ratio of uranyl to pore formula units.  Dividing `q_e` by 1000
converts mg/g to g/g before applying the two molar masses.  Entity ratios equal
mole ratios because the same Avogadro factor multiplies numerator and
denominator. -/
def uranylIonsPerPore : ℚ :=
  (equilibriumCapacityMgPerG / Source.mgPerG) *
    cof9MolarMass / uranylMolarMass

theorem uranyl_ions_per_pore_raw :
    uranylIonsPerPore = 45095897 / 45005000 := by
  norm_num [uranylIonsPerPore, equilibriumCapacityMgPerG,
    absorbedUranylMassMg, solutionVolumeDm3, cof9MassG,
    cof9MolarMass, molarMass, cof9PerPore, cof8PerPore,
    AtomCounts.add, AtomCounts.scale, AtomCounts.removeWater,
    uranylMolarMass, Source.initialConcentrationMgPerDm3,
    Source.equilibriumConcentrationMgPerDm3,
    Source.solutionVolumeMl, Source.cof9MassMg, Source.mlPerDm3,
    Source.mgPerG, Source.d2, Source.e1, Source.hydroxylamine,
    Source.carbonMolarMass, Source.hydrogenMolarMass,
    Source.nitrogenMolarMass, Source.oxygenMolarMass,
    Source.uraniumMolarMass]

/-! ## Three-significant-figure reporting -/

noncomputable def capacitySubmission : NumericSubmission where
  rawValue := equilibriumCapacityMgPerG
  reportedValue := 427
  reportingQuantum := 1

noncomputable def ionsPerPoreSubmission : NumericSubmission where
  rawValue := uranylIonsPerPore
  reportedValue := 1
  reportingQuantum := 1 / 100

theorem equilibrium_capacity_three_significant_figures :
    ValidNumericSubmission (equilibriumCapacityMgPerG : ℝ)
      capacitySubmission := by
  constructor
  · rfl
  · change ReportsAtQuantum (equilibriumCapacityMgPerG : ℝ) 427 1
    rw [equilibrium_capacity_raw]
    refine ⟨by norm_num, ⟨427, by norm_num⟩, ?_⟩
    norm_num

theorem uranyl_ions_per_pore_three_significant_figures :
    ValidNumericSubmission (uranylIonsPerPore : ℝ)
      ionsPerPoreSubmission := by
  constructor
  · rfl
  · change ReportsAtQuantum (uranylIonsPerPore : ℝ) 1 (1 / 100)
    rw [uranyl_ions_per_pore_raw]
    refine ⟨by norm_num, ⟨100, by norm_num⟩, ?_⟩
    norm_num

/-- A single theorem collecting both requested raw and reported outputs. -/
theorem t3_a7_requested_outputs :
    equilibriumCapacityMgPerG = 427 ∧
    ValidNumericSubmission (equilibriumCapacityMgPerG : ℝ)
      capacitySubmission ∧
    uranylIonsPerPore = 45095897 / 45005000 ∧
    ValidNumericSubmission (uranylIonsPerPore : ℝ)
      ionsPerPoreSubmission := by
  exact ⟨equilibrium_capacity_raw,
    equilibrium_capacity_three_significant_figures,
    uranyl_ions_per_pore_raw,
    uranyl_ions_per_pore_three_significant_figures⟩

#print axioms pore_stoichiometry
#print axioms cof9_formula_per_pore
#print axioms equilibrium_capacity_raw
#print axioms uranyl_ions_per_pore_raw
#print axioms equilibrium_capacity_three_significant_figures
#print axioms uranyl_ions_per_pore_three_significant_figures
#print axioms t3_a7_requested_outputs

end IChO2026Problems.T3A7
