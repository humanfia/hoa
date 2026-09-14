import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 7.7

This file formalizes the compositional calculation in the problem.  Atomic
masses are the values printed on page G1-5 of the supplied problem paper.
The percentages and mass ratios on Q7-4 are treated as displayed
measurements, so matching means lying in the closed half-last-place interval
defined in `IChO2026Chem.Reporting`.

The chemical input used in the formal charge calculation is exactly the one
stated in the question: nitride is N(−III), while La, Ca, and Si are in their
highest ordinary oxidation states, +III, +II, and +IV respectively.
-/

namespace IChO2026Problems.T7A7

open IChO2026Chem.Reporting

noncomputable section

/-- Atom counts for the five elements which occur in the reaction. -/
structure Composition where
  la : ℕ
  ca : ℕ
  si : ℕ
  n : ℕ
  o : ℕ
  deriving DecidableEq, Repr

namespace Composition

/-- Extensionality specialized to the five atom-count fields. -/
theorem extensionality {x y : Composition}
    (hla : x.la = y.la) (hca : x.ca = y.ca) (hsi : x.si = y.si)
    (hn : x.n = y.n) (ho : x.o = y.o) : x = y := by
  cases x
  cases y
  simp_all

/-- Componentwise addition of atom counts. -/
def add (x y : Composition) : Composition :=
  ⟨x.la + y.la, x.ca + y.ca, x.si + y.si, x.n + y.n, x.o + y.o⟩

/-- Multiplication of every atom count by a stoichiometric coefficient. -/
def scale (k : ℕ) (x : Composition) : Composition :=
  ⟨k * x.la, k * x.ca, k * x.si, k * x.n, k * x.o⟩

instance : Add Composition := ⟨add⟩
instance : SMul ℕ Composition := ⟨scale⟩

/-- Total number of atoms in one formula unit. -/
def atomCount (x : Composition) : ℕ := x.la + x.ca + x.si + x.n + x.o

@[simp] theorem add_la (x y : Composition) : (x + y).la = x.la + y.la := rfl
@[simp] theorem add_ca (x y : Composition) : (x + y).ca = x.ca + y.ca := rfl
@[simp] theorem add_si (x y : Composition) : (x + y).si = x.si + y.si := rfl
@[simp] theorem add_n (x y : Composition) : (x + y).n = x.n + y.n := rfl
@[simp] theorem add_o (x y : Composition) : (x + y).o = x.o + y.o := rfl

@[simp] theorem scale_la (k : ℕ) (x : Composition) : (k • x).la = k * x.la := rfl
@[simp] theorem scale_ca (k : ℕ) (x : Composition) : (k • x).ca = k * x.ca := rfl
@[simp] theorem scale_si (k : ℕ) (x : Composition) : (k • x).si = k * x.si := rfl
@[simp] theorem scale_n (k : ℕ) (x : Composition) : (k • x).n = k * x.n := rfl
@[simp] theorem scale_o (k : ℕ) (x : Composition) : (k • x).o = k * x.o := rfl

end Composition

/-! ## Candidate formulae recovered from the three nitrogen percentages -/

/-- Compound 7: LaN. -/
def formula7 : Composition := ⟨1, 0, 0, 1, 0⟩

/-- Compound 8: Ca₃N₂. -/
def formula8 : Composition := ⟨0, 3, 0, 2, 0⟩

/-- Compound 9: Si₃N₄. -/
def formula9 : Composition := ⟨0, 0, 3, 4, 0⟩

/-- Silicon dioxide, the fourth reactant. -/
def silica : Composition := ⟨0, 0, 1, 0, 2⟩

/- Atomic masses printed in the supplied periodic table (G1-5). -/
def atomicMassLa : ℝ := 1389 / 10
def atomicMassCa : ℝ := 4008 / 100
def atomicMassSi : ℝ := 2809 / 100
def atomicMassN : ℝ := 1401 / 100
def atomicMassO : ℝ := 1600 / 100

/-- Formula mass calculated without intermediate rounding. -/
def molarMass (x : Composition) : ℝ :=
  x.la * atomicMassLa + x.ca * atomicMassCa +
  x.si * atomicMassSi + x.n * atomicMassN + x.o * atomicMassO

/-- Nitrogen mass percentage (rather than a unit fraction). -/
def nitrogenMassPercent (x : Composition) : ℝ :=
  100 * (x.n * atomicMassN) / molarMass x

/-- Mass of `k` moles of formula units, up to the common molar unit. -/
def batchMass (k : ℕ) (x : Composition) : ℝ := k * molarMass x

theorem candidate_molar_masses :
    molarMass formula7 = 15291 / 100 ∧
    molarMass formula8 = 14826 / 100 ∧
    molarMass formula9 = 14031 / 100 ∧
    molarMass silica = 6009 / 100 := by
  norm_num [molarMass, formula7, formula8, formula9, silica,
    atomicMassLa, atomicMassCa, atomicMassSi, atomicMassN, atomicMassO]

/-- The exact raw nitrogen percentages of LaN, Ca₃N₂, and Si₃N₄ agree with
the three values printed to 0.01 percentage point on Q7-4. -/
theorem nitride_percentages_match_source :
    ConsistentMeasurement (nitrogenMassPercent formula7) (916 / 100) (1 / 100) ∧
    ConsistentMeasurement (nitrogenMassPercent formula8) (1890 / 100) (1 / 100) ∧
    ConsistentMeasurement (nitrogenMassPercent formula9) (3994 / 100) (1 / 100) := by
  norm_num [ConsistentMeasurement, nitrogenMassPercent, molarMass,
    formula7, formula8, formula9, atomicMassLa, atomicMassCa, atomicMassSi,
    atomicMassN, atomicMassO, abs_of_nonneg, abs_of_nonpos]

/-! ## Stoichiometric reconstruction of compound 10 -/

/-- The atom counts obtained after reducing the conserved product counts by
the common factor two: La₅Ca₉Si₁₃N₂₅O₅. -/
def formula10 : Composition := ⟨5, 9, 13, 25, 5⟩

/-- The small whole-number batch behind the printed mass ratio is
10 LaN : 6 Ca₃N₂ : 7 Si₃N₄ : 5 SiO₂. -/
theorem stoichiometric_mass_ratios_match_source :
    ConsistentMeasurement
        (batchMass 10 formula7 / batchMass 5 silica) (509 / 100) (1 / 100) ∧
    ConsistentMeasurement
        (batchMass 6 formula8 / batchMass 5 silica) (296 / 100) (1 / 100) ∧
    ConsistentMeasurement
        (batchMass 7 formula9 / batchMass 5 silica) (327 / 100) (1 / 100) := by
  norm_num [ConsistentMeasurement, batchMass, molarMass, formula7, formula8,
    formula9, silica, atomicMassLa, atomicMassCa, atomicMassSi, atomicMassN,
    atomicMassO, abs_of_nonneg, abs_of_nonpos]

/-- Conservation of every atom in the quantitative synthesis. -/
theorem synthesis_atom_balance :
    10 • formula7 + 6 • formula8 + 7 • formula9 + 5 • silica =
      2 • formula10 := by
  decide

/-- `formula10` is empirical: it cannot be a positive integral multiple of a
smaller composition.  The proof uses the coprime La and Ca counts 5 and 9. -/
theorem formula10_is_primitive
    (k : ℕ) (smaller : Composition) (_hk : 0 < k)
    (h : formula10 = k • smaller) : k = 1 := by
  have hla : k ∣ 5 := by
    refine ⟨smaller.la, ?_⟩
    simpa [formula10] using congrArg Composition.la h
  have hca : k ∣ 9 := by
    refine ⟨smaller.ca, ?_⟩
    simpa [formula10] using congrArg Composition.ca h
  have hgcd : k ∣ Nat.gcd 5 9 := Nat.dvd_gcd hla hca
  have hk_one : k ∣ 1 := by simpa using hgcd
  exact Nat.eq_one_of_dvd_one hk_one

/-! ## Ionic decomposition in the notation of the question -/

/-- Q₅ when Q = La³⁺. -/
def qCations : Composition := ⟨5, 0, 0, 0, 0⟩

/-- R₉ when R = Ca²⁺. -/
def rCations : Composition := ⟨0, 9, 0, 0, 0⟩

/-- S is the monoatomic oxide ion O²⁻. -/
def anionS : Composition := ⟨0, 0, 0, 0, 1⟩

/-- T is the tetrahedral mixed-anion silicate unit [SiO₃N]⁵⁻. -/
def anionT : Composition := ⟨0, 0, 1, 1, 3⟩

/-- The bracketed nitridosilicate framework written explicitly in Q7-4. -/
def framework : Composition := ⟨0, 0, 12, 24, 0⟩

/-- Formal charge from La(III), Ca(II), Si(IV), N(−III), and O(−II). -/
def formalCharge (x : Composition) : ℤ :=
  3 * x.la + 2 * x.ca + 4 * x.si - 3 * x.n - 2 * x.o

/-- Each recovered binary nitride is neutral with N in oxidation state −III. -/
theorem nitride_charge_neutrality :
    formalCharge formula7 = 0 ∧
    formalCharge formula8 = 0 ∧
    formalCharge formula9 = 0 := by
  norm_num [formalCharge, formula7, formula8, formula9]

theorem formula10_ionic_decomposition :
    qCations + rCations + 2 • anionS + anionT + framework = formula10 := by
  decide

theorem ionic_charge_certificate :
    formalCharge qCations = 15 ∧
    formalCharge rCations = 18 ∧
    formalCharge anionS = -2 ∧
    formalCharge anionT = -5 ∧
    formalCharge framework = -24 ∧
    formalCharge formula10 = 0 := by
  norm_num [formalCharge, qCations, rCations, anionS, anionT, framework,
    formula10]

/-- The compositional content of “monoatomic”. -/
def IsMonoatomic (x : Composition) : Prop := x.atomCount = 1

/-- The atom-count consequence of a Si-centred tetrahedral Si/O/N anion: one
central Si and four O/N ligands.  Geometry itself is chemical input; this
predicate records exactly the compositional consequence used here. -/
def HasSiON_TetrahedralStoichiometry (x : Composition) : Prop :=
  x.si = 1 ∧ x.n + x.o = 4

theorem anionS_is_monoatomic : IsMonoatomic anionS := by
  norm_num [IsMonoatomic, Composition.atomCount, anionS]

theorem anionT_has_tetrahedral_stoichiometry :
    HasSiON_TetrahedralStoichiometry anionT := by
  norm_num [HasSiON_TetrahedralStoichiometry, anionT]

/-- Atom balance plus the stated monoatomic/tetrahedral constraints uniquely
force S = O and T = [SiO₃N]. -/
theorem anion_compositions_forced
    (s t : Composition)
    (hs : IsMonoatomic s)
    (ht : HasSiON_TetrahedralStoichiometry t)
    (hbalance : qCations + rCations + 2 • s + t + framework = formula10) :
    s = anionS ∧ t = anionT := by
  have hla := congrArg Composition.la hbalance
  have hca := congrArg Composition.ca hbalance
  have hsi := congrArg Composition.si hbalance
  have hn := congrArg Composition.n hbalance
  have ho := congrArg Composition.o hbalance
  simp [qCations, rCations, framework, formula10] at hla hca hsi hn ho
  have hs_atoms : s.la + s.ca + s.si + s.n + s.o = 1 := by
    simpa [IsMonoatomic, Composition.atomCount] using hs
  have ht_si : t.si = 1 := ht.1
  have ht_ligands : t.n + t.o = 4 := ht.2
  constructor
  · apply Composition.extensionality <;> simp [anionS]
    all_goals omega
  · apply Composition.extensionality <;> simp [anionT]
    all_goals omega

/-- The complete set of six requested outputs, accompanied by all numerical,
stoichiometric, minimality, structural, and charge certificates used to
identify them. -/
theorem icho_2026_t7_a7 :
    formula7 = ⟨1, 0, 0, 1, 0⟩ ∧
    formula8 = ⟨0, 3, 0, 2, 0⟩ ∧
    formula9 = ⟨0, 0, 3, 4, 0⟩ ∧
    formula10 = ⟨5, 9, 13, 25, 5⟩ ∧
    anionS = ⟨0, 0, 0, 0, 1⟩ ∧
    anionT = ⟨0, 0, 1, 1, 3⟩ ∧
    formalCharge anionS = -2 ∧
    formalCharge anionT = -5 ∧
    ConsistentMeasurement (nitrogenMassPercent formula7) (916 / 100) (1 / 100) ∧
    ConsistentMeasurement (nitrogenMassPercent formula8) (1890 / 100) (1 / 100) ∧
    ConsistentMeasurement (nitrogenMassPercent formula9) (3994 / 100) (1 / 100) ∧
    10 • formula7 + 6 • formula8 + 7 • formula9 + 5 • silica =
      2 • formula10 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [formalCharge, anionS]
  · norm_num [formalCharge, anionT]
  · exact nitride_percentages_match_source.1
  · exact nitride_percentages_match_source.2.1
  · exact nitride_percentages_match_source.2.2
  · exact synthesis_atom_balance

#print axioms nitride_percentages_match_source
#print axioms stoichiometric_mass_ratios_match_source
#print axioms synthesis_atom_balance
#print axioms formula10_is_primitive
#print axioms nitride_charge_neutrality
#print axioms anion_compositions_forced
#print axioms icho_2026_t7_a7

end

end IChO2026Problems.T7A7
