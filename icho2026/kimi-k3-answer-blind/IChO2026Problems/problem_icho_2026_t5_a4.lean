import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T5 (Cardiolipins) — subquestion 5.4, target `icho_2026_t5_a4`

**Problem (T5_page-3.png).** "100 g of RCOOH reacts with 181.0 g of iodine.
RCOOH also reacts in similar way with X and forms an adduct with an iodine
mass fraction of 36.57 %." — **5.4: Determine the molecular formula of X.**

## Answer-blind derivation carried by this file

1. **Inline re-derivation of the T5-A3 prerequisite** (dependency policy
   `derive_in_answer_blind_run_or_use_problem_stated_fallback`; no printed
   fallback for the acid formula exists, so it is derived from problem-only
   material).  From the fragment assembly on T5_page-1.png (a: `n` × –H,
   b: 2 × phosphate –P(=O)(OH)–, c: 3 × glycerol –O–CH₂–CH(O–)–CH₂–O–,
   d: 4 × acyl –C(=O)–R, no peroxide bonds, acyclic non-ionised PL1), the
   molecular formula of PL1 is `C₉₊₄ₘH₁₄₊₈ₘ₋₈ᵤO₁₇P₂` for a fatty acid
   `C_mH_{2m−2u}O₂`.  Since PL1 is connected and acyclic, its σ+π bond count
   is `(atoms − 1) + (4 C=O + 2 P=O + 4u C=C) = 47 + 12m − 4u`; the stated
   255 bonds give `3m − u = 52`.  Reductive ozonolysis of RCOOH gives three
   different products in equimolar amounts (T5_page-3.png), which forces
   `u = 2`; hence `m = 18` and **RCOOH = C₁₈H₃₂O₂** (`M = 280.452 g/mol`,
   pinned CIAAW-2024 weights).
2. **Iodine benchmark** (T5_page-3.png): `n(I₂)/n(RCOOH) =
   (181.0/253.80)/(100/280.452) ≈ 2.000`, integer-forced to **two C=C
   addition sites** per acid molecule (one I₂ per C=C).
3. **Candidate domain for X.**  Contest-semantics policy
   `analogous_halogen_addition` (pinned registry, record sha256
   `15887cce8fd742825ce406fccd5cc7a2daeb54d417361a7d7a7423a4313458c5`).
   Activation cues, each bound to a problem locator on T5_page-3.png: the
   benchmark elemental-halogen addition ("reacts with 181.0 g of iodine"),
   the comparison wording ("reacts in similar way"), the requested molecular
   formula of X, and the quantitative adduct context ("an adduct with an
   iodine mass fraction of 36.57 %").  No contrary problem statement.  The
   policy admits exactly: neutral diatomic halogens/interhalogens over
   {F, Cl, Br, I}, one reagent molecule per unsaturated site (the same two
   C=C sites as the iodine benchmark), both addend atoms retained in the
   product (template `binary_two_fragment_electrophilic_addition`, record
   sha256 `5457da93c91682da2ead97d6600b3de8cca83461005397299519ce11cea80791`).
4. **Uniform filter.**  Adduct `= C₁₈H₃₂O₂ + 2X`; its iodine mass fraction
   must lie in the displayed-measurement interval `[0.36565, 0.36575]`
   (36.57 % with half-quantum 0.005 %).  With pinned weights: IBr gives
   `253.80/694.060 = 0.36568` (inside); ICl `0.41940`, IF `0.44351`,
   I₂ `0.64412`, iodine-free reagents `0` — all outside.  Unique survivor:
   **X = IBr**.

Pinned dataset: `ciaaw-abridged-2024+ame2020-subset+archon-templates-v1`
extended with `+contest-interpretation-v1+trusted-empirical-rules-v1`,
dataset sha256 `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`.
Atomic-weight record sha256 values: C
`0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a`, H
`8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5`, O
`d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588`, F
`96f1d50213dac1410f593d656038a9faa513227e1fd342c16b54096aa2e3b1bb`, Cl
`8f8a36c33295a00c3869eb35edc210319378ef30e7224aa9aea7368d73d287c8`, Br
`dbf8e7117c46a2f42658cb13979799052784f339befe8d9e6e45a8b1da93c568`, I
`8938a0102ab270e66ebacf9c20e8315c50df879a2baffbcc7c8646b6035b025b`, P
`171e07793988f216dc4d307fcbfa9f95c99219f3ffc6e2760a74cf82cfaf6850`.
-/

namespace IChO2026Problems.Icho2026T5A4

/-! ## Elements, formulas, molar masses -/

/-- Elements occurring in problem T5: the halogen candidate domain
{F, Cl, Br, I} plus the fatty-acid/cardiolipin elements C, H, O, P. -/
inductive Elem : Type where
  | C | H | O | F | Cl | Br | I | P
  deriving DecidableEq, Fintype, Repr

/-- Pinned abridged standard atomic weights (CIAAW 2024) from the offline
chemistry registry; the problem prints no atomic weights, so these pinned
values (dataset sha256
`11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`) are the
admissible constants.  The problem-stipulated masses (100 g, 181.0 g,
36.57 %) remain exact measured/displayed values. -/
def atomicWeight : Elem → ℝ
  | .C => 12.011
  | .H => 1.0080
  | .O => 15.999
  | .F => 18.998
  | .Cl => 35.45
  | .Br => 79.904
  | .I => 126.90
  | .P => 30.974

/-- A molecular formula as atom counts per element. -/
def Formula : Type := Elem → ℕ

/-- Build a formula from explicit counts (order C, H, O, F, Cl, Br, I, P). -/
def mkFormula (c h o f cl br i p : ℕ) : Formula := fun
  | .C => c
  | .H => h
  | .O => o
  | .F => f
  | .Cl => cl
  | .Br => br
  | .I => i
  | .P => p

/-- Total atom count of a formula. -/
def atomCount (f : Formula) : ℕ := Finset.univ.sum f

/-- Molar mass in g mol⁻¹ from the pinned atomic weights. -/
noncomputable def molarMass (f : Formula) : ℝ :=
  Finset.univ.sum (fun e => (f e : ℝ) * atomicWeight e)

/-- The full element finset as an explicit insert-chain (computation helper). -/
theorem elem_univ : (Finset.univ : Finset Elem) =
    {.C, .H, .O, .F, .Cl, .Br, .I, .P} := by
  ext e
  cases e <;> simp

/-- Atom count of an explicit formula expands to the plain sum of counts. -/
theorem atomCount_mkFormula (c h o f cl br i p : ℕ) :
    atomCount (mkFormula c h o f cl br i p) = c + h + o + f + cl + br + i + p := by
  unfold atomCount
  rw [elem_univ]
  simp [mkFormula, Finset.sum_insert, Finset.sum_singleton]
  omega

/-- Molar mass of an explicit formula expands to the weighted sum with the
pinned CIAAW-2024 abridged weights. -/
theorem molarMass_mkFormula (c h o f cl br i p : ℕ) :
    molarMass (mkFormula c h o f cl br i p) =
      (c : ℝ) * 12.011 + (h : ℝ) * 1.0080 + (o : ℝ) * 15.999 + (f : ℝ) * 18.998 +
        (cl : ℝ) * 35.45 + (br : ℝ) * 79.904 + (i : ℝ) * 126.90 + (p : ℝ) * 30.974 := by
  unfold molarMass
  rw [elem_univ]
  simp [mkFormula, atomicWeight, Finset.sum_insert, Finset.sum_singleton]
  ring

/-! ## The fatty acid RCOOH and the PL1 assembly (T5-A3 prerequisite, inline) -/

/-- The fatty acid RCOOH of T5, modelled as an acyclic monocarboxylic acid
`C_mH_{2m−2u}O₂` whose hydrocarbon substituent R carries exactly
`doubleBonds` C=C bonds and no rings or further unsaturation.  Provenance:
problem_text — "Cardiolipins are a family of acyclic phospholipids", "R is a
hydrocarbon substituent in the fatty acid structure" (T5_page-1.png), and the
reductive-ozonolysis-to-carbonyls context (T5_page-3.png). -/
structure FattyAcid where
  /-- number of carbon atoms `m` (including the carboxyl carbon) -/
  carbons : ℕ
  /-- number `u` of C=C double bonds -/
  doubleBonds : ℕ
  carbons_pos : 1 ≤ carbons
  doubleBonds_le : doubleBonds ≤ carbons

/-- Molecular formula `C_mH_{2m−2u}O₂` of the fatty acid (trusted general law:
tetravalent carbon, acyclic saturated monocarboxylic acid `C_mH_{2m}O₂`, each
C=C removes two hydrogens). -/
def FattyAcid.formula (a : FattyAcid) : Formula :=
  mkFormula a.carbons (2 * a.carbons - 2 * a.doubleBonds) 2 0 0 0 0 0

/-- Atom inventory of non-ionised PL1 assembled from the fragments of
T5_page-1.png: `n` a-fragments (–H: H₁), 2 b-fragments (phosphate: H O₂ P per
fragment), 3 c-fragments (glycerol: C₃H₅O₃ per fragment) and 4 d-fragments
(acyl –C(=O)–R with R = `C_{m−1}H_{2m−2u−1}`: C_m H_{2m−2u−1} O per
fragment).  Pairing open valences into inter-fragment bonds removes no atoms,
so the PL1 formula is the plain fragment sum. -/
def pl1Formula (n : ℕ) (a : FattyAcid) : Formula :=
  mkFormula
    (9 + 4 * a.carbons)
    (n + 13 + 8 * a.carbons - 8 * a.doubleBonds)
    17 0 0 0 0 2

/-- Source-stated assembly constraints for non-ionised PL1 (T5_page-1.png):
fragment quantities `n, 2, 3, 4`; every open valence is paired into exactly
one inter-fragment bond (`2 * bonds = n + 2*2 + 3*3 + 4*1`, since b, c, d, a
fragments carry 2, 3, 1, 1 open valences); the cardiolipin connectivity —
each acyl (d) and each phosphate (b) valence esterifies a glycerol (c)
oxygen, no peroxide (O–O) bonds, connected acyclic molecule — fixes nine
inter-fragment bonds (4 d–c esters, 4 b–c phosphate esters, 1 a–c cap on the
central glycerol's remaining OH). -/
def ValidPL1Assembly (n : ℕ) (_a : FattyAcid) : Prop :=
  ∃ bonds : ℕ,
    -- valence bookkeeping: each bond consumes two open valences
    2 * bonds = n + 2 * 2 + 3 * 3 + 4 * 1 ∧
    -- the cardiolipin connectivity fixes nine bonds
    bonds = 9

/-- The assembly forces exactly one a-fragment: `n = 1` (in particular odd —
the 5.1 observation) and `2 * bonds = 17 + n`. -/
theorem pl1_a_count_eq_one {n : ℕ} {a : FattyAcid} (h : ValidPL1Assembly n a) :
    n = 1 := by
  obtain ⟨b, hvp, hbc⟩ := h
  omega

/-- Total σ+π bond count of non-ionised PL1: the molecule is connected and
acyclic, so σ bonds = atoms − 1; π bonds = 4 C=O (d fragments) + 2 P=O
(b fragments) + one π bond per C=C of the four fatty-acid residues (4u). -/
def pl1SigmaPiBonds (n : ℕ) (a : FattyAcid) : ℕ :=
  (atomCount (pl1Formula n a) - 1) + (6 + 4 * a.doubleBonds)

/-- Closed form of the PL1 σ+π bond count with `n = 1`:
`47 + 12m − 4u` (atoms `42 + 12m − 8u`, π bonds `6 + 4u`). -/
theorem pl1SigmaPiBonds_closed (a : FattyAcid) :
    (pl1SigmaPiBonds 1 a : ℤ) =
      47 + 12 * (a.carbons : ℤ) - 4 * (a.doubleBonds : ℤ) := by
  have hu := a.doubleBonds_le
  unfold pl1SigmaPiBonds
  rw [show pl1Formula 1 a =
      mkFormula (9 + 4 * a.carbons) (1 + 13 + 8 * a.carbons - 8 * a.doubleBonds)
        17 0 0 0 0 2 from rfl,
    atomCount_mkFormula]
  omega

/-- Reductive-ozonolysis fragment data for an acyclic fatty acid: cleaving
every C=C bond once gives `doubleBonds + 1` carbonyl fragments per molecule
(trusted general law: ozonolysis cleaves each C=C of the acyclic chain). -/
structure OzonolysisData where
  /-- number of C=C bonds cleaved -/
  doubleBonds : ℕ
  /-- fragments formed per acid molecule -/
  fragments : ℕ
  /-- how many of the fragments are pairwise different compounds -/
  distinctProducts : ℕ
  fragments_eq : fragments = doubleBonds + 1
  distinct_le : distinctProducts ≤ fragments

/-- The products are equimolar iff every fragment position gives a different
compound — each product is then formed exactly once per acid molecule, while
coinciding fragments would appear in doubled amount. -/
def OzonolysisData.Equimolar (d : OzonolysisData) : Prop :=
  d.fragments = d.distinctProducts

/-- Problem-stated ozonolysis evidence (T5_page-3.png: "During reductive
ozonolysis, RCOOH forms three different organic products in equimolar
amounts"). -/
def OzonolysisEvidence (a : FattyAcid) : Prop :=
  ∃ d : OzonolysisData,
    d.doubleBonds = a.doubleBonds ∧ d.distinctProducts = 3 ∧ d.Equimolar

/-- Three different equimolar ozonolysis products force exactly two C=C bonds:
`u = 1` gives only two fragments; `u = 2` gives three fragments, all
different, in 1:1:1 ratio; `u ≥ 3` gives at least four fragments, so with
only three different products some product would have to be doubled,
contradicting equimolarity. -/
theorem ozonolysis_two_double_bonds {a : FattyAcid} (h : OzonolysisEvidence a) :
    a.doubleBonds = 2 := by
  obtain ⟨d, hdb, hthree, heq⟩ := h
  have hfr : d.fragments = d.doubleBonds + 1 := d.fragments_eq
  have heq' : d.fragments = d.distinctProducts := heq
  omega

/-- Inline answer-blind re-derivation of the T5-A3 prerequisite: the fatty
acid of PL1 has 18 carbons and two C=C bonds, i.e. RCOOH = C₁₈H₃₂O₂.  From
`n = 1`, the 255-bond condition gives `47 + 12m − 4u = 255`; the ozonolysis
evidence gives `u = 2`; hence `3m = 54` and `m = 18`. -/
theorem fatty_acid_identity {n : ℕ} {a : FattyAcid}
    (assembly : ValidPL1Assembly n a)
    (bonds : pl1SigmaPiBonds n a = 255)
    (ozo : OzonolysisEvidence a) :
    a.carbons = 18 ∧ a.doubleBonds = 2 := by
  have hn : n = 1 := pl1_a_count_eq_one assembly
  have hu : a.doubleBonds = 2 := ozonolysis_two_double_bonds ozo
  subst hn
  have hcl := pl1SigmaPiBonds_closed a
  rw [bonds, hu] at hcl
  have hm : (a.carbons : ℤ) = 18 := by omega
  exact ⟨by exact_mod_cast hm, hu⟩

/-- The derived fatty-acid candidate: `C₁₈H₃₂O₂` (the linoleic-acid
composition). -/
def rcoohDerived : FattyAcid := ⟨18, 2, by decide, by decide⟩

/-- Its molecular formula is `C₁₈H₃₂O₂`. -/
theorem rcoohDerived_formula :
    rcoohDerived.formula = mkFormula 18 32 2 0 0 0 0 0 := by
  funext e
  cases e <;> rfl

/-- The derived candidate realises the PL1 assembly constraints with `n = 1`
(nine inter-fragment bonds; `2 * 9 = 1 + 17`). -/
theorem rcoohDerived_assembly : ValidPL1Assembly 1 rcoohDerived :=
  ⟨9, rfl, rfl⟩

/-- The derived candidate realises the stated 255 σ+π bond count of
non-ionised PL1: atoms `= 81 + 142 + 17 + 2 = 242`, σ bonds `= 241`,
π bonds `= 4 + 2 + 8 = 14`, total `255`. -/
theorem rcoohDerived_bonds : pl1SigmaPiBonds 1 rcoohDerived = 255 := by
  decide

/-- The derived candidate realises the ozonolysis evidence: two C=C bonds
cleave to three pairwise different fragments in 1:1:1 (equimolar) ratio. -/
theorem rcoohDerived_ozonolysis : OzonolysisEvidence rcoohDerived :=
  ⟨⟨2, 3, 3, rfl, le_refl 3⟩, rfl, rfl, rfl⟩

/-- Molar mass of the derived acid from the pinned weights:
`18·12.011 + 32·1.0080 + 2·15.999 = 280.452` g mol⁻¹. -/
theorem molarMass_rcoohDerived :
    molarMass rcoohDerived.formula = 280.452 := by
  rw [rcoohDerived_formula, molarMass_mkFormula]
  norm_num

/-- Iodine benchmark (T5_page-3.png): 100 g of RCOOH reacts with 181.0 g of
iodine.  Both masses are displayed measurements (source measurement policy:
half of the last displayed quantum, i.e. 181.0 ± 0.05 g and 100 ± 0.5 g), so
the I₂-per-acid mole ratio lies strictly between 1.98 and 2.02; being an
integer (one I₂ per C=C site, template `reagent_molecules_per_site = 1`), it
is exactly 2 — two C=C addition sites per acid molecule, consistent with the
ozonolysis count. -/
theorem benchmark_iodine_ratio :
    1.98 < (181.0 / (2 * atomicWeight .I)) / (100 / molarMass rcoohDerived.formula) ∧
      (181.0 / (2 * atomicWeight .I)) / (100 / molarMass rcoohDerived.formula) < 2.02 := by
  rw [molarMass_rcoohDerived]
  refine ⟨?_, ?_⟩ <;> norm_num [atomicWeight]

/-! ## The reagent X: candidate domain and adduct -/

/-- Halogen domain admitted by the contest-policy receipt
`analogous_halogen_addition`
(`ordinary_olympiad_element_domain = ["F", "Cl", "Br", "I"]`). -/
inductive Halogen : Type where
  | F | Cl | Br | I
  deriving DecidableEq, Fintype, Repr

/-- Candidate reagent X: a neutral diatomic halogen or interhalogen
(`unknown_reagent_kind = neutral_diatomic_halogen_or_interhalogen`,
`atoms_per_reagent_molecule = 2`, `charge = 0`, `same_element_allowed`,
`different_elements_allowed`).  The domain has 10 unordered (16 ordered)
members. -/
structure DiatomicHalogenReagent where
  atom1 : Halogen
  atom2 : Halogen
  deriving DecidableEq, Repr

/-- Map a halogen to its element. -/
def Halogen.toElem : Halogen → Elem
  | .F => .F
  | .Cl => .Cl
  | .Br => .Br
  | .I => .I

/-- Molecular formula of a diatomic reagent: one atom of each constituent
(two of the same element when `atom1 = atom2`, e.g. I₂). -/
def reagentFormula (x : DiatomicHalogenReagent) : Formula := fun e =>
  (if x.atom1.toElem = e then 1 else 0) + (if x.atom2.toElem = e then 1 else 0)

/-- The adduct of the fatty acid with reagent X: one reagent molecule per C=C
site (`u = 2` sites, the same sites as the iodine benchmark), both addend
atoms retained in the product — per the contest-policy receipt
`analogous_halogen_addition` (record sha256
`15887cce8fd742825ce406fccd5cc7a2daeb54d417361a7d7a7423a4313458c5`) and the
reaction template `binary_two_fragment_electrophilic_addition` (record sha256
`5457da93c91682da2ead97d6600b3de8cca83461005397299519ce11cea80791`:
`reagent_molecules_per_site = 1`, `addends_delivered_per_site = 2`,
`all_reagent_addends_retained_in_product`).  Staged-transformation class:
`quantitative_material_stage` with the mass/iodine-atom ledger
`adduct = acid + 2·X`; no further streams are claimed or needed. -/
def adductFormula (a : FattyAcid) (x : DiatomicHalogenReagent) : Formula := fun e =>
  a.formula e + a.doubleBonds * reagentFormula x e

/-- Iodine mass fraction of a formula: total iodine mass over molar mass. -/
noncomputable def iodineMassFraction (f : Formula) : ℝ :=
  (f .I : ℝ) * atomicWeight .I / molarMass f

/-- The displayed adduct iodine mass fraction is 36.57 % (T5_page-3.png).
Per the source measurement policy (`measured_display_half_width =
one_half_of_last_displayed_quantum`) the true fraction `w` satisfies
`|w − 0.3657| ≤ 0.00005`. -/
def MeasuredIodineFraction (w : ℝ) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement w 0.3657 0.0001

/-- The derived candidate reagent: iodine monobromide. -/
def ibrReagent : DiatomicHalogenReagent := ⟨.I, .Br⟩

/-- Molecular formula IBr (one iodine, one bromine). -/
def formulaIBr : Formula := mkFormula 0 0 0 0 0 1 1 0

/-- The IBr adduct's iodine mass fraction as an exact pinned-weight
expression: the adduct is `C₁₈H₃₂O₂I₂Br₂`, so the fraction is
`2·126.90 / (280.452 + 2·(126.90 + 79.904)) = 253.80/694.060`. -/
theorem adduct_fraction_ibr_value :
    iodineMassFraction (adductFormula rcoohDerived ibrReagent) =
      (2 * atomicWeight .I) /
        (molarMass rcoohDerived.formula + 2 * (atomicWeight .I + atomicWeight .Br)) := by
  have hadd : adductFormula rcoohDerived ibrReagent = mkFormula 18 32 2 0 0 2 2 0 := by
    funext e
    cases e <;> rfl
  unfold iodineMassFraction
  rw [hadd, molarMass_mkFormula, molarMass_rcoohDerived,
    show (mkFormula 18 32 2 0 0 2 2 0 : Formula) .I = 2 from rfl]
  norm_num [atomicWeight]

/-- The IBr adduct meets the displayed 36.57 % measurement:
`253.80/694.060 = 0.365674 ∈ [0.36565, 0.36575]`. -/
theorem ibr_adduct_fraction_mem :
    MeasuredIodineFraction
      (iodineMassFraction (adductFormula rcoohDerived ibrReagent)) := by
  unfold MeasuredIodineFraction IChO2026Chem.Reporting.ConsistentMeasurement
  rw [adduct_fraction_ibr_value, molarMass_rcoohDerived]
  refine ⟨by norm_num, ?_⟩
  rw [abs_le]
  constructor <;> norm_num [atomicWeight]

/-! ## Result specifications and machine-readable answer-blind contracts -/

/-- Raw derivation spec for the requested output `compound_x_formula`:
every policy-domain reagent whose fatty-acid adduct matches the displayed
36.57 % iodine mass fraction has molecular formula IBr.  (Uniform exclusions
at two addition sites with pinned weights: ICl gives 0.41940, IF gives
0.44351, I₂ gives 0.64412, iodine-free reagents give 0 — all outside
`[0.36565, 0.36575]`.) -/
def RawResultProp : Prop :=
  ∀ x : DiatomicHalogenReagent,
    MeasuredIodineFraction (iodineMassFraction (adductFormula rcoohDerived x)) →
      reagentFormula x = formulaIBr

/-- Reported result for T5-A4 (reporting policy `exact_symbolic`: no
rounding): the molecular formula of X is IBr — the IBr reagent realises the
measurement, and every compatible policy-domain reagent has formula IBr. -/
def ReportedResultProp : Prop :=
  reagentFormula ibrReagent = formulaIBr ∧
    MeasuredIodineFraction (iodineMassFraction (adductFormula rcoohDerived ibrReagent)) ∧
      RawResultProp

/-- Answer-blind raw-result contract: binds the candidate payload digest to
the raw derivation spec. -/
theorem raw_result_contract :
    ("34c856e4f73119422b9ad37da2e8e703e73f3b5cf7cc31ba800e47389b5e3ef8" : String) =
      "34c856e4f73119422b9ad37da2e8e703e73f3b5cf7cc31ba800e47389b5e3ef8" ∧
    IChO2026Problems.Icho2026T5A4.RawResultProp := by
  refine ⟨rfl, ?_⟩
  intro x h
  obtain ⟨a1, a2⟩ := x
  unfold MeasuredIodineFraction IChO2026Chem.Reporting.ConsistentMeasurement at h
  obtain ⟨-, h⟩ := h
  unfold iodineMassFraction at h
  rw [abs_le] at h
  cases a1 <;> cases a2
  -- ⟨F, F⟩
  · have hf : adductFormula rcoohDerived ⟨.F, .F⟩ = mkFormula 18 32 2 4 0 0 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 4 0 0 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨F, Cl⟩
  · have hf : adductFormula rcoohDerived ⟨.F, .Cl⟩ = mkFormula 18 32 2 2 2 0 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 2 2 0 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨F, Br⟩
  · have hf : adductFormula rcoohDerived ⟨.F, .Br⟩ = mkFormula 18 32 2 2 0 2 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 2 0 2 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨F, I⟩
  · have hf : adductFormula rcoohDerived ⟨.F, .I⟩ = mkFormula 18 32 2 2 0 0 2 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 2 0 0 2 0 : Formula) .I = 2 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Cl, F⟩
  · have hf : adductFormula rcoohDerived ⟨.Cl, .F⟩ = mkFormula 18 32 2 2 2 0 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 2 2 0 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Cl, Cl⟩
  · have hf : adductFormula rcoohDerived ⟨.Cl, .Cl⟩ = mkFormula 18 32 2 0 4 0 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 0 4 0 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Cl, Br⟩
  · have hf : adductFormula rcoohDerived ⟨.Cl, .Br⟩ = mkFormula 18 32 2 0 2 2 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 0 2 2 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Cl, I⟩
  · have hf : adductFormula rcoohDerived ⟨.Cl, .I⟩ = mkFormula 18 32 2 0 2 0 2 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 0 2 0 2 0 : Formula) .I = 2 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Br, F⟩
  · have hf : adductFormula rcoohDerived ⟨.Br, .F⟩ = mkFormula 18 32 2 2 0 2 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 2 0 2 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Br, Cl⟩
  · have hf : adductFormula rcoohDerived ⟨.Br, .Cl⟩ = mkFormula 18 32 2 0 2 2 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 0 2 2 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Br, Br⟩
  · have hf : adductFormula rcoohDerived ⟨.Br, .Br⟩ = mkFormula 18 32 2 0 0 4 0 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 0 0 4 0 0 : Formula) .I = 0 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨Br, I⟩ — survivor: adduct C₁₈H₃₂O₂I₂Br₂, fraction 253.80/694.060
  · funext e; cases e <;> rfl
  -- ⟨I, F⟩
  · have hf : adductFormula rcoohDerived ⟨.I, .F⟩ = mkFormula 18 32 2 2 0 0 2 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 2 0 0 2 0 : Formula) .I = 2 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨I, Cl⟩
  · have hf : adductFormula rcoohDerived ⟨.I, .Cl⟩ = mkFormula 18 32 2 0 2 0 2 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 0 2 0 2 0 : Formula) .I = 2 from rfl] at h
    norm_num [atomicWeight] at h
  -- ⟨I, Br⟩ — survivor
  · funext e; cases e <;> rfl
  -- ⟨I, I⟩
  · have hf : adductFormula rcoohDerived ⟨.I, .I⟩ = mkFormula 18 32 2 0 0 0 4 0 := by
      funext e; cases e <;> rfl
    rw [hf, molarMass_mkFormula,
      show (mkFormula 18 32 2 0 0 0 4 0 : Formula) .I = 4 from rfl] at h
    norm_num [atomicWeight] at h

/-- Answer-blind reported-result contract: binds the candidate payload digest
to the reported answer spec (molecular formula of X is IBr). -/
theorem reported_result_contract :
    ("a5cf78f69180e2224459b6d1ea97f2722b2b71f59aa3cbcf272fbcb4578c97bd" : String) =
      "a5cf78f69180e2224459b6d1ea97f2722b2b71f59aa3cbcf272fbcb4578c97bd" ∧
    IChO2026Problems.Icho2026T5A4.ReportedResultProp := by
  refine ⟨rfl, ?_, ibr_adduct_fraction_mem, raw_result_contract.2⟩
  funext e
  cases e <;> rfl

end IChO2026Problems.Icho2026T5A4
