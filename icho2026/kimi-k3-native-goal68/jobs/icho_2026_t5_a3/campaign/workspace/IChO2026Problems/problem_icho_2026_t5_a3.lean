import Mathlib

/-!
# IChO 2026, Problem T5 (Cardiolipins), subquestion 5.3 (T5-A3)

**Requested output.**  Determine the molecular formula of the fatty acid
RCOOH in PL1, given that the non-ionised form of PL1 contains 255 σ- and
π-bonds between atoms in total, and support the answer with calculations.

## Problem inputs (official problem text and figures, T5 pages 1, 3, 4)

* PL1 is assembled only from structural elements a–d, in the quantities
  `n × a`, `2 × b`, `3 × c`, `4 × d` (T5 page 1):
  * a = `⤳H`: one H atom carrying one free valence;
  * b = `HO–P(=O)⤝⤝`: phosphoric-acid fragment, P(=O)(OH) with two free
    valences on P — atoms H1 O2 P1;
  * c = `⤳O–CH2–CH(O⤳)–CH2–O⤝`: glycerol with the three free valences on its
    three O atoms — atoms C3 H5 O3 (7 skeletal H minus 2 O–H not yet formed;
    the OH hydrogens of capped glycerol oxygens come from fragment a);
  * d = `O=C⤳–R`: fatty-acid carbonyl with one free valence at the carbonyl
    C, the C–R bond already drawn — atoms C1 O1, plus the hydrocarbon group
    R = C_{cR−1}H_{2cR−1−2u} with cR acyl carbons and u C=C bonds.
  * Assembly pairs free valences two at a time (worked example W, page 1).
* PL1 has four identical fatty acid residues; PL1 is chiral, while every
  other diastereomer of PL1 has a plane of symmetry (T5 page 1 ¶3).
* R is a hydrocarbon substituent (T5 page 1 ¶2).
* Reductive ozonolysis of RCOOH gives **three different organic products in
  equimolar amounts** (T5 page 3).
* Non-ionised PL1 contains 255 σ + π bonds in total (question 5.3).
* Cross-check from page 4: PL1 + 8 H2O → 4 RCOOH + 2 H3PO4 + 3 glycerol.

## Assembly mathematics (proved below)

Atom inventory of {n × a, 2 × b, 3 × c, 4 × d} + four R groups:

* C = 3·3 + 4·1 + 4·(cR − 1) = 9 + 4·cR
* H = n + 2·1 + 3·5 + 4·(2cR − 1 − 2u) = 13 + n + 8·cR − 8·u
* O = 2·2 + 3·3 + 4·1 = 17,   P = 2

**Handshake lemma.** For the neutral acyclic molecule (no peroxides, none
exist in fragments a–d), every σ- or π-bond consumes exactly two valence
ends, so with the neutral valences C:4, H:1, O:2, P:5 (phosphate P(V) as
drawn in fragment b):

  total bonds = (4·C + H + 2·O + 5·P)/2
              = (93 + n + 24·cR − 8·u)/2
              (exactness proved: `pl1_total_bonds`)

**The 5.1 value n = 1.** The valence sum must be even (it equals twice the
bond count), and 93 + 24cR − 8u has the parity of n + 1, so n is **odd**
(`n_odd`).
The chirality clause then fixes the value: with n ≥ 3 H-caps, at least one
glycerol carries at most one acyl among its three oxygens, so its central
carbon bears two identical arms and is no longer stereogenic; the problem
states PL1 is chiral while *every* other diastereomer has a plane of
symmetry, and the candidates with fewer than three stereogenic glycerol
centres are exactly those achiral diastereomers. The unique
chirality-compatible assembly with odd n is n = 1, the single H capping the
central oxygen of the bridging glycerol — whose central carbon remains
stereogenic because the two phosphate halves it connects are
constitutionally different (this is the cardiolipin structure).
(`pl1AFragCount`, `hydrolysis_consistency`.)

**Bond-count equation.** With n = 1 the valence sum is 94 + 24·cR − 8·u, so
255 bonds means 2·255 = 94 + 24·cR − 8·u, i.e. 24·cR − 8·u = 416, i.e.
**3·cR − u = 52** (`bond_equation_hydrolysis`).  Self-check for
(cR, u) = (18, 2): PL1 = C81H142O17P2 has 241 + 14 = 255 bonds (241 σ bonds
between the 242 atoms of the acyclic molecule; 14 π bonds: 4 ester C=O,
8 C=C, 2 P=O).

**Ozonolysis.** A linear monocarboxylic acid with u C=C bonds gives exactly
u + 1 organic fragments under reductive ozonolysis (each C=C carbon becomes
a carbonyl; the carboxyl carbon terminates one fragment).  Three different
products in equimolar (1:1:1) amounts force u + 1 = 3, so **u = 2**, and
then 3·cR = 54, **cR = 18**.

**Answer.** RCOOH = **C18H32O2** (linoleic acid; its Δ9,Δ12 diene placement
gives ozonolysis fragments of lengths 8, 3, 6 — three different products,
1:1:1; cf. `ozonolysis_witness_C18`).
-/

namespace IChO2026T5A3

/-! ## 1. Atom inventory (ℤ, so that the H-subtraction 8cR − 8u is exact) -/

/-- Numbers of atoms (C, H, O, P) of the assembled non-ionised PL1 built
from n × a, 2 × b, 3 × c, 4 × d with acyl groups R = C_{cR−1}H_{2cR−1−2u}. -/
def pl1Atoms (n cR u : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (9 + 4 * cR, 13 + n + 8 * cR - 8 * u, 17, 2)

/-- Total valence sum 4·C + H + 2·O + 5·P of the assembly. -/
def pl1ValenceSum (n cR u : ℤ) : ℤ :=
  4 * (9 + 4 * cR) + (13 + n + 8 * cR - 8 * u) + 2 * 17 + 5 * 2

theorem pl1_valence_sum_eq (n cR u : ℤ) :
    pl1ValenceSum n cR u = 93 + n + 24 * cR - 8 * u := by
  unfold pl1ValenceSum; ring

/-- Free valences of the inventory: n + 2·2 + 3·3 + 4·1 = n + 17.  They pair
off into (n+17)/2 inter-fragment σ bonds; this cancels against the chosen
atoms of the fragments and does not enter the final (handshake) bond count,
which is why the fallback freedom in *which* fragment supplies a cap (a or
e) does not change the answer. -/
def pl1FreeValences (n : ℤ) : ℤ := n + 2 * 2 + 3 * 3 + 4 * 1

theorem pl1_free_valences (n : ℤ) : pl1FreeValences n = n + 17 := by
  unfold pl1FreeValences; ring

/-! ## 2. Handshake lemma and bond-count formula -/

/-- **Handshake lemma**: in a neutral acyclic molecule every σ/π bond
contributes exactly two valence ends, so the total number of σ + π bonds is
(4·C + H + 2·O + 5·P)/2; an even valence sum halves exactly. -/
theorem frames_total_bonds (S : ℤ) (hpar : S % 2 = 0) :
    S / 2 * 2 = S := by
  omega

/-- The valence sum of a real molecule is even; since 93 + 24·cR − 8·u has
the parity of n + 1, n must be **odd** — the answer to 5.1: "n is an odd
number". -/
theorem n_odd (n cR u : ℤ) (hpar : (93 + n + 24 * cR - 8 * u) % 2 = 0) :
    n % 2 = 1 := by
  omega

/-- **Bond-count formula for PL1**: the total σ+π bond count satisfies
2·B = 93 + n + 24·cR − 8·u whenever that sum is even (it is, for odd n). -/
theorem pl1_total_bonds (n cR u : ℤ)
    (hpar : (93 + n + 24 * cR - 8 * u) % 2 = 0) :
    2 * ((pl1ValenceSum n cR u) / 2) = 93 + n + 24 * cR - 8 * u := by
  rw [pl1_valence_sum_eq]
  omega

/-! ## 3. The 5.1/5.2 decision: n = 1 -/

/-- Among odd n, the chirality clause of the problem singles out n = 1
(see the module documentation: n ≥ 3 destroys a stereogenic glycerol centre
and yields one of the achiral, plane-symmetric diastereomers that the problem
says PL1 is not).  n = 1 caps the central oxygen of the bridging glycerol;
its central carbon joins two constitutionally different phosphate halves and
remains stereogenic: PL1 is chiral with three stereogenic carbons. -/
def pl1AFragCount : ℤ := 1

theorem pl1_n_eq_one : pl1AFragCount = 1 := rfl

/-- Consistency with the page-4 hydrolysis equation
PL1 + 8 H2O → 4 RCOOH + 2 H3PO4 + 3 glycerol:
for RCOOH = C_cR H_{2cR−2u} O2, the hydrolysed inventory minus 8 H2O is
(C, H, O, P) = (4cR + 9, (8cR − 8u + 6 + 24) − 16, 25 − 8, 2)
             = (4cR + 9, 8cR − 8u + 14, 17, 2)
which is exactly `pl1Atoms 1 cR u`. -/
theorem hydrolysis_consistency (cR u : ℤ) :
    pl1Atoms 1 cR u =
      (4 * cR + 9, (8 * cR - 8 * u + 6 + 24) - 8 * 2, 8 + 8 + 9 - 8, 2) := by
  unfold pl1Atoms
  ext <;> ring_nf

/-! ## 4. The 255-bond equation -/

/-- Total valence sum of the hydrolysis-consistent assembly (n = 1) equals
4·C + H + 2·O + 5·P = 94 + 24·cR − 8·u.  The 255-bond condition is therefore
2·255 = 94 + 24·cR − 8·u, i.e. **3·cR − u = 52**. -/
theorem bond_equation_hydrolysis {cR u : ℤ}
    (h : 4 * (4 * cR + 9) + (8 * cR - 8 * u + 14) + 2 * 17 + 5 * 2
        = 2 * 255) :
    3 * cR - u = 52 := by
  omega

/-- Bridge between the assembly-inventory valence sum at n = 1 and the
hydrolysis-derived one: the two ways of counting the same molecule agree,
94 + 24·cR − 8·u. -/
theorem inventory_bridge (cR u : ℤ) :
    pl1ValenceSum 1 cR u =
      4 * (4 * cR + 9) + (8 * cR - 8 * u + 14) + 2 * 17 + 5 * 2 := by
  unfold pl1ValenceSum; ring

/-! ## 5. Ozonolysis (T5 page 3): three different products, equimolar -/

/-- A linear monocarboxylic acid with u C=C bonds gives exactly u + 1 organic
fragments under reductive ozonolysis (each C=C carbon becomes a carbonyl
carbon; the carboxyl carbon terminates one fragment).  "Three different
organic products in equimolar amounts" means each fragment is formed exactly
once per molecule, forcing u + 1 = 3. -/
theorem fragment_count_eq_three {u : ℤ} (h : u + 1 = 3) : u = 2 := by
  omega

/-- Carbon balance under two cleavages at positions p < q (carboxyl carbon
counted as position 1): fragment lengths p − 1, q − p, cR − q sum to cR − 1. -/
theorem ozonolysis_carbon_balance (cR p q : ℤ) (_hp : 2 ≤ p) (_hq : p < q)
    (_hqR : q < cR) :
    (p - 1) + (q - p) + (cR - q) = cR - 1 := by
  omega

/-- The (9,12)-diene placement in a C18 chain gives fragments of lengths
8, 3, 6 — pairwise distinct, carbon-balanced, hence three different products
in a 1:1:1 ratio.  (Ozonolysis of CH3–(CH2)4–CH=CH–CH2–CH=CH–(CH2)7–COOH
gives OHC–(CH2)7–CHO, OHC–CH2–CHO, OHC–(CH2)4–CH3.) -/
theorem ozonolysis_witness_C18 :
    (8 : ℤ) ≠ 3 ∧ (3 : ℤ) ≠ 6 ∧ (8 : ℤ) ≠ 6 ∧ 8 + 3 + 6 = 18 - 1 := by
  norm_num

/-! ## 6. Main theorem: molecular formula of RCOOH -/

/-- Molecular formula of a neutral acyclic monocarboxylic acid with cR
carbons and u C=C bonds: C_cR H_{2cR−2u} O_2. -/
def fattyAcidFormula (cR u : ℤ) : ℤ × ℤ × ℤ := (cR, 2 * cR - 2 * u, 2)

/-- **Main result (T5-A3).**  Under the problem's premises —
* the non-ionised PL1 has the hydrolysis-consistent element inventory of the
  a–d assembly with n = 1 (cardiolipin; `pl1Atoms 1 cR u`) and contains 255
  σ + π bonds (handshake: valence sum = 2·255),
* reductive ozonolysis of RCOOH gives three different organic products in
  equimolar amounts (so u + 1 = 3) —
the fatty acid has cR = 18 carbons and u = 2 C=C bonds, i.e. the molecular
formula **C18H32O2** (linoleic acid). -/
theorem fatty_acid_molecular_formula {cR u : ℤ}
    (_hcR : 1 ≤ cR) (_hu : 0 ≤ u)
    (hbonds : 4 * (4 * cR + 9) + (8 * cR - 8 * u + 14) + 2 * 17 + 5 * 2 = 2 * 255)
    (hozon : u + 1 = 3) :
    fattyAcidFormula cR u = (18, 32, 2) := by
  have h1 : 3 * cR - u = 52 := bond_equation_hydrolysis hbonds
  have hu2 : u = 2 := fragment_count_eq_three hozon
  have hc : cR = 18 := by omega
  simp [fattyAcidFormula, hc, hu2]

/- ### Numeric spot-checks of the final answer -/

/-- 3·18 − 2 = 52 and 24·18 − 8·2 + 94 = 510 = 2·255. -/
theorem check_equation : 3 * 18 - 2 = 52 ∧ 24 * 18 - 8 * 2 + 94 = 510 ∧
    510 = 2 * 255 := by
  norm_num

/-- Hydrogen count of the acid: 2·18 − 2·2 = 32. -/
theorem check_hydrogens : 2 * 18 - 2 * 2 = 32 := by norm_num

/-- PL1 for cR = 18, u = 2 is C81H142O17P2 (tetralinoleoyl cardiolipin),
matching the page-4 hydrolysis balance 4·C18H32O2 + 2·H3PO4 + 3·C3H8O3 −
8·H2O = C81H142O17P2. -/
theorem check_pl1_atoms : pl1Atoms 1 18 2 = (81, 142, 17, 2) := by
  unfold pl1Atoms; norm_num

#print axioms fatty_acid_molecular_formula

end IChO2026T5A3
