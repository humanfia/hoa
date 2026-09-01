/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T5, subquestion 5.3 (target `icho_2026_t5_a3`)

**Problem.** (Sealed problem bundle: T5 page 1 — fragment figure and shared
context; T5 page 3 — question 5.3 box.)  **PL1** is a cardiolipin, an
*acyclic* phospholipid.  Its non-ionised form can be assembled from the
structural elements a–d in the quantities

  a : b : c : d  =  n : 2 : 3 : 4,

where a = ∿–H, b = (HO)(O)P(∿)₂, c = ∿O–CH₂–CH(O∿)–CH₂–O∿ and
d = ∿–C(=O)–R (problem_image, T5 page 1 lower fragment row); R is a
hydrocarbon substituent in the fatty acid structure, and PL1 contains no
peroxide (O–O) bonds (problem_text).  During reductive ozonolysis the fatty
acid RCOOH forms three different organic products in equimolar amounts
(problem_text, shared context before 5.3).  Question 5.3: **determine the
molecular formula of the fatty acid (RCOOH), if the non-ionised form of PL1
contains 255 σ and π bonds between atoms in total** (problem_text).

**Derivation.**

*Assembly ledger.*  Every wavy end is consumed into a covalent bond (worked
example W on T5 page 1).  The inventory supplies n hydrogen ends, 4 phosphorus
ends, 9 glyceryl oxygen ends and 4 carbonyl-carbon ends.  In this fragment
system every phosphorus, carbonyl-carbon and hydrogen end pairs with an
oxygen end (the W example forms exactly P–O, C(=O)–O and O–H bonds; PL1 is a
diprotic phospholipid whose fatty-acid residues are ester-linked), and O–O
bonds are excluded (problem_text), so 9 = 4 + 4 + n, i.e. n = 1, and 9 bonds
are formed in assembly.

*Bond count.*  Fragment-internal σ+π bonds: a contributes 0; b contributes 4
(P=O is one σ and one π, plus P–OH and O–H); c contributes 10 (3 C–O, 2 C–C,
5 C–H); d contributes 3 + bonds(R) (C=O as σ+π, the C–R σ-bond, plus the
bonds inside R).  For an acyclic monovalent hydrocarbon residue R with
k carbons, d double bonds and t triple bonds (U = d + 2t π-bonds), R has
2k + 1 − 2U hydrogens and bonds(R) = (k − 1) + U + (2k + 1 − 2U) = 3k − U.
Total: 2·4 + 3·10 + 4·(3 + (3k − U)) + 9 = 59 + 12k − 4U = 255, hence
3k − U = 49.

*Ozonolysis.*  Reductive ozonolysis cleaves the acyclic carbon skeleton at
each of the d + t multiple-bond sites, giving d + t + 1 organic fragments,
exactly one of which bears the original carboxyl group.  Three different
products in equimolar amounts therefore force d + t + 1 = 3, i.e. d + t = 2,
so U = d + 2t ∈ {2, 3, 4}.

*Uniqueness.*  49 + U must be divisible by 3; among U ∈ {2, 3, 4} only U = 2
survives, forcing t = 0, d = 2 and k = 17.  Hence R = C₁₇H₃₁ and
**RCOOH = C₁₈H₃₂O₂**.  Cross-check: the assembled non-ionised PL1 has atom
inventory C₈₁H₁₄₂O₁₇P₂, and half the valence sum (4·81 + 142 + 2·17 + 5·2)/2
recounts the stated 255 bonds.

The two result contracts at the end are the answer-blind certificates binding
the payload digests to the semantic specifications.
-/

namespace IChO2026Problems.Icho2026T5A3

/-! ## Fragment inventory (problem_image, T5 page 1, lower fragment row) -/

/-- The four structural element types from which non-ionised PL1 is assembled
(problem_image, lower fragment row of T5 page 1). -/
inductive FragmentKind
  | /-- a: ∿–H — a hydrogen cap with one free valence -/ a
  | /-- b: (HO)(O)P(∿)₂ — phosphate fragment with two free valences -/ b
  | /-- c: ∿O–CH₂–CH(O∿)–CH₂–O∿ — glyceryl fragment with three free valences -/ c
  | /-- d: ∿–C(=O)–R — fatty-acyl fragment with one free valence -/ d
deriving DecidableEq

/-- Free valences ("wavy ends") of one fragment of each kind, read off the
drawn fragment structures (problem_image): a = ∿–H has 1, b = (HO)(O)P(∿)₂
has 2, c = ∿O–CH₂–CH(O∿)–CH₂–O∿ has 3, d = ∿–C(=O)–R has 1. -/
def FragmentKind.freeValences : FragmentKind → ℕ
  | .a => 1
  | .b => 2
  | .c => 3
  | .d => 1

/-- Stated quantities of the four fragment types for the assembly of PL1
(problem_image, lower fragment row: `n ×` a, `2 ×` b, `3 ×` c, `4 ×` d). -/
def FragmentKind.quantity (n : ℕ) : FragmentKind → ℕ
  | .a => n
  | .b => 2
  | .c => 3
  | .d => 4

/-- The chemical element whose atom carries the free valence(s) of each
fragment kind (problem_image): a bonds through its hydrogen atom, b through
phosphorus, c through its glyceryl oxygens, d through the carbonyl carbon. -/
inductive ValenceAtom
  | hydrogen
  | phosphorus
  | oxygen
  | carbonylCarbon
deriving DecidableEq

/-- The atom label of the free valence(s) of each fragment kind. -/
def FragmentKind.valenceAtom : FragmentKind → ValenceAtom
  | .a => .hydrogen
  | .b => .phosphorus
  | .c => .oxygen
  | .d => .carbonylCarbon

/-- Total number of free valences supplied by the stated fragment inventory
for PL1. -/
def totalFreeValences (n : ℕ) : ℕ :=
  FragmentKind.quantity n .a * FragmentKind.freeValences .a
    + FragmentKind.quantity n .b * FragmentKind.freeValences .b
    + FragmentKind.quantity n .c * FragmentKind.freeValences .c
    + FragmentKind.quantity n .d * FragmentKind.freeValences .d

/-- The valence inventory is `n + 17` (valence counts from the drawn
fragments; pure arithmetic). -/
theorem totalFreeValences_eq (n : ℕ) : totalFreeValences n = n + 17 := by
  change n * 1 + 2 * 2 + 3 * 3 + 4 * 1 = n + 17
  omega

/-! ## The hydrocarbon residue R of the fatty acid -/

/-- The hydrocarbon substituent R of the fatty acid RCOOH (problem_text: "R is
a hydrocarbon substituent in the fatty acid structure"; cardiolipins are a
family of *acyclic* phospholipids, so the carbon skeleton of R is a tree).
R is monovalent: its single free valence bonds to the carbonyl carbon of a
type-d fragment (worked example W).

* `carbons` — the number k of carbon atoms (k ≥ 1);
* `doubleBonds` — the number d of carbon–carbon double bonds C=C;
* `tripleBonds` — the number t of carbon–carbon triple bonds C≡C;
* the side condition `doubleBonds + 2 * tripleBonds ≤ carbons` keeps the
  valence count physically meaningful (at least one hydrogen remains). -/
structure HydrocarbonResidue where
  /-- Number k of carbon atoms of R. -/
  carbons : ℕ
  /-- Number d of C=C double bonds of R. -/
  doubleBonds : ℕ
  /-- Number t of C≡C triple bonds of R. -/
  tripleBonds : ℕ
  /-- R has at least one carbon atom. -/
  carbons_pos : 0 < carbons
  /-- Valence feasibility: the π-bond count `d + 2t` does not exceed k. -/
  unsat_le : doubleBonds + 2 * tripleBonds ≤ carbons

/-- The π-bond count (degree of unsaturation) of R: each C=C contributes one
and each C≡C contributes two. -/
def HydrocarbonResidue.unsat (R : HydrocarbonResidue) : ℕ :=
  R.doubleBonds + 2 * R.tripleBonds

/-- Hydrogen count of R (trusted_general_law valence law for an acyclic
monovalent hydrocarbon group): a saturated acyclic monovalent group C_k has
2k + 1 hydrogens, and each π-bond removes two. -/
def HydrocarbonResidue.hydrogens (R : HydrocarbonResidue) : ℕ :=
  2 * R.carbons + 1 - 2 * R.unsat

/-- σ+π bonds inside R (trusted_general_law bond bookkeeping on the acyclic
carbon skeleton): k − 1 carbon–carbon σ-bonds (tree on k carbons), U π-bonds,
and one C–H σ-bond per hydrogen. -/
def HydrocarbonResidue.bondCount (R : HydrocarbonResidue) : ℕ :=
  (R.carbons - 1) + R.unsat + R.hydrogens

/-- The residue bond count in closed linear form: `3k − U`. -/
theorem HydrocarbonResidue.bondCount_eq (R : HydrocarbonResidue) :
    (R.bondCount : ℤ) = 3 * R.carbons - R.unsat := by
  have hU : R.unsat ≤ R.carbons := R.unsat_le
  have hk : 0 < R.carbons := R.carbons_pos
  simp only [HydrocarbonResidue.bondCount, HydrocarbonResidue.hydrogens]
  omega

/-! ## Molecular formula of the fatty acid -/

/-- A molecular formula over the elements occurring in the fatty acid RCOOH
(carbon, hydrogen, oxygen). -/
structure MolecularFormula where
  /-- Number of carbon atoms. -/ C : ℕ
  /-- Number of hydrogen atoms. -/ H : ℕ
  /-- Number of oxygen atoms. -/ O : ℕ
deriving DecidableEq

/-- The molecular formula of the fatty acid RCOOH with hydrocarbon residue R
(problem_text: the fatty acid is RCOOH): R contributes its k carbons and its
hydrogens, and the carboxyl group –COOH adds one carbon, one hydrogen and two
oxygens. -/
def acidFormula (R : HydrocarbonResidue) : MolecularFormula :=
  ⟨R.carbons + 1, R.hydrogens + 1, 2⟩

/-! ## Fragment internal bonds -/

/-- σ+π bonds internal to one fragment, read off the drawn structures
(problem_image, T5 page 1):

* a (∿–H): none;
* b ((HO)(O)P(∿)₂): P=O (one σ and one π), P–OH and O–H — four;
* c (∿O–CH₂–CH(O∿)–CH₂–O∿): three C–O, two C–C and five C–H — ten;
* d (∿–C(=O)–R): C=O (one σ and one π) and C–R, plus the bonds inside R. -/
def FragmentKind.internalBonds (R : HydrocarbonResidue) : FragmentKind → ℕ
  | .a => 0
  | .b => 4
  | .c => 10
  | .d => 3 + R.bondCount

/-! ## The assembly bond ledger -/

/-- A bond ledger for an assembly of non-ionised PL1 from the fragment
inventory: the fields `hh`, `hp`, …, `cc` count the assembled bonds by the
pair of valence-atom types they join (h = hydrogen ends from fragments a,
p = phosphorus ends from fragments b, o = glyceryl oxygen ends from
fragments c, c = carbonyl-carbon ends from fragments d).

The four balance equations express completeness of the assembly
(problem_text: "it is possible to assemble the non-ionised form of PL1" from
exactly the stated fragments; worked example W: every wavy end is consumed
into a bond).  The seven vanishing equations are the chemical exclusions of
this fragment system (problem_image worked example W, which forms only P–O,
C(=O)–O and O–H bonds; problem_text: PL1 is a phospholipid — a diprotic acid
with two identical acidic groups, the two phosphate –OH — whose fatty-acid
residues are ester-linked; and PL1 contains no peroxide bonds):

* no H–H bonds (an H₂ molecule would not be part of the single assembled
  PL1 molecule);
* no P–H, P–P or P–C bonds (the phosphorus atoms remain P(V) oxoacid centres,
  each keeping its one –OH and forming phosphoester bonds);
* no C(=O)–H or C(=O)–C bonds (the acyl fragments stay ester-linked
  fatty-acid residues, as in W);
* no O–O bonds (the stated peroxide exclusion). -/
structure BondLedger (n : ℕ) where
  /-- Assembled H–H bonds. -/ hh : ℕ
  /-- Assembled H–P bonds. -/ hp : ℕ
  /-- Assembled O–H bonds. -/ ho : ℕ
  /-- Assembled H–C(=O) bonds. -/ hc : ℕ
  /-- Assembled P–P bonds. -/ pp : ℕ
  /-- Assembled P–O (phosphoester) bonds. -/ po : ℕ
  /-- Assembled P–C(=O) bonds. -/ pc : ℕ
  /-- Assembled O–O (peroxide) bonds. -/ oo : ℕ
  /-- Assembled O–C(=O) (fatty-ester) bonds. -/ oc : ℕ
  /-- Assembled C(=O)–C(=O) bonds. -/ cc : ℕ
  /-- No H–H bonds: every a-fragment hydrogen caps another fragment's valence
  inside the single assembled molecule (worked example W). -/
  hh_zero : hh = 0
  /-- No P–H bonds: phosphorus valences form P–O (phosphoester) bonds, as in
  W; PL1 is a diprotic acid whose two identical acidic groups are the two
  phosphate –OH groups (problem_text). -/
  hp_zero : hp = 0
  /-- No C(=O)–H bonds: the acyl fragments remain ester-linked fatty-acid
  residues (problem_text: cardiolipins differ in fatty-acid residues; worked
  example W forms an ester). -/
  hc_zero : hc = 0
  /-- No P–P bonds in this phospholipid fragment chemistry (worked example W
  pairs phosphorus valences with oxygen ends). -/
  pp_zero : pp = 0
  /-- No P–C bonds in this phospholipid fragment chemistry (worked example W
  pairs phosphorus valences with oxygen ends). -/
  pc_zero : pc = 0
  /-- No C(=O)–C(=O) bonds: acyl fragments attach to glyceryl oxygens as
  esters (worked example W). -/
  cc_zero : cc = 0
  /-- No O–O bonds: PL1 does not contain any peroxide bonds (problem_text). -/
  oo_zero : oo = 0
  /-- All n hydrogen valence ends are consumed (n fragments a, one end
  each). -/
  h_balance : 2 * hh + hp + ho + hc = n
  /-- All 4 phosphorus valence ends are consumed (2 fragments b, two ends
  each). -/
  p_balance : hp + 2 * pp + po + pc = 2 * 2
  /-- All 9 glyceryl oxygen valence ends are consumed (3 fragments c, three
  ends each). -/
  o_balance : ho + po + 2 * oo + oc = 3 * 3
  /-- All 4 carbonyl-carbon valence ends are consumed (4 fragments d, one end
  each). -/
  c_balance : hc + pc + oc + 2 * cc = 4 * 1

/-- Completeness of the assembly forces the fragment count n = 1: the nine
glyceryl oxygen ends consume exactly the four phosphorus ends, the four
carbonyl-carbon ends and the n hydrogen ends. -/
theorem BondLedger.n_eq_one {n : ℕ} (L : BondLedger n) : n = 1 := by
  obtain ⟨hh, hp, ho, hc, pp, po, pc, oo, oc, cc, z1, z2, z3, z4, z5, z6, z7, hb,
    pb, ob, cb⟩ := L
  omega

/-- Consistency with question 5.1 (derived inline, per the previous-part
dependency policy): the fragment count of any complete assembly is odd. -/
theorem BondLedger.n_odd {n : ℕ} (L : BondLedger n) : Odd n := by
  have h := L.n_eq_one
  exact ⟨0, by omega⟩

/-- The number of bonds formed in assembly: every ledger entry is one covalent
bond (worked example W: two wavy ends per bond, one bond per pair). -/
def BondLedger.assembledBonds {n : ℕ} (L : BondLedger n) : ℕ :=
  L.hh + L.hp + L.ho + L.hc + L.pp + L.po + L.pc + L.oo + L.oc + L.cc

/-- The assembly forms `n + 8` bonds: four P–O phosphoester bonds, four
C(=O)–O fatty-ester bonds and n O–H bonds. -/
theorem BondLedger.assembledBonds_eq {n : ℕ} (L : BondLedger n) :
    L.assembledBonds = n + 8 := by
  obtain ⟨hh, hp, ho, hc, pp, po, pc, oo, oc, cc, z1, z2, z3, z4, z5, z6, z7, hb,
    pb, ob, cb⟩ := L
  change hh + hp + ho + hc + pp + po + pc + oo + oc + cc = n + 8
  omega

/-- Handshake consistency check (trusted_general_law: two valence ends per
bond): the ledger accounts exactly for the fragment valence inventory
`n + 17`. -/
theorem BondLedger.handshake {n : ℕ} (L : BondLedger n) :
    2 * L.assembledBonds = totalFreeValences n := by
  rw [totalFreeValences_eq]
  have h := L.assembledBonds_eq
  have h1 := L.n_eq_one
  omega

/-! ## Total σ+π bond count of non-ionised PL1 -/

/-- Total σ+π bonds between atoms of the assembled non-ionised PL1
(problem_text, 5.3): the fragment-internal bonds in the stated quantities
`n, 2, 3, 4` plus the bonds formed in assembly. -/
def pl1TotalBonds (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n) : ℕ :=
  n * FragmentKind.internalBonds R .a
    + 2 * FragmentKind.internalBonds R .b
    + 3 * FragmentKind.internalBonds R .c
    + 4 * FragmentKind.internalBonds R .d
    + L.assembledBonds

/-- The total bond count in closed linear form: `58 + 12k − 4U + n`, where k
is the residue carbon count and U its π-bond count. -/
theorem pl1TotalBonds_eq (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n) :
    (pl1TotalBonds n R L : ℤ) = 58 + 12 * R.carbons - 4 * R.unsat + n := by
  have hb := R.bondCount_eq
  have ha := L.assembledBonds_eq
  simp only [pl1TotalBonds, FragmentKind.internalBonds]
  omega

/-! ## Atom inventory and valence-sum cross-check -/

/-- Atom inventory (C, H, O, P) of an assembled phospholipid. -/
structure AtomInventory where
  /-- Number of carbon atoms. -/ C : ℕ
  /-- Number of hydrogen atoms. -/ H : ℕ
  /-- Number of oxygen atoms. -/ O : ℕ
  /-- Number of phosphorus atoms. -/ P : ℕ
deriving DecidableEq

/-- Atom inventory of the assembled non-ionised PL1 (problem_image fragment
structures and quantities; assembly only joins fragments, so every fragment
atom is retained): three glyceryl fragments C₃H₅O₃, two phosphate fragments
HPO₂, four acyl fragments –C(=O)–R and n hydrogen caps. -/
def pl1Inventory (n : ℕ) (R : HydrocarbonResidue) : AtomInventory :=
  ⟨3 * 3 + 4 * 1 + 4 * R.carbons, 3 * 5 + 2 * 1 + n + 4 * R.hydrogens,
    3 * 3 + 2 * 2 + 4 * 1, 2⟩

/-- Independent valence-sum recount (trusted_general_law: each σ/π bond
consumes two valence incidences; carbon is tetravalent, hydrogen monovalent,
oxygen divalent, and P(V) pentavalent with its P=O double bond): half the
valence sum of the atom inventory equals the fragment-wise bond count. -/
theorem pl1_bonds_valence_sum (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n) :
    ((4 * (pl1Inventory n R).C + (pl1Inventory n R).H + 2 * (pl1Inventory n R).O
        + 5 * (pl1Inventory n R).P : ℕ) : ℤ) / 2
      = (pl1TotalBonds n R L : ℤ) := by
  have hlin := pl1TotalBonds_eq n R L
  have hn := L.n_eq_one
  have hU : R.unsat = R.doubleBonds + 2 * R.tripleBonds := rfl
  have hUle := R.unsat_le
  have hk := R.carbons_pos
  change ((4 * (3 * 3 + 4 * 1 + 4 * R.carbons)
      + (3 * 5 + 2 * 1 + n + 4 * (2 * R.carbons + 1 - 2 * R.unsat))
      + 2 * (3 * 3 + 2 * 2 + 4 * 1) + 5 * 2 : ℕ) : ℤ) / 2
      = (pl1TotalBonds n R L : ℤ)
  omega

/-! ## The ozonolysis report -/

/-- Model of the ozonolysis sentence (problem_text, shared context before
5.3): "During reductive ozonolysis, RCOOH forms three different organic
products in equimolar amounts."

Reductive ozonolysis cleaves the acyclic carbon skeleton of RCOOH at each of
its `m = d + t` carbon–carbon multiple-bond sites (trusted_general_law:
ozonolysis cleaves carbon–carbon multiple bonds), so one molecule of acid
gives `m + 1` organic fragments.  The sentence is modeled as a surjective
assignment `f` of the `m + 1` fragments to three product classes such that

* every class contains equally many fragments (equimolar amounts: each
  fragment of a class yields one molecule of that product per molecule of
  acid), and
* the carboxyl-bearing fragment `0` is alone in its class — no other fragment
  contains the carboxyl carbon, so no other fragment can be the same
  molecule. -/
def ThreeEquimolarProducts (m : ℕ) : Prop :=
  ∃ f : Fin (m + 1) → Fin 3,
    Function.Surjective f
      ∧ (∀ i : Fin (m + 1), f i = f 0 → i = 0)
      ∧ (∀ y : Fin 3,
          (Finset.univ.filter fun i => f i = y).card
            = (Finset.univ.filter fun i => f i = f 0).card)

/-- The ozonolysis report is satisfiable exactly when the acid skeleton has
exactly two multiple-bond sites: the carboxyl class is a singleton,
equimolarity then makes every one of the three classes a singleton, and
counting fragments gives `m + 1 = 3`. -/
theorem threeEquimolarProducts_iff (m : ℕ) :
    ThreeEquimolarProducts m ↔ m = 2 := by
  constructor
  · rintro ⟨f, -, hcarb, hequi⟩
    have hfib0 : (Finset.univ.filter fun i => f i = f 0) = {0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨hcarb i, fun hi => by rw [hi]⟩
    have hcard1 : ∀ y : Fin 3, (Finset.univ.filter fun i => f i = y).card = 1 := by
      intro y
      rw [hequi y, hfib0, Finset.card_singleton]
    have key := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin (m + 1)))) (t := (Finset.univ : Finset (Fin 3)))
      (f := f) (by simp only [Finset.coe_univ]; exact Set.mapsTo_univ _ _)
    rw [Finset.card_univ, Fintype.card_fin,
      Finset.sum_congr rfl (fun y _ => hcard1 y), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at key
    omega
  · rintro rfl
    refine ⟨fun i => i, fun y => ⟨y, rfl⟩, fun i hi => hi, fun y => ?_⟩
    fin_cases y <;> decide

/-! ## The derivation: the fatty acid is C₁₈H₃₂O₂ -/

/-- Solving the two problem constraints: the stated 255-bond total and the
ozonolysis report together force k = 17, d = 2, t = 0 (hence U = 2 and
R = C₁₇H₃₁).  Indeed the bond total gives `3k − U = 49`, the ozonolysis
report gives `d + t = 2`, so `U = 2 + t` with `t ≤ 2`; divisibility of
`49 + U` by 3 then forces `t = 0`. -/
theorem fatty_acid_parameters {n : ℕ} {R : HydrocarbonResidue} (L : BondLedger n)
    (hbonds : pl1TotalBonds n R L = 255)
    (hozone : ThreeEquimolarProducts (R.doubleBonds + R.tripleBonds)) :
    R.carbons = 17 ∧ R.doubleBonds = 2 ∧ R.tripleBonds = 0 := by
  have hn : n = 1 := L.n_eq_one
  have hlin := pl1TotalBonds_eq n R L
  rw [hbonds] at hlin
  have hm := (threeEquimolarProducts_iff (R.doubleBonds + R.tripleBonds)).mp hozone
  have hU : R.unsat = R.doubleBonds + 2 * R.tripleBonds := rfl
  omega

/-- The molecular formula of the fatty acid is determined by the problem
constraints: C₁₈H₃₂O₂ (R = C₁₇H₃₁ attached to –COOH). -/
theorem fatty_acid_formula {n : ℕ} {R : HydrocarbonResidue} (L : BondLedger n)
    (hbonds : pl1TotalBonds n R L = 255)
    (hozone : ThreeEquimolarProducts (R.doubleBonds + R.tripleBonds)) :
    acidFormula R = ⟨18, 32, 2⟩ := by
  obtain ⟨hk, hd, ht⟩ := fatty_acid_parameters L hbonds hozone
  have hU : R.unsat = 2 := by
    change R.doubleBonds + 2 * R.tripleBonds = 2
    rw [hd, ht]
  have hH : R.hydrogens = 31 := by
    change 2 * R.carbons + 1 - 2 * R.unsat = 31
    rw [hk, hU]
  change (⟨R.carbons + 1, R.hydrogens + 1, 2⟩ : MolecularFormula) = ⟨18, 32, 2⟩
  rw [hk, hH]

/-! ## The derived witness -/

/-- The cardiolipin bond ledger at n = 1 (the unique ledger compatible with
the inventory and the chemical exclusions): four P–O phosphoester bonds, four
C(=O)–O fatty-ester bonds and one O–H bond — the free 2-hydroxyl of the
central glycerol of the cardiolipin skeleton. -/
def cardiolipinLedger : BondLedger 1 where
  hh := 0
  hp := 0
  ho := 1
  hc := 0
  pp := 0
  po := 4
  pc := 0
  oo := 0
  oc := 4
  cc := 0
  hh_zero := rfl
  hp_zero := rfl
  hc_zero := rfl
  pp_zero := rfl
  pc_zero := rfl
  cc_zero := rfl
  oo_zero := rfl
  h_balance := by decide
  p_balance := by decide
  o_balance := by decide
  c_balance := by decide

/-- The derived residue parameters (the unique solution of the bond-count and
ozonolysis constraints): k = 17 carbons, d = 2 double bonds, t = 0 triple
bonds — R = C₁₇H₃₁. -/
def derivedResidue : HydrocarbonResidue where
  carbons := 17
  doubleBonds := 2
  tripleBonds := 0
  carbons_pos := by decide
  unsat_le := by decide

/-- The derived residue meets the stated 255-bond total on the cardiolipin
ledger, satisfies the ozonolysis report, and yields the acid formula
C₁₈H₃₂O₂. -/
theorem derivedResidue_satisfies :
    pl1TotalBonds 1 derivedResidue cardiolipinLedger = 255
      ∧ ThreeEquimolarProducts (derivedResidue.doubleBonds + derivedResidue.tripleBonds)
      ∧ acidFormula derivedResidue = ⟨18, 32, 2⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · exact (threeEquimolarProducts_iff (2 + 0)).mpr rfl
  · decide

/-- With the derived parameters the non-ionised PL1 has atom inventory
C₈₁H₁₄₂O₁₇P₂ (the tetra-acyl cardiolipin with four C₁₇H₃₁ residues). -/
theorem pl1Inventory_derived : pl1Inventory 1 derivedResidue = ⟨81, 142, 17, 2⟩ := by
  decide

/-- The valence sum of C₈₁H₁₄₂O₁₇P₂ recounts the stated 255 σ+π bonds
(supporting calculation). -/
theorem pl1_bonds_check : (4 * 81 + 142 + 2 * 17 + 5 * 2 : ℕ) / 2 = 255 := by
  decide

/-! ## Raw and reported result specifications -/

/-- Raw derivation spec for question 5.3 (before any reporting step):

1. assembly completeness with the chemical exclusions forces the fragment
   count `n = 1` (`BondLedger.n_eq_one`);
2. the total σ+π bond count of non-ionised PL1 is `58 + 12k − 4U + n`
   (`pl1TotalBonds_eq`);
3. the ozonolysis report (three different organic products in equimolar
   amounts) is satisfiable iff the acid skeleton has exactly two
   multiple-bond sites (`threeEquimolarProducts_iff`);
4. the stated total of 255 bonds together with the ozonolysis report forces
   the fatty-acid molecular formula C₁₈H₃₂O₂ (`fatty_acid_formula`);
5. the independent valence-sum recount agrees with the fragment-wise bond
   count (`pl1_bonds_valence_sum`). -/
def RawResultSpec : Prop :=
  (∀ n : ℕ, BondLedger n → n = 1)
    ∧ (∀ (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n),
        (pl1TotalBonds n R L : ℤ) = 58 + 12 * R.carbons - 4 * R.unsat + n)
    ∧ (∀ m : ℕ, ThreeEquimolarProducts m ↔ m = 2)
    ∧ (∀ (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n),
        pl1TotalBonds n R L = 255 →
        ThreeEquimolarProducts (R.doubleBonds + R.tripleBonds) →
        acidFormula R = ⟨18, 32, 2⟩)
    ∧ (∀ (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n),
        ((4 * (pl1Inventory n R).C + (pl1Inventory n R).H + 2 * (pl1Inventory n R).O
            + 5 * (pl1Inventory n R).P : ℕ) : ℤ) / 2 = (pl1TotalBonds n R L : ℤ))

/-- Reported (final) spec for question 5.3: the molecular formula of the
fatty acid is C₁₈H₃₂O₂ — the problem constraints are satisfiable (witnessed by
the derived parameters k = 17, d = 2, t = 0 on the cardiolipin ledger at
n = 1) and every residue satisfying them has formula C₁₈H₃₂O₂ (determinacy of
the requested identification).  The requested output is an exact symbolic
formula; no rounding applies (reporting policy of the requested output:
`exact_symbolic`). -/
def ReportedResultSpec : Prop :=
  (∃ (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n),
      pl1TotalBonds n R L = 255
      ∧ ThreeEquimolarProducts (R.doubleBonds + R.tripleBonds)
      ∧ acidFormula R = ⟨18, 32, 2⟩)
    ∧ (∀ (n : ℕ) (R : HydrocarbonResidue) (L : BondLedger n),
        pl1TotalBonds n R L = 255 →
        ThreeEquimolarProducts (R.doubleBonds + R.tripleBonds) →
        acidFormula R = ⟨18, 32, 2⟩)

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("b617f6e9ff2f54788ba0522ea69a0b9b6ca87c76d992fd612259f9fe74103c54" : String)
      = "b617f6e9ff2f54788ba0522ea69a0b9b6ca87c76d992fd612259f9fe74103c54"
      ∧ RawResultSpec :=
  ⟨rfl, fun _ L => BondLedger.n_eq_one L, fun n R L => pl1TotalBonds_eq n R L,
    fun m => threeEquimolarProducts_iff m,
    fun _ _ L hb ho => fatty_acid_formula L hb ho,
    fun n R L => pl1_bonds_valence_sum n R L⟩

/-- Reported result certificate: binds the answer-blind reported-role payload
digest to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("67cd15dccf307f14810b8f82785c8ea7cea90d1db7437a510cd9c2b042fdac62" : String)
      = "67cd15dccf307f14810b8f82785c8ea7cea90d1db7437a510cd9c2b042fdac62"
      ∧ ReportedResultSpec :=
  ⟨rfl, ⟨1, derivedResidue, cardiolipinLedger, derivedResidue_satisfies⟩,
    fun _ _ L hb ho => fatty_acid_formula L hb ho⟩

end IChO2026Problems.Icho2026T5A3
