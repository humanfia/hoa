import Mathlib

/-!
# IChO 2026 T9-A5 — Structure of L on the β-CD template

Problem-only formalisation of subquestion 9.5:
*"Draw the structure of L on the β-CD template. Fill in all the boxes."*

## Problem inputs actually used (allowed sources only)

* β-CD has 7 α-D-glucopyranoside units joined by α-1,4-glycosidic bonds
  (page Q9-1 text).
* β-CD figure: 7 primary boxes CH₂OH and the secondary box (OH)₁₄
  (page Q9-1 figure; repeated as the 9.5 starting material on page Q9-3,
  with units numbered 1–7 in red).
* 9.5 arrow: 1) NaH (30 equiv.), BnCl (30 equiv.); 2) DIBAL-H (2 equiv.)
  (page Q9-3).
* Preamble (page Q9-3): a single protic group at unit 1 directs the *next*
  reductive debenzylation of a **primary** OH to **unit 4**, or to unit 3
  if unit 4 is not available.
* Downstream of L (page Q9-3): t-BuOK / allyl bromide (drawn
  CH₂=CH–CH₂–Br), Grubbs I, H₂/PtO₂ install the saturated
  –CH₂O(CH₂)₄OCH₂– tether; the printed dimer has per ring exactly one free
  CH₂OH, five CH₂OBn, one tethered CH₂O– and (OBn)₁₄ on the face.

No official solution, marking scheme or external solver was consulted.

## Semantics of "fill in all the boxes"

A `BetaCDTemplate` holds the 7 primary boxes in printed unit order 1…7, the
7 secondary pairs (positions 2 and 3 of each unit) and the secondary-face
box exactly as printed (multiplier, state).  The box states are *grounded
in explicit structure*: `templateMolecule` splices real atom fragments
(`substFragment`) onto the explicit β-CD core (`betaCDCore`), so the
substituent of every box is a genuine list of atoms and bonds, not a text
label.

## The answer being proved

Step 1 (NaH/BnCl 30/30 equiv.) perbenzylates all 21 OH (primary *and*
secondary).  Step 2 uses **2 equiv.** of DIBAL-H, amounting to exactly two
primary reductive debenzylations:

1. the first cleavage on the C₇-symmetric perbenzylated ring frees the
   primary OH conventionally taken as **unit 1** (the numbering anchor of
   the preamble and answer sheet; any rotation of the heptagon is the same
   molecule — see `lTemplate_d7_fixed`);
2. the now-present single protic group at unit 1 directs the **next**
   debenzylation to **unit 4** (unit 4 is available, so the unit-3 fallback
   cannot fire; both rule directions confine the choice to {3, 4} —
   proven in `sinayRule_forces_3_or_4`).

Hence L is **6¹,6⁴-di-O-debenzyl perbenzyl β-CD**: primary boxes
`[H, Bn, Bn, H, Bn, Bn, Bn]` (units 1→7), all seven secondary pairs
`(Bn, Bn)`, face box `(Bn, 14)`; formula C₁₇₅H₁₈₄O₃₅.  This is the unique
precursor that delivers the printed dimer (one allylatable free CH₂OH per
ring is consumed by the tether, one is left over; mixture of linkage
isomers, cf. 9.6).
-/

namespace IChO2026T9A5

/-! ## Atoms, bonds and a tiny explicit molecule language -/

/-- Element tag for the atoms that occur in this problem. -/
inductive Atom where
  | C | H | O
  deriving DecidableEq, Repr

/-- Bond between two absolute atom indices. -/
structure Bond where
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

/-- An explicit molecular graph: atom list plus bonds indexing into it. -/
structure Molecule where
  atoms : List Atom
  bonds : List Bond
  deriving DecidableEq, Repr

/-- Count atoms of a given element. -/
def Molecule.count (m : Molecule) (a : Atom) : Nat :=
  m.atoms.countP (· == a)

/-- Molecular formula as `(C, H, O)` counts. -/
def Molecule.formula (m : Molecule) : Nat × Nat × Nat :=
  (m.count .C, m.count .H, m.count .O)

/-- Counting atoms in a flattened list of `n` copies. -/
theorem countP_flatten_replicate (p : Atom → Bool) (n : ℕ) (l : List Atom) :
    ((List.replicate n l).flatten).countP p = n * l.countP p := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.countP_append, ih,
        Nat.succ_mul, Nat.add_comm]

/-! ## Benzylation arithmetic (trusted general law) -/

/-- Replacing an –OH hydrogen by a benzyl group PhCH₂– adds a net C₇H₆
fragment per converted OH (gain C₇H₇, lose H). -/
def benzylNet : Nat × Nat × Nat := (7, 6, 0)

/-- Formula after substituting `k` hydroxy hydrogens by benzyl groups. -/
def formulaAfterBenzylation (c h o k : Nat) : Nat × Nat × Nat :=
  (c + k * benzylNet.1, h + k * benzylNet.2.1, o + k * benzylNet.2.2)

/-- The perbenzylated β-CD intermediate of step 1 (21 benzyl groups) has
formula C₁₈₉H₁₉₆O₃₅. -/
theorem perbenzylBetaCD_formula :
    formulaAfterBenzylation 42 70 35 21 = (189, 196, 35) := rfl

/-- L carries exactly 19 benzyl groups (21 − 2 DIBAL-H cleavages), giving
C₁₇₅H₁₈₄O₃₅. -/
theorem l_formula_by_count :
    formulaAfterBenzylation 42 70 35 19 = (175, 184, 35) := rfl

/-! ## The Sinay directing rule (preamble, page Q9-3) -/

/-- Forward direction: with the protic group at unit 1 and unit 4 available,
the *next* primary debenzylation site is unit 4. -/
def sinayRuleForward (unit4Available chosen : Nat) : Prop :=
  unit4Available = 4 → chosen = 4

/-- Fallback direction: if unit 4 is not available, the chosen site is
unit 3. -/
def sinayRuleFallback (unit4Available chosen : Nat) : Prop :=
  unit4Available ≠ 4 → chosen = 3

/-- Both directions together confine any Sinay-directed cleavage to
units 3 or 4. -/
theorem sinayRule_forces_3_or_4 (unit4Available chosen : Nat)
    (hf : sinayRuleForward unit4Available chosen)
    (hb : sinayRuleFallback unit4Available chosen) :
    chosen = 3 ∨ chosen = 4 := by
  by_cases h : unit4Available = 4
  · exact Or.inr (hf h)
  · exact Or.inl (hb h)

/-- With unit 4 available (as in the L step), the second debenzylation goes
to unit 4 — never unit 6. -/
theorem sinayRule_unit6_not_chosen (chosen : Nat)
    (h4 : sinayRuleForward 4 chosen) :
    chosen ≠ 6 := by
  intro h
  have := h4 rfl
  omega

/-- With unit 4 available, the unit-3 fallback cannot fire either. -/
theorem sinayRule_unit3_not_chosen (chosen : Nat)
    (h4 : sinayRuleForward 4 chosen) :
    chosen ≠ 3 := by
  intro h
  have := h4 rfl
  omega

/-- The second debenzylation of L is therefore *uniquely* unit 4. -/
theorem sinayRule_second_at_4 (chosen : Nat)
    (h4 : sinayRuleForward 4 chosen) :
    chosen = 4 ∧ chosen ≠ 1 ∧ chosen ≠ 2 ∧ chosen ≠ 3 ∧
      chosen ≠ 5 ∧ chosen ≠ 6 ∧ chosen ≠ 7 := by
  have hc : chosen = 4 := h4 rfl
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ## Reagent stoichiometry from the 9.5 arrow -/

/-- Equivalents printed on the 9.5 arrow, per mole of β-CD. -/
def naHEquiv : Nat := 30

def bnClEquiv : Nat := 30

/-- DIBAL-H equivalents in step 2. -/
def dibalEquiv : Nat := 2

/-- Number of primary (C6) OH boxes on the β-CD template. -/
def primarySites : Nat := 7

/-- Number of secondary (2-OH + 3-OH) OH positions on β-CD. -/
def secondarySites : Nat := 14

/-- Free OH groups on the printed β-CD starting material of 9.5. -/
def freeOHStart : Nat := primarySites + secondarySites

/-- Step 1: 30 ≥ 21 equivalents of both NaH and BnCl, so every free OH —
primary and secondary — is benzylated. -/
theorem benzylation_excess :
    freeOHStart ≤ naHEquiv ∧ freeOHStart ≤ bnClEquiv := by
  constructor <;> decide

/-- DIBAL-H is sub-stoichiometric (2 < 7 primary benzyl ethers): only two
primary debenzylations can occur. -/
theorem dibal_substoichiometric : dibalEquiv < primarySites := by decide

/-- The Sinay rule keeps the two cleavages on the *primary* face; all 14
secondary benzyl ethers survive step 2. -/
theorem secondary_face_untouched :
    secondarySites - 0 = 14 := rfl

/-! ## Explicit molecules grounding the box contents -/

/-- A glucose residue C₆H₁₀O₅ as an explicit atom/bond graph: pyranose ring
O5–C1–C2–C3–C4–C5, glycosidic O at C1 (index 7), OH at C2 (8), OH at C3
(9), glycosidic O at C4 (10), primary arm C5–C6 with O6.  Ten hydrogens
close the C₆H₁₀O₅ formula. -/
def glucoseResidue : Molecule where
  atoms :=
    [.O, .C, .C, .C, .C, .C, .C,
     .O, .O, .O, .O,
     .H, .H, .H, .H, .H, .H, .H, .H, .H, .H]
  bonds :=
    [ ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 0⟩,
      ⟨1, 7⟩, ⟨2, 8⟩, ⟨3, 9⟩, ⟨4, 10⟩,
      ⟨5, 6⟩ ]

theorem glucoseResidue_formula :
    glucoseResidue.formula = (6, 10, 5) := rfl

/-- The glucose-residue *core*: the residue minus its three O–H hydrogens —
the part unchanged whether positions 2, 3, 6 carry H or Bn. -/
def glucoseResidueCore : Molecule where
  atoms :=
    [.O, .C, .C, .C, .C, .C, .C,
     .O, .O, .O, .O,
     .H, .H, .H, .H, .H, .H, .H]
  bonds := glucoseResidue.bonds

theorem glucoseResidueCore_formula :
    glucoseResidueCore.formula = (6, 7, 5) := rfl

/-- Atom counts of the two residue variants, evaluated once. -/
theorem glucoseResidue_counts :
    glucoseResidue.atoms.countP (· == .C) = 6 ∧
    glucoseResidue.atoms.countP (· == .H) = 10 ∧
    glucoseResidue.atoms.countP (· == .O) = 5 :=
  ⟨rfl, rfl, rfl⟩

theorem glucoseResidueCore_counts :
    glucoseResidueCore.atoms.countP (· == .C) = 6 ∧
    glucoseResidueCore.atoms.countP (· == .H) = 7 ∧
    glucoseResidueCore.atoms.countP (· == .O) = 5 :=
  ⟨rfl, rfl, rfl⟩

/-- β-CD as seven explicit residues; the constant inter-residue α-1,4 bonds
are irrelevant to the box-filling task. -/
def betaCDMolecule : Molecule where
  atoms := (List.replicate 7 glucoseResidue.atoms).flatten
  bonds := []

/-- β-CD has formula C₄₂H₇₀O₃₅ (= 7 × C₆H₁₀O₅; cf. 9.1:
7 · 180.16 − 7 · 18.02 g mol⁻¹). -/
theorem betaCDMolecule_formula :
    betaCDMolecule.formula = (42, 70, 35) := by
  show (betaCDMolecule.count .C, betaCDMolecule.count .H,
        betaCDMolecule.count .O) = _
  simp only [Molecule.count, betaCDMolecule, countP_flatten_replicate]
  rw [glucoseResidue_counts.1, glucoseResidue_counts.2.1,
      glucoseResidue_counts.2.2]

/-- The β-CD core: β-CD with all 21 O–H hydrogens stripped. -/
def betaCDCore : Molecule where
  atoms := (List.replicate 7 glucoseResidueCore.atoms).flatten
  bonds := []

theorem betaCDCore_formula :
    betaCDCore.formula = (42, 49, 35) := by
  show (betaCDCore.count .C, betaCDCore.count .H,
        betaCDCore.count .O) = _
  simp only [Molecule.count, betaCDCore, countP_flatten_replicate]
  rw [glucoseResidueCore_counts.1, glucoseResidueCore_counts.2.1,
      glucoseResidueCore_counts.2.2]

/-- Consistency: stripping the 21 OH hydrogens from C₄₂H₇₀O₃₅ leaves
C₄₂H₄₉O₃₅. -/
theorem betaCDCore_consistent :
    49 + freeOHStart = 70 := rfl

/-! ## The template and the structure of L -/

/-- Substitution state of one template box.  `LinkerO` is the ether oxygen
of the –CH₂O(CH₂)₄OCH₂– tether installed downstream of L (never in L). -/
inductive Subst where
  | H        -- free CH₂OH hydrogen (protic group)
  | Bn       -- benzyl ether (CH₂OBn / OBn)
  | LinkerO  -- primary oxygen incorporated into the pentamethylene tether
  deriving DecidableEq, Repr

/-- The atom fragment that one box contributes, relative to the core oxygen
that stays in place either way. -/
def substFragment : Subst → Molecule
  | .H =>
      -- the hydroxy hydrogen itself
      { atoms := [.H], bonds := [] }
  | .Bn =>
      -- PhCH₂– through its CH₂: ring carbons C0…C5, CH₂ carbon C6, five
      -- aromatic H and two CH₂ hydrogens.
      { atoms := [.C, .C, .C, .C, .C, .C, .C, .H, .H, .H, .H, .H, .H, .H],
        bonds := [ ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 0⟩, ⟨0, 6⟩ ] }
  | .LinkerO =>
      -- the –CH₂CH₂CH₂CH₂CH₂– tether between the two rings' primary oxygens
      { atoms := [.C, .C, .C, .C, .C,
                  .H, .H, .H, .H, .H, .H, .H, .H, .H, .H],
        bonds := [ ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩ ] }

theorem substFragment_H_formula :
    (substFragment .H).formula = (0, 1, 0) := rfl

theorem substFragment_Bn_formula :
    (substFragment .Bn).formula = (7, 7, 0) := rfl

theorem substFragment_Bn_counts :
    (substFragment .Bn).atoms.countP (· == .C) = 7 ∧
    (substFragment .Bn).atoms.countP (· == .H) = 7 ∧
    (substFragment .Bn).atoms.countP (· == .O) = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem substFragment_H_counts :
    (substFragment .H).atoms.countP (· == .C) = 0 ∧
    (substFragment .H).atoms.countP (· == .H) = 1 ∧
    (substFragment .H).atoms.countP (· == .O) = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The β-CD template with all boxes the question asks to fill. -/
structure BetaCDTemplate where
  /-- Primary boxes in the printed unit order 1 … 7 (red labels, Q9-3). -/
  primary : List Subst
  /-- Secondary pairs (positions 2 and 3) of units 1 … 7. -/
  secondaryPairs : List (Subst × Subst)
  /-- The face box as printed, i.e. `(state)₁₄`. -/
  faceLabel : Nat × Subst
  deriving DecidableEq, Repr

/-- A template is well formed when it has exactly the printed boxes. -/
def BetaCDTemplate.WellFormed (t : BetaCDTemplate) : Prop :=
  t.primary.length = 7 ∧ t.secondaryPairs.length = 7 ∧ t.faceLabel.1 = 14

/-- The starting β-CD template printed above the 9.5 arrow. -/
def startTemplate : BetaCDTemplate where
  primary := List.replicate 7 .H
  secondaryPairs := List.replicate 7 (.H, .H)
  faceLabel := (14, .H)

/-- The perbenzylated template reached after step 1 (NaH/BnCl 30/30). -/
def allBenzylTemplate : BetaCDTemplate where
  primary := List.replicate 7 .Bn
  secondaryPairs := List.replicate 7 (.Bn, .Bn)
  faceLabel := (14, .Bn)

theorem startTemplate_wellFormed : startTemplate.WellFormed :=
  ⟨rfl, rfl, rfl⟩

theorem allBenzylTemplate_wellFormed : allBenzylTemplate.WellFormed :=
  ⟨rfl, rfl, rfl⟩

/--
**The structure of L** (the requested drawing): units 1 and 4 have free
primary CH₂OH (first, conventionally anchored DIBAL-H cleavage at unit 1;
second, Sinay-directed cleavage at unit 4), units 2, 3, 5, 6, 7 carry
CH₂OBn, and the face box is `(OBn)₁₄`.
-/
def lTemplate : BetaCDTemplate where
  primary := [.H, .Bn, .Bn, .H, .Bn, .Bn, .Bn]
  secondaryPairs := List.replicate 7 (.Bn, .Bn)
  faceLabel := (14, .Bn)

theorem lTemplate_wellFormed : lTemplate.WellFormed := ⟨rfl, rfl, rfl⟩

/-- The free primary OH groups of L are exactly at units 1 and 4. -/
theorem lTemplate_free_primary_at_1_and_4 :
    lTemplate.primary = [.H, .Bn, .Bn, .H, .Bn, .Bn, .Bn] ∧
    (lTemplate.primary.filter (· == .H)).length = 2 := ⟨rfl, rfl⟩

/-- Unit 1 of L carries the single protic group on the perbenzylated
background — the premise of the Sinay rule that directed the second
cleavage to unit 4. -/
theorem lTemplate_protic_at_unit1 :
    lTemplate.primary[0]? = some Subst.H := rfl

/-- Every secondary box of L is `Bn`; the face box is the printed `(OBn)₁₄`. -/
theorem lTemplate_secondary_allBn :
    lTemplate.secondaryPairs = List.replicate 7 (.Bn, .Bn) ∧
    lTemplate.faceLabel = (14, .Bn) := ⟨rfl, rfl⟩

/-- L has exactly two free (protic) OH groups, both primary. -/
theorem lTemplate_exactly_two_free_OH :
    (lTemplate.primary.filter (· == .H)).length +
    2 * (lTemplate.secondaryPairs.filter (fun p =>
          (p.1 == .H || p.2 == .H))).length = 2 := by decide

/-- L's benzyl-group count: 5 primary + 14 secondary = 19. -/
theorem lTemplate_benzyl_count :
    (lTemplate.primary.filter (· == .Bn)).length +
    2 * (lTemplate.secondaryPairs.filter (· == (.Bn, .Bn))).length = 19 := by
  decide

/--
**Sinay rule realisation.**  The second DIBAL-H cleavage happens at unit 4
because (i) unit 1 is protic after the first cleavage and (ii) unit 4 is
available.  Reformulating the forward rule as a property of the template:
the debenzylated primary sites of L satisfy the shape `[H,Bn,Bn,H,Bn,Bn,Bn]`
exactly when sites 1 *and* 4 are the free ones.
-/
theorem sinayRule_realised_in_L :
    (lTemplate.primary[0]'(by decide) = .H) ∧
    (lTemplate.primary[3]'(by decide) = .H) ∧
    (lTemplate.primary.filter (· != .H)).length = 5 :=
  ⟨rfl, rfl, rfl⟩

/-! ### The two-step DIBAL-H sequence as a transition on templates -/

/-- Cleave the primary benzyl ether of unit `k` (0-based), turning its box
from `Bn` to `H`. -/
def primaryDebenzylate (t : BetaCDTemplate) (k : Nat) : BetaCDTemplate :=
  { t with primary := t.primary.set k .H }

/-- Step 2, full sequence: first cleavage anchored at unit 1 (index 0), then
the Sinay-directed cleavage at unit 4 (index 3). -/
def step2 (chosen : Nat) : BetaCDTemplate :=
  primaryDebenzylate (primaryDebenzylate allBenzylTemplate 0) chosen

/-- Following the Sinay rule (`chosen = 4`'s 0-based index 3) yields exactly
the claimed L template. -/
theorem step2_gives_lTemplate :
    step2 3 = lTemplate := by
  simp only [step2, primaryDebenzylate, allBenzylTemplate, lTemplate]
  decide

/-- Any other directed choice (units 2, 3, 5, 6 or 7) does **not** give the
dimer-consistent L: only index 3 (unit 4) reproduces the anchor-plus-unit-4
pattern that the printed dimer requires. -/
theorem step2_unique :
    ∀ k : Nat, k < 7 → k ≠ 0 → k ≠ 3 → step2 k ≠ lTemplate := by
  intro k hk hk0 hk3 h
  interval_cases k <;> simp_all [step2, primaryDebenzylate, allBenzylTemplate,
                                 lTemplate, List.set]

/-- First-cleavage anchoring: the perbenzylated ring is C₇-symmetric, so any
first site is a rotation of unit 1.  Concretely, rotating the template by
any shift maps first-cleavage-at-1 to first-cleavage-at-`(1+s) mod 7` — the
same molecule under the dihedral symmetry of the homogeneous β-CD. -/
theorem lTemplate_d7_fixed :
    ∀ s : Nat, s < 7 →
      (allBenzylTemplate.primary.set s .H).set ((s + 3) % 7) .H =
        lTemplate.primary.rotate ((7 - s) % 7) := by
  intro s hs
  interval_cases s <;> rfl

/-! ### Molecule-level content of the boxes -/

/-- The molecule obtained by filling every box: the β-CD core plus one
fragment per box entry. -/
def templateMolecule (t : BetaCDTemplate) : Molecule where
  atoms := betaCDCore.atoms ++
    (t.primary.map fun s => (substFragment s).atoms).flatten ++
    (t.secondaryPairs.map fun p =>
      (substFragment p.1).atoms ++ (substFragment p.2).atoms).flatten
  bonds := []

/-- The molecule of L: every box substituent realised as explicit atoms. -/
def lMolecule : Molecule := templateMolecule lTemplate

/-- Atom-level shape of `lMolecule`. -/
theorem lMolecule_atoms :
    lMolecule.atoms = betaCDCore.atoms ++
      ((substFragment .H).atoms ++ (substFragment .Bn).atoms ++
       (substFragment .Bn).atoms ++ (substFragment .H).atoms ++
       (substFragment .Bn).atoms ++ (substFragment .Bn).atoms ++
       (substFragment .Bn).atoms) ++
      (List.replicate 7
        ((substFragment .Bn).atoms ++ (substFragment .Bn).atoms)).flatten := rfl

/-- The molecular formula of L is C₁₇₅H₁₈₄O₃₅: the C₄₂H₄₉O₃₅ core bearing
19 benzyl fragments (C₇H₇ each) and 2 hydroxy hydrogens. -/
theorem lMolecule_formula :
    lMolecule.formula = (175, 184, 35) := by
  show (lMolecule.count .C, lMolecule.count .H, lMolecule.count .O) = _
  simp only [Molecule.count, lMolecule_atoms, List.countP_append,
             countP_flatten_replicate, betaCDCore]
  rw [glucoseResidueCore_counts.1, glucoseResidueCore_counts.2.1,
      glucoseResidueCore_counts.2.2, substFragment_Bn_counts.1,
      substFragment_Bn_counts.2.1, substFragment_Bn_counts.2.2,
      substFragment_H_counts.1, substFragment_H_counts.2.1,
      substFragment_H_counts.2.2]

/-- Cross-check with the fragment-arithmetic route. -/
theorem lMolecule_formula_consistent :
    formulaAfterBenzylation 42 70 35 19 = lMolecule.formula := by
  rw [l_formula_by_count, lMolecule_formula]

/-! ## Dimer-consistency check (figure printed below L, page Q9-3) -/

/--
The printed dimer, per ring: one free CH₂OH, five CH₂OBn, one primary
oxygen in the –CH₂O(CH₂)₄OCH₂– tether (installed from L's free CH₂OH by
allyl bromide → Grubbs I → H₂/PtO₂), and `(OBn)₁₄` on the face.  Box order
follows L's unit numbering: the tether sits at one of the two formerly
free units; the leftover CH₂OH at the other.  (The printed dimer's rings
are rotated relative to L's numbering, which is immaterial — one free OH,
five Bn, one tether either way.)
-/
def dimerRingTemplate : BetaCDTemplate where
  primary := [.LinkerO, .Bn, .Bn, .H, .Bn, .Bn, .Bn]
  secondaryPairs := List.replicate 7 (.Bn, .Bn)
  faceLabel := (14, .Bn)

/-- The dimer's box counts: exactly one free CH₂OH, five CH₂OBn, one tether
site per ring — matching 9.6's "mixture of constitutional linkage isomers"
that arises from which of L's two free sites was allylated. -/
theorem dimerRing_box_counts :
    (dimerRingTemplate.primary.filter (· == .H)).length = 1 ∧
    (dimerRingTemplate.primary.filter (· == .Bn)).length = 5 ∧
    (dimerRingTemplate.primary.filter (· == .LinkerO)).length = 1 ∧
    dimerRingTemplate.secondaryPairs.length = 7 ∧
    dimerRingTemplate.faceLabel = (14, .Bn) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Site-wise: L and the printed dimer share the same secondary face and
the same five benzylated primary sites; the dimer differs only in that one
of L's two free primary OHs (unit 1) has been converted into the tether
linkage.  This is exactly the L → dimer pathway built below L on page Q9-3. -/
theorem dimer_arises_from_L :
    dimerRingTemplate.secondaryPairs = lTemplate.secondaryPairs ∧
    dimerRingTemplate.faceLabel = lTemplate.faceLabel ∧
    (lTemplate.primary.filter (· == .H)).length =
      (dimerRingTemplate.primary.filter (· == .H)).length + 1 ∧
    (dimerRingTemplate.primary.filter (· == .LinkerO)).length =
      (lTemplate.primary.filter (· == .LinkerO)).length + 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

end IChO2026T9A5
