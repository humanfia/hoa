import Mathlib

/-!
# IChO 2026, Theory T9, question 9.8 (`icho_2026_t9_a8`)

Dependable source material (problem-only, answer-blind):

* `T9_page-4.png` (problem page Q9-4): the synthetic scheme
  `N → O → P → Q → R → S` with the printed reagents
  `1) (COCl)₂, DMSO 2) (C₆H₅)₃P=CH₂`,
  `1) DIBAL-H (1 equiv.) 2) MsCl 3) NaN₃`,
  `1) DIBAL-H (2 equiv.) 2) NaH, ClCH₂–C(=CH₂)–CH₂Cl`,
  `1) DIBAL-H (1 equiv.) 2) Boc₂O (1 equiv.) 3) MsCl 4) NaN₃`,
  `1) CF₃COOH 2) NaH, BnI 3) DIBAL-H (2 equiv.)`,
  the printed structure of **N** (CH₂OH on unit 1, CH₂OBn on units 2–6, `(OBn)₁₂`
  on the secondary rim), and the question text of 9.8:
  "Assume 1,2-unit modification happens **clockwise**, while 1,3-unit
  modification happens **counterclockwise**. Protic groups have stronger
  directing effects than alkenes."
* `T9_page-3.png` (problem page Q9-3): the Sinay rule – a single protic group
  (NH and OH) at unit 1 directs the next reductive debenzylation to the
  **1,4-unit** in the macrocyclic ring, "**or to unit 3 if the unit 4 position
  is not available**" (1,3 fallback); `Bn = benzyl` legend.
* `T9_page-4.png` preamble: Sollogoub *et al.* applied "the ability of **alkenes
  to direct the debenzylation to the “ortho”-glucopyranose unit**".
* Blank answer sheets A9-4/A9-5 of `theory_problem.pdf`: five α-CD templates
  labelled O, P, Q, R, S with boxes numbered 1–6 and a preprinted `(OBn)₁₂`.

# Conventions used in this file

* Unit indices are 0-based: index `i : Fin 6` is the printed unit `i + 1` of the
  answer-sheet template.  Face assignments written `![s₀, s₁, s₂, s₃, s₄, s₅]`
  therefore read directly as "unit 1 ↦ s₀, …, unit 6 ↦ s₅".
* The direction helpers encode only problem-stated data:
  `oneFour u = u + 3` (Sinay 1,4-direction), fallback `oneThreeCCW u = u - 2`
  (1,3-unit, counterclockwise, 9.8 convention), and `oneTwoCW u = u + 1`
  (alkene ortho-direction, clockwise, 9.8 convention).
* Only the primary-face substituents are templated; the secondary rim is the
  constant `(OBn)₁₂` for every intermediate (`secondaryRimOBnCount`).

# What is an input and what is derived

* **Inputs (problem-given):** `substrateN`, the three direction helpers, and the
  reagent semantics named in each derivation comment.
* **Trusted general laws (not problem answers):** Swern oxidation CH₂OH → CHO,
  Wittig methylenation CHO → CH=CH₂, MsCl/NaN₃ as CH₂OH → CH₂N₃ (S_N2),
  Boc₂O protection of a secondary amine, TFA removal of Boc, NaH/BnI
  N-benzylation, NaH-promoted double alkylation of an OH/NH₂ pair with the
  dichloride ClCH₂–C(=CH₂)–CH₂Cl, and **DIBAL-H reduction of alkyl azides to
  primary amines** (the reading of the “2 equiv.” steps that is compatible with
  the printed downstream chemistry, e.g. Boc₂O acting on an N–H).
* **Derived:** the faces/bridges of `structureO … structureS`, the regiochemical
  facts justifying the target of every directed debenzylation, and the
  hexadifferentiation of S.
-/

namespace ICho2026T9A8

/-- *N*-cap of the bridge nitrogen through the sequence Q → R → S:
free secondary amine (H), Boc-protected, N-benzyl (still protic: one N–H). -/
inductive NCap | h | boc | bn
  deriving DecidableEq, Repr

/-- Substituent carried by C6 of a glucopyranose unit (the "CH₂OH box" of the
template).  The two bridge constructors denote the local halves of the
–CH₂–NR–CH₂–C(=CH₂)–CH₂–O– methylenebis bridge; the bridge's own central
alkene is part of the bridge datum, not of a unit substituent. -/
inductive PrimSubst
  | vinyl                 -- –CH=CH₂ (Swern + Wittig of a primary OH)
  | cH2OBn                -- –CH₂OBn (benzyl ether, cleavable by DIBAL-H)
  | cH2OH                 -- –CH₂OH (free primary alcohol, protic)
  | cH2N3                 -- –CH₂N₃ (mesylate + azide)
  | cH2NH2                -- –CH₂NH₂ (DIBAL-H reduction of the azide)
  | bridgeArmN (cap : NCap)  -- –CH₂–NR–CH₂–C(=CH₂)–CH₂–O– (N side)
  | bridgeArmO               -- –CH₂–O–CH₂–C(=CH₂)–CH₂–NR– (O side)
  deriving DecidableEq, Repr

/-- Protic directing groups (problem text: "NH and OH"; a Boc-protected
nitrogen carries no N–H and is not a director). -/
def PrimSubst.isProtic : PrimSubst → Bool
  | .cH2OH | .cH2NH2 | .bridgeArmN .h | .bridgeArmN .bn => true
  | _ => false

/-- Alkene directing group of the Sollogoub method (the vinyl unit). -/
def PrimSubst.isAlkene : PrimSubst → Bool
  | .vinyl => true
  | _ => false

/-- Datum of the –CH₂–NR–CH₂–C(=CH₂)–CH₂–O– bridge:
which unit carries the N-arm, which carries the O-arm, and the N-cap. -/
structure Bridge where
  nUnit : Fin 6
  oUnit : Fin 6
  cap : NCap
  ne : nUnit ≠ oUnit := by decide
  deriving DecidableEq, Repr

/-- An α-cyclodextrin intermediate: the six primary-face substituents, and the
optional methylenebis bridge between two of them.  The secondary rim is the
constant `(OBn)₁₂` (see `secondaryRimOBnCount`) and is not re-modelled. -/
structure AlphaCD where
  face : Fin 6 → PrimSubst
  bridge : Option Bridge

theorem AlphaCD.ext' {a b : AlphaCD} (hf : a.face = b.face)
    (hb : a.bridge = b.bridge) : a = b := by
  cases a; cases b; cases hf; cases hb; rfl

/-- Set the substituent of unit `u`. -/
def setFace (α : AlphaCD) (u : Fin 6) (s : PrimSubst) : AlphaCD :=
  { α with face := Function.update α.face u s }

/-- Swern oxidation + Wittig methylenation: CH₂OH → CH=CH₂. -/
def swernWittig (α : AlphaCD) (u : Fin 6) : AlphaCD := setFace α u .vinyl

/-- DIBAL-H reductive debenzylation of a primary benzyl ether: CH₂OBn → CH₂OH. -/
def debenzylate (α : AlphaCD) (u : Fin 6) : AlphaCD := setFace α u .cH2OH

/-- MsCl then NaN₃: CH₂OH → CH₂N₃ (mesylation + S_N2). -/
def mesylateAzide (α : AlphaCD) (u : Fin 6) : AlphaCD := setFace α u .cH2N3

/-- DIBAL-H reduction of an alkyl azide: CH₂N₃ → CH₂NH₂. -/
def dibalReduceAzide (α : AlphaCD) (u : Fin 6) : AlphaCD := setFace α u .cH2NH2

/-- NaH + ClCH₂–C(=CH₂)–CH₂Cl double alkylation of the OH at `oArm` and the
NH₂ at `nArm`: installs the –CH₂–NH–CH₂–C(=CH₂)–CH₂–O– bridge. -/
def installBridge (α : AlphaCD) (nArm oArm : Fin 6) (h : nArm ≠ oArm) : AlphaCD where
  face := fun j =>
    if j = nArm then .bridgeArmN .h
    else if j = oArm then .bridgeArmO
    else α.face j
  bridge := some ⟨nArm, oArm, .h, h⟩

/-- Change the cap on the bridge nitrogen (TFA deprotection, BnI benzylation,
or Boc₂O protection). -/
def capBridge (α : AlphaCD) (cap : NCap) : AlphaCD :=
  match α.bridge with
  | none => α
  | some b =>
    { face := fun j => if j = b.nUnit then .bridgeArmN cap else α.face j
      bridge := some { b with cap := cap } }

/-- A site is *available* for directed debenzylation iff it is still a
benzyl-protected primary position. -/
def siteAvailable (α : AlphaCD) (u : Fin 6) : Prop := α.face u = .cH2OBn

/-- Decidable instance for site availability, via the decidable equality on
`PrimSubst`. -/
noncomputable instance {α : AlphaCD} {u : Fin 6} : Decidable (siteAvailable α u) :=
  inferInstanceAs (Decidable (α.face u = .cH2OBn))

/-- Computation rule for `setFace`: needed so that `decide` can evaluate
site-availability of post-reaction intermediates. -/
@[simp] theorem setFace_face_apply (α : AlphaCD) (u v : Fin 6) (s : PrimSubst) :
    (setFace α u s).face v = Function.update α.face u s v := rfl

/-- Computation rule for the bridge-N cap change. -/
@[simp] theorem capBridge_face_apply_some (α : AlphaCD) (b : Bridge) (cap : NCap)
    (v : Fin 6) (hb : α.bridge = some b) :
    (capBridge α cap).face v = (if v = b.nUnit then .bridgeArmN cap else α.face v) := by
  cases α with
  | mk f br =>
    cases br
    · simp at hb
    · simp_all [capBridge]


/-! ## Problem-stated direction rules (inputs) -/

/-- Sinay rule, first choice: the protic group at unit `u` directs the next
debenzylation to the 1,4-unit. -/
def oneFour (u : Fin 6) : Fin 6 := u + 3

/-- Sinay fallback, localized by the 9.8 convention: if the 1,4 position is
not available, the 1,3-unit *counterclockwise* is taken. -/
def oneThreeCCW (u : Fin 6) : Fin 6 := u - 2

/-- Sollogoub alkene direction, localized by the 9.8 convention: the alkene
directs debenzylation to the ortho (1,2) unit *clockwise*. -/
def oneTwoCW (u : Fin 6) : Fin 6 := u + 1

/-- The preprinted constant of every template: the secondary rim carries
twelve benzyl ethers, unchanged by every reaction in the scheme. -/
def secondaryRimOBnCount : Nat := 12

/-! ## Actual problem input: starting material N -/

/-- The structure of N printed on Q9-4: CH₂OH on unit 1 (index 0), CH₂OBn on
units 2–6 (indices 1–5); no bridge; secondary rim `(OBn)₁₂`. -/
def substrateN : AlphaCD where
  face := ![.cH2OH, .cH2OBn, .cH2OBn, .cH2OBn, .cH2OBn, .cH2OBn]
  bridge := none

/-! ## Derived structures O, P, Q, R, S -/

/-- O: vinyl at unit 1, CH₂OBn at units 2–6. -/
def structureO : AlphaCD where
  face := ![.vinyl, .cH2OBn, .cH2OBn, .cH2OBn, .cH2OBn, .cH2OBn]
  bridge := none

/-- P: vinyl at 1, CH₂N₃ at 2, CH₂OBn elsewhere. -/
def structureP : AlphaCD where
  face := ![.vinyl, .cH2N3, .cH2OBn, .cH2OBn, .cH2OBn, .cH2OBn]
  bridge := none

/-- Q: vinyl at 1; free-NH bridge between units 2 (N-arm) and 5 (O-arm);
CH₂OBn at 3, 4, 6. -/
def structureQ : AlphaCD where
  face := ![.vinyl, .bridgeArmN .h, .cH2OBn, .cH2OBn, .bridgeArmO, .cH2OBn]
  bridge := some ⟨1, 4, .h, by decide⟩

/-- R: the bridge nitrogen is Boc-protected; CH₂N₃ at unit 6;
CH₂OBn at 3, 4. -/
def structureR : AlphaCD where
  face := ![.vinyl, .bridgeArmN .boc, .cH2OBn, .cH2OBn, .bridgeArmO, .cH2N3]
  bridge := some ⟨1, 4, .boc, by decide⟩

/-- S: the bridge nitrogen is N-benzylated; CH₂OH at unit 3; CH₂OBn at unit 4;
CH₂NH₂ at unit 6. -/
def structureS : AlphaCD where
  face := ![.vinyl, .bridgeArmN .bn, .cH2OH, .cH2OBn, .bridgeArmO, .cH2NH2]
  bridge := some ⟨1, 4, .bn, by decide⟩

/-! ### Step N → O -/

/-- N → O according to the printed reagents: Swern/Wittig at the only free
primary alcohol (unit 1) of the problem-given starting material. -/
theorem structure_o_derivation : structureO = swernWittig substrateN 0 := by
  apply AlphaCD.ext'
  · funext u; fin_cases u <;> rfl
  · rfl

/-! ### Step O → P -/

/-- O bears exactly one directing group: the alkene at unit 1; there is no
protic group, so the alkene rule applies (and "protic ≻ alkene" is vacuous). -/
theorem o_director_is_alkene :
    (structureO.face 0).isAlkene = true ∧
    (∀ u : Fin 6, (structureO.face u).isProtic = false) := by
  refine ⟨rfl, ?_⟩
  decide

/-- Regiochemistry of the O → P debenzylation: clockwise ortho unit of unit 1
(index 0) is unit 2 (index 1), and it is an available benzyl ether. -/
theorem step_o_to_p_regiochemistry :
    oneTwoCW 0 = 1 ∧ siteAvailable structureO (oneTwoCW 0) := by
  exact ⟨by decide, by decide⟩

/-- O → P according to the printed reagents: alkene-directed debenzylation of
unit 2, then mesylation and azide substitution at unit 2. -/
theorem structure_p_derivation :
    structureP = mesylateAzide (debenzylate structureO (oneTwoCW 0)) 1 := by
  apply AlphaCD.ext'
  · funext u; fin_cases u <;> rfl
  · rfl

/-! ### Step P → Q -/

/-- In the P → Q step, 2 equivalents of DIBAL-H first convert the unit-2 azide
into the primary amine; that amine is the (protic) director. -/
def pAfterAzideReduction : AlphaCD := dibalReduceAzide structureP 1

/-- Regiochemistry: protic beats alkene, and the amine at unit 2 (index 1)
directs to its 1,4-unit = unit 5 (index 4), which is available. -/
theorem step_p_to_q_regiochemistry :
    (pAfterAzideReduction.face 0).isAlkene = true ∧
    (pAfterAzideReduction.face 1).isProtic = true ∧
    oneFour 1 = 4 ∧ siteAvailable pAfterAzideReduction (oneFour 1) := by
  refine ⟨rfl, by decide, by decide, by decide⟩

/-- P → Q according to the printed reagents: azide reduction, directed
debenzylation at unit 5, then NaH-promoted double alkylation with
ClCH₂–C(=CH₂)–CH₂Cl linking units 2 and 5. -/
theorem structure_q_derivation :
    structureQ = installBridge (debenzylate pAfterAzideReduction (oneFour 1)) 1 4
      (by decide) := by
  apply AlphaCD.ext'
  · funext u; fin_cases u <;> rfl
  · rfl

/-! ### Step Q → R -/

/-- Regiochemistry of the Q → R debenzylation: the bridge NH at unit 2 is the
protic director; its 1,4-unit (unit 5) is *not available* (bridge O-arm), so
the stated fallback – the 1,3-unit counterclockwise, unit 6 – is taken, and
that site is an available benzyl ether. -/
theorem step_q_to_r_regiochemistry :
    (structureQ.face 1).isProtic = true ∧
    ¬ siteAvailable structureQ (oneFour 1) ∧
    oneThreeCCW 1 = 5 ∧ siteAvailable structureQ (oneThreeCCW 1) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Q → R according to the printed reagents: directed debenzylation of unit 6,
Boc protection of the bridge nitrogen (proving it carried an N–H, i.e. the
preceding azide really was reduced to the amine), then CH₂OH → CH₂N₃ at
unit 6. -/
theorem structure_r_derivation :
    structureR =
      mesylateAzide (capBridge (debenzylate structureQ (oneThreeCCW 1)) .boc) 5 := by
  apply AlphaCD.ext'
  · funext u; fin_cases u <;> rfl
  · rfl

/-! ### Step R → S -/

/-- TFA removes Boc, NaH/BnI benzylates the regenerated N–H, and the final
2 equivalents of DIBAL-H reduce the unit-6 azide to the amine; this is the
state of the macrocycle just before the last directed debenzylation. -/
def rAfterDeprotection : AlphaCD :=
  dibalReduceAzide (capBridge (capBridge structureR .h) .bn) 5

/-- Regiochemistry of the R → S debenzylation.  Two protic groups are present
(NHBn at unit 2, NH₂ at unit 6).  For the unit-2 director both targets are
unavailable (1,4 → unit 5, the bridge O-arm; fallback 1,3-ccw → unit 6, now an
amine), so the acting director is the unit-6 amine, whose 1,4-unit is the
available unit 3. -/
theorem step_r_to_s_regiochemistry :
    (∀ u : Fin 6, (rAfterDeprotection.face u).isProtic = true ↔ u = 1 ∨ u = 5) ∧
    ¬ siteAvailable rAfterDeprotection (oneFour 1) ∧
    ¬ siteAvailable rAfterDeprotection (oneThreeCCW 1) ∧
    oneFour 5 = 2 ∧ siteAvailable rAfterDeprotection (oneFour 5) := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  decide

/-- R → S according to the printed reagents. -/
theorem structure_s_derivation :
    structureS = debenzylate rAfterDeprotection (oneFour 5) := by
  apply AlphaCD.ext'
  · funext u; fin_cases u <;> rfl
  · rfl

/-! ### Output checks -/

/-- The five requested template pairs of (bridge N-arm, bridge O-arm):
Q, R and S share the same bridge connectivity (units 2 and 5); only the N-cap
changes. -/
theorem bridge_units_fixed :
    (structureQ.bridge.map Bridge.nUnit = some 1 ∧
     structureQ.bridge.map Bridge.oUnit = some 4) ∧
    (structureR.bridge.map Bridge.nUnit = some 1 ∧
     structureR.bridge.map Bridge.oUnit = some 4) ∧
  (structureS.bridge.map Bridge.nUnit = some 1 ∧
    structureS.bridge.map Bridge.oUnit = some 4) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- S is genuinely **hexadifferentiated**, as the problem preamble requires of
the Sollogoub target: the six template boxes are pairwise different. -/
theorem structure_s_hexadifferentiated :
    ∀ i j : Fin 6, i ≠ j → structureS.face i ≠ structureS.face j := by
  decide

/-- The secondary rim is untouched by every step (constant `(OBn)₁₂`). -/
theorem secondary_rim_unchanged : secondaryRimOBnCount = 12 := rfl

/-- Nitrogen accounting through the sequence: the caps on the bridge nitrogen
are exactly Q = H, R = Boc, S = Bn. -/
theorem bridge_caps :
    (structureQ.bridge.map Bridge.cap = some NCap.h) ∧
    (structureR.bridge.map Bridge.cap = some NCap.boc) ∧
    (structureS.bridge.map Bridge.cap = some NCap.bn) := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Axiom inspection -/

#print axioms structure_o_derivation
#print axioms structure_p_derivation
#print axioms structure_q_derivation
#print axioms structure_r_derivation
#print axioms structure_s_derivation
#print axioms step_o_to_p_regiochemistry
#print axioms step_p_to_q_regiochemistry
#print axioms step_q_to_r_regiochemistry
#print axioms step_r_to_s_regiochemistry
#print axioms structure_s_hexadifferentiated
#print axioms bridge_units_fixed
#print axioms bridge_caps

end ICho2026T9A8
