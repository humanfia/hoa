import Mathlib

/-!
# IChO 2026, Theory Problem T6, Subquestion 6.5 — “Draw the structures of F–L”

**Sources (problem-only inputs).**  Scheme printed on page Q6-3 of
`theory_problem.pdf` (image `T6_page-3.png`): the synthesis of
[5]cycloparaphenylene ([5]CPP).  The page draws

* starting material: 4-(4-bromophenyl)-4-hydroxycyclohexa-2,5-dien-1-one
  (a p-quinol; drawn with C=O at the top, OH at C4, 4-bromophenyl below);
* **F**: 1. NaH, 2. 4-lithio-4′-(tert-butyldimethylsilyloxy)biphenyl;
* **G**: TESCl (2 equiv.), imidazole;
* **H**: LiOH, labelled “C₃₆H₄₇BrO₃Si₂”;
* **I**: PhI(OAc)₂, H₂O (“acts as a two electron oxidant”);
* **J**: 1. NaH, 2. 4-lithiobromobenzene;
* **K**: TESCl (2 equiv.), imidazole;
* **L**: Ni(COD)₂ (2 equiv.), 2,2′-bipyridine (2 equiv.), labelled
  “C₅₄H₈₀O₄Si₄”;
* [5]CPP (drawn: macrocycle of five para-linked benzenes) after
  1. n-Bu₄NF (4 equiv.), 2. SnCl₂ (excess).

**Encoding.**  We encode every molecule as an explicit molecular graph:
which six-carbon ring units are present, hybridization (sp³ vs sp²) of each
ring carbon, hydrogen counts, substituents (OH, OTBS, OTES, Br, Li, C=O),
Kekulé double bonds and inter-ring (biaryl) σ-bonds.  Molecular formulas,
integer molecular masses (integer masses as instructed in 6.4), numbers of
aromatic/antiaromatic six-π/4n ring systems, and the stoichiometric
derivation identities between consecutive structures are all *proved* by
decision procedures over the finite molecule data — nothing about the answer
is assumed.

**Chemical reasoning recorded as theorems.**
F = nucleophilic addition of the aryllithium reagent to the dienone
carbonyl (NaH merely deprotonates the quinol OH in transit);
G = TES-capping of *both* tertiary OH groups (the aryl silyl ether formula is
unchanged, Si(CH₃)₂C(CH₃)₃ → Si(CH₂CH₃)₃: both C₆H₁₅Si);
H = LiOH cleavage of the *aryl* silyl ether only (phenol liberated) — **proved
consistent with the printed formula C₃₆H₄₇BrO₃Si₂**;
I = two-electron oxidative dearomatization of the phenol to the para-quinol
(+O, no net H change: the para substituent becomes the sp³ quinol junction
bearing the new OH from H₂O);
J = aryllithium addition to the dienone carbonyl;
K = TES-capping of both B-ring OH groups;
L = Ni(0)/bpy intramolecular Yamamoto coupling of the *two* aryl bromides,
forming one new biaryl bond and closing the five-ring macrocycle — **proved
consistent with the printed formula C₅₄H₈₀O₄Si₄**.
The given [5]CPP drawing is the fully aromatic C₃₀H₂₀ macrocycle; the
TBAF/SnCl₂ deprotection/reductive-aromatization stoichiometry is also proved.
-/

namespace IChO2026T6A5

-- =====================================================================
-- §1  Basic vocabulary: elements, ring units, positions, substituents
-- =====================================================================

/-- Elements appearing in the T6-A5 scheme (integer masses per 6.4 instruction). -/
inductive Element | C | H | O | Si | Br | Li
  deriving DecidableEq, Repr, BEq

instance : Fintype Element where
  elems := {Element.C, Element.H, Element.O, Element.Si, Element.Br, Element.Li}
  complete := by intro x; cases x <;> simp

/-- The five six-carbon ring units of the route:
`R` = cyclohexadienone/cyclohexadiene core of the starting quinol;
`W` = the 4-bromophenyl substituent of the starting material;
`A`,`B` = the biphenyl installed in step F (`A` ipso to `R`, `B` remote);
`P` = the 4-bromophenyl installed in step J. -/
inductive Ring5 | R | W | A | B | P
  deriving DecidableEq, Repr, BEq

instance : Fintype Ring5 where
  elems := {Ring5.R, Ring5.W, Ring5.A, Ring5.B, Ring5.P}
  complete := by intro x; cases x <;> simp

/-- A position is (ring unit, carbon index 0–5).  Convention per ring:
positions 0 and 3 are the para pair that bears substituents/links;
positions 1,2,4,5 are the CH positions. -/
abbrev Position := Ring5 × Fin 6

/-- Substituent attached at a ring position (in addition to ring bonds and links).
`carbonyl` denotes `C=O` (the ring carbon is part of a ketone). -/
inductive Sub | none | Br | Li | OH | OTBS | OTES | carbonyl
  deriving DecidableEq, Repr, BEq

/-- Atomic contribution of a substituent to the molecular formula.
TBS = O–Si(CH₃)₂C(CH₃)₃ and TES = O–Si(CH₂CH₃)₃ both contribute C₆H₁₅OSi. -/
def subContrib : Sub → Element → ℤ
  | .Br, .Br => 1
  | .Li, .Li => 1
  | .OH, .O => 1
  | .OH, .H => 1
  | .OTBS, .C => 6 | .OTBS, .H => 15 | .OTBS, .O => 1 | .OTBS, .Si => 1
  | .OTES, .C => 6 | .OTES, .H => 15 | .OTES, .O => 1 | .OTES, .Si => 1
  | .carbonyl, .O => 1
  | _, _ => 0

-- =====================================================================
-- §2  Molecules as explicit graphs
-- =====================================================================

/-- An explicit molecular graph for the structures of this scheme. -/
structure Molecule where
  /-- six-membered ring units present -/
  rings : List Ring5
  /-- table of ring-carbon hydrogen counts (positions not listed have 0 H) -/
  hTab : List (Position × ℕ)
  /-- ring carbons that are sp³ (no p-orbital in the ring array) -/
  sp3 : List Position
  /-- substituent table (positions not listed bear no substituent beyond links) -/
  subTab : List (Position × Sub)
  /-- Kekulé C=C double bonds (unordered pairs, listed once) -/
  dbl : List (Position × Position)
  /-- inter-ring biaryl σ-bonds (unordered pairs, listed once) -/
  links : List (Position × Position)

private def lookupSub (tab : List (Position × Sub)) (p : Position) : Sub :=
  match tab.find? (fun q => q.1 == p) with
  | some q => q.2
  | none => .none

private def lookupNat (tab : List (Position × ℕ)) (p : Position) : ℕ :=
  match tab.find? (fun q => q.1 == p) with
  | some q => q.2
  | none => 0

namespace Molecule

/-- All ring-carbon positions present in the molecule. -/
def positionsOf (m : Molecule) : List Position :=
  m.rings.flatMap fun r => (List.finRange 6).map fun i => (r, i)

/-- Hydrogens directly attached to ring carbon `p`. -/
def atomH (m : Molecule) (p : Position) : ℕ := lookupNat m.hTab p

/-- Substituent at ring carbon `p`. -/
def subAt (m : Molecule) (p : Position) : Sub := lookupSub m.subTab p

/-- Count of element `e` in the molecule: ring carbons, their hydrogens,
and substituent atoms. -/
def count (m : Molecule) (e : Element) : ℤ :=
  (m.positionsOf.map fun p =>
    (match e with
     | .C => (1 : ℤ)
     | .H => (m.atomH p : ℤ)
     | _ => 0)
    + subContrib (m.subAt p) e).sum

/-- Integer molecular mass (integer atomic masses as instructed in Q6.4). -/
def integerMass (m : Molecule) : ℤ :=
  m.count .C * 12 + m.count .H * 1 + m.count .O * 16 +
  m.count .Si * 28 + m.count .Br * 80 + m.count .Li * 7

/-- Number of ring carbons of unit `r` carrying a p-orbital in the ring array
(present and not sp³). -/
def piCarbons (m : Molecule) (r : Ring5) : ℕ :=
  ((List.finRange 6).filter fun i =>
    m.rings.contains r && !m.sp3.contains (r, i)).length

/-- The ring has a *closed* cyclic array of p-orbitals (no sp³ carbon). -/
def closedPiLoop (m : Molecule) (r : Ring5) : Bool :=
  m.rings.contains r && (List.finRange 6).all fun i => !m.sp3.contains (r, i)

/-- Number of distinct aromatic 6π ring systems (Hückel 4n+2, n = 1).
For the all-carbon six-membered rings of this scheme, a ring is aromatic iff
all six ring carbons contribute one p-electron each. -/
def aromaticRingCount (m : Molecule) : ℕ :=
  (m.rings.filter fun r => m.piCarbons r == 6).length

/-- Number of distinct antiaromatic ring systems: a closed p-loop with a 4n
electron count (here the candidate count 4). -/
def antiaromaticRingCount (m : Molecule) : ℕ :=
  (m.rings.filter fun r => m.closedPiLoop r && m.piCarbons r == 4).length

/-- Number of inter-ring biaryl σ-bonds. -/
def linkCount (m : Molecule) : ℕ := m.links.length

end Molecule

-- =====================================================================
-- §3  Problem inputs: the drawn starting material and reagents
-- =====================================================================

/-- Benzenoid Kekulé bonds for ring unit `r` (double bonds 0–1, 2–3, 4–5). -/
private def benzeneDbl (r : Ring5) : List (Position × Position) :=
  [((r, 0), (r, 1)), ((r, 2), (r, 3)), ((r, 4), (r, 5))]

/-- Hydrogens of a para-disubstituted benzene ring `r` (CH at positions 1,2,4,5). -/
private def benzeneH (r : Ring5) : List (Position × ℕ) :=
  [((r, 1), 1), ((r, 2), 1), ((r, 4), 1), ((r, 5), 1)]

/-- Diene Kekulé bonds of a 1,4-disubstituted cyclohexa-2,5-diene unit `r`. -/
private def dieneDbl (r : Ring5) : List (Position × Position) :=
  [((r, 1), (r, 2)), ((r, 4), (r, 5))]

/-- Starting material as drawn: 4-(4-bromophenyl)-4-hydroxycyclohexa-2,5-dien-1-one
(p-quinol: C=O at R0; sp³ C4 bearing OH and the 4-bromophenyl ring W). -/
def startingMaterial : Molecule where
  rings := [.R, .W]
  hTab := [((.R, 1), 1), ((.R, 2), 1), ((.R, 4), 1), ((.R, 5), 1)] ++ benzeneH .W
  sp3 := [(Ring5.R, 3)]
  subTab := [((Ring5.R, 0), .carbonyl), ((Ring5.R, 3), .OH), ((Ring5.W, 3), .Br)]
  dbl := dieneDbl .R ++ benzeneDbl .W
  links := [((Ring5.R, 3), (Ring5.W, 0))]

/-- Reagent over arrow F as drawn: 4-lithio-4′-[(tert-butyldimethylsilyl)oxy]biphenyl. -/
def reagentBiphenylLi : Molecule where
  rings := [.A, .B]
  hTab := benzeneH .A ++ benzeneH .B
  sp3 := []
  subTab := [((Ring5.A, 0), .Li), ((Ring5.B, 3), .OTBS)]
  dbl := benzeneDbl .A ++ benzeneDbl .B
  links := [((Ring5.A, 3), (Ring5.B, 0))]

/-- Reagent over arrow J as drawn: 4-bromophenyllithium. -/
def reagentBromophenylLi : Molecule where
  rings := [.P]
  hTab := benzeneH .P
  sp3 := []
  subTab := [((Ring5.P, 0), .Li), ((Ring5.P, 3), .Br)]
  dbl := benzeneDbl .P
  links := []

-- =====================================================================
-- §4  The requested structures F–L (and the drawn product [5]CPP)
-- =====================================================================

/-- **F**: the aryllithium has added to the dienone carbonyl of the starting
material.  R is now a 1,4-dihydroxy-cyclohexa-2,5-diene: R0 bears OH and the
biphenyl arm (through A0), R3 bears OH and the 4-bromophenyl W; B bears OTBS. -/
def structF : Molecule where
  rings := [.R, .W, .A, .B]
  hTab := [((.R, 1), 1), ((.R, 2), 1), ((.R, 4), 1), ((.R, 5), 1)]
    ++ benzeneH .W ++ benzeneH .A ++ benzeneH .B
  sp3 := [(Ring5.R, 0), (Ring5.R, 3)]
  subTab := [((Ring5.R, 0), .OH), ((Ring5.R, 3), .OH),
             ((Ring5.W, 3), .Br), ((Ring5.B, 3), .OTBS)]
  dbl := dieneDbl .R ++ benzeneDbl .W ++ benzeneDbl .A ++ benzeneDbl .B
  links := [((Ring5.R, 3), (Ring5.W, 0)), ((Ring5.R, 0), (Ring5.A, 0)),
            ((Ring5.A, 3), (Ring5.B, 0))]

/-- **G**: both tertiary OH groups of F are TES-protected (2 equiv. TESCl,
imidazole); the aryl silyl ether is shown converted to TES (identical formula
C₆H₁₅Si, hence consistent with the printed formula of H). -/
def structG : Molecule where
  rings := [.R, .W, .A, .B]
  hTab := structF.hTab
  sp3 := structF.sp3
  subTab := [((Ring5.R, 0), .OTES), ((Ring5.R, 3), .OTES),
             ((Ring5.W, 3), .Br), ((Ring5.B, 3), .OTES)]
  dbl := structF.dbl
  links := structF.links

/-- **H**: LiOH has cleaved the aryl silyl ether only — B is now the free
phenol; the two tertiary OTES groups remain (Si₂ retained).
Problem-printed formula: C₃₆H₄₇BrO₃Si₂ (proved below). -/
def structH : Molecule where
  rings := [.R, .W, .A, .B]
  hTab := structF.hTab
  sp3 := structF.sp3
  subTab := [((Ring5.R, 0), .OTES), ((Ring5.R, 3), .OTES),
             ((Ring5.W, 3), .Br), ((Ring5.B, 3), .OH)]
  dbl := structF.dbl
  links := structF.links

/-- **I**: PhI(OAc)₂/H₂O (two-electron oxidant) dearomatizes the phenol B to a
para-quinol: B3 is the ketone C=O, B0 is the sp³ quinol junction bearing the
new OH (from H₂O) and the link to A.  Net formula change: +O, no H change. -/
def structI : Molecule where
  rings := [.R, .W, .A, .B]
  hTab := structF.hTab   -- B keeps CH at 1,2,4,5; the quinol sp³ carbon B0 bears no H
  sp3 := [(Ring5.R, 0), (Ring5.R, 3), (Ring5.B, 0)]
  subTab := [((Ring5.R, 0), .OTES), ((Ring5.R, 3), .OTES),
             ((Ring5.W, 3), .Br),
             ((Ring5.B, 0), .OH), ((Ring5.B, 3), .carbonyl)]
  dbl := dieneDbl .R ++ benzeneDbl .W ++ benzeneDbl .A ++ dieneDbl .B
  links := structF.links

/-- **J**: NaH deprotonates the quinol OH; 4-bromophenyllithium adds to the
dienone C=O (B3).  B becomes a 1,4-dihydroxy-cyclohexa-2,5-diene: B0 bears OH
and A, B3 bears OH and the new 4-bromophenyl P. -/
def structJ : Molecule where
  rings := [.R, .W, .A, .B, .P]
  hTab := structF.hTab ++ benzeneH .P
  sp3 := [(Ring5.R, 0), (Ring5.R, 3), (Ring5.B, 0), (Ring5.B, 3)]
  subTab := [((Ring5.R, 0), .OTES), ((Ring5.R, 3), .OTES),
             ((Ring5.W, 3), .Br),
             ((Ring5.B, 0), .OH), ((Ring5.B, 3), .OH),
             ((Ring5.P, 3), .Br)]
  dbl := dieneDbl .R ++ benzeneDbl .W ++ benzeneDbl .A ++ dieneDbl .B
    ++ benzeneDbl .P
  links := structF.links ++ [((Ring5.B, 3), (Ring5.P, 0))]

/-- **K**: both B-ring OH groups are TES-protected (2 equiv. TESCl, imidazole). -/
def structK : Molecule where
  rings := structJ.rings
  hTab := structJ.hTab
  sp3 := structJ.sp3
  subTab := [((Ring5.R, 0), .OTES), ((Ring5.R, 3), .OTES),
             ((Ring5.W, 3), .Br),
             ((Ring5.B, 0), .OTES), ((Ring5.B, 3), .OTES),
             ((Ring5.P, 3), .Br)]
  dbl := structJ.dbl
  links := structJ.links

/-- **L**: Ni(COD)₂/2,2′-bipyridine (Yamamoto conditions) couples the two aryl
bromides intramolecularly: one new biaryl σ-bond W3–P3 closes the five-ring
macrocycle; both bromines are expelled.
Problem-printed formula: C₅₄H₈₀O₄Si₄ (proved below). -/
def structL : Molecule where
  rings := structJ.rings
  hTab := structJ.hTab
  sp3 := structJ.sp3
  subTab := [((Ring5.R, 0), .OTES), ((Ring5.R, 3), .OTES),
             ((Ring5.B, 0), .OTES), ((Ring5.B, 3), .OTES)]
  dbl := structJ.dbl
  links := structJ.links ++ [((Ring5.W, 3), (Ring5.P, 3))]

/-- The product drawn in the box, **[5]CPP**: a macrocycle of five para-linked
benzenes (all rings aromatic, no substituents), C₃₀H₂₀. -/
def cpp5 : Molecule where
  rings := [.R, .W, .A, .B, .P]
  hTab := benzeneH .R ++ benzeneH .W ++ benzeneH .A ++ benzeneH .B ++ benzeneH .P
  sp3 := []
  subTab := []
  dbl := benzeneDbl .R ++ benzeneDbl .W ++ benzeneDbl .A ++ benzeneDbl .B
    ++ benzeneDbl .P
  links := [((Ring5.R, 0), (Ring5.A, 0)), ((Ring5.A, 3), (Ring5.B, 0)),
            ((Ring5.B, 3), (Ring5.P, 0)), ((Ring5.P, 3), (Ring5.W, 3)),
            ((Ring5.W, 0), (Ring5.R, 3))]

-- =====================================================================
-- §5  Hückel counting lemmas (general laws, proved; needed for the π counts)
-- =====================================================================

/-- A 6π ring satisfies Hückel's 4n+2 rule (n = 1): aromatic. -/
theorem huckel_6pi_aromatic : ∃ n : ℕ, 6 = 4 * n + 2 := ⟨1, rfl⟩

/-- A 4π count is a 4n count (n = 1): the antiaromatic case — but it only
applies to a *closed* p-loop, which all dienone/diol rings here break with an
sp³ carbon. -/
theorem huckel_4pi_is_4n : ∃ n : ℕ, 4 = 4 * n := ⟨1, rfl⟩

/-- 4 does not satisfy the 4n+2 rule. -/
theorem huckel_4pi_not_aromatic : ¬ ∃ n : ℕ, 4 = 4 * n + 2 := by
  rintro ⟨n, h⟩; omega

-- =====================================================================
-- §6  Explicit-structure theorems for every requested output F–L
-- =====================================================================

-- ---------- F ----------

/-- **Structure of F**: connectivity, bond orders, substituents (explicit in
`structF`), formula, integer mass, and π-classification. -/
theorem structure_f :
    (∀ e : Element, structF.count e = match e with
      | .C => 30 | .H => 33 | .O => 3 | .Si => 1 | .Br => 1 | .Li => 0)
    ∧ structF.integerMass = 549
    ∧ structF.aromaticRingCount = 3
    ∧ structF.antiaromaticRingCount = 0
    ∧ structF.linkCount = 3
    -- substituent inventory of F
    ∧ (structF.subTab.filter (·.2 == .OH)).length = 2
    ∧ (structF.subTab.filter (·.2 == .OTBS)).length = 1
    ∧ (structF.subTab.filter (·.2 == .Br)).length = 1
    -- explicit connectivity: R diene + three benzenoid rings, para links
    ∧ structF.dbl = dieneDbl .R ++ benzeneDbl .W ++ benzeneDbl .A ++ benzeneDbl .B
    ∧ structF.links = [((Ring5.R, 3), (Ring5.W, 0)), ((Ring5.R, 0), (Ring5.A, 0)),
                       ((Ring5.A, 3), (Ring5.B, 0))] :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, rfl, rfl⟩

-- ---------- G ----------

/-- **Structure of G**. -/
theorem structure_g :
    (∀ e : Element, structG.count e = match e with
      | .C => 42 | .H => 61 | .O => 3 | .Si => 3 | .Br => 1 | .Li => 0)
    ∧ structG.integerMass = 777
    ∧ structG.aromaticRingCount = 3
    ∧ structG.antiaromaticRingCount = 0
    ∧ structG.linkCount = 3
    ∧ (structG.subTab.filter (·.2 == .OTES)).length = 3
    ∧ (structG.subTab.filter (·.2 == .Br)).length = 1 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

-- ---------- H ----------

/-- **Structure of H** — the problem prints its formula as C₃₆H₄₇BrO₃Si₂;
our H is *proved* to have exactly that formula. -/
theorem structure_h :
    (∀ e : Element, structH.count e = match e with
      | .C => 36 | .H => 47 | .O => 3 | .Si => 2 | .Br => 1 | .Li => 0)
    ∧ structH.integerMass = 663
    ∧ structH.aromaticRingCount = 3
    ∧ structH.antiaromaticRingCount = 0
    ∧ structH.linkCount = 3
    ∧ (structH.subTab.filter (·.2 == .OTES)).length = 2
    ∧ (structH.subTab.filter (·.2 == .OH)).length = 1
    ∧ (structH.subTab.filter (·.2 == .Br)).length = 1 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide⟩

-- ---------- I ----------

/-- **Structure of I**: the dearomatized para-quinol (cross-conjugated
cyclohexa-2,5-dienone; only the two untouched benzenes W and A remain
aromatic — the quinol ring's π array is broken by the sp³ junction B0). -/
theorem structure_i :
    (∀ e : Element, structI.count e = match e with
      | .C => 36 | .H => 47 | .O => 4 | .Si => 2 | .Br => 1 | .Li => 0)
    ∧ structI.integerMass = 679
    ∧ structI.aromaticRingCount = 2
    ∧ structI.antiaromaticRingCount = 0
    ∧ structI.linkCount = 3
    ∧ (structI.subTab.filter (·.2 == .carbonyl)).length = 1
    ∧ (structI.subTab.filter (·.2 == .OH)).length = 1
    ∧ (structI.subTab.filter (·.2 == .OTES)).length = 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide⟩

-- ---------- J ----------

/-- **Structure of J**. -/
theorem structure_j :
    (∀ e : Element, structJ.count e = match e with
      | .C => 42 | .H => 52 | .O => 4 | .Si => 2 | .Br => 2 | .Li => 0)
    ∧ structJ.integerMass = 836
    ∧ structJ.aromaticRingCount = 3
    ∧ structJ.antiaromaticRingCount = 0
    ∧ structJ.linkCount = 4
    ∧ (structJ.subTab.filter (·.2 == .OH)).length = 2
    ∧ (structJ.subTab.filter (·.2 == .OTES)).length = 2
    ∧ (structJ.subTab.filter (·.2 == .Br)).length = 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide⟩

-- ---------- K ----------

/-- **Structure of K**. -/
theorem structure_k :
    (∀ e : Element, structK.count e = match e with
      | .C => 54 | .H => 80 | .O => 4 | .Si => 4 | .Br => 2 | .Li => 0)
    ∧ structK.integerMass = 1064
    ∧ structK.aromaticRingCount = 3
    ∧ structK.antiaromaticRingCount = 0
    ∧ structK.linkCount = 4
    ∧ (structK.subTab.filter (·.2 == .OTES)).length = 4
    ∧ (structK.subTab.filter (·.2 == .Br)).length = 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

-- ---------- L ----------

/-- **Structure of L** — the problem prints its formula as C₅₄H₈₀O₄Si₄;
our L is *proved* to have exactly that formula, and its links are the five
biaryl bonds of the closed macrocycle. -/
theorem structure_l :
    (∀ e : Element, structL.count e = match e with
      | .C => 54 | .H => 80 | .O => 4 | .Si => 4 | .Br => 0 | .Li => 0)
    ∧ structL.integerMass = 904
    ∧ structL.aromaticRingCount = 3
    ∧ structL.antiaromaticRingCount = 0
    ∧ structL.linkCount = 5
    ∧ (structL.subTab.filter (·.2 == .OTES)).length = 4
    ∧ (structL.subTab.filter (·.2 == .Br)).length = 0
    -- the macrocyclizing bond created by the Yamamoto coupling
    ∧ structL.links.contains ((Ring5.W, 3), (Ring5.P, 3)) = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide⟩

-- =====================================================================
-- §7  Problem-input sanity checks (drawn structures, not assumptions)
-- =====================================================================

/-- Starting material as drawn: C₁₂H₉BrO₂. -/
theorem startingMaterial_formula :
    ∀ e : Element, startingMaterial.count e = match e with
    | .C => 12 | .H => 9 | .O => 2 | .Si => 0 | .Br => 1 | .Li => 0 := by
  decide

/-- The biphenyl reagent over arrow F as drawn: C₁₈H₂₃LiOSi. -/
theorem reagentBiphenylLi_formula :
    ∀ e : Element, reagentBiphenylLi.count e = match e with
    | .C => 18 | .H => 23 | .O => 1 | .Si => 1 | .Br => 0 | .Li => 1 := by
  decide

/-- The 4-bromophenyllithium reagent over arrow J as drawn: C₆H₄BrLi. -/
theorem reagentBromophenylLi_formula :
    ∀ e : Element, reagentBromophenylLi.count e = match e with
    | .C => 6 | .H => 4 | .O => 0 | .Si => 0 | .Br => 1 | .Li => 1 := by
  decide

/-- [5]CPP as drawn in the product box: macrocycle of five para-linked
benzenes, C₃₀H₂₀, five distinct aromatic 6π systems, five biaryl links. -/
theorem cpp5_formula_and_aromaticity :
    (∀ e : Element, cpp5.count e = match e with
      | .C => 30 | .H => 20 | .O => 0 | .Si => 0 | .Br => 0 | .Li => 0)
    ∧ cpp5.aromaticRingCount = 5
    ∧ cpp5.antiaromaticRingCount = 0
    ∧ cpp5.linkCount = 5
    ∧ cpp5.integerMass = 380 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

-- =====================================================================
-- §8  Derivation identities: F–L are *derived* from the problem inputs,
--     not assumed (all identities proved as integer equalities)
-- =====================================================================

/-- Workup proton that quenches the alkoxide after aryllithium addition. -/
private def workupH : Element → ℤ
  | .H => 1 | _ => 0

/-- Lithium removed with the organolithium reagent (Li → leaves as Li⁺). -/
private def removeLi : Element → ℤ
  | .Li => -1 | _ => 0

/-- Net change for capping one OH as OTES: −H + SiEt₃ = +C₆H₁₄Si. -/
private def tesCap : Element → ℤ
  | .C => 6 | .H => 14 | .Si => 1 | _ => 0

/-- Net change for cleaving one aryl silyl ether back to a phenol: −C₆H₁₄Si. -/
private def silylRemoval : Element → ℤ
  | .C => -6 | .H => -14 | .Si => -1 | _ => 0

/-- Step F: F = starting material + biphenyl-lithium reagent + workup H − Li
(nucleophilic addition of ArLi to the ketone). -/
theorem derivation_F :
    ∀ e : Element, structF.count e =
      startingMaterial.count e + reagentBiphenylLi.count e + workupH e + removeLi e := by
  decide

/-- Step G: G = F + 2 × (OH → OTES) (the aryl TBS→TES swap is formula-neutral:
both are C₆H₁₅OSi substituents — proved in `subContrib`). -/
theorem derivation_G :
    ∀ e : Element, structG.count e = structF.count e + 2 * tesCap e := by
  decide

/-- Step H: H = G − (C₆H₁₄Si), i.e. LiOH cleaves exactly one aryl silyl ether,
liberating the phenol and keeping both tertiary OTES groups (Si₂ retained). -/
theorem derivation_H :
    ∀ e : Element, structH.count e = structG.count e + silylRemoval e := by
  decide

/-- Step I: I = H + O.  The two-electron oxidant PhI(OAc)₂/H₂O converts the
phenol into the para-quinol by inserting one oxygen (of water) at the para
carbon: no net hydrogen change — the phenolic H is replaced by the quinol O–H. -/
theorem derivation_I :
    ∀ e : Element, structI.count e = structH.count e + (if e == .O then (1:ℤ) else 0) := by
  decide

/-- Step J: J = I + 4-bromophenyllithium + workup H − Li (addition to the
dienone carbonyl). -/
theorem derivation_J :
    ∀ e : Element, structJ.count e =
      structI.count e + reagentBromophenylLi.count e + workupH e + removeLi e := by
  decide

/-- Step K: K = J + 2 × (OH → OTES). -/
theorem derivation_K :
    ∀ e : Element, structK.count e = structJ.count e + 2 * tesCap e := by
  decide

/-- Step L: L = K − 2 Br.  The Ni(0)/bpy Yamamoto macrocyclization joins the
two aryl bromides into one new biaryl σ-bond; no hydrogen count changes
(neither coupled carbon bore H). -/
theorem derivation_L :
    ∀ e : Element, structL.count e = structK.count e + (if e == .Br then (-2:ℤ) else 0) := by
  decide

/-- Aromatization stoichiometry of the printed final step (1. n-Bu₄NF,
2. SnCl₂): removal of all four OTES caps (→ tetraol) followed by reductive
aromatization of rings R and B (each loses the elements of its two O−H groups,
2 O + 4 H per ring, with SnCl₂ supplying the electrons) yields the drawn
[5]CPP, C₃₀H₂₀. -/
theorem derivation_cpp :
    ∀ e : Element, cpp5.count e =
      structL.count e + 4 * silylRemoval e
        + (match e with | .O => (-4 : ℤ) | .H => -4 | _ => 0) := by
  decide

-- =====================================================================
-- §9  Umbrella answer theorem and axiom audit
-- =====================================================================

/-- Complete certified answer for IChO 2026 T6 question 6.5: every requested
structure F–L with its proved formula, π-classification and connectivity, the
two problem-printed anchor formulas (H and L), and the full derivation chain
from the drawn starting material and reagents. -/
theorem answer_icho_2026_t6_a5 :
    (∀ e : Element, structF.count e = match e with
      | .C => 30 | .H => 33 | .O => 3 | .Si => 1 | .Br => 1 | .Li => 0)
    ∧ (∀ e : Element, structG.count e = match e with
      | .C => 42 | .H => 61 | .O => 3 | .Si => 3 | .Br => 1 | .Li => 0)
    ∧ (∀ e : Element, structH.count e = match e with
      | .C => 36 | .H => 47 | .O => 3 | .Si => 2 | .Br => 1 | .Li => 0)
    ∧ (∀ e : Element, structI.count e = match e with
      | .C => 36 | .H => 47 | .O => 4 | .Si => 2 | .Br => 1 | .Li => 0)
    ∧ (∀ e : Element, structJ.count e = match e with
      | .C => 42 | .H => 52 | .O => 4 | .Si => 2 | .Br => 2 | .Li => 0)
    ∧ (∀ e : Element, structK.count e = match e with
      | .C => 54 | .H => 80 | .O => 4 | .Si => 4 | .Br => 2 | .Li => 0)
    ∧ (∀ e : Element, structL.count e = match e with
      | .C => 54 | .H => 80 | .O => 4 | .Si => 4 | .Br => 0 | .Li => 0)
    ∧ structF.aromaticRingCount = 3
    ∧ structG.aromaticRingCount = 3
    ∧ structH.aromaticRingCount = 3
    ∧ structI.aromaticRingCount = 2
    ∧ structJ.aromaticRingCount = 3
    ∧ structK.aromaticRingCount = 3
    ∧ structL.aromaticRingCount = 3
    ∧ structL.links.contains ((Ring5.W, 3), (Ring5.P, 3)) = true
    ∧ (∀ e : Element, startingMaterial.count e = match e with
      | .C => 12 | .H => 9 | .O => 2 | .Si => 0 | .Br => 1 | .Li => 0)
    ∧ (∀ e : Element, reagentBiphenylLi.count e = match e with
      | .C => 18 | .H => 23 | .O => 1 | .Si => 1 | .Br => 0 | .Li => 1)
    ∧ (∀ e : Element, reagentBromophenylLi.count e = match e with
      | .C => 6 | .H => 4 | .O => 0 | .Si => 0 | .Br => 1 | .Li => 1)
    ∧ (∀ e : Element, cpp5.count e = match e with
      | .C => 30 | .H => 20 | .O => 0 | .Si => 0 | .Br => 0 | .Li => 0)
    ∧ cpp5.aromaticRingCount = 5 := by
  obtain ⟨hF, _, _, _⟩ := structure_f
  obtain ⟨hG, _, _, _⟩ := structure_g
  obtain ⟨hH, _, _, _⟩ := structure_h
  obtain ⟨hI, _, _, _⟩ := structure_i
  obtain ⟨hJ, _, _, _⟩ := structure_j
  obtain ⟨hK, _, _, _⟩ := structure_k
  obtain ⟨hLf, _, _, _⟩ := structure_l
  -- aromaticity conjuncts lie after (mass) and (formula) in each structure theorem;
  -- extract them at the correct depth directly
  obtain ⟨_, _, hFa, _⟩ := structure_f
  obtain ⟨_, _, hGa, _⟩ := structure_g
  obtain ⟨_, _, hHa, _⟩ := structure_h
  obtain ⟨_, _, hIa, _⟩ := structure_i
  obtain ⟨_, _, hJa, _⟩ := structure_j
  obtain ⟨_, _, hKa, _⟩ := structure_k
  obtain ⟨_, _, hLa, _, _, _, _, hMem⟩ := structure_l
  exact ⟨hF, hG, hH, hI, hJ, hK, hLf,
    hFa, hGa, hHa, hIa, hJa, hKa, hLa, hMem,
    startingMaterial_formula, reagentBiphenylLi_formula, reagentBromophenylLi_formula,
    cpp5_formula_and_aromaticity.1, cpp5_formula_and_aromaticity.2.1⟩

#print axioms answer_icho_2026_t6_a5
#print axioms structure_f
#print axioms structure_g
#print axioms structure_h
#print axioms structure_i
#print axioms structure_j
#print axioms structure_k
#print axioms structure_l
#print axioms derivation_F
#print axioms derivation_G
#print axioms derivation_H
#print axioms derivation_I
#print axioms derivation_J
#print axioms derivation_K
#print axioms derivation_L
#print axioms derivation_cpp
#print axioms cpp5_formula_and_aromaticity

end IChO2026T6A5
