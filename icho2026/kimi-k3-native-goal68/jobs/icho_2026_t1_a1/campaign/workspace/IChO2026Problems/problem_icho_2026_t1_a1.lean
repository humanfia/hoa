import Mathlib

/-!
# IChO 2026, Problem T1, subquestion 1.1 — target `icho_2026_t1_a1`

## Problem (official English, `theory_problem.pdf`, printed page Q1-2)

The table of compounds extractable from the only four plants seen in
Avicenna's laboratory (numbers 1–10 as printed; "3" occurs in three rows but
is one and the same compound, drawn identically):

* Zingiber: **1** (C₁₁H₁₄O₃), **2** (C₁₀H₁₈O), **3** (C₁₀H₁₈O)
* Hypericum: **4** (C₆H₁₂O), **5** (C₁₀H₁₂O₂), **6** (C₁₀H₁₈O)
* Chamomilla: **7** (C₁₄H₁₆), **8** (C₁₅H₂₄), **3** (C₁₀H₁₈O)
* Artemisia: **9** (C₁₀H₁₆O), **10** (C₁₀H₁₈O), **3** (C₁₀H₁₈O)

Chromatography: the elixir consists of **four different** substances X, Y, Z, W.
"X can isomerise into Y in an acidic medium" and "Y has a plane of symmetry".
**1.1 Identify X and Y.**  The answer sheet requires one number each for X
and Y among 1–10.

## Reading of the printed structures (checked against `T1_page-2.png`)

* **2** = borneol: bicyclo[2.2.1]heptan-2-ol skeleton with a gem-dimethyl
  pair on the one-carbon bridge, one methyl on the second bridgehead, and
  the –OH on a bridge carbon adjacent to that bridgehead.  Bicyclic
  secondary alcohol, no C=C bond, C₁₀H₁₈O ✓ (counts checked in
  `borneol_Ccount/Ocount/Hcount`).
* **3** = 1,8-cineole (eucalyptol), 1,3,3-trimethyl-2-oxabicyclo[2.2.2]octane:
  the ether oxygen is bonded to a bridgehead carbon (one methyl) and to the
  gem-dimethyl carbon; two equivalent –CH₂–CH₂– bridges connect the two
  bridgeheads.  Mirror plane: through the oxygen, both bridgeheads and all
  three methyl carbons, exchanging the two bridges and the two gem-methyls.
* **6** = linalool, CH₂=CH–C(OH)(Me)–CH₂–CH₂–CH=C(Me)₂ as drawn: acyclic
  tertiary alcohol whose classical acid-catalysed cyclisation affords
  1,8-cineole: every existing C–C/C–O bond maps onto a cineole bond and only
  two new σ bonds are formed (`cyclisation_preserved`, `cyclisation_newbond*`).
* **10** = umbellulone skeleton as drawn: bicyclo[3.1.0]hexan-2-one carrying
  one methyl on the carbon α to the carbonyl and one isopropyl group on the
  opposite ring-junction carbon.  A ketone: no O–H, and no symmetry beyond
  the isopropyl methyl swap.  Note: the drawn skeleton corresponds to H
  count 16 (C₁₀H₁₆O) while the printed label says C₁₀H₁₈O; the discrepancy
  does not affect the elimination (compound 10 is excluded structurally
  either way) — recorded in `result.json`'s `source_gaps`.
* **1, 4, 5, 7, 8, 9** are excluded at once by the printed molecular
  formulae: isomers share the formula, and among the ten printed formulae
  only C₁₀H₁₈O is carried by more than one distinct compound
  (`shared_formula_class`).

## What this file proves

Fully mechanised (kernel `decide` on the printed formula table and on
bounded label/bond constraints, plus stepwise forcing lemmas):

* the only repeated printed formula is C₁₀H₁₈O, carried by exactly
  {2, 3, 6, 10} (`shared_formula_class`);
* every labelled involutory symmetry of the drawn heavy-atom graph of
  **2** is the identity or the gem-methyl swap (8 9) fixing all seven cage
  atoms (`borneol_sym_cases`); analogously **6**: identity or the
  isopropylidene methyl swap (9 10) (`linalool_sym_cases`); **10**: identity
  or the isopropyl methyl swap (9 10) (`umbellulone_sym_cases`);
* **3** possesses the labelled involution (4 5)(7 9)(8 10) realising the
  drawn mirror plane (`cineoleMirror_valid`), which moves cage atoms
  (`cineoleMirror_moves`) and fixes the oxygen and both bridgeheads
  (`cineoleMirror_fixed`);
* encoding sanity: each of 2, 3, 6 has 10 carbons, 1 oxygen and 18 implicit
  hydrogens (`*_Ccount`, `*_Ocount`, `*_Hcount`);
* linalool→cineole cyclisation consistency (`linToCin_inj`,
  `cyclisation_preserved`, `cyclisation_newbond1/2`, `cyclisation_elements`);
* given the trusted general stereochemical/mechanistic laws below (stated as
  explicit hypotheses — no `axiom`, no custom constants), compounds
  2, 6, 10 cannot have a mirror plane (`borneol_no_mirror`,
  `linalool_no_mirror`, `umbellulone_no_mirror`), and the identification
  `X = 6 ∧ Y = 3` is the theorem `t1_a1_answer` (indices ⟨5⟩ and ⟨2⟩ of
  `Fin 10`, i.e. answer-sheet compounds 6 and 3).

## Named hypotheses (trusted general laws — `trusted_general_law`)

These are passed as explicit arguments to `t1_a1_answer`; each is a standard
fact of stereochemistry/physical organic chemistry invoked tacitly by every
elementary solution and not derivable from the problem data alone (the
problem supplies no spectra and no coordinates).

* `law_mirror`: a molecular mirror plane realises a *non-identity*
  involutory symmetry of the labelled heavy-atom graph.
* `law_tetra`: a mirror plane cannot fix a tetrahedral (sp³) carbon atom
  together with all four of its substituent atoms when those substituents
  are pairwise non-equivalent (distinguishable in the labelled graph): the
  central atom and four inequivalent substituents cannot all lie in one
  plane.
* `law_cage`: a mirror plane of a molecule containing a rigid non-planar
  bicyclic cage must move at least one cage atom.  Applied with the
  geometric premises `NonPlanarRigidCage gBorneol [0…6]` and
  `NonPlanarRigidCage gUmbellulone [0,1,2,4,5,6,7,8]`, read off the printed
  drawings (rigid bridged bicyclic skeletons — problem-image grounded).
* `law_isomer_formula`: isomerisation preserves the molecular formula.
* `law_ether_cyclisation`: acid-catalysed isomerisation to a cyclic ether
  (a molecule containing an ether oxygen, label code 3) requires in the
  starting material an alcoholic O–H (code 2, the future ether oxygen) and a
  C=C double bond (the cyclisation target).
-/

namespace IChO2026T1A1

/-! ## 1. Printed formula table (problem input, page Q1-2) -/

/-- A molecular formula as printed on the problem page. -/
structure Formula where
  C : ℕ
  H : ℕ
  O : ℕ
  deriving DecidableEq, Repr

/-- The ten printed molecular formulae, indexed by compound number minus one.
    Compound 3 appears in three table rows but is one compound; the list
    follows the answer-sheet numbering 1–10. -/
def printedFormula : Fin 10 → Formula
  | ⟨0, _⟩ => ⟨11, 14, 3⟩
  | ⟨1, _⟩ => ⟨10, 18, 1⟩
  | ⟨2, _⟩ => ⟨10, 18, 1⟩
  | ⟨3, _⟩ => ⟨6, 12, 1⟩
  | ⟨4, _⟩ => ⟨10, 12, 2⟩
  | ⟨5, _⟩ => ⟨10, 18, 1⟩
  | ⟨6, _⟩ => ⟨14, 16, 0⟩
  | ⟨7, _⟩ => ⟨15, 24, 0⟩
  | ⟨8, _⟩ => ⟨10, 16, 1⟩
  | ⟨9, _⟩ => ⟨10, 18, 1⟩

/-- C₁₀H₁₈O, the formula shared by compounds 2, 3, 6, 10. -/
def formulaC10H18O : Formula := ⟨10, 18, 1⟩

/-- The printed table: compounds 2, 3, 6, 10 and only they have formula
    C₁₀H₁₈O (indices 1, 2, 5, 9). -/
theorem formulaC10H18O_carriers :
    ∀ k : Fin 10, printedFormula k = formulaC10H18O ↔
      k.val = 1 ∨ k.val = 2 ∨ k.val = 5 ∨ k.val = 9 := by decide

/-- The only way two table compounds share a printed formula is being equal
    or both lying in the C₁₀H₁₈O family {2, 3, 6, 10}. -/
theorem shared_formula_class :
    ∀ a b : Fin 10, printedFormula a = printedFormula b →
      a = b ∨ ((a = ⟨1, by decide⟩ ∨ a = ⟨2, by decide⟩
                  ∨ a = ⟨5, by decide⟩ ∨ a = ⟨9, by decide⟩) ∧
               (b = ⟨1, by decide⟩ ∨ b = ⟨2, by decide⟩
                  ∨ b = ⟨5, by decide⟩ ∨ b = ⟨9, by decide⟩)) := by
  decide

/-! ## 2. Labelled heavy-atom graphs -/

/-- Atoms as printed: `(element-type code, implicit hydrogen count)`.
    Element codes: 0 = sp³ carbon, 1 = sp² (alkene) carbon, 2 = O–H oxygen,
    3 = ether oxygen, 4 = carbonyl carbon, 5 = carbonyl oxygen. -/
abbrev Atm := ℕ × ℕ

/-- Element code for an atom type: 8 for oxygen (labels 2/3/5), 6 for carbon
    (labels 0/1/4).  Used for cyclisation bookkeeping and count checks. -/
def elemOf : Atm → ℕ := fun p => if p.1 = 2 ∨ p.1 = 3 ∨ p.1 = 5 then 8 else 6

/-- A molecular graph: heavy atoms `0 … n-1` with labels, and a symmetric
    bond-order function (`0` = no bond, `1`/`2` = single/double). -/
structure Gr where
  n : ℕ
  atoms : ℕ → Atm
  bo : ℕ → ℕ → ℕ
  bosymm : ∀ i j, bo i j = bo j i

/-- Bond-order function built from a list of normalised single-bond pairs and
    a list of normalised double-bond pairs; symmetric by construction. -/
def mkBo (sg db : List (ℕ × ℕ)) : ℕ → ℕ → ℕ := fun i j =>
  let k := (min i j, max i j)
  if k ∈ sg then 1 else if k ∈ db then 2 else 0

theorem mkBo_symm (sg db : List (ℕ × ℕ)) (i j : ℕ) :
    mkBo sg db i j = mkBo sg db j i := by
  simp only [mkBo, min_comm i j, max_comm i j]

theorem mkBo_bosymm (sg db : List (ℕ × ℕ)) : ∀ i j, mkBo sg db i j = mkBo sg db j i :=
  fun i j => mkBo_symm sg db i j

/-- Kernel-transparent equality test for `mkBo` values: by case analysis the
    goal becomes a decidable literal comparison. -/
instance mkBoDecEq (sg db : List (ℕ × ℕ)) (i j m : ℕ) :
    Decidable (mkBo sg db i j = m) := by
  unfold mkBo
  by_cases hsg : (min i j, max i j) ∈ sg
  · rw [if_pos hsg]
    infer_instance
  · rw [if_neg hsg]
    by_cases hdb : (min i j, max i j) ∈ db
    · rw [if_pos hdb]
      infer_instance
    · rw [if_neg hdb]
      infer_instance

namespace Gr

variable (g : Gr)

/-- An involutive labelled symmetry of the graph on `[0, k)`: a pairing that
    is involutive, label- and bond-order-preserving, with values in the
    vertex set.  The full group of symmetry candidates is `Valid g.n`.
    `Valid k` quantifies over `Fin k` so that decidability is automatic.
    `ValidN` is the unrestricted form used for applications over `ℕ`. -/
def ValidN (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ u : Fin k, f u < g.n) ∧
  (∀ u : Fin k, f (f u) = u) ∧
  (∀ u : Fin k, g.atoms (f u) = g.atoms u) ∧
  (∀ u v : Fin k, g.bo (f u) (f v) = g.bo u v)

/-- Unrestricted presentation of `ValidN` over natural indices. -/
def Valid (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ u, u < k → f u < g.n) ∧
  (∀ u, u < k → f (f u) = u) ∧
  (∀ u, u < k → g.atoms (f u) = g.atoms u) ∧
  (∀ u v, u < k → v < k → g.bo (f u) (f v) = g.bo u v)

/-- The two presentations agree: `Valid` is decidable via `ValidN`. -/
theorem valid_iffValidN (k : ℕ) (f : ℕ → ℕ) : g.Valid k f ↔ g.ValidN k f := by
  unfold Valid ValidN
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun u ↦ h1 u u.2, fun u ↦ h2 u u.2, fun u ↦ h3 u u.2,
           fun u v ↦ h4 u v u.2 v.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun u hu ↦ h1 ⟨u, hu⟩, fun u hu ↦ h2 ⟨u, hu⟩, fun u hu ↦ h3 ⟨u, hu⟩,
           fun u v hu hv ↦ h4 ⟨u, hu⟩ ⟨v, hv⟩⟩

/-- `ValidN` is decidable: it quantifies over `Fin k` (finite) and the
    components compare natural numbers and `ℕ × ℕ` pairs, all with decidable
    equality. -/
instance decidableValidN (k : ℕ) (f : ℕ → ℕ) : Decidable (g.ValidN k f) := by
  unfold ValidN
  infer_instance

/-- Decidability of the full symmetry condition on an `n`-vertex graph.
    Atom labels (`Atm = ℕ × ℕ`) and bond orders (`ℕ`) both have decidable
    equality, and the quantifiers over `Fin k` are finite, so every `Valid`
    proposition is decidable. -/
instance decidableValid (g : Gr) (k : ℕ) (f : ℕ → ℕ) :
    Decidable (g.Valid k f) :=
  decidable_of_iff _ (g.valid_iffValidN k f).symm

/-- If atom `u` is the only atom of the graph carrying its label, any valid
    symmetry fixes it. -/
theorem fixed_of_unique {σ : ℕ → ℕ} (hσ : g.Valid g.n σ) {u : ℕ} (hu : u < g.n)
    (huq : ∀ v, v < g.n → g.atoms v = g.atoms u → v = u) : σ u = u :=
  huq (σ u) (hσ.1 u hu) (hσ.2.2.1 u hu)

/-- If `v` is a fixed atom and `u` is the only atom carrying its label among
    the bonded neighbours of `v`, any valid symmetry fixes `u`. -/
theorem fixed_of_nb {σ : ℕ → ℕ} (hσ : g.Valid g.n σ) {u v : ℕ}
    (hu : u < g.n) (hv : v < g.n) (hb : g.bo v u ≠ 0) (hσv : σ v = v)
    (huq : ∀ x, x < g.n → g.atoms x = g.atoms u → g.bo v x ≠ 0 → x = u) :
    σ u = u := by
  refine huq (σ u) (hσ.1 u hu) (hσ.2.2.1 u hu) ?_
  have h2 := hσ.2.2.2 v u hv hu
  rw [hσv] at h2
  rw [h2]; exact hb

/-- A valid pairing is involutive, hence injective on `[0, n)`. -/
theorem inj {σ : ℕ → ℕ} (hσ : g.Valid g.n σ) {u v : ℕ}
    (hu : u < g.n) (hv : v < g.n) (h : σ u = σ v) : u = v := by
  have a := hσ.2.1 u hu
  have b := hσ.2.1 v hv
  rw [← a, h, b]

end Gr

open Gr

/-! ## 3. The drawn molecules (problem-image input) -/

/-- **Compound 2 (borneol), 11 heavy atoms.**
    0 = upper bridgehead CH, 1 = lower bridgehead C (methyl 10),
    2/3 = first –CH₂–CH₂– bridge, 4 = carbinol CH (OH oxygen 7), 5 = second
    bridge CH₂, 6 = one-carbon bridge C (gem-methyls 8, 9). -/
def gBorneol : Gr :=
  ⟨11, fun
    | 0 => (0, 1) | 1 => (0, 0) | 2 => (0, 2) | 3 => (0, 2) | 4 => (0, 1)
    | 5 => (0, 2) | 6 => (0, 0) | 7 => (2, 1) | 8 => (0, 3) | 9 => (0, 3)
    | 10 => (0, 3) | _ => (0, 0),
   mkBo [(0, 2), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (1, 10),
         (2, 3), (4, 5), (4, 7), (6, 8), (6, 9)] [],
   mkBo_bosymm _ _⟩

/-- **Compound 3 (1,8-cineole), 11 heavy atoms.**
    0 = ether O, 1 = bridgehead C (methyl 2), 3 = gem-dimethyl carbon
    (methyls 4, 5), 6 = second bridgehead CH, 7/8 and 9/10 = the two
    –CH₂–CH₂– bridges between 1 and 6.  Bonds: 0–1, 0–3, 3–6, the bridges
    1–7–8–6 and 1–9–10–6. -/
def gCineole : Gr :=
  ⟨11, fun
    | 0 => (3, 0) | 1 => (0, 0) | 2 => (0, 3) | 3 => (0, 0) | 4 => (0, 3)
    | 5 => (0, 3) | 6 => (0, 1) | 7 => (0, 2) | 8 => (0, 2) | 9 => (0, 2)
    | 10 => (0, 2) | _ => (0, 0),
   mkBo [(0, 1), (0, 3), (1, 2), (1, 7), (1, 9), (3, 4), (3, 5), (3, 6),
         (6, 8), (6, 10), (7, 8), (9, 10)] [],
   mkBo_bosymm _ _⟩

/-- **Compound 6 (linalool), 11 heavy atoms.**
    0 = OH oxygen, 1 = tertiary carbinol C (methyl 8), 2/3 = vinyl CH–CH₂
    (double bond), 4/5 = chain CH₂–CH₂, 6/7 = alkene CH–C (double bond),
    9/10 = methyls on the alkene carbon 7. -/
def gLinalool : Gr :=
  ⟨11, fun
    | 0 => (2, 1) | 1 => (0, 0) | 2 => (1, 1) | 3 => (1, 2) | 4 => (0, 2)
    | 5 => (0, 2) | 6 => (1, 1) | 7 => (1, 0) | 8 => (0, 3) | 9 => (0, 3)
    | 10 => (0, 3) | _ => (0, 0),
   mkBo [(0, 1), (1, 2), (1, 4), (1, 8), (4, 5), (5, 6), (7, 9), (7, 10)]
        [(2, 3), (6, 7)],
   mkBo_bosymm _ _⟩

/-- Atom table of compound 10 (umbellulone skeleton as drawn); extracted as
    a reducible abbreviation so that `show`/kernel unfolding stays cheap for
    arbitrary indices. -/
abbrev uAtoms : ℕ → Atm
  | 0 => (4, 0) | 1 => (5, 0) | 2 => (0, 1) | 3 => (0, 3) | 4 => (0, 1)
  | 5 => (0, 2) | 6 => (0, 0) | 7 => (0, 1) | 8 => (0, 2) | 9 => (0, 3)
  | 10 => (0, 3) | _ => (0, 0)

/-- **Compound 10 (umbellulone skeleton as drawn), 11 heavy atoms.**
    0 = carbonyl C, 1 = carbonyl O, 2 = α-CH (methyl 3), 4 = ring-junction
    CH, 5 = cyclopropane CH₂, 6 = opposite junction C (isopropyl 7–10),
    8 = ring CH₂.  Bonds: five-ring 0–2–4–6–8–0, cyclopropane 4–5–6–4,
    and the isopropyl 6–7(–9)(–10). -/
def gUmbellulone : Gr :=
  ⟨11, uAtoms,
   mkBo [(0, 2), (0, 8), (2, 3), (2, 4), (4, 5), (4, 6), (5, 6), (6, 7),
         (6, 8), (7, 9), (7, 10)] [(0, 1)],
   mkBo_bosymm _ _⟩

/-! ### Vertex index aliases (all four drawn molecules have 11 heavy atoms) -/

/-- Vertex type of every drawn molecule below. -/
abbrev V11 := Fin 11

/-- Vertices of the drawn borneol graph. -/
abbrev Vb := V11
/-- Vertices of the drawn cineole graph. -/
abbrev Vc := V11
/-- Vertices of the drawn linalool graph. -/
abbrev Vl := V11
/-- Vertices of the drawn umbellulone graph. -/
abbrev Vu := V11

/-- The heavy-atom graph attached to each compound of the C₁₀H₁₈O family;
    the other compounds never survive the formula filter, so no graphs are
    needed for them. -/
def graphOf : Fin 10 → Option Gr
  | ⟨1, _⟩ => some gBorneol
  | ⟨2, _⟩ => some gCineole
  | ⟨5, _⟩ => some gLinalool
  | ⟨9, _⟩ => some gUmbellulone
  | _ => none

/-! ### 3a. Encoding sanity checks: 10 carbons, 1 oxygen, 18 hydrogens each -/

/-- Number of carbons among atoms `0 … k-1`. -/
def Ccount (g : Gr) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc u => acc + if elemOf (g.atoms u) = 6 then 1 else 0) 0

/-- Number of oxygens among atoms `0 … k-1`. -/
def Ocount (g : Gr) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc u => acc + if elemOf (g.atoms u) = 8 then 1 else 0) 0

/-- Sum of the implicit hydrogen counts over atoms `0 … k-1`. -/
def Hcount (g : Gr) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc u => acc + (g.atoms u).2) 0

theorem borneol_Ccount : Ccount gBorneol 11 = 10 := by decide
theorem borneol_Ocount : Ocount gBorneol 11 = 1 := by decide
theorem borneol_Hcount : Hcount gBorneol 11 = 18 := by decide
theorem cineole_Ccount : Ccount gCineole 11 = 10 := by decide
theorem cineole_Ocount : Ocount gCineole 11 = 1 := by decide
theorem cineole_Hcount : Hcount gCineole 11 = 18 := by decide
theorem linalool_Ccount : Ccount gLinalool 11 = 10 := by decide
theorem linalool_Ocount : Ocount gLinalool 11 = 1 := by decide
theorem linalool_Hcount : Hcount gLinalool 11 = 18 := by decide

/-- The umbellulone skeleton *as drawn* has H count 16 (C₁₀H₁₆O); the printed
    label C₁₀H₁₈O is recorded as a source discrepancy.  The elimination of
    compound 10 below uses only its functional groups and (lack of)
    symmetry, so the conclusion is unaffected either way. -/
theorem umbellulone_Ccount : Ccount gUmbellulone 11 = 10 := by decide
theorem umbellulone_Ocount : Ocount gUmbellulone 11 = 1 := by decide
theorem umbellulone_Hcount_drawn : Hcount gUmbellulone 11 = 16 := by decide

/-! ## 4. The mirror symmetry of cineole (Y candidate) -/

/-- The labelled involution of `gCineole` realising the drawn mirror plane:
    it exchanges the two –CH₂–CH₂– bridges (7 9)(8 10) and the two methyls
    of the gem-dimethyl carbon (4 5), fixing the oxygen, both bridgehead
    carbons and the bridgehead methyl. -/
def cineoleMirror : ℕ → ℕ
  | 4 => 5 | 5 => 4 | 7 => 9 | 9 => 7 | 8 => 10 | 10 => 8 | u => u

theorem cineoleMirror_valid : gCineole.Valid 11 cineoleMirror := by decide

/-- The mirror moves cage atoms (e.g. bridge atom 7). -/
theorem cineoleMirror_moves : ∃ u, u < 11 ∧ cineoleMirror u ≠ u :=
  ⟨7, by decide, by decide⟩

/-- The mirror fixes the oxygen and both bridgehead carbons. -/
theorem cineoleMirror_fixed :
    cineoleMirror 0 = 0 ∧ cineoleMirror 1 = 1 ∧ cineoleMirror 6 = 6 :=
  ⟨rfl, rfl, rfl⟩

/-- Cineole contains an ether oxygen (label code 3). -/
theorem cineole_etherO : ∃ u : Fin gCineole.n, (gCineole.atoms u).1 = 3 :=
  ⟨⟨0, by decide⟩, rfl⟩

/-! ## 5. Functional-group checks (problem-image data, by kernel `decide`) -/

/-- Borneol contains no C=C double bond: `gBorneol.bo` never equals `2`
    (its double-bond pair list is empty, a definitional fact the kernel
    unfolds directly). -/
theorem borneol_noCC (i j : Vb) : gBorneol.bo i j ≠ 2 := by
  show mkBo _ [] i j ≠ 2
  show (if (min i.val j.val, max i.val j.val) ∈
      [(0, 2), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (1, 10),
       (2, 3), (4, 5), (4, 7), (6, 8), (6, 9)]
    then 1 else 0) ≠ 2
  split <;> omega
theorem borneol_hasOH : ∃ u : Vb, (gBorneol.atoms u).1 = 2 := ⟨⟨7, by decide⟩, rfl⟩
theorem linalool_hasOH : ∃ u : Vl, (gLinalool.atoms u).1 = 2 := ⟨⟨0, by decide⟩, rfl⟩
theorem linalool_hasCC : ∃ i j : Vl, gLinalool.bo i j = 2 :=
  ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by decide⟩
/-- Umbellulone contains no O–H: no vertex carries label code 2 (the atom
    table is a literal pattern-match the kernel unfolds directly). -/
theorem umbellulone_noOH (u : Vu) : (gUmbellulone.atoms u).1 ≠ 2 := by
  show (uAtoms u.val).1 ≠ 2
  have hu : u.val < 11 := u.2
  interval_cases u.val <;> decide

/-! ## 6. Classification of the labelled symmetries of 2, 6 and 10

Each forcing step uses `Gr.fixed_of_unique` / `Gr.fixed_of_nb` with the
uniqueness / candidate-list facts discharged by the kernel (`decide`). -/

/-- Every valid involutory symmetry of the drawn borneol graph is the
    identity or the gem-methyl swap (8 9); in both cases all seven cage
    atoms 0–6 are fixed. -/
theorem borneol_sym_cases (σ : ℕ → ℕ) (h : gBorneol.Valid 11 σ) :
    (∀ u, u < 11 → σ u = u) ∨
    (σ 8 = 9 ∧ σ 9 = 8 ∧ ∀ u, u < 11 → u ≠ 8 → u ≠ 9 → σ u = u) := by
  have h7 : σ 7 = 7 := gBorneol.fixed_of_unique h (by decide) (by decide)
  have h4 : σ 4 = 4 := gBorneol.fixed_of_nb h (by decide) (by decide) (by decide) h7 (by decide)
  have h5 : σ 5 = 5 := gBorneol.fixed_of_nb h (by decide) (by decide) (by decide) h4 (by decide)
  have h1 : σ 1 = 1 := gBorneol.fixed_of_nb h (by decide) (by decide) (by decide) h4 (by decide)
  have h10 : σ 10 = 10 := gBorneol.fixed_of_nb h (by decide) (by decide) (by decide) h1 (by decide)
  have h6 : σ 6 = 6 := gBorneol.fixed_of_nb h (by decide) (by decide) (by decide) h1 (by decide)
  have h3 : σ 3 = 3 := gBorneol.fixed_of_nb h (by decide) (by decide) (by decide) h1 (by decide)
  have h0 : σ 0 = 0 := gBorneol.fixed_of_nb h (by decide) (by decide) (by decide) h6 (by decide)
  have h2 : σ 2 = 2 := by
    have hbound : σ 2 < 11 := h.1 2 (by decide)
    have hlabel : gBorneol.atoms (σ 2) = gBorneol.atoms 2 := h.2.2.1 2 (by decide)
    have hbond : gBorneol.bo 0 (σ 2) ≠ 0 := by
      have h' := h.2.2.2 0 2 (by decide) (by decide)
      rw [h0] at h'; rw [h']; decide
    have key : ∀ x, x < 11 → gBorneol.atoms x = gBorneol.atoms 2 →
        gBorneol.bo 0 x ≠ 0 → x = 2 ∨ x = 5 := by decide
    rcases key _ hbound hlabel hbond with h' | h'
    · exact h'
    · have hh : σ (σ 2) = 2 := h.2.1 2 (by decide)
      rw [h', h5] at hh; omega
  have h8 : σ 8 = 8 ∨ σ 8 = 9 := by
    have hbound : σ 8 < 11 := h.1 8 (by decide)
    have hlabel : gBorneol.atoms (σ 8) = gBorneol.atoms 8 := h.2.2.1 8 (by decide)
    have hbond : gBorneol.bo 6 (σ 8) ≠ 0 := by
      have h' := h.2.2.2 6 8 (by decide) (by decide)
      rw [h6] at h'; rw [h']; decide
    have key : ∀ x, x < 11 → gBorneol.atoms x = gBorneol.atoms 8 →
        gBorneol.bo 6 x ≠ 0 → x = 8 ∨ x = 9 := by decide
    exact key _ hbound hlabel hbond
  rcases h8 with h8 | h8
  · have h9 : σ 9 = 9 := by
      have hbound : σ 9 < 11 := h.1 9 (by decide)
      have hlabel : gBorneol.atoms (σ 9) = gBorneol.atoms 9 := h.2.2.1 9 (by decide)
      have hbond : gBorneol.bo 6 (σ 9) ≠ 0 := by
        have h' := h.2.2.2 6 9 (by decide) (by decide)
        rw [h6] at h'; rw [h']; decide
      have key : ∀ x, x < 11 → gBorneol.atoms x = gBorneol.atoms 9 →
          gBorneol.bo 6 x ≠ 0 → x = 8 ∨ x = 9 := by decide
      rcases key _ hbound hlabel hbond with h' | h'
      · have hh : σ (σ 9) = 9 := h.2.1 9 (by decide)
        rw [h', h8] at hh; omega
      · exact h'
    left
    intro u hu
    interval_cases u <;> assumption
  · have h9 : σ 9 = 8 := by
      have hh : σ (σ 8) = 8 := h.2.1 8 (by decide)
      rw [h8] at hh; exact hh
    right
    refine ⟨h8, h9, ?_⟩
    intro u hu h8n h9n
    interval_cases u <;> first | exact absurd rfl h8n | exact absurd rfl h9n | assumption

/-- Every valid involutory symmetry of the drawn linalool graph is the
    identity or the alkene-methyl swap (9 10); in both cases the carbinol
    carbon 1 and its four pairwise inequivalent substituents 0 (OH), 2
    (vinyl CH), 4 (chain CH₂), 8 (methyl) are fixed. -/
theorem linalool_sym_cases (σ : ℕ → ℕ) (h : gLinalool.Valid 11 σ) :
    (∀ u, u < 11 → σ u = u) ∨
    (σ 9 = 10 ∧ σ 10 = 9 ∧ ∀ u, u < 11 → u ≠ 9 → u ≠ 10 → σ u = u) := by
  have h0 : σ 0 = 0 := gLinalool.fixed_of_unique h (by decide) (by decide)
  have h3 : σ 3 = 3 := gLinalool.fixed_of_unique h (by decide) (by decide)
  have h7 : σ 7 = 7 := gLinalool.fixed_of_unique h (by decide) (by decide)
  have h1 : σ 1 = 1 := gLinalool.fixed_of_nb h (by decide) (by decide) (by decide) h0 (by decide)
  have h2 : σ 2 = 2 := gLinalool.fixed_of_nb h (by decide) (by decide) (by decide) h1 (by decide)
  have h4 : σ 4 = 4 := gLinalool.fixed_of_nb h (by decide) (by decide) (by decide) h1 (by decide)
  have h8 : σ 8 = 8 := gLinalool.fixed_of_nb h (by decide) (by decide) (by decide) h1 (by decide)
  have h5 : σ 5 = 5 := gLinalool.fixed_of_nb h (by decide) (by decide) (by decide) h4 (by decide)
  have h6 : σ 6 = 6 := gLinalool.fixed_of_nb h (by decide) (by decide) (by decide) h5 (by decide)
  have h9 : σ 9 = 9 ∨ σ 9 = 10 := by
    have hbound : σ 9 < 11 := h.1 9 (by decide)
    have hlabel : gLinalool.atoms (σ 9) = gLinalool.atoms 9 := h.2.2.1 9 (by decide)
    have hbond : gLinalool.bo 7 (σ 9) ≠ 0 := by
      have h' := h.2.2.2 7 9 (by decide) (by decide)
      rw [h7] at h'; rw [h']; decide
    have key : ∀ x, x < 11 → gLinalool.atoms x = gLinalool.atoms 9 →
        gLinalool.bo 7 x ≠ 0 → x = 9 ∨ x = 10 := by decide
    exact key _ hbound hlabel hbond
  rcases h9 with h9 | h9
  · have h10 : σ 10 = 10 := by
      have hbound : σ 10 < 11 := h.1 10 (by decide)
      have hlabel : gLinalool.atoms (σ 10) = gLinalool.atoms 10 := h.2.2.1 10 (by decide)
      have hbond : gLinalool.bo 7 (σ 10) ≠ 0 := by
        have h' := h.2.2.2 7 10 (by decide) (by decide)
        rw [h7] at h'; rw [h']; decide
      have key : ∀ x, x < 11 → gLinalool.atoms x = gLinalool.atoms 10 →
          gLinalool.bo 7 x ≠ 0 → x = 9 ∨ x = 10 := by decide
      rcases key _ hbound hlabel hbond with h' | h'
      · have hh : σ (σ 10) = 10 := h.2.1 10 (by decide)
        rw [h', h9] at hh; omega
      · exact h'
    left
    intro u hu
    interval_cases u <;> assumption
  · have h10 : σ 10 = 9 := by
      have hh : σ (σ 9) = 9 := h.2.1 9 (by decide)
      rw [h9] at hh; exact hh
    right
    refine ⟨h9, h10, ?_⟩
    intro u hu h9n h10n
    interval_cases u <;> first | exact absurd rfl h9n | exact absurd rfl h10n | assumption

/-- Every valid involutory symmetry of the drawn umbellulone graph is the
    identity or the isopropyl-methyl swap (9 10); in both cases the whole
    cage 0,1,2,4,5,6,7,8 (and the methyl 3) is fixed. -/
theorem umbellulone_sym_cases (σ : ℕ → ℕ) (h : gUmbellulone.Valid 11 σ) :
    (∀ u, u < 11 → σ u = u) ∨
    (σ 9 = 10 ∧ σ 10 = 9 ∧ ∀ u, u < 11 → u ≠ 9 → u ≠ 10 → σ u = u) := by
  have h1 : σ 1 = 1 := gUmbellulone.fixed_of_unique h (by decide) (by decide)
  have h0 : σ 0 = 0 := gUmbellulone.fixed_of_unique h (by decide) (by decide)
  have h2 : σ 2 = 2 := gUmbellulone.fixed_of_nb h (by decide) (by decide) (by decide) h0 (by decide)
  have h8 : σ 8 = 8 := gUmbellulone.fixed_of_nb h (by decide) (by decide) (by decide) h0 (by decide)
  have h3 : σ 3 = 3 := gUmbellulone.fixed_of_nb h (by decide) (by decide) (by decide) h2 (by decide)
  have h4 : σ 4 = 4 := gUmbellulone.fixed_of_nb h (by decide) (by decide) (by decide) h2 (by decide)
  have h5 : σ 5 = 5 := gUmbellulone.fixed_of_nb h (by decide) (by decide) (by decide) h4 (by decide)
  have h6 : σ 6 = 6 := gUmbellulone.fixed_of_nb h (by decide) (by decide) (by decide) h4 (by decide)
  have h7 : σ 7 = 7 := by
    have hbound : σ 7 < 11 := h.1 7 (by decide)
    have hlabel : gUmbellulone.atoms (σ 7) = gUmbellulone.atoms 7 := h.2.2.1 7 (by decide)
    have hbond : gUmbellulone.bo 6 (σ 7) ≠ 0 := by
      have h' := h.2.2.2 6 7 (by decide) (by decide)
      rw [h6] at h'; rw [h']; decide
    have key : ∀ x, x < 11 → gUmbellulone.atoms x = gUmbellulone.atoms 7 →
        gUmbellulone.bo 6 x ≠ 0 → x = 4 ∨ x = 7 := by decide
    rcases key _ hbound hlabel hbond with h' | h'
    · have hh : σ (σ 7) = 7 := h.2.1 7 (by decide)
      rw [h', h4] at hh; omega
    · exact h'
  have h9 : σ 9 = 9 ∨ σ 9 = 10 := by
    have hbound : σ 9 < 11 := h.1 9 (by decide)
    have hlabel : gUmbellulone.atoms (σ 9) = gUmbellulone.atoms 9 := h.2.2.1 9 (by decide)
    have hbond : gUmbellulone.bo 7 (σ 9) ≠ 0 := by
      have h' := h.2.2.2 7 9 (by decide) (by decide)
      rw [h7] at h'; rw [h']; decide
    have key : ∀ x, x < 11 → gUmbellulone.atoms x = gUmbellulone.atoms 9 →
        gUmbellulone.bo 7 x ≠ 0 → x = 9 ∨ x = 10 := by decide
    exact key _ hbound hlabel hbond
  rcases h9 with h9 | h9
  · have h10 : σ 10 = 10 := by
      have hbound : σ 10 < 11 := h.1 10 (by decide)
      have hlabel : gUmbellulone.atoms (σ 10) = gUmbellulone.atoms 10 := h.2.2.1 10 (by decide)
      have hbond : gUmbellulone.bo 7 (σ 10) ≠ 0 := by
        have h' := h.2.2.2 7 10 (by decide) (by decide)
        rw [h7] at h'; rw [h']; decide
      have key : ∀ x, x < 11 → gUmbellulone.atoms x = gUmbellulone.atoms 10 →
          gUmbellulone.bo 7 x ≠ 0 → x = 9 ∨ x = 10 := by decide
      rcases key _ hbound hlabel hbond with h' | h'
      · have hh : σ (σ 10) = 10 := h.2.1 10 (by decide)
        rw [h', h9] at hh; omega
      · exact h'
    left
    intro u hu
    interval_cases u <;> assumption
  · have h10 : σ 10 = 9 := by
      have hh : σ (σ 9) = 9 := h.2.1 9 (by decide)
      rw [h9] at hh; exact hh
    right
    refine ⟨h9, h10, ?_⟩
    intro u hu h9n h10n
    interval_cases u <;> first | exact absurd rfl h9n | exact absurd rfl h10n | assumption

/-! ## 7. Mirror-plane eliminations (trusted laws as explicit hypotheses) -/

/-- Borneol cannot have a mirror plane: a realised mirror is a non-identity
    valid involution (`law_mirror`), hence the gem-methyl swap (8 9) — but a
    mirror of the rigid bicyclo[2.2.1] cage must move a cage atom
    (`law_cage`), and (8 9) fixes them all. -/
theorem borneol_no_mirror
    {RealizedMirror : Gr → (ℕ → ℕ) → Prop} {NonPlanarRigidCage : Gr → List ℕ → Prop}
    (law_cage : ∀ (g : Gr) (C : List ℕ) (σ : ℕ → ℕ), RealizedMirror g σ →
      g.Valid g.n σ → NonPlanarRigidCage g C → (∀ u, u ∈ C → σ u = u) → False)
    (hC : NonPlanarRigidCage gBorneol [0, 1, 2, 3, 4, 5, 6])
    {σ : ℕ → ℕ} (hσ : gBorneol.Valid gBorneol.n σ) (hR : RealizedMirror gBorneol σ)
    (hm : ∃ u, u < gBorneol.n ∧ σ u ≠ u) : False := by
  rcases borneol_sym_cases σ hσ with hid | ⟨_h89, _h98, hfix⟩
  · obtain ⟨u, hu, hne⟩ := hm
    exact hne (hid u hu)
  · exact law_cage gBorneol [0, 1, 2, 3, 4, 5, 6] σ hR hσ hC (by
      intro u hu
      have hmem : u ∈ ([0, 1, 2, 3, 4, 5, 6] : List ℕ) := hu
      fin_cases hmem <;> exact hfix _ (by decide) (by decide) (by decide))

/-- Linalool cannot have a mirror plane: a realised non-identity mirror
    would have to fix the tetrahedral carbinol carbon 1 together with its
    four pairwise inequivalent substituents 0 (OH), 2 (vinyl CH), 4 (chain
    CH₂), 8 (methyl) — impossible (`law_tetra`). -/
theorem linalool_no_mirror
    {RealizedMirror : Gr → (ℕ → ℕ) → Prop}
    (law_tetra : ∀ (g : Gr) (σ : ℕ → ℕ) (c a b d e : ℕ), RealizedMirror g σ →
      g.Valid g.n σ → c < g.n → (g.atoms c).1 = 0 →
      g.bo c a ≠ 0 → g.bo c b ≠ 0 → g.bo c d ≠ 0 → g.bo c e ≠ 0 →
      a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
      g.atoms a ≠ g.atoms b → g.atoms a ≠ g.atoms d → g.atoms a ≠ g.atoms e →
      g.atoms b ≠ g.atoms d → g.atoms b ≠ g.atoms e → g.atoms d ≠ g.atoms e →
      σ c = c → σ a = a → σ b = b → σ d = d → σ e = e → False)
    {σ : ℕ → ℕ} (hσ : gLinalool.Valid gLinalool.n σ) (hR : RealizedMirror gLinalool σ)
    (hm : ∃ u, u < gLinalool.n ∧ σ u ≠ u) : False := by
  rcases linalool_sym_cases σ hσ with hid | ⟨_h910, _h109, hfix⟩
  · obtain ⟨u, hu, hne⟩ := hm
    exact hne (hid u hu)
  · exact law_tetra gLinalool σ 1 0 2 4 8 hR hσ (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hfix 1 (by decide) (by decide) (by decide))
      (hfix 0 (by decide) (by decide) (by decide))
      (hfix 2 (by decide) (by decide) (by decide))
      (hfix 4 (by decide) (by decide) (by decide))
      (hfix 8 (by decide) (by decide) (by decide))

/-- Umbellulone (10) cannot have a mirror plane: its only non-identity
    labelled symmetry is the isopropyl-methyl swap (9 10), which fixes the
    whole rigid bicyclo[3.1.0] cage — impossible (`law_cage`). -/
theorem umbellulone_no_mirror
    {RealizedMirror : Gr → (ℕ → ℕ) → Prop} {NonPlanarRigidCage : Gr → List ℕ → Prop}
    (law_cage : ∀ (g : Gr) (C : List ℕ) (σ : ℕ → ℕ), RealizedMirror g σ →
      g.Valid g.n σ → NonPlanarRigidCage g C → (∀ u, u ∈ C → σ u = u) → False)
    (hC : NonPlanarRigidCage gUmbellulone [0, 1, 2, 4, 5, 6, 7, 8])
    {σ : ℕ → ℕ} (hσ : gUmbellulone.Valid gUmbellulone.n σ) (hR : RealizedMirror gUmbellulone σ)
    (hm : ∃ u, u < gUmbellulone.n ∧ σ u ≠ u) : False := by
  rcases umbellulone_sym_cases σ hσ with hid | ⟨_h910, _h109, hfix⟩
  · obtain ⟨u, hu, hne⟩ := hm
    exact hne (hid u hu)
  · exact law_cage gUmbellulone [0, 1, 2, 4, 5, 6, 7, 8] σ hR hσ hC (by
      intro u hu
      have hmem : u ∈ ([0, 1, 2, 4, 5, 6, 7, 8] : List ℕ) := hu
      fin_cases hmem <;> exact hfix _ (by decide) (by decide) (by decide))

/-! ## 8. Linalool → cineole cyclisation consistency (acidic medium) -/

/-- Atom correspondence from the drawn linalool graph to the drawn cineole
    graph realising the classical acid-catalysed cyclisation (linalool →
    α-terpineol-type intermediate → 1,8-cineole): OH oxygen ↦ ether oxygen,
    carbinol carbon ↦ methylated bridgehead, alkene C(Me)₂ ↦ gem-dimethyl
    carbon, alkene CH ↦ second bridgehead, vinyl group and chain ↦ the two
    –CH₂–CH₂– bridges. -/
def linToCin : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 10 | 4 => 7 | 5 => 8
  | 6 => 6 | 7 => 3 | 8 => 2 | 9 => 4 | 10 => 5 | _ => 0

theorem linToCin_inj : ∀ i j : Fin 11, linToCin i = linToCin j → i = j := by
  decide

/-- Every bond of linalool maps onto a bond of cineole: the connectivity of
    the product is realised by the starting skeleton plus two new σ bonds. -/
theorem cyclisation_preserved :
    ∀ i j : Fin 11, gLinalool.bo i j ≠ 0 →
      gCineole.bo (linToCin i.val) (linToCin j.val) ≠ 0 := by
  decide

/-- Elements are preserved under the correspondence (C ↦ C, O ↦ O). -/
theorem cyclisation_elements :
    ∀ i : Fin 11, elemOf (gCineole.atoms (linToCin i.val)) = elemOf (gLinalool.atoms i) := by
  decide

/-- The new ether σ-bond of cineole (0–3) connects atoms that carry an O–H
    and an alkene carbon in linalool, and which are non-bonded in linalool:
    the O–H attacks the C=C bond during the acid-catalysed cyclisation. -/
theorem cyclisation_newbond1 :
    gLinalool.bo 0 7 = 0 ∧ gCineole.bo 0 3 ≠ 0 ∧
    (gLinalool.atoms 0).1 = 2 ∧ (gLinalool.atoms 7).1 = 1 :=
  ⟨by decide, by decide, rfl, rfl⟩

/-- The new ring-closing C–C σ-bond of cineole (6–10) connects two alkene
    carbons of linalool that are non-bonded in linalool. -/
theorem cyclisation_newbond2 :
    gLinalool.bo 3 6 = 0 ∧ gCineole.bo 6 10 ≠ 0 ∧
    (gLinalool.atoms 3).1 = 1 ∧ (gLinalool.atoms 6).1 = 1 :=
  ⟨by decide, by decide, rfl, rfl⟩

/-! ## 9. The identification of X and Y -/

/-- **T1-A1 answer.**  X (the starting material) is compound **6**
    (linalool); Y (the product with a plane of symmetry) is compound **3**
    (1,8-cineole).

    Encoded in `Fin 10` (compound number minus one): `X = ⟨5⟩`, `Y = ⟨2⟩`.

    All stereochemical/mechanistic input beyond the problem page is passed
    explicitly as hypotheses; the conclusion is a fully mechanised case
    analysis over the four C₁₀H₁₈O candidates using the `decide`-checked
    symmetry classifications above. -/
theorem t1_a1_answer
    (HasMirrorPlane : Gr → Prop)
    (RealizedMirror : Gr → (ℕ → ℕ) → Prop)
    (NonPlanarRigidCage : Gr → List ℕ → Prop)
    (Isom : Fin 10 → Fin 10 → Prop)
    (law_mirror : ∀ g : Gr, HasMirrorPlane g →
      ∃ σ : ℕ → ℕ, g.Valid g.n σ ∧ RealizedMirror g σ ∧ ∃ u, u < g.n ∧ σ u ≠ u)
    (law_tetra : ∀ (g : Gr) (σ : ℕ → ℕ) (c a b d e : ℕ), RealizedMirror g σ →
      g.Valid g.n σ → c < g.n → (g.atoms c).1 = 0 →
      g.bo c a ≠ 0 → g.bo c b ≠ 0 → g.bo c d ≠ 0 → g.bo c e ≠ 0 →
      a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
      g.atoms a ≠ g.atoms b → g.atoms a ≠ g.atoms d → g.atoms a ≠ g.atoms e →
      g.atoms b ≠ g.atoms d → g.atoms b ≠ g.atoms e → g.atoms d ≠ g.atoms e →
      σ c = c → σ a = a → σ b = b → σ d = d → σ e = e → False)
    (law_cage : ∀ (g : Gr) (C : List ℕ) (σ : ℕ → ℕ), RealizedMirror g σ →
      g.Valid g.n σ → NonPlanarRigidCage g C → (∀ u, u ∈ C → σ u = u) → False)
    (law_isomer_formula : ∀ x y : Fin 10, Isom x y → printedFormula x = printedFormula y)
    (law_ether_cyclisation : ∀ (x y : Fin 10) (gy : Gr), Isom x y →
      graphOf y = some gy → (∃ u : Fin gy.n, (gy.atoms u).1 = 3) →
      (∃ gx : Gr, graphOf x = some gx ∧
        (∃ u : Fin gx.n, (gx.atoms u).1 = 2) ∧
        (∃ i j : Fin gx.n, gx.bo i j = 2)))
    (hCageB : NonPlanarRigidCage gBorneol [0, 1, 2, 3, 4, 5, 6])
    (hCageU : NonPlanarRigidCage gUmbellulone [0, 1, 2, 4, 5, 6, 7, 8])
    (X Y : Fin 10)
    (hXY : X ≠ Y)
    (hiso : Isom X Y)
    (hYm : ∀ gy : Gr, graphOf Y = some gy → HasMirrorPlane gy) :
    X = ⟨5, by omega⟩ ∧ Y = ⟨2, by omega⟩ := by
  have hform : printedFormula X = printedFormula Y := law_isomer_formula X Y hiso
  have hcls := shared_formula_class X Y hform
  have ⟨hA, hB⟩ : ((X = (⟨1, by decide⟩ : Fin 10) ∨ X = ⟨2, by decide⟩
        ∨ X = ⟨5, by decide⟩ ∨ X = ⟨9, by decide⟩) ∧
      (Y = (⟨1, by decide⟩ : Fin 10) ∨ Y = ⟨2, by decide⟩
        ∨ Y = ⟨5, by decide⟩ ∨ Y = ⟨9, by decide⟩)) :=
    hcls.elim (fun h ↦ absurd h hXY) id
  rcases hB with rfl | rfl | rfl | rfl
  · -- Y = 2 (borneol): impossible, borneol has no mirror plane.
    exfalso
    obtain ⟨σ, hσ, hR, hm⟩ := law_mirror gBorneol (hYm gBorneol rfl)
    exact borneol_no_mirror law_cage hCageB hσ hR hm
  · -- Y = 3 (cineole): the only symmetric candidate.  Now identify X.
    refine ⟨?_, rfl⟩
    rcases hA with hX | hX | hX | hX
    · -- X = 2 (borneol): no C=C bond, so no acid-catalysed ether cyclisation.
      exfalso
      obtain ⟨gx, hgx, _hOH, hDB⟩ :=
        law_ether_cyclisation X ⟨2, by decide⟩ gCineole hiso rfl cineole_etherO
      rw [hX] at hgx
      have hgg : gx = gBorneol := Option.some.inj hgx.symm
      subst hgg
      obtain ⟨i, j, hbo⟩ := hDB
      have hnb : gBorneol.n = 11 := rfl
      exact borneol_noCC (i.cast hnb) (j.cast hnb) hbo
    · -- X = 3 = Y, but X and Y are different substances.
      exact absurd hX hXY
    · exact hX
    · -- X = 10 (umbellulone): no O–H, so no acid-catalysed ether cyclisation.
      exfalso
      obtain ⟨gx, hgx, hOH, _hDB⟩ :=
        law_ether_cyclisation X ⟨2, by decide⟩ gCineole hiso rfl cineole_etherO
      rw [hX] at hgx
      have hgg : gx = gUmbellulone := Option.some.inj hgx.symm
      subst hgg
      obtain ⟨u, hlab⟩ := hOH
      have hnu : gUmbellulone.n = 11 := rfl
      exact umbellulone_noOH (u.cast hnu) hlab
  · -- Y = 6 (linalool): impossible, linalool has no mirror plane.
    exfalso
    obtain ⟨σ, hσ, hR, hm⟩ := law_mirror gLinalool (hYm gLinalool rfl)
    exact linalool_no_mirror law_tetra hσ hR hm
  · -- Y = 10 (umbellulone): impossible, no mirror plane.
    exfalso
    obtain ⟨σ, hσ, hR, hm⟩ := law_mirror gUmbellulone (hYm gUmbellulone rfl)
    exact umbellulone_no_mirror law_cage hCageU hσ hR hm

/-- Corollary in answer-sheet numbering (1–10): X is compound 6, Y is
    compound 3. -/
theorem t1_a1_answer_compound_numbers
    (HasMirrorPlane : Gr → Prop)
    (RealizedMirror : Gr → (ℕ → ℕ) → Prop)
    (NonPlanarRigidCage : Gr → List ℕ → Prop)
    (Isom : Fin 10 → Fin 10 → Prop)
    (law_mirror : ∀ g : Gr, HasMirrorPlane g →
      ∃ σ : ℕ → ℕ, g.Valid g.n σ ∧ RealizedMirror g σ ∧ ∃ u, u < g.n ∧ σ u ≠ u)
    (law_tetra : ∀ (g : Gr) (σ : ℕ → ℕ) (c a b d e : ℕ), RealizedMirror g σ →
      g.Valid g.n σ → c < g.n → (g.atoms c).1 = 0 →
      g.bo c a ≠ 0 → g.bo c b ≠ 0 → g.bo c d ≠ 0 → g.bo c e ≠ 0 →
      a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
      g.atoms a ≠ g.atoms b → g.atoms a ≠ g.atoms d → g.atoms a ≠ g.atoms e →
      g.atoms b ≠ g.atoms d → g.atoms b ≠ g.atoms e → g.atoms d ≠ g.atoms e →
      σ c = c → σ a = a → σ b = b → σ d = d → σ e = e → False)
    (law_cage : ∀ (g : Gr) (C : List ℕ) (σ : ℕ → ℕ), RealizedMirror g σ →
      g.Valid g.n σ → NonPlanarRigidCage g C → (∀ u, u ∈ C → σ u = u) → False)
    (law_isomer_formula : ∀ x y : Fin 10, Isom x y → printedFormula x = printedFormula y)
    (law_ether_cyclisation : ∀ (x y : Fin 10) (gy : Gr), Isom x y →
      graphOf y = some gy → (∃ u : Fin gy.n, (gy.atoms u).1 = 3) →
      (∃ gx : Gr, graphOf x = some gx ∧
        (∃ u : Fin gx.n, (gx.atoms u).1 = 2) ∧
        (∃ i j : Fin gx.n, gx.bo i j = 2)))
    (hCageB : NonPlanarRigidCage gBorneol [0, 1, 2, 3, 4, 5, 6])
    (hCageU : NonPlanarRigidCage gUmbellulone [0, 1, 2, 4, 5, 6, 7, 8])
    (X Y : Fin 10)
    (hXY : X ≠ Y)
    (hiso : Isom X Y)
    (hYm : ∀ gy : Gr, graphOf Y = some gy → HasMirrorPlane gy) :
    X.val = 5 ∧ Y.val = 2 := by
  obtain ⟨hX, hY⟩ := t1_a1_answer HasMirrorPlane RealizedMirror NonPlanarRigidCage Isom
    law_mirror law_tetra law_cage law_isomer_formula law_ether_cyclisation
    hCageB hCageU X Y hXY hiso hYm
  exact ⟨by rw [hX], by rw [hY]⟩

#print axioms t1_a1_answer
#print axioms t1_a1_answer_compound_numbers

end IChO2026T1A1
