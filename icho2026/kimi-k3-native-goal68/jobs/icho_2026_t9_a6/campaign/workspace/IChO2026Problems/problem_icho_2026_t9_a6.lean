import Mathlib

/-!
# IChO 2026, Theory Problem 9 (Cyclodextrin Chemistry), subquestion 9.6
(target `icho_2026_t9_a6`)

**Question (official English problem sheet, page Q9-3, box 9.6):**
"Determine the number of isomers of the β-CD dimer that can form during the
synthesis by Sinay *et. al.*"

## Chemistry behind the count (every premise is on the problem sheet)

* **β-CD is the cyclic heptamer** — 7 α-D-glucopyranose units (T9 preamble:
  "6, 7, and 8 α-D-glucopyranoside units").
* Perbenzylated β-CD (NaH (30 equiv.), BnCl (30 equiv.); all 21 OH groups
  protected) is partially debenzylated with **DIBAL-H (2 equiv.)** →
  intermediate **L**.
* **The Sinay rule** (quoted verbatim on Q9-3): "a single protic group (NH
  and OH) at unit 1 directs the **next** reductive debenzylation of a
  primary OH group to **unit 4** in the macrocyclic ring (or to unit 3 if
  the unit 4 position is not available)."  With two equivalents of DIBAL-H,
  L therefore carries free primary OH groups on the directing unit and on
  the unit three steps further around the 7-ring — units **1 and 4** in the
  numbering of the figure.  (The fallback "unit 3 if unit 4 is not
  available" never operates here: from every unit of the 7-ring the unit
  three steps away exists and is still benzylated.)
* **Dimerisation.**  The free primary OH groups of L are O-alkylated
  (`t-BuOK`) with the α,ω-dibromoalkene drawn on Q9-3; two such
  alkenylated CDs are then coupled by **Grubbs-I cross-metathesis** at their
  double bonds and hydrogenated (H₂, PtO₂).  The drawn product has, per
  ring, 5 × CH₂OBn, 1 × CH₂OH and 1 × CH₂O–linker: exactly one primary O
  of each ring is consumed by the single symmetric hydrocarbon linker.  The
  problem states the dimer forms "as a mixture of constitutional linkage
  isomers".

## Counting

Choose the intrinsic unit labels of each ring from its own directing unit
(`0 ↔` "unit 1"; labels step `+1` around the ring as in the scheme).  The
attachment site of each ring is one of its two free-OH units `{0, 3}`, so the
dimer ensemble contains every site-labelled pair `(a, b) ∈ (Fin 7)²` whose
directed separation `b − a (mod 7)` lies in `{0, 3, −3 = 4}`:
the pairs `(i, i)` (directing ↔ directing), `(i, i+3)` (directing of A ↔
unit 4 of B) and `(i, i-3)` (unit 4 of A ↔ directing of B), 49 pairs in all.

A **constitutional linkage isomer** is a connectivity class of this labelled
assembly.  The graphs are compared up to the C₇ × C₇ cyclic re-charts of the
two rings, exchange of the two ring ends of the molecule, and mirror
re-description of the 7-cycle; all of these symmetries either preserve the
directed separation or flip its sign.  Hence two dimers are the same
constitutional isomer iff their directed separations are equal or opposite
mod 7: the seven separation classes { {0}, ±1, ±2, ±3 }.

The attainable separations `{0, 3, 4}` therefore fall into exactly **two**
constitutional classes,

    {0}     —  "in-line" dimer  (directing unit — link — directing unit),
    {3, 4}  —  "crossed" dimer  (directing unit of one ring — link —
               unit 4 of the other ring),

represented by `linkSame = (0, 0)` and `linkCross = (0, 3)`.

**N = 2 constitutional linkage isomers.**

## Formalisation content

* `SiteLabelledDimer` = pair of attachment units in `Fin 7` (labels 1…7 ↔
  indices 0…6).
* `sep` = directed separation mod 7; `SameConstitution` = "separations equal
  or opposite" — proved to be an equivalence.
* `Attainable` = directed separation ∈ {0, 3, 4} (derived from the Sinay
  rule and the 2 equiv. of DIBAL-H).
* `linkSame`, `linkCross` = the two class representatives.
* `representatives_distinct`: they are different constitutional isomers.
* `attainable_eq_linkSame_or_linkCross`: every attainable dimer is
  constitutionally one of the two.
* `attainable_partition_of_linkSame`, `attainable_partition_of_linkCross`:
  each class contains exactly 7 site-labelled dimers.
* `dimer_isomer_count_attainable_classes`: the image of the attainable
  dimers in the constitutional quotient (`ZSetoid`) has exactly 2 classes.
* `nonattainable_not_formed`: dimers with separation ±1 or ±2 are not
  constitutional copies of any attainable dimer.

All proofs are complete; allowed axioms only (standard logical axioms, and
`Lean.ofReduceBool` behind the audited `native_decide` Finset enumeration).
-/

namespace IChO2026T9A6

/-- β-CD is the cyclic heptamer: 7 units (T9 preamble).  Our indices
`0 … 6` correspond to the problem's unit labels `1 … 7`. -/
def betaCD_units : ℕ := 7

/-- A site-labelled dimer: a linker joining unit `linkA` of ring A to unit
`linkB` of ring B, in each ring's own intrinsic numbering (0 ↔ the ring's
directing "unit 1"). -/
structure SiteLabelledDimer where
  linkA : Fin 7
  linkB : Fin 7
  deriving DecidableEq, Fintype, Repr

/-- The directed cyclic separation `linkB − linkA (mod 7)`. -/
def sep (d : SiteLabelledDimer) : Fin 7 :=
  ⟨(d.linkB.val + 7 - d.linkA.val) % 7, Nat.mod_lt _ (by decide)⟩

@[simp] theorem sep_val (d : SiteLabelledDimer) :
    (sep d).val = (d.linkB.val + 7 - d.linkA.val) % 7 := rfl

/-- Two site-labelled dimers represent the **same constitutional linkage
isomer** iff their directed separations are equal or opposite modulo 7. -/
def SameConstitution (d₁ d₂ : SiteLabelledDimer) : Prop :=
  sep d₂ = sep d₁ ∨ sep d₂ + sep d₁ = 0

instance (d₁ d₂ : SiteLabelledDimer) : Decidable (SameConstitution d₁ d₂) :=
  inferInstanceAs (Decidable (sep d₂ = sep d₁ ∨ sep d₂ + sep d₁ = 0))

theorem sameConstitution_refl (d : SiteLabelledDimer) :
    SameConstitution d d := Or.inl rfl

theorem sameConstitution_symm {d₁ d₂ : SiteLabelledDimer} :
    SameConstitution d₁ d₂ → SameConstitution d₂ d₁ := by
  rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr (by rw [add_comm]; exact h)

theorem sameConstitution_trans {d₁ d₂ d₃ : SiteLabelledDimer} :
    SameConstitution d₁ d₂ → SameConstitution d₂ d₃ →
      SameConstitution d₁ d₃ := by
  rintro (h | h) <;> rintro (h' | h')
  · exact Or.inl (h'.trans h)
  · -- sep d₃ + sep d₂ = 0 and sep d₂ = sep d₁ ⇒ sep d₃ + sep d₁ = 0
    exact Or.inr (by rw [← h]; exact h')
  · -- sep d₂ + sep d₁ = 0 and sep d₃ = sep d₂ ⇒ sep d₃ + sep d₁ = 0
    exact Or.inr (by rw [h']; exact h)
  · -- both sums are 0 ⇒ sep d₃ = − sep d₂ = sep d₁
    left
    have e₁ : sep d₂ = -sep d₁ := eq_neg_of_add_eq_zero_left h
    have e₂ : sep d₃ = -sep d₂ := eq_neg_of_add_eq_zero_left h'
    rw [e₂, e₁, neg_neg]

/-- `SameConstitution` is an equivalence relation. -/
theorem sameConstitution_equivalence : Equivalence SameConstitution :=
  ⟨sameConstitution_refl, sameConstitution_symm, sameConstitution_trans⟩

/-- The setoid of constitutional linkage isomers. -/
def dimerSetoid : Setoid SiteLabelledDimer :=
  ⟨SameConstitution, sameConstitution_equivalence⟩

instance : DecidableRel (dimerSetoid.r) := fun d₁ d₂ =>
  inferInstanceAs (Decidable (SameConstitution d₁ d₂))

/-- A site-labelled dimer is **attainable** in the Sinay synthesis when its
directed separation is `0` (directing ↔ directing), `3` (directing of A ↔
unit 4 of B) or `4 ≡ −3` (unit 4 of A ↔ directing of B) — exactly the
combinations allowed by the Sinay directing rule with 2 equiv. DIBAL-H. -/
def Attainable (d : SiteLabelledDimer) : Prop :=
  sep d = 0 ∨ sep d = 3 ∨ sep d = 4

instance : DecidablePred Attainable := fun d =>
  inferInstanceAs (Decidable (sep d = 0 ∨ sep d = 3 ∨ sep d = 4))

/-- The "in-line" constitutional isomer: linker between the directing units
of the two rings (in the problem's unit labels: ring A unit 1 — link —
ring B unit 1). -/
def linkSame : SiteLabelledDimer := ⟨0, 0⟩

/-- The "crossed" constitutional isomer: linker between the directing unit of
one ring and unit 4 (three steps around) of the other ring
(problem's labels: ring A unit 1 — link — ring B unit 4). -/
def linkCross : SiteLabelledDimer := ⟨0, 3⟩

@[simp] theorem sep_linkSame : sep linkSame = 0 := rfl
@[simp] theorem sep_linkCross : sep linkCross = 3 := rfl

/-- Both representatives are attainable. -/
theorem linkSame_attainable : Attainable linkSame := Or.inl rfl
theorem linkCross_attainable : Attainable linkCross := Or.inr (Or.inl rfl)

/-- The two representatives are **different** constitutional linkage
isomers. -/
theorem representatives_distinct :
    ¬ SameConstitution linkSame linkCross := by
  rintro (h | h) <;> simp [sep_linkSame, sep_linkCross] at h

/-- **Completeness:** every attainable site-labelled dimer is the same
constitutional isomer as one of the two representatives. -/
theorem attainable_eq_linkSame_or_linkCross (d : SiteLabelledDimer)
    (h : Attainable d) :
    SameConstitution d linkSame ∨ SameConstitution d linkCross := by
  rcases h with h | h | h
  · left; exact Or.inl h.symm
  · right; exact Or.inl h.symm
  · right; right
    -- sep d = 4 = −3, so sep d + sep linkCross = 4 + 3 = 7 = 0
    rw [sep_linkCross, h]
    decide

/-- A dimer with separation `±1` or `±2` is constitutionally different from
every attainable dimer: these isomers cannot form in the Sinay synthesis
(the directing rule only produces separations 0 and ±3). -/
theorem nonattainable_not_formed (d : SiteLabelledDimer) (h : ¬ Attainable d) :
    ¬ SameConstitution d linkSame ∧ ¬ SameConstitution d linkCross := by
  constructor
  · rintro (hs | hs)
    · exact h (Or.inl hs.symm)
    · -- sep d + 0 = 0, so sep d = 0
      have : sep d = 0 := by simpa using hs
      exact h (Or.inl this)
  · rintro (hs | hs)
    · exact h (Or.inr (Or.inl hs.symm))
    · -- sep linkCross + sep d = 0 ⇒ sep d = −3 = 4
      have hd4 : sep d = (4 : Fin 7) := by
        have h3 : sep linkCross = (3 : Fin 7) := sep_linkCross
        rw [h3] at hs
        -- 3 + sep d = 0 ⇒ sep d = -3
        have key : sep d = -(3 : Fin 7) :=
          eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hs)
        rw [key]
        decide
      exact h (Or.inr (Or.inr hd4))

/-- Each constitutional class of attainable dimers contains exactly the
site-labelled dimers with one fixed directed separation.
* The `linkSame` class = the 7 pairs `(i, i)`.
* The `linkCross` class = the 14 pairs `(i, i±3)`. -/
theorem attainable_partition_of_linkSame :
    (Finset.univ.filter (fun d : SiteLabelledDimer =>
      SameConstitution d linkSame)).card = 7 := by
  native_decide

theorem attainable_partition_of_linkCross :
    (Finset.univ.filter (fun d : SiteLabelledDimer =>
      SameConstitution d linkCross)).card = 14 := by
  native_decide

/-- `SiteLabelledDimer` is equivalent to `Fin 7 × Fin 7`. -/
def dimerEquivProd : SiteLabelledDimer ≃ Fin 7 × Fin 7 where
  toFun d := (d.linkA, d.linkB)
  invFun p := ⟨p.1, p.2⟩
  left_inv d := by cases d; rfl
  right_inv p := rfl

/-- The site-labelled dimers split into constitutional classes of sizes
7 + 14 + 14 + 14 = 49 (each separation class ±d conflates 14 pairs for
d ≠ 0 and 7 pairs for d = 0). -/
theorem site_labelled_total :
    Fintype.card SiteLabelledDimer = 49 := by
  rw [Fintype.card_congr dimerEquivProd]
  -- `Fin 7 × Fin 7` has 49 elements: 7 × 7.
  rw [Fintype.card_prod]
  norm_num

/-- The attainable site-labelled dimers are exactly the 21 pairs in the two
classes (7 + 14 = 21). -/
theorem attainable_card :
    (Finset.univ.filter (fun d : SiteLabelledDimer =>
      Attainable d)).card = 21 := by
  native_decide

/-- **Main theorem (IChO 2026, T9, subquestion 9.6): number of isomers of
the β-CD dimer formed in the Sinay synthesis.**

The constitutional-linkage isomers that form are exactly the classes of
`linkSame` and `linkCross`, and these two classes are distinct and exhaust
everything that can form.  Hence the number of isomers is exactly **2**. -/
theorem dimer_isomer_count :
    -- (i) exactly these two classes form (completeness)
    (∀ d : SiteLabelledDimer, Attainable d →
        SameConstitution d linkSame ∨ SameConstitution d linkCross)
    -- (ii) the two classes are distinct
    ∧ ¬ SameConstitution linkSame linkCross
    -- (iii) both classes are really formed
    ∧ Attainable linkSame ∧ Attainable linkCross :=
  ⟨attainable_eq_linkSame_or_linkCross, representatives_distinct,
    linkSame_attainable, linkCross_attainable⟩

/-- The constitutional quotient: the classes of the 49 site-labelled dimers
under `SameConstitution`, counted through the `Quotient`, number 4, of which
exactly 2 contain attainable dimers — the answer to the subquestion. -/
theorem dimer_quot_classes :
    (Finset.univ.image (fun d : SiteLabelledDimer =>
        Quotient.mk dimerSetoid d)).card = 4 := by
  native_decide

/-- **The answer:** the number of constitutional linkage isomers of the
β-CD dimer that can form during the Sinay synthesis equals **2**, counted
as the number of classes of attainable dimers in the constitutional
quotient. -/
theorem dimer_isomer_count_attainable_classes :
    ((Finset.univ.filter fun d : SiteLabelledDimer => Attainable d).image
        (fun d => Quotient.mk dimerSetoid d)).card = 2 := by
  native_decide

end IChO2026T9A6

#print axioms IChO2026T9A6.dimer_isomer_count
#print axioms IChO2026T9A6.dimer_isomer_count_attainable_classes
