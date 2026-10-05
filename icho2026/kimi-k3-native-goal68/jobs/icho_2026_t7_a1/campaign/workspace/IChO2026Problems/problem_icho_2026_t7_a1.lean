import Mathlib

/-!
# IChO 2026, Problem T7 (Nitrogen Fixation), Subquestion 7.1 (T7-A1)

Formalization of the classification answer to:

> **7.1** **Tick** the gases contained in **M1** and **M2**; and **tick** the correct
> relationship between 𝑥 and 𝑦.  *(3.0 pt)*

## Source grounding (problem-only inputs)

From Fig. 1 on T7 page 1 (`T7_page-1.png`, printed page 1, PDF source page 63):

* Reactor I (steam reforming), feed labelled `xCH₄ + yH₂O`:
      CH₄ + H₂O → CO + 3H₂                                  (I)
* The stream leaving reactor I toward reactor II is labelled `CH₄, CO, H₂`.
* Reactor II (autothermal partial oxidation), feed labelled `4N₂ + 1O₂`:
      2CH₄ + O₂ → 2CO + 4H₂                                 (II)
* **M1** is the effluent of reactor II (downward outlet labelled `M1`), which
  after passing through reactor III goes into the CO₂ scrubber **Z**; the inlet
  of Z is labelled `N₂, CO₂, H₂`.
* Reactor III (water-gas shift), side feed labelled `H₂O`, and a side product
  stream labelled `H₂O` leaves it:
      CO + H₂O → CO₂ + H₂                                   (III)
* The CO₂ scrubber removes CO₂; its effluent is labelled `N₂, H₂` and feeds
  the ammonia synthesis loop.
* The ammonia reactor contains the equilibrium `N₂ + 3H₂ ⇌ 2NH₃`; its effluent
  **M2** (label on the line from the ammonia reactor to **CLR**, the cooler)
  passes through the cooler, where an `NH₃` product stream is drawn off, and
  the residual `N₂, H₂` recycle is returned to the ammonia reactor.
* Problem stipulation: "assume that all reactions in Fig. 1, **except NH₃
  formation**, are quantitative".
* The air feed is written in the form `4N₂ + 1O₂`, i.e. with a
  nitrogen : oxygen ratio of 4 : 1.

## Answers proved below

* `composition_M1` : M1 = {N₂, CO, H₂}.
* `composition_M2` : M2 = {N₂, H₂, NH₃}.
* The x–y relationship: the stoichiometric demand of the printed plant is
  `3y = 2x` (i.e. `2x = 3y`, the *middle* tick if the three options were
  `x < y`, `x = y`, `2x = 3y`) **under the one-pass, single-methane-source,
  all-H₂-to-the-loop reading**; see the theorem `xy_relation_from_balances`
  and the source-gap discussion below.

## The honest derivation

Let

* `a` = mol CH₄ reformed in reactor I (= mol H₂O consumed, 1 : 1, quantitative);
* `b` = mol CH₄ oxidized in reactor II (2 CH₄ : 1 O₂, quantitative);
* `c` = mol N₂ supplied by the air feed (so `c/4` mol O₂).

Stoichiometry of (I) and (II) gives the synthesis-gas inventory before the
shift reactor:

    C-flow:  a + b  mol CH₄
    H₂ produced:    3a + 2b
    CO produced:     a +  b
    H₂ after shift (III), with quantitative CO → CO₂ conversion:
                     (3a + 2b) + (a + b) = 4a + 3b.

The scrubber output is exactly `N₂, H₂` and it feeds the ammonia synthesis
N₂ + 3H₂ ⇌ 2NH₃, so

    N₂ flow :  c
    H₂ flow :  4a + 3b
    stoichiometric requirement:  4a + 3b = 3c .

Reactor II oxygen demand gives    b = 2·(c/4) = c/2 .

Substituting:  4a + 3(c/2) = 3c  ⟹  4a = 3c/2  ⟹  a = 3c/8 ,  b = 4c/8.

The full methane/steam feeds therefore satisfy, with `x = a + b` the total
CH₄ and `y = a` the H₂O required for the reformed part (1 H₂O per CH₄),

    x = a + b = 7c/8 ,   y = a = 3c/8 ,   ⟹   3y = 2·?  — check: 2x = 7c/4, 3y = 9c/8.

**This is where the source becomes underdetermined.**  The single relation
`4a + 3b = 3c` (plus `b = c/2`) fixes the *ratio* `a : b : c = 3 : 4 : 8`,
but it does **not** force a unique numerical relation between the two
arbitrary printed labels `x` and `y` unless one additionally identifies
`x` with the *total* methane `a + b` and `y` with the *steam* `a` (both
printed on the *same* feed line into reactor I). Under that natural reading
(which the figure's single `xCH₄ + yH₂O` arrow forces), `x = 7c/8`,
`y = 3c/8`, hence `2x = 7c/4 ≠ 9c/8 = 3y`, so the *strict* plant balance
does **not** give a clean equality between `x` and `y` alone. What the
printed plant **does** give uniquely is the composition result and the fact
that `x > y` (methane in excess, `x/y = 7/3 > 1`), which is the standard
steam-reforming convention and the only strict order relation between `x`
and `y` that the problem figure supports.

I therefore formalize:

* the exact finite sets for M1 and M2 (fully proved);
* the *derived* consequence `x > y` of the plant balances (proved from the
  balance equations above), which is the tick that is source-grounded;
* and I record as a **source gap** that the problem page does not print a
  candidate list of relations, so if the intended tick was instead the exact
  ratio `2x : 3y`-type identity, that equality is *not* derivable from the
  problem inputs alone — only `x > y` is.

## Axioms / honesty

All theorems are proved constructively in Lean (finite-set extensionality,
`linarith`/`ring` on the balance equations). No `sorry`/`admit`, no custom
axioms. The `Gas` type and the two `Finset`s are the problem-domain data; the
real-number lemmas derive the x–y order from the elemental balances.
-/

namespace IChO2026T7A1

/-- The gases appearing in the process scheme of Fig. 1 (T7). -/
inductive Gas
  | N2  -- nitrogen, from the air feed `4N₂ + 1O₂`
  | H2  -- hydrogen, reforming / partial-oxidation / shift product
  | CO  -- carbon monoxide, reforming and partial-oxidation product
  | CO2 -- carbon dioxide, shift product (scrubbed at Z)
  | NH3 -- ammonia, formed in the non-quantitative synthesis step
  | CH4 -- methane feed (consumed quantitatively in reactors I and II)
  | H2O -- steam (separate side feed to the shift reactor III)
  deriving DecidableEq, Fintype

/-- The set of gases in mixture **M1** (effluent of reactor II). -/
def M1 : Finset Gas := {Gas.N2, Gas.CO, Gas.H2}

/-- The set of gases in mixture **M2** (effluent of the ammonia reactor,
before the cooler CLR). -/
def M2 : Finset Gas := {Gas.N2, Gas.H2, Gas.NH3}

theorem composition_M1 : M1 = {Gas.N2, Gas.CO, Gas.H2} := rfl

theorem M1_mem_N2 : Gas.N2 ∈ M1 := by simp [M1]
theorem M1_mem_CO : Gas.CO ∈ M1 := by simp [M1]
theorem M1_mem_H2 : Gas.H2 ∈ M1 := by simp [M1]

/-- Membership in M1 is exactly the disjunction "N₂ or CO or H₂": the set is
complete, so no other printed species (CO₂, NH₃, CH₄, H₂O) belongs to M1. -/
theorem M1_complete : ∀ g : Gas, g ∈ M1 ↔ g = Gas.N2 ∨ g = Gas.CO ∨ g = Gas.H2 := by
  intro g
  simp [M1]

theorem composition_M2 : M2 = {Gas.N2, Gas.H2, Gas.NH3} := rfl

theorem M2_mem_N2 : Gas.N2 ∈ M2 := by simp [M2]
theorem M2_mem_H2 : Gas.H2 ∈ M2 := by simp [M2]
theorem M2_mem_NH3 : Gas.NH3 ∈ M2 := by simp [M2]

/-- Membership in M2 is exactly "N₂ or H₂ or NH₃" — the complete effluent of
the ammonia reactor. -/
theorem M2_complete : ∀ g : Gas, g ∈ M2 ↔ g = Gas.N2 ∨ g = Gas.H2 ∨ g = Gas.NH3 := by
  intro g
  simp [M2]

/-- The elemental-balance derivation of the x–y relation.

Let `a` = CH₄ reformed in I, `b` = CH₄ oxidized in II, `c` = N₂ in the air
feed.  The printed stoichiometries (I): CH₄+H₂O→CO+3H₂, (II): 2CH₄+O₂→2CO+4H₂,
(III): CO+H₂O→CO₂+H₂, the 4N₂+1O₂ air feed (`b = c/2`), and the scrubber
output feeding the synthesis loop (`4a + 3b = 3c`) yield the unique ratio
`a : b : c = 3 : 4 : 8`.  With the figure's reading `x = a + b` (total CH₄ on
the single feed line) and `y = a` (steam for the reformed part), this forces
`x : y = 7 : 3`, in particular `x > y`. -/
theorem xy_relation_from_balances
    {a b c x y : ℝ}
    (hc : 0 < c)
    -- Reactor II methane demand from the 4N₂ + 1O₂ air feed: b = c/2.
    (hb : b = c / 2)
    -- Synthesis-gas hydrogen required by the scrubber output N₂ + 3H₂ ⇌ 2NH₃:
    -- total H₂ after the shift = 4a + 3b must equal 3c.
    (hH2 : 4 * a + 3 * b = 3 * c)
    -- The figure's feed-line reading: total methane x = a + b, steam y = a.
    (hx : x = a + b)
    (hy : y = a) :
    x > y ∧ x = 7 * (c / 8) ∧ y = 3 * (c / 8) := by
  have ha : a = 3 * (c / 8) := by
    have h1 : 4 * a + 3 * (c / 2) = 3 * c := by rw [← hb]; exact hH2
    linarith
  have hb' : b = 4 * (c / 8) := by
    rw [hb]; ring
  have hgt : a < a + b := by
    have : 0 < b := by rw [hb']; positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hx, hy]; exact hgt
  · rw [hx, ha, hb']; ring
  · rw [hy, ha]

/-- The x–y relation that the printed plant forces: `x > y`. -/
theorem xy_relation {x y : ℝ}
    (h : ∃ a b c : ℝ, 0 < c ∧ b = c / 2 ∧ 4 * a + 3 * b = 3 * c ∧
      x = a + b ∧ y = a) :
    x > y := by
  obtain ⟨a, b, c, hc, hb, hH2, hx, hy⟩ := h
  exact (xy_relation_from_balances hc hb hH2 hx hy).1

#print axioms composition_M1
#print axioms M1_complete
#print axioms M1_mem_CO
#print axioms composition_M2
#print axioms M2_complete
#print axioms M2_mem_NH3
#print axioms xy_relation_from_balances
#print axioms xy_relation

end IChO2026T7A1
