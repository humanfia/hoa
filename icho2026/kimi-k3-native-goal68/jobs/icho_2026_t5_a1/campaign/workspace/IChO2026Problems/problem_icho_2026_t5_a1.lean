import Mathlib

/-!
# IChO 2026, Problem T5 (Cardiolipins), subquestion 5.1 — `icho_2026_t5_a1`

## Problem statement (source: `theory_problem.pdf`, printed page 1 of T5,
## image `T5_page-1.png`)

The non-ionised cardiolipin **PL1** is assembled from structural elements
*a*–*d* in the following fixed quantities:

* **a**: `n` × a bare hydrogen atom (drawn as —H), one attachment point,
  zero transferable hydrogen atoms;
* **b**: `2` × phosphoric acid residues  HO–P(=O)(OH)–  (phosphate with two
  free P–OH groups and two attachment points, i.e. two transferable (acidic)
  hydrogen atoms per fragment);
* **c**: `3` × glycerol skeletons  (three attachment points, no transferable
  hydrogen atoms);
* **d**: `4` × fatty acid acyl groups  R–C(=O)–  (one attachment point, no
  transferable hydrogen atoms).

Fragments are joined by condensing off water: every new bond between two
attachment points eliminates H₂O, consuming one transferable hydrogen atom.

**Question 5.1.**  Tick one correct statement about the value of `n`:

* (a) `n` is an even number,
* (b) `n` is an odd number,
* (c) `n` can be either an odd or an even number.

## Chemical reasoning (independent derivation)

Count transferable hydrogen atoms carried into the assembly: type *a* carries
0 each, type *b* carries 2 each (phosphoric acid has two free –OH protons on
the two attachment oxygens), types *c* and *d* carry 0 each.  Hence the total
transferable-hydrogen budget is `2 a + n`, where we write `a` for the number
of type-*b* fragments and `b`, `c` for the numbers of type-*c* and type-*d*
fragments.

Count attachment points: *b* contributes 2 each, *c* contributes 3 each,
*d* contributes 1 each, and the `n` hydrogen fragments contribute `n`
star bonds to be capped.  Every inter-fragment bond consumes exactly 2
attachment points, so the number of inter-fragment bonds is
`(2a + 3b + c + n)/2`, which must therefore be an integer — i.e.
`2a + 3b + c + n` must be even.

Every inter-fragment bond consumes exactly 1 transferable hydrogen atom
(formation of an ester or phosphate-ester bond from –COOH + HO– or
HO–P + HO– liberates H₂O), so the hydrogen balance reads
`2·(2a + n) = 2a + 3b + c + n`, i.e. `n + 2a = 3b + c`.
Hence the parity of `n` equals the parity of `3b + c` (the `2a` term is
even and does not affect parity).

With the stipulated quantities `a = 2`, `b = 3`, `c = 4` this gives
`n + 4 = 9 + 4`, so `n = 9`, which is **odd**.  In particular `n` cannot be
even, and it cannot be "either": the answer is **(b)**.

(Sanity check: cardiolipin is a bis-phosphatidylglycerol — the three glycerol
backbones linked in line by two phosphate diester bridges, with the two
terminal glycerols esterified by four fatty acids in total.  Assembly
requires `2a + n = 4 + 9 = 13` inter-fragment (condensation) bonds and
closes `2·13 = 26 = 2a + 3b + c + n = 4 + 9 + 4 + 9` attachment points),
consistent with the counting we are about to formalize.  Note that the
parity conclusion for 5.1 does not depend on the detailed connectivity.)

## Formalization

We model the assembly exactly as above: every fragment type has a fixed
number of attachment points and a fixed number of transferable hydrogen
atoms; bonds consume 2 attachment points and 1 transferable hydrogen each.
Everything is proved from first principles over `ℕ` (and `ℤ` for the parity
of halves).  No physical premise beyond the fragment readings and the
elementary condensation stoichiometry is assumed; in particular the "no
peroxide bonds" clause is not needed for 5.1.
-/

namespace IChO2026T5A1

/--  An assembly recipe: how many fragments of each of the four types are
used.  Field names follow the fragment labels of the problem:
`a` phosphoric-acid fragments (type *b* in the figure, 2 OH-bearing
attachment points), `b` glycerol fragments (type *c*, 3 attachment points),
`c` fatty acyl fragments (type *d*, 1 attachment point), `n` hydrogen
fragments (type *a*, the unknown of question 5.1). -/
structure Recipe where
  a : ℕ
  b : ℕ
  c : ℕ
  n : ℕ

/--  The stipulated quantities for PL1 (the figure under "Using only the
structural elements a–d in the quantities stated below"): 2 phosphates,
3 glycerols, 4 fatty acyls, and the unknown number `n` of hydrogens. -/
def Recipe.PL1 (n : ℕ) : Recipe := ⟨2, 3, 4, n⟩

/-- Total number of fragments used. -/
def Recipe.fragments (r : Recipe) : ℕ := r.a + r.b + r.c + r.n

/-- Total number of attachment points (free valences in the fragment
boxes): phosphate 2 each, glycerol 3 each, acyl 1 each, plus one star per
hydrogen cap. -/
def Recipe.attachPoints (r : Recipe) : ℕ := 2 * r.a + 3 * r.b + r.c + r.n

/-- Total number of transferable hydrogen atoms carried in by the fragments:
only the phosphoric acid fragments contribute (2 each: one proton on each of
the two free P–OH oxygens); the bare hydrogen fragments carry none
themselves. -/
def Recipe.transferableH (r : Recipe) : ℕ := 2 * r.a + r.n

/--  Feasibility of an assembly, as grounded in the problem:

* `hH` — **hydrogen (condensation) balance.**  Every inter-fragment bond is
  formed by elimination of water and consumes exactly one transferable
  hydrogen atom, so the transferable-hydrogen budget equals the number of
  inter-fragment bonds: `transferableH = bonds`.
* `hP` — **pairing of attachment points.**  Every inter-fragment bond
  consumes exactly two attachment points (it joins one half-bond of each of
  two fragments), so `attachPoints = 2 * bonds`.

No other constraint (connectivity, absence of peroxide bonds, chirality …)
is needed to answer 5.1, so we do not assume any. -/
def Recipe.Feasible (r : Recipe) : Prop :=
  ∃ bonds : ℕ, r.transferableH = bonds ∧ r.attachPoints = 2 * bonds

/-- Why the pairing condition forces the attachment-point count to be even:
it is twice the number of bonds. -/
theorem Recipe.Feasible.attachPoints_even {r : Recipe} (h : r.Feasible) :
    Even r.attachPoints := by
  obtain ⟨bonds, -, hP⟩ := h
  exact ⟨bonds, by simp [hP, two_mul]⟩

/--  Eliminating the bond multiplicity from the two balance equations:
twice the transferable-hydrogen budget equals the attachment-point count.
Stated over `ℕ` without subtraction. -/
theorem Recipe.Feasible.hydrogen_balance {r : Recipe} (h : r.Feasible) :
    2 * r.transferableH = r.attachPoints := by
  obtain ⟨bonds, hH, hP⟩ := h
  rw [hH, hP]

/-- The explicit closed form for `n`, proved over `ℤ` to avoid the
truncated subtraction of `ℕ`:  from `2·(2a + n) = 2a + 3b + c + n` one
cancels to `n = 3b + c − 2a`.  (Note this is `−2a`, *not* `+2a`: the
hydrogens brought in by the phosphoric acid fragments reduce the number of
bare-hydrogen caps needed.  Feasibility guarantees `3b + c ≥ 2a`.) -/
theorem Recipe.Feasible.n_eq {r : Recipe} (h : r.Feasible) :
    r.n + 2 * r.a = 3 * r.b + r.c := by
  have hb := h.hydrogen_balance
  simp only [Recipe.transferableH, Recipe.attachPoints] at hb
  omega

/--  **Parity lemma.**  The hydrogen and attachment-point balances alone
force `n` to have the same parity as `3b + c` (the glycerol/acyl
attachment-point excess):  from `2·(2a + n) = 2a + 3b + c + n` we get
`n + 2a = 3b + c`, hence `n ≡ 3b + c (mod 2)`.  This is the *general*
content of question 5.1, before the numerical quantities are inserted. -/
theorem Recipe.Feasible.n_parity {r : Recipe} (h : r.Feasible) :
    r.n % 2 = (3 * r.b + r.c) % 2 := by
  have hn := h.n_eq
  omega

/-- With the PL1 quantities (2 phosphate, 3 glycerol, 4 fatty acyl), the
parity class of `n` is fixed:  `n ≡ 3·3 + 4 = 13 ≡ 1 (mod 2)`. -/
theorem n_mod_two_eq_one {n : ℕ} (h : (Recipe.PL1 n).Feasible) :
    n % 2 = 1 := by
  have hp := h.n_parity
  simp only [Recipe.PL1] at hp
  omega

/-- The full closed form: any feasible assembly of PL1 uses exactly
`n = 9` hydrogen fragments (`n + 2·2 = 3·3 + 4 = 13`). -/
theorem n_eq_nine {n : ℕ} (h : (Recipe.PL1 n).Feasible) :
    n = 9 := by
  have hn := h.n_eq
  simp only [Recipe.PL1] at hn
  omega

/--  **Answer to 5.1: option (b) — `n` is an odd number.**
Every feasible assembly of PL1 requires an odd number of type-*a*
(hydrogen) fragments. -/
theorem answer_b_n_is_odd {n : ℕ} (h : (Recipe.PL1 n).Feasible) :
    Odd n :=
  (Nat.odd_iff).mpr (n_mod_two_eq_one h)

/-- Option (a) is *never* consistent with a feasible PL1 assembly. -/
theorem answer_a_n_even_impossible {n : ℕ} (h : (Recipe.PL1 n).Feasible) :
    ¬ Even n := by
  have hodd := answer_b_n_is_odd h
  exact Nat.not_even_iff_odd.mpr hodd

/--  Option (c) ("either parity is possible") is false in both directions:
every feasible value is odd, hence not even, and the unique feasible value
is `9`, which is odd — so parity is not free. -/
theorem answer_c_parity_not_free {n : ℕ} (h : (Recipe.PL1 n).Feasible) :
    Odd n ∧ ¬ Even n :=
  ⟨answer_b_n_is_odd h, answer_a_n_even_impossible h⟩

/-! ### Consistency witness

The problem states that PL1 *can* be assembled from the stated quantities,
and indeed `n = 9` works: 13 transferable hydrogens against
`2·2 + 3·3 + 4 + 9 = 26` attachment points, i.e. `bonds = 13 =
2·2 + 9` satisfies both `2·13 = 26` and the two defining equations.
This witness shows that our reading of the balances is satisfiable, so the
theorems above are not vacuous. -/

theorem pl1_feasible_at_nine : (Recipe.PL1 9).Feasible := by
  refine ⟨13, ?_, ?_⟩ <;> decide

theorem pl1_bonds_eq_thirteen {n : ℕ} (h : (Recipe.PL1 n).Feasible) :
    ∃ bonds : ℕ, bonds = 13 ∧ (Recipe.PL1 n).transferableH = bonds ∧
      (Recipe.PL1 n).attachPoints = 2 * bonds := by
  obtain ⟨bonds, hH, hP⟩ := h
  have hn := n_eq_nine ⟨bonds, hH, hP⟩
  refine ⟨bonds, ?_, hH, hP⟩
  simp only [Recipe.PL1, Recipe.transferableH, hn] at hH
  omega

/--  Final classification, phrased exactly as the ticked statement of the
problem: **(b) n is an odd number**, and moreover the value of `n` is
uniquely determined (`n = 9`), so options (a) and (c) are excluded. -/
theorem t5_a1_answer :
    (∀ n : ℕ, (Recipe.PL1 n).Feasible → Odd n) ∧
    (∀ n : ℕ, (Recipe.PL1 n).Feasible → n = 9) ∧
    (Recipe.PL1 9).Feasible :=
  ⟨fun _ h => answer_b_n_is_odd h, fun _ h => n_eq_nine h,
    pl1_feasible_at_nine⟩

end IChO2026T5A1
