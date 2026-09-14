# IChO 2026 — Problem 9 (Cyclodextrin Chemistry), Subquestion 9.6 (T9-A6)

**Question** (official English sheet, page Q9-3, box 9.6):
"Determine the number of isomers of the β-CD dimer that can form during the
synthesis by Sinay *et. al.*" — 4.0 pt.

## Answer

**2 constitutional linkage isomers.**

## Reasoning (all premises from the problem sheets Q9‑1…Q9‑3)

### Step 1 — What intermediate L looks like

The β-CD ring has **7 glucopyranose units** (preamble of T9: α‑, β‑, γ‑CD
contain 6, 7, 8 units).  After NaH (30 equiv.) / BnCl (30 equiv.) every
hydroxy group is benzylated; DIBAL‑H (2 equiv.) then strips exactly two
benzyl ethers (reductive debenzylation of primary OH groups).

The scheme quotes Sinay's directing rule verbatim (page Q9‑3):

> "a single protic group (NH and OH) at unit 1 directs the **next** reductive
> debenzylation of a primary OH group to **unit 4** in the macrocyclic ring
> (or to unit 3 if the unit 4 position is not available)."

Applied twice (2 equiv. DIBAL‑H), the first cleavage liberates a unit
("unit 1") and the second cleavage is directed to the unit **three steps**
away around the ring ("unit 4").  In β-CD the fallback to unit 3 never
operates, because from any unit of a 7-membered ring the unit at distance 3
always exists and is still benzylated when needed.  Hence **L = β-CD with
free primary OH groups on a pair of units at cyclic distance 3** (the
1/4-pair; a third cleavage would have gone to unit 7 = 4 + 3).

### Step 2 — What the dimer looks like

In the last synthetic block (page Q9‑3) L is treated with
`1) t-BuOK, Br–(CH₂)ₙ–CH=CH–(CH₂)ₙ–Br; 2) Grubbs I; 3) H₂, PtO₂`.
The free primary OH of one L is alkylated by one end of the dibromide and
the pendant terminal alkene is cross-metathesised with the analogous
alkenylated group of a second L, finally giving, after hydrogenation, a
dimer in which the two β-CD rings are joined by a single symmetric
hydrocarbon bridge between one primary face oxygen of each ring.  The
drawn product confirms this: each ring carries 5 × CH₂OBn, 1 × CH₂OH and
1 × CH₂O–linker — exactly one primary O per ring has been consumed by the
linker, the other free OH of the 1/4-pair remains.

The problem text states the dimer is obtained **"as a mixture of
constitutional linkage isomers"**.

### Step 3 — Counting the linkage isomers

Label the 7 units of each ring by its *own* directing unit (`0` =
directing unit; labels step `+1` around the ring as in the figure).  The
attachment site of each ring of the dimer is then one of its two free-OH
units `{0, 3}`, so a dimer is described by an ordered pair
`(a, b) ∈ {0, …, 6}²` — 49 site-labelled outcomes in total, of which the
chemically attainable ones (both ends taken from the `{i, i+3}` pattern of
the corresponding L) have directed separation
`b − a (mod 7) ∈ {0, 3, −3 = 4}`:

* separation **0**: the linker joins the directing units of the two rings
  (label pairs `(i, i)` — 7 pairs);
* separation **3**: directing unit of ring A to unit 4 of ring B
  (`(i, i+3)` — 7 pairs);
* separation **4 ≡ −3**: unit 4 of ring A to the directing unit of ring B
  (`(i, i−3)` — 7 pairs).

Two site-labelled dimers are the **same constitutional linkage isomer**
iff they differ by the symmetry operations of the assembly — cyclic
re-charts of the two rings, exchange of the two ends of the symmetric
linker, and mirror re-description of the 7-cycle.  All of these leave the
*undirected* separation `min(d, 7−d)` invariant, so the constitution is
fixed by the pair `{d, −d}`.  Among the attainable separations,
`{3, −3} = {3, 4}` is a *single* constitution class (reflection of one
ring, or exchange of the rings, turns `+3` into `−3`), while `{0}` is
another.  Different undirected separations give different carbon skeletons
(different connectivity of the 7-cycle–to–linker–to–7-cycle graph), so the
two classes are genuinely different compounds.

Therefore the dimer mixture contains exactly

    N = 2 constitutional linkage isomers:
        (a) the "in-line" dimer 1—link—1   (separation 0),
        (b) the "crossed" dimer 1—link—4   (separation ±3).

## Lean 4 formalization

File: `IChO2026Problems/problem_icho_2026_t9_a6.lean`.

* `SiteLabelledDimer` — ordered pair of attachment units in `Fin 7`
  (index 0 ↔ problem's unit 1, …, index 6 ↔ unit 7).
* `sep` — directed separation `linkB − linkA (mod 7)`.
* `SameConstitution` — "separations equal or opposite mod 7"; proved to be
  an equivalence (`sameConstitution_equivalence`).
* `Attainable` — separation ∈ {0, 3, 4} (the Sinay-rule outcomes).
* `linkSame = (0,0)`, `linkCross = (0,3)` — the two class representatives.
* `representatives_distinct` — the two classes differ constitutionally.
* `attainable_eq_linkSame_or_linkCross` — every attainable dimer is
  constitutionally one of the two (completeness of the count).
* `nonattainable_not_formed` — separations ±1, ±2 never arise.
* `attainable_partition_of_linkSame` / `_linkCross` — the two classes
  comprise 7 and 14 site-labelled dimers (21 = 49 × the 3 attainable
  separation values).
* `dimer_quot_classes` — the constitutional quotient of all 49 labelled
  dimers has 4 classes ({0}, ±1, ±2, ±3), of which only
* `dimer_isomer_count_attainable_classes` — **exactly 2** are formed:
  the image of the attainable dimers in the quotient has cardinality 2.
* `dimer_isomer_count` — packaging: completeness, distinctness and
  realizability of the two isomers.

No `sorry`/`admit`; `native_decide` is used only for the finite
enumerations (49 × 49 comparisons).

## Source grounding and gaps

* Number of glucose units in β-CD (7), the NaH/BnCl benzyl benzylation and
  DIBAL-H (2 equiv.) partial debenzylation, the verbatim Sinay directing
  rule (unit 1 → unit 4, fallback unit 3), the alkylation/Grubbs/H₂
  sequence, and the phrase "mixture of constitutional linkage isomers" are
  all taken from the official English problem sheets T9 Q9‑1–Q9‑3
  (`icho_2026_source/image/T9_page-1.png … T9_page-3.png`, bundled with
  `theory_problem.pdf`).
* The problem itself calls the products "constitutional linkage isomers",
  so E/Z or other stereochemical distinctions (absent anyway after the H₂
  step saturates the linker) are not requested; the requested integer is the
  exact count 2.
* No external or answer-key sources were consulted.  No grounding gaps
  remain for the stated count.
