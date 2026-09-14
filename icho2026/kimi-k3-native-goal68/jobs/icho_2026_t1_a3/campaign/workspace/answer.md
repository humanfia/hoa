# IChO 2026 · Theory 1 · Part 1.3 (subquestion **icho_2026_t1_a3**)

**Question (printed page Q1-3 of `theory_problem.pdf`, English (Official)).**
The chemist extracted **W** from the elixir. When **W** was added to an
aqueous Fe³⁺ solution, a characteristic colour change was observed. Mass
spectrometric analysis of **W** revealed the intensity ratio
`[M]⁺ : [M + 1]⁺ = 9:1`, where M is the molecular ion. Carbon consists
exclusively of ¹²C and ¹³C, the natural abundance of ¹²C is 98.9 %, and all
other elements are monoisotopic. *Determine the number of carbon atoms (n)
from the mass spec data and identify W. Show your calculations.*

## Answer

* **n = 10**.
* **W is compound 5** of the extraction table (`C₁₀H₁₂O₂`) — the eugenol
  methyl ether **4-allyl-1-methoxy-2-hydroxybenzene**
  (2-methoxy-4-(prop-2-en-1-yl)phenol): a benzene ring bearing –OH, –OCH₃ and
  –CH₂–CH=CH₂ substituents.

## Calculation for n

Because every element other than carbon is monoisotopic, and carbon is a
two-isotope system (p(¹²C) = 0.989, p(¹³C) = 1 − 0.989 = 0.011), the
molecular-ion peak `[M]⁺` contains only all-¹²C molecules, while the first
satellite `[M + 1]⁺` is dominated by molecules carrying exactly one ¹³C
(two or more ¹³C atoms contribute at mass +2 and higher, and are negligible
at this abundance). For a molecule with n carbon atoms the binomial model
gives

```
I[M]⁺    :  pⁿ
I[M + 1]⁺ :  n · pⁿ⁻¹ · q       (choose which of the n carbons is ¹³C)
```

so

```
I[M]⁺ / I[M + 1]⁺  =  p / (n · q)  =  989 / (11 · n)  =  9
```

Solving:

```
n = 989 / (11 · 9) = 989 / 99 = 9.99 ≈ 10.
```

Check backward: with n = 10 the predicted ratio is
989/110 = 8.99 ≈ 9 (|error| = 1/110 ≤ ½ of the unit quantum of “9:1”),
whereas n = 11 would give 989/121 = 8.17 (|error| = 100/121 > ½) — so the
only integer consistent with the printed ratio is **n = 10**.

## Identification of W

The elixir's four constituents X, Y, Z, W come from the extraction table of
the four plants (printed page Q1-2). Two facts select W:

1. **Fe³⁺ test** — a colour change with aqueous Fe³⁺ is the standard
   qualitative test for a **phenolic –OH** (–OH bonded to an aromatic ring).
   Inspecting the ten drawn structures, only **compound 1**
   (`C₁₁H₁₄O₃`, zingiberone: HO–C₆H₃–(OCH₃)–side-chain) and **compound 5**
   (`C₁₀H₁₂O₂`, eugenol methyl ether) carry a phenolic –OH.
   Compounds 2, 6, 9, 10 have only aliphatic –OH or C=O, 3 is an ether, and
   7, 8 are hydrocarbons — none gives the Fe³⁺ colour reaction.
2. **Mass spectrum** — n = 10 (above).

Compound 1 has 11 carbons and is ruled out by the isotope ratio (989/121 ≠ 9
at the printed precision). The intersection is unique:

```
W = compound 5,  C₁₀H₁₂O₂  (eugenol methyl ether).
```

## Source grounding

* Problem text and numeric assumptions transcribed verbatim from
  `theory_problem.pdf` (page Q1-3) and `icho_2026_source/image/T1_page-3.png`.
* Candidate table transcribed from page Q1-2 (`T1_page-2.png`); the drawn
  structure of compound 5 was inspected at high resolution: benzene ring with
  –OH, –OCH₃ and –CH₂CH=CH₂ substituents, formula printed `C₁₀H₁₂O₂`.
* The natural-abundance relation `I[M]⁺/I[M+1]⁺ = (¹²C abundance) /
  (n · ¹³C abundance)` is the standard first-order binomial isotope
  treatment; the problem itself supplies every numerical ingredient.
* The Fe³⁺-colour→phenol link is ordinary textbook qualitative-analysis
  chemistry (trusted general law), applied to the drawn structures.

## Formalization

The whole argument above is formalized in
`IChO2026Problems/problem_icho_2026_t1_a3.lean`:

* the Bernoulli-product probability model and its n-slot recurrence
  (`prob_pair_mul`, `binomialRecurrence`);
* the ratio formula `I[M]⁺/I[M+1]⁺ = p/(n·q)` (`isotope_ratio`);
* solving for n with the printed abundances (unique rational solution
  989/99; `carbon_count_ratio`);
* the integer fit test at the displayed precision
  (`candidate_arithmetic`, `fitsRatio`);
* the extraction-table encoding, phenolic filtering and the identifcation
  of W as compound 5 (`table`, `phenolicCandidates`,
  `phenolic_candidates_correct`, `identification_of_W`);
* all packaged in the final conjunction `t1_a3_main`.

The final theorem depends only on Lean's standard logical axioms
(`propext`, `Classical.choice`, `Quot.sound`); no custom axioms, no `sorry`.
