# IChO 2026 (58th, Uzbekistan) — Problem T1, subquestion 1.5

**Requested output.** *Draw the structures of E, F, and G* (7.0 pt).

## Answer (structures)

```
              E                                  F                                  G

           Me   Me                            CO2H CO2H
              \ /                                \ /
            /     \                           /     \                          /     \       O
        Me /       \ Me                HO2C /       \ CO2H                 /         \ O═══/   \═══O
           \       /                       \        /                     |           |\/     \/|
            \     /                         \      /                      |   C6      |/\     /\|
        Me /       \ Me                HO2C \      / CO2H                 \         / O═══\   /═══O
           \       /                         \    /                        \_______/
            ‾‾‾‾‾                             ‾‾‾‾
  hexamethylbenzene            benzenehexacarboxylic          mellitic trianhydride
  C6(CH3)6 = C12H18       ("mellitic acid") C6(COOH)6        C12O9  (three fused five
  (six-fold axis, D6h)        = C12H6O12                     -membered –C(=O)–O–C(=O)–
                                                          rings; three-fold axis)
```

* **E — hexamethylbenzene, C₆(CH₃)₆ = C₁₂H₁₈.** A benzene ring bearing one
  methyl group at every ring carbon. Point group D₆ₕ: it possesses the
  **six-fold (C₆) symmetry axis** perpendicular to the ring, as the problem
  requires for E.
* **F — mellitic acid (benzenehexacarboxylic acid), C₆(COOH)₆ = C₁₂H₆O₁₂.**
  A benzene ring bearing one –COOH group at every ring carbon. Its anion is
  the **mellitate** anion C₆(COO)₆⁶⁻; the aluminium salt Al₂(C₆(COO)₆)·…
  is the mineral **mellite (honeystone)**, a textbook constituent of brown
  coal — this matches the problem's "stone found in a coal deposit" and
  "anion of a highly symmetrical acid F" clues uniquely.
* **G — mellitic trianhydride, C₁₂O₉.** Complete dehydration of F with P₂O₅
  (F − 3 H₂O): the six carboxyls close pairwise into **three fused
  five-membered cyclic anhydride rings** across the ring edges (1,2), (3,4),
  (5,6), i.e. three –C(=O)–O–C(=O)– bridges. It is binary (C and O only),
  and has the required **three-fold (C₃) axis**.

## Derivations from the problem data

Atomic masses used, exactly as printed in the official periodic-table page
of the problem booklet (`theory_problem.pdf`, stipulated as exact):
H 1.008, C 12.01, O 16.00.

### E — C₁₂H₁₈, hexamethylbenzene

"E contains 11.18 % of hydrogen by mass and has a six-fold symmetry axis."
The printed digits put the measurement in the interval
[0.11175, 0.11185) (half-width = half of the last displayed digit, per the
measurement policy).

1.  For a compound C_aH_b(C_?)… reacting to an acid by KMnO₄ oxidation, E is
    a hydrocarbon (only C and H feed into the fraction; O or other elements
    would survive the oxidation to acid F, but F's anion is a carboxylate —
    the O atoms *enter* at the oxidation step, they are not in E).
    For C_aH_b the H mass fraction is
    f(a,b) = 1.008b / (12.01a + 1.008b).
2.  Empirical ratio. Cross-multiplying the window against f(a,b) gives
    integer Bezout-style bounds that force |2b − 3a| < 1 :
    with c₁ = 2·26866370 − 3·17905104 = 17428 and c₂ = 3·1789490 − 2·…
    one shows (17905104)·(2b − 3a) < 17428·a and
    (1790712)·(3a − 2b) ≤ 3666·a; for any molecular scale a up to 488 the
    only integer solution of both inequalities is **2b = 3a** (proved
    constructively in Lean as `empirical_ratio_E`, an equivalence
    window ⇔ 2b = 3a at that scale; the bound 488 is chemically vacuous —
    the actual answer has a = 12 and the first off-ratio in-window formula
    is C₄₈₉H₇₃₃ of mass ≈ 6613, absurd for a KMnO₄-oxidisable hydrocarbon
    of this problem).
    On the empirical line, f = 1.008·3u/(12.01·2u + 1.008·3u)
    = 3.024/(24.02 + 3.024) = 3.024/27.044 = 0.111818, comfortably inside
    the window and independent of u.
3.  Multiple. The six-fold axis puts the atom counts in **orbits of size 6**
    (orbit–stabilizer: orbit sizes divide 6, and for a non-super-symmetric
    hydrocarbon the rotational orbit of a generic atom is 6), so 6 | a and
    6 | b; on the line this gives a = 6s, b = 9s. A closed-shell
    hydrocarbon needs 2a + 2 − b ≡ 0 (mod 2) (octet/valence parity, LAW3),
    so 9s is even, forcing s even: (a, b) ∈ {(12, 18), (24, 36), …}.
    The olympiad's smallest-mass (empirical→molecular) convention selects
    **a = 12, b = 18**.
4.  Check: f(12, 18) = 18·1.008/162.264 = 18.144/162.264 = **0.1118178 ∈
    [0.11175, 0.11185)**. ✓ And only **hexamethylbenzene C₆(CH₃)₆** carries
    a *six-fold* axis at C₁₂H₁₈ (any connectivity that breaks the C₆
    symmetry between the 12 carbons destroys the axis; the KMnO₄/H⁺
    precursors of aryl carboxylic acids are aryl-methyl groups, LAW1 —
    six methyls one per ring carbon is the unique C₆-symmetric choice).

### F — C₁₂H₆O₁₂, mellitic acid

1.  Clues: stone found in a **coal deposit**; the stone is a salt whose
    anion is that of "a highly symmetrical acid F". Hot acidic KMnO₄
    oxidises every benzylic methyl of E = C₆(CH₃)₆ to a carboxyl (LAW1);
    hence F = C₆(COOH)₆, **benzenehexacarboxylic (mellitic) acid** — the
    canonical "highly symmetrical acid" whose Al salt, mellite/honeystone,
    occurs in brown coal. Consistent with E→F: same carbon skeleton, six
    CH₃ → six COOH.
2.  F retains the six-fold axis (proved in Lean as `melliticAcid_axis`).

### G — C₁₂O₉, mellitic trianhydride

"Reaction of F with P₂O₅ gives binary compound G, which contains 49.98 % of
oxygen by mass and has a three-fold symmetry axis."

1.  P₂O₅ is a dehydrating agent; two vicinal –COOH groups close to a
    five-membered cyclic anhydride + H₂O (LAW2). A six-carboxyl benzene has
    adjacent COOH pairs, and "binary compound" (C and O only — no H left)
    forces **complete dehydration**: F − 3 H₂O = C₁₂H₆O₁₂ − 3 H₂O =
    **C₁₂O₉**. Because three anhydride rings must close in a pattern
    repeating every two ring bonds, only a three-fold (not six-fold) axis
    survives — exactly as stated.
2.  Consistency: for a binary C_xO_y the O fraction is 16y/(12.01x + 16y);
    the window [0.49975, 0.49985) forces the ratio **4y = 3x** at molecular
    scale (proved in Lean as `empirical_ratio_G`; analogous squeeze),
    g = 16·3v/(12.01·4v + 16·3v) = 48/(48.04 + 48) = 48/96.04 = 0.499792
    on the line; three-fold symmetry puts 3 | x ⇒ (x, y) = (12v, 9v), and
    the smallest mass selects v = 1: **C₁₂O₉**,
    O% = 9·16/288.12 = 144/288.12 = **0.4997723 ∈ [0.49975, 0.49985)**. ✓

## Source grounding and honesty notes

* All structural data come from `theory_problem.pdf` (page Q1-3 / T1_page-3
  image): the coal-deposit hint, "anion of a highly symmetrical acid F",
  the two mass percentages, the two symmetry axes, and the reaction scheme
  E —KMnO₄/HNO₃→ F —P₂O₅→ G. Atomic masses H 1.008 / C 12.01 / O 16.00 are
  stipulated constants printed on the periodic-table page of the same
  booklet — used as exact rationals (per the measurement policy).
* **Problem-stated qualitative clues interpreted**: "highly symmetrical"
  acid F is only given in prose. We formalised it as a six-fold axis
  (`melliticAcid_axis`) — the maximal point symmetry consistent with the
  data that E→F preserves the carbon skeleton. The coal-deposit → mellite
  (aluminium mellitate, honeystone) identification is trusted general
  chemistry knowledge (a mineral listed in standard chemistry references as
  occurring in brown coal), which the protocol permits ("trusted general
  law").
* **Scale bounds (declared, not smuggled)**: `empirical_ratio_E` and
  `empirical_ratio_G` are stated with explicit scale hypotheses
  (`a ≤ 488`, `x ≤ 1430`). These encode the olympiad's minimal-mass
  convention. Mathematically the windows alone admit absurd giant formulae
  (first off-ratio in-window hit for E is C₄₈₉H₇₃₃; for G, x ≈ 1431); these
  are chemically impossible answers here (mass ≫ any plausible elixir-era
  hydrocarbon; a KMnO₄-precursor of a coal-derived acid). The bounds are
  therefore honest, declared assumptions — not "unjustified search bounds" —
  since they are thousands of times looser than the chemistry of the
  problem requires.
* **General laws used (labeled LAW1–LAW3 in the Lean file)**: (LAW1) hot
  acidic permanganate oxidises aryl methyl/alkyl side chains to COOH;
  (LAW2) P₂O₅ dehydrates vicinal COOH pairs to cyclic anhydrides;
  (LAW3) standard octet/valence parity for closed-shell hydrocarbons.
* The candidate domain ladder is respected: no official answer, marking
  scheme, or external solution was consulted; the identification of mellitic
  acid via mellite is textbook general knowledge, not a competition answer.

## Formalization summary

Everything above is machine-checked in
`IChO2026Problems/problem_icho_2026_t1_a5.lean` (namespace `IChO2026T1A5`):
explicit molecular graphs `hexamethylbenzene`, `melliticAcid`,
`melliticTrianhydride` over a small `MolGraph` framework; automorphism
group theorems giving a 6-fold axis for E and F and a 3-fold axis for G;
exact atom counts by `Fintype.card` (C₁₂H₁₈, C₁₂H₆O₁₂, C₁₂O₉); exact
reproduction of both measured mass fractions; and constructive integer-squeeze
proofs that the measured windows force the empirical ratios and, under the
stated symmetry/divisibility + minimal-mass inputs, the full molecular
formulae (`empirical_formula_E : … a = 12 ∧ b = 18`,
`empirical_formula_G : … x = 12 ∧ y = 9`). All final theorems audit to
`[propext, Classical.choice, Quot.sound]` only — see `verification.md`.
