# IChO 2026, Problem T6 (Carbon Nanorings), subquestion 6.3 (T6-A3)

## Question (official, Q6-2)

> The voltages applied during the AFM-mediated synthesis of C𝑛 may vary.
> Using the given C–X bond energies, **choose** the possible halogen(s) in the
> halogenated reagent for C18 synthesis via a retro-Bergman reaction with a
> voltage of 2.5 V acting on the electrons.
>
> | Bond (C–X) | BDE / kJ mol⁻¹ |
> |---|---|
> | C–F | 467 |
> | C–Cl | 346 |
> | C–Br | 290 |
> | C–I | 228 |

The official answer sheet (A6-2) provides the blank `6.3 (2.0 pt)  X = _______`.

## Answer

**X = I (iodine only).**

## Working

### Step 1 — Energy carried by the 2.5 V electrons

An electron accelerated through a potential difference V = 2.5 V gains kinetic
energy

    E = e·V = 1.602 × 10⁻¹⁹ C × 2.5 V = 4.005 × 10⁻¹⁹ J per electron = 2.5 eV.

Converting to a per-mole basis using the printed constant sheet values
(e = 1.602 × 10⁻¹⁹ C, N_A = 6.022 × 10²³ mol⁻¹, sheet G1-3):

    E = 1.602 × 10⁻¹⁹ × 2.5 × 6.022 × 10²³ J mol⁻¹
      = 241.1811 × 10³ J mol⁻¹ ≈ 241 kJ mol⁻¹.

(No intermediate rounding was performed; 241.1811 kJ mol⁻¹ is the exact value
of the product of the printed constants.)

### Step 2 — Compare with each C–X bond dissociation energy

A voltage-driven dissociative event of this kind can cleave a C–X bond only
when the electron delivers at least the bond dissociation energy; otherwise
the C–X bond stays intact and that halogen cannot be the substituent on the
reagent used for an electron-driven retro-Bergman synthesis:

| Halogen X | BDE(C–X) / kJ mol⁻¹ | BDE ≤ 241.18? | Possible? |
|---|---|---|---|
| F  | 467 | no  | no |
| Cl | 346 | no  | no |
| Br | 290 | no  | no |
| I  | 228 | yes | **yes** |

E lies strictly between BDE(C–I) = 228 and BDE(C–Br) = 290 kJ mol⁻¹, so the
only halogen whose C–X bond can be broken by 2.5 V electrons is iodine.

### Step 3 — Answer

    X = I

### Consistency note (context from the shared problem statement)

The 6.2 example of C14 synthesis uses a **chlorinated** precursor
(dechlorination steps −2 Cl·, −5 Cl·, etc.); that synthesis used a larger
voltage than 2.5 V (Cl requires ≥ 346 kJ mol⁻¹ ≈ 3.59 V), and the present
subquestion deliberately varies the voltage to 2.5 V, for which only the much
weaker C–I bond is accessible. This cross-check confirms the intended energy
comparison logic: the given BDE table brackets the electron energy.

## Source-grounding

- BDE table (467 / 346 / 290 / 228 kJ mol⁻¹), voltage 2.5 V, and the phrase
  "acting on the electrons": official question page Q6-2
  (theory_problem.pdf p. 53; image T6_page-2.png).
- Constants e = 1.602 × 10⁻¹⁹ C, 1 eV = 1.602 × 10⁻¹⁹ J,
  N_A = 6.022 × 10²³ mol⁻¹: official Physical Constants sheet G1-3
  (theory_problem.pdf p. 3).
- Answer format "X = _______": official blank answer sheet A6-2
  (theory_problem.pdf p. 58).
- Physical principle used (the cleaving electron must supply at least the
  bond dissociation energy): trusted general physical law (energy
  conservation for dissociative electron attachment / bond cleavage), not a
  competition-derived answer.

## Formalization

See [IChO2026Problems/problem_icho_2026_t6_a3.lean](IChO2026Problems/problem_icho_2026_t6_a3.lean):

- Problem inputs kept separate: `bdeKJ` (the printed table), `voltageV = 2.5`,
  `electronChargeC = 1.602e-19`, `avogadro = 6.022e23`.
- Derived: `electronEnergyKJ = V·e·N_A/1000 = 241.1811 kJ mol⁻¹`
  (`electronEnergyKJ_value`), bracketing lemma `electronEnergyKJ_bounds`.
- Criterion `Possible X := bdeKJ X ≤ electronEnergyKJ` and the main theorem
  `possible_halogens : ∀ X, Possible X ↔ X = .I`, with the answer-sheet form
  `possible_set : {X | Possible X} = {.I}`.
