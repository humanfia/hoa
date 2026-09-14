# IChO 2026 — T8, subquestion 8.8 (target `icho_2026_t8_a8`)

## The question

> The system was irradiated using different LEDs. The diagram below shows the
> mole percentages, χ, of H₂ and CO produced during the reduction of CO₂
> under four different conditions: no irradiation (N) and irradiation with
> red (R), green (G), and blue (B) light.
>
> **8.8** – Tick which of the four conditions, mentioned above, corresponds
> to **a**, **b**, **c** and **d** in the diagram. (4.0 pt)

Bar chart (Q8-4, `T8_page-4.png`, `theory_problem.pdf` p. 75), stacked
percentages of H₂ (blue, hatched) and CO (red, hatched):

| bar | χ(H₂) | χ(CO) |
|-----|-------|-------|
| a   | — (no measurable product at all) | — |
| b   | ≈ 29 % | ≈ 71 % (= 100 − 29) |
| c   | ≈ 10 % | ≈ 90 % (= 100 − 10) |
| d   | ≈ 3 %  | ≈ 97 % (= 100 − 3) |

## Answer

| bar | condition | tick |
|-----|-----------|------|
| **a** | **N** (no irradiation) | a–N |
| **b** | **R** (red light)    | b–R |
| **c** | **G** (green light)  | c–G |
| **d** | **B** (blue light)   | d–B |

One tick per row of the answer sheet (`theory_problem.pdf` p. 82/A8-6).

## Source-grounding and derivation

Everything used here comes from the problem pages themselves plus one
elementary physical law (photon energy increases as wavelength decreases,
`E = h c / λ`).

**1. What the ΔG diagram says (Q8-3, `T8_page-3.png`, p. 74).**
Two competing pathways start from the common first reduction intermediate of
the Fe catalyst on C₃N₄:

* H₂-evolution branch (via bound H): `+H⁺ +0.756 eV; +e⁻ +1.832 eV;
  +H⁺ −0.168 eV; +H₂ −1.14 eV`. Its largest step, **`+e⁻, +1.832 eV`**, is a
  *photo-driven electron transfer*: an excited electron of the
  catalyst-support assembly can instead be captured through this branch to
  evolve H₂.
* CO₂-to-CO branch: `+e⁻ −0.04 eV; +CO₂ +0.02 eV; +e⁻ +0.16 eV;
  +H⁺ −0.36 eV; (+H⁺, −H₂O) −0.22 eV; −CO +0.1 eV` (overall ΔG = −0.34 eV).
  Its cumulative endergonic deficit is only `−0.04 + 0.02 + 0.16 = 0.14 eV`.

**2. The dark condition produces nothing (a = N).**
The CO branch is thermally activated in the dark − it still needs the first
photo-electron (`+e⁻`) to start. With no irradiation no product (H₂ or CO)
can be formed measurably, so the *only* bar with no bar drawn at all, **a**,
must be **N**.

**3. Every LED produces products; shorter wavelength ⇒ less H₂
(b = R, c = G, d = B).**
`0.14 eV ⇔ λ ≲ 1097 nm`: all three LEDs (red 620–700 nm, green ~530 nm,
blue ~470 nm; the problem's own illumination at λ = 390 nm in 8.6 confirms
blue-end excitation works) more than cover the deficit of the CO branch, so
all of R, G, B give CO-dominated product mixtures — consistent with
b, c, d being the three non-empty bars.

Photon energies order as `E_B > E_G > E_R`. The CO-route charging needs only
0.14 eV, whereas the competing H branch requires the second photo-electron
step `+1.832 eV` (and a proton to be reduced). The more energetic the
photon, the faster/more completely the photoexcited electron is funnelled
into CO formation and the fewer protons get reduced instead — i.e. the
smaller the H₂ mole percentage ("the fewer protons, the lower the H₂ mol %").
Therefore

  χ(H₂, R) > χ(H₂, G) > χ(H₂, B) > 0.

Reading the chart: χ(H₂) ≈ 29 % at b, ≈ 10 % at c, ≈ 3 % at d. The bars in
decreasing H₂ share are b > c > d, so they must match R, G, B in that order:

  **b = R, c = G, d = B**, and together with step 2, **a = N**.

## Faithfulness notes for the Lean formalization

`IChO2026Problems/problem_icho_2026_t8_a8.lean` proves:

* the exact data content of the ΔG diagram (sums: CO branch ΔG = −0.34 eV;
  the `+1.832 eV` step is the strict maximum of the H₂ branch steps; the
  photon threshold `0.14 eV < h c / 1097 nm` using the exact SI values of
  `h`, `c`, `e`);
* the wavelength ordering λ_B < λ_G < λ_R and the monotonicity of photon
  energy in 1/λ;
* the classification crossing facts: a product-free bar cannot coincide with
  any product-forming condition (`no_product_bar_is_distinct`), the red bar
  differs from the green bar since χ(H₂) drops going R → G
  (`green_lower_H2_than_red`), and the blue bar differs from the green bar
  (`blue_lower_H2_than_green`); the stacked-bar identity χ(CO) = 100 − χ(H₂)
  (`stacked_bars_sum_to_100`);
* the main theorem `assignment_forced`: from the printed diagram data
  (χ(H₂) = 0 % at a; 29/10/3 % at b/c/d), the bijection between conditions
  and bars, the uniqueness of the dark, product-free condition, and the
  selectivity ordering χ(H₂, B) < χ(H₂, G) < χ(H₂, R), the assignment is
  forced to be a ↦ N, b ↦ R, c ↦ G, d ↦ B. The requested tick table is
  `officialSubmission`, proved unique per row by
  `officialSubmission_matches`.

Declared as (physical, answer-blind) problem/principle inputs rather than
proved are: (i) the monotonic relation between photon energy and the H₂/CO
selectivity (the "fewer protons, lower H₂ mol %" principle explained above);
(ii) that all three LEDs photodrive the catalyst (grounded by the 0.14 eV ⇔
λ ≤ 1097 nm threshold proved in `co_requirement_wavelength`); (iii) the
reading of the chart percentages. These are stated explicitly as hypotheses
of the theorems, not hidden — `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` (and no axioms at all for
`officialSubmission_matches`).

## Source gaps

None affecting the four requested outputs: the bar percentages needed for
the crossing are fully legible in the printed diagram, the ΔG steps are
printed explicitly, and the four conditions are named in the problem text.
The only "gap" is the pedagogical one usual for IChO: the direction of the
selectivity–photon-energy dependence is physical reasoning (step 3), not a
numerical computation from printed data; it is isolated in exactly one
hypothesis of the main theorem.
