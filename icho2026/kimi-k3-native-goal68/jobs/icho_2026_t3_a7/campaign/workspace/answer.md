# IChO 2026 — Theory 3, Subquestion 3.7 (target `icho_2026_t3_a7`)

## Question (from the official Q3-7 sheet)

> COF-9, obtained from COF-8, adsorbs UO₂²⁺ ions and loses its fluorescence.
> In an experiment, a suspension of 5.000 mg COF-9 in 19.90 mg dm⁻³ UO₂²⁺
> solution (200.0 mL) was filtered after equilibrium was reached. The final
> concentration of UO₂²⁺ was 9.225 mg dm⁻³. Calculate the equilibrium
> absorption capacity at a given temperature (qₑ) in mg g⁻¹ of COF-9.
> Indicate the number of UO₂²⁺ ions absorbed per pore. Assume that all
> uranium exists as UO₂²⁺ ions.

## Answers

- **Equilibrium adsorption capacity: qₑ = 427 mg g⁻¹** (exact from the
  printed data; 3 s.f. display is 427).
- **UO₂²⁺ ions absorbed per pore: 1.00 ions pore⁻¹** (raw value ≈ 1.0020;
  3 s.f.).

## Derivations

### Output 1 — qₑ (exact mass balance)

The mass of UO₂²⁺ removed from solution is (C₀ − Cₑ)·V:

  Δm(UO₂²⁺) = (19.90 − 9.225) mg dm⁻³ × 0.2000 dm³ = 10.675 × 0.2000 = 2.135 mg.

Dividing by the adsorbent mass m = 5.000 mg = 0.005000 g:

  qₑ = 2.135 mg / 0.005000 g = 427 mg g⁻¹ (exactly, with no intermediate
  rounding).

### Output 2 — uranyl ions per pore

**Framework repeat per pore.** COF-9 has the same 3,3-connected honeycomb
(hcb) 2D net as COF-8; the peripheral –C≡N groups are converted to
amidoximes –C(=NOH)NH₂ by NH₂OH, which does not alter the skeleton. For any
3-connected periodic net, Euler's polyhedron formula (V − E + F = 2 on the
torus of the unit cell, E = 3V/2) gives one hexagonal face — one pore — per
two vertices. One two-vertex cell (equivalently, one pore's worth of
framework) therefore contains:

- 1 E1-derived node: 1,3,5-trisubstituted benzene ring, C₆H₃, carrying the
  three amidoxime carbon/nitrogen/oxygen atoms (3 × CNH₃O);
- 1 D2-derived node: 1,3,5-triazine core, C₃N₃;
- 3 edges, each with two p-phenylene spacers (C₆H₄) and one vinylene bridge
  (–CH=C<, C₂H).

Summing: C₆₊₃₊₁₈₊₆₊₃ = C₃₆, H₃₊₁₂₊₃₊₉ = H₂₇, N₃₊₃₊₃ = N₉, O₃, i.e.
**C₃₆H₂₇N₉O₃ per pore** (= E1 + D2 − 3 H₂O + 3 NH₂OH). With CODATA 2022
relative atomic masses (C 12.011, H 1.008, N 14.007, O 15.999 — *not printed
on the sheet; stated below as an assumption*):

  M_pore = 36(12.011) + 27(1.008) + 9(14.007) + 3(15.999) = 633.672 g mol⁻¹

  M(UO₂²⁺) = 238.02891 + 2(15.999) = 270.02691 g mol⁻¹ (U = 238.02891).

**Ion count.** The number of uranyl ions adsorbed per gram of COF-9 is
`(qₑ/1000)/M(UO₂²⁺) · N_A`, and the number of pores per gram is
`N_A / M_pore`. The ratio is Avogadro-free:

  n(UO₂²⁺)/pore = qₑ · M_pore / (1000 · M(UO₂²⁺))
                = 427 × 633.672 / (1000 × 270.02691)
                = 270576.264 / 270026.91 = 33822243/33753363.75 ≈ 1.0020.

Rounded to three significant figures: **1.00 UO₂²⁺ ions per pore** — the
material adsorbs essentially one uranyl ion per pore, which is consistent
with each amidoxime-decorated pore acting as a single bidentate chelating
pocket for one UO₂²⁺ ion.

## Source grounding

All experimental inputs (19.90 mg dm⁻³, 9.225 mg dm⁻³, 200.0 mL, 5.000 mg)
are printed in the Q3-7 problem text; the structures needed for the pore
count (D2 = 2,4,6-tris(4-formylphenyl)-1,3,5-triazine, E1 =
benzene-1,3,5-triacetonitrile, the COF-8 honeycomb repeat with dashed
boundaries, and the COF-9 amidoxime drawing) are printed on the Q3-6 and
Q3-7 pages of the official English theory paper (`theory_problem.pdf`,
printed pages 30–31; images `T3_page-6.png`, `T3_page-7.png`).

## Assumptions and source gaps (explicit)

- **Not printed in the problem:** tabulated relative atomic masses
  (C 12.011, H 1.008, N 14.007, O 15.999, U 238.02891, CODATA 2022) and the
  Avogadro constant. The final answers are insensitive to the choice of
  standard table: with integer school-book masses (U = 238.0, etc.)
  M_pore = 645.00 and M(UO₂²⁺) = 270.00 give 427 × 645.00/270000 = 1.020,
  which also rounds to **1.02**; with CODATA values the answer is 1.00. The
  robust conclusion is "essentially one uranyl ion per pore". The
  Avogadro constant itself cancels exactly (proved in Lean).
- **Interpretive premise (grounded in the printed structures):** a "pore" is
  one hexagonal opening of the honeycomb layer, containing one two-vertex
  cell of framework of mass M_pore.
- The Lean development states these separately: the mass balance (Output 1)
  is unconditional; Output 2 is proved as the exact ratio plus its CODATA
  evaluation with the molar-mass assumption recorded.
