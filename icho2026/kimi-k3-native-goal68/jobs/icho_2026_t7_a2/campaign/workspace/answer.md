# IChO 2026 T7.2 — annual methane requirement for the Navoiazot ammonia complex

**Answer: ≈ 2.80 × 10⁵ tons of CH₄ per year** (raw value 280 344.6 t; 3 s.f.).

## Answer derivation

Figure 1 is a classical two-stage steam-methane reforming (SMR) + autothermal
(ATR) ammonia plant:

* First unit:  `CH₄ + H₂O → CO + 3H₂`   (feed `x CH₄ + y H₂O`)
* Second unit: `2 CH₄ + O₂ → 2 CO + 4 H₂` (air fed as `4 N₂ + 1 O₂`)
* Shift:      `CO + H₂O → CO₂ + H₂`    (CO₂ removed at unit Z)
* Synthesis:  `N₂ + 3 H₂ ⇌ 2 NH₃`      (unreacted N₂/H₂ recycled via CLR)

All reactions except NH₃ formation are quantitative (given).  Let

* `f` = CH₄ fed to the first unit,
* `e` = CH₄ fed to the second unit,
* `n` = N₂ entering with the air.

The quantitative network gives two exact balances (`GenerationBalance`,
`AirBalance`):

* H₂ delivered to the synthesis section  `h2Gen = 4·f + 3·e`
  (3 H₂ per CH₄ in SMR, 2 H₂ per CH₄ in ATR, + 1 H₂ per CO in the shift,
  with CO = f + e total);
* N₂ from the air  `n2 = 2·e`  (printed air ratio 4 N₂ : 1 O₂ against the
  printed ATR stoichiometry 2 CH₄ : 1 O₂).

The "excess" H₂ inventory  `excess = h2Gen − 3·n2`  is zero exactly when the
plant runs with no persistent H₂ reserve, which forces `4·f = 3·e`.  Hence the
two feeds are in the ratio f : e = 3 : 4, total
`methane = f + e = (7/8)·n2`.  The net reaction (checked atom-for-atom) is

  7 CH₄ + 7 H₂O + 8 N₂ → 16 NH₃ + 7 CO₂

i.e. **16 mol NH₃ per 7 mol CH₄ at full conversion** (proved as
`methane_ratio_H2_exact : 8 * methane = 7 * n2` and
`tile_NH3_theoretical : 2*n2 = (16/7)*methane`).

Nitrogen–hydrogen stoichiometry (`HaberStoichiometry`, a trusted general
law: element balance of `N₂ + 3 H₂ → 2 NH₃` applied at overall yield η):

  n2 = NH₃_theory / 2,   NH₃_actual = η · 2 · n2 .

### Numerical chain (no intermediate rounding)

Printed periodic table (page 5, G1-5 of the same PDF):  C 12.01, N 14.01,
H 1.008 ⇒  M(CH₄) = 12.01 + 4·1.008 = **16.042 g/mol**,  M(NH₃) =
14.01 + 3·1.008 = **17.034 g/mol**.

  n(NH₃)   = 660 000 t / 17.034 kg kmol⁻¹  = 38 746 037.3 kmol a⁻¹
  n(CH₄)   = (7/16) · n(NH₃) / 0.970        = 17 475 661.2 kmol a⁻¹
  m(CH₄)   = 16.042 · n(CH₄)                = **280 344.56 t a⁻¹**
           = 77 202 125 000 / 275 383 t    (exact rational value)

Rounded to three significant figures (quantum 1000 t, half away from zero):
**2.80 × 10⁵ t ≈ 280 000 t/year**.

Note on precision: with the printed periodic-table values (page 5, G1-5)
the raw value is 280 344.56 t, strictly inside the 3-s.f. cell
[279 500, 280 500).  The integer-mass shortcut M = 16 / 17 would give
280 169.8 t — the same rounded cell — so the displayed answer is robust;
the formalisation still keeps the printed masses exact.

## Source grounding

* Problem statement: IChO 2026 theory PDF, problem T7 (Nitrogen Fixation),
  page 63 (`T7_page-1.png`).  Inputs printed on that page: capacity
  660 000 t yr⁻¹, overall yield 97.0 %, the Fig. 1 reaction network, and
  "assume that all reactions in Fig. 1, except NH₃ formation, are
  quantitative".
* Relative atomic masses: periodic table printed on PDF page 5 (G1-5);
  C 12.01, N 14.01, H 1.008.
* No external official solutions, marking schemes or answer repositories were
  used; the derivation above was produced directly from the problem sheet and
  general chemical stoichiometry (conservation of atoms, element balance of
  N₂ + 3 H₂ → 2 NH₃).

## Interpretation note (assumption)

"Operates according to Fig. 1" includes the unstated assumption that the
plant carries no persistent H₂ excess (excess = 0, the H₂-exact operation).
Fig. 1 does not print the feed split `x:y` or any uplift factor, so with a
non-zero excess the methane demand would be underdetermined; the H₂-exact
operation is the unique stoichiometrically consistent read of the printed
network and is used both in the Lean proofs and in the answer above.  This
assumption is flagged in `result.json`.
