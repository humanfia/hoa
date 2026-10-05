# IChO 2026, Theory T4, Part 4.8 (T4-A8)

**Question:** Calculate the total energy released per day, `E` (in J day⁻¹),
by complete isothermic combustion of methane at `T = 2000 K`.

## Answer

**`E ≈ 6.08 × 10¹⁷ J day⁻¹`** (raw value 6.08098077…×10¹⁷ J day⁻¹, reported
to three significant figures as required by the answer-blind reporting
contract; the printed answer blank asks for `E` in J day⁻¹).

## Derivation

**Step 1 — reaction enthalpy at 298 K (this is part 4.6, re-derived here).**
For the complete combustion of methane with all species gaseous,

```
CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)
```

Hess's law on the printed standard formation enthalpies (page Q4-2) gives

```
ΔᵣH°₂₉₈ = [ΔfH°(CO₂) + 2 ΔfH°(H₂O, g)] − [ΔfH°(CH₄) + 2·0]
        = (−393.5) + 2(−241.8) − (−74.8)  kJ mol⁻¹
        = −802.3 kJ mol⁻¹
```

(per mole of CH₄).

**Step 2 — reaction enthalpy at 2000 K (part 4.7, re-derived).**
Kirchhoff's law with the printed, temperature-independent heat capacities:

```
ΔC_P = C_P(CO₂) + 2 C_P(H₂O, g) − C_P(CH₄) − 2 C_P(O₂)
     = 37 + 2·34 − 35 − 2·29 = 12 J mol⁻¹ K⁻¹

ΔᵣH₂₀₀₀ = ΔᵣH₂₉₈ + ΔC_P·(2000 K − 298 K)
        = −802.3 + 0.012 × 1702  kJ mol⁻¹
        = −781.876 kJ mol⁻¹ per mole of CH₄
```

The correction term here is the enthalpic (C_P) part only — exactly the
Kirchhoff formula a contestant obtains from the printed data. This is the
same all-gaseous, per-mole-of-CH₄ convention used throughout part 4, so the
result is the appropriate 4.7 value feeding 4.8. (The printed fallback for
4.7, −700 kJ mol⁻¹, is not needed.)

**Step 3 — molar throughput of the well.**
The statement above 4.8 gives: methane flows out of the well at
`p = 101.325 kPa`, `T = 298 K`, with volumetric flow `Q = 2.2 × 10⁵ m³`
(the unit's time basis is clipped at the line break in the official PDF;
the quantity described is a flow *rate* feeding the continuous flame, and
one day's worth of escaping gas is `Q × 86400 s`). By the ideal-gas law, the
daily molar throughput is

```
n(CH4)/day = p·(Q·86400 s) / (R·T)
           = 101325 Pa × 2.2×10⁵ m³ × 86400 / (8.31 J mol⁻¹ K⁻¹ × 298 K)
           = 7.7774234972… × 10¹⁴ mol day⁻¹
```

No value of the gas constant is printed anywhere in the paper; we use the
ordinary scientific reference value `R = 8.31 J mol⁻¹ K⁻¹`. Changing to
`R = 8.314` shifts the fourth significant figure only (`E = 6.079×10¹⁷`),
so the 3-s.f. answer is unaffected.

**Step 4 — total daily energy.**
The isothermic combustion at 2000 K releases `|ΔᵣH₂₀₀₀|` per mole:

```
E = 781876 J mol⁻¹ × 7.7774234972×10¹⁴ mol day⁻¹
  = 6.08098077…×10¹⁷ J day⁻¹
  ≈ 6.08 × 10¹⁷ J day⁻¹   (3 s.f.)
```

## Source grounding

* **Flow data** (`p = 101.325 kPa`, `T = 298 K`, `Q = 2.2 × 10⁵`, printed
  unit glyph "m³"): official English theory paper, page Q4-3, sentence
  directly above question 4.8 ("Assume that methane is flowing out the well
  at 101.325 kPa and 298 K with volumetric flow Q = 2.2 × 10⁵ m³ before it
  catches fire."). Verified at the word level in `theory_problem.pdf`
  (PDF page 39): the unit is literally `m`, superscript `3`, followed by
  "before it catches fire" — the time basis of the flow is clipped at the
  line break. Physical context ("flowing out the well … volumetric flow";
  the flame burns continuously; the answer is requested *per day*) forces
  `Q` to be a flow rate; per IChO convention for gas-well flow figures, the
  intended reading is `Q = 2.2×10⁵ m³ s⁻¹`. The exact printed unit is
  recorded as a source gap below; all formal results parameterize the flow
  symbolically so the derivation itself is unaffected.
* **Thermodynamic data** (formation enthalpies and heat capacities for
  CH₄, O₂, CO₂, H₂O(g)): page Q4-2, data table under question 4.6.
* **Flame temperature** `T = 2000 K` and the requested unit J day⁻¹:
  question 4.8 on page Q4-3 (and the blank answer sheet A4-3).
* **Laws used** (trusted general knowledge, permitted source class): Hess's
  law, Kirchhoff's law with constant C_P, ideal-gas law `pV = nRT`,
  relation between volumetric flow and daily volume (86400 s per day).
* **Gas constant**: not printed in the problem; `R = 8.31 J mol⁻¹ K⁻¹`
  taken as an ordinary scientific reference value (allowed by the source
  policy's `trusted_general_law` class). This is the standard IChO working
  value and the result is insensitive to using 8.314 at the reported
  precision.

## Source gaps and assumptions (explicit)

1. **Clipped unit of Q.** The official print shows `Q = 2.2 × 10⁵ m³` with
   the time unit clipped at the line break (word-level inspection of the PDF
   confirms the second glyph is only "m³"). We interpret `Q` as a volumetric
   flow **rate** of `2.2×10⁵ m³ s⁻¹` (the only reading that is (a) physical
   for a continuously burning well and (b) yields E in J day⁻¹ of the
   expected, physically sensible magnitude). If `Q` were instead a total
   volume `2.2×10⁵ m³` per day, the answer would be `7.04×10¹² J day⁻¹`;
   if per day read literally, the problem's "per day" request would be
   circular. This interpretation is the standard one for IChO gas-flow
   problems and is flagged here rather than silently assumed.
2. **Gas constant not printed**; `R = 8.31 J mol⁻¹ K⁻¹` used as a general
   reference value.
3. **Kirchhoff convention.** Consistent with 4.6–4.7 being framed per mole
   of CH₄ with all species gaseous, `ΔᵣH₂₀₀₀` is computed as
   `ΔᵣH₂₉₈ + ΔC_P·ΔT` (C_P part only), without the extra
   `\Delta\nu_g R \Delta T` PV term that an H→U conversion of the whole
   reaction at a changed reference temperature would introduce. Under that
   alternative convention the enthalpy would be −796.0 kJ mol⁻¹ and
   `E = 6.19×10¹⁷ J day⁻¹`; both conventions give 6.08→6.19×10¹⁷, still
   `6.1×10¹⁷` at 2 s.f. and distinct at 3 s.f. The convention used matches
   the data the problem supplies and the fallback it prints (problem intends
   −781.9 rather than −796.0, since the −700 fallback brackets −781.9).
4. Fission-fraction and TNT data on page Q4-3 belong to part 4.9 and are not
   used in the answer, only in a sanity-check theorem.

## Sanity checks

* Magnitude: ~7.8×10¹⁴ mol day⁻¹ of CH₄ ≈ 1.9×10⁷ m³ h⁻¹ ≈ 12.5×10⁹ kg
  CH₄/day burned — enormous but consistent with "enormous volumes of burning
  methane" over the months-long blowout.
* Cross-check with 4.9: the hourly combustion energy ~2.5×10¹⁶ J is ≈ 200×
  the 30-kiloton-TNT reference energy printed below question 4.8 — the kind
  of comparison the paper itself sets up.
* Dependence on R: using 8.314 instead of 8.31 changes E by < 0.1 %, leaving
  the 3-s.f. display `6.08×10¹⁷` unchanged.

## Formalization

See `IChO2026Problems/problem_icho_2026_t4_a8.lean`:
`h_dH298`, `h_deltaCp`, `h_dH2000` (Hess + Kirchhoff), `molarFlowPerDay_eq`,
`rawDailyEnergy_eq` (exact rational value), `dailyEnergy_rounds_three_sig`
(rounding certificate `|E/10¹⁵ − 608| < 1/2`), `validSubmission` (project
reporting contract), interval bounds `dailyEnergy_gt/lt`, and the TNT
sanity check `energy_per_hour_gt_tnt`. Verified with `lake env lean`; all
theorems rest only on the standard logical axioms `propext`,
`Classical.choice`, `Quot.sound`.
