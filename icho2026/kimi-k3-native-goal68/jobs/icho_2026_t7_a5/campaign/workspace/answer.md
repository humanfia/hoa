# IChO 2026 T7 — Subquestion T7-A5

**Task id:** `icho_2026_t7_a5`  
**Paper / part:** T7 "Nitrogen Fixation", question 7.5 (6.0 pt), printed page 3 (Q7-3),
source PDF page 65. Assets examined: `T7_page-2.png` (the scheme), `T7_page-3.png`
(the question), the answer sheet A7-4 (PDF p. 70), and `theory_problem.pdf`.

## The question

> **7.5 Draw the structure of 5 using simplified scheme for the ligand.**
> Note that 1.00 g of **4** will react stoichiometrically with 94.97 cm³ of N₂
> at 273.15 K and 1.0 bar.

From the Q7-2 scheme, **4** is the PNP-pincer molybdenum trichloride complex
`(PNP)MoCl₃`, with `M_W(4) = 597.824 g mol⁻¹`, treated with `N₂ (1.0 bar)` and
`Na-Hg (3 equiv.)` to give **5**. The dashed box on Q7-2 defines the
"simplified scheme for the ligand": the tridentate PNP pincer
2,6-bis[(di-tert-butylphosphino)methyl]pyridine, drawn as a central pyridine N
flanked by two arcs to the two P donors (a meridional pincer). The answer sheet
A7-4 is a plain blank box labelled "5" (no extra template fields).

## Working: how many N₂ per Mo?

Using the ideal-gas law on the printed quantities:

- `n(4) = m/M = 1.00 g / 597.824 g mol⁻¹ = 1.6727×10⁻³ mol`
- `n(N₂) = pV/RT = (1.0 bar × 94.97 cm³) / (83.1446 cm³ bar mol⁻¹ K⁻¹ × 273.15 K)`
  `= 4.1817×10⁻³ mol`

(Using R = 8.314462618 J K⁻¹ mol⁻¹ and the bar·cm³ ↔ Pa·m³ conversion.)

Therefore

    n(N₂) / n(4) = 4.1817×10⁻³ / 1.6727×10⁻³ = 2.5000 ≈ 2.5 = 5/2

So **one N₂ molecule is fixed per two Mo centres**. Because the mild reductant
Na-Hg (3 equiv per Mo) reduces Mo(III) → Mo(0), the N₂ is *not* cleaved; it is
retained as an intact, bridging dinitrogen ligand. This pins **5** as a
dinuclear complex containing a single μ-N₂ shared by two (PNP)Mo fragments.

## Answer — structure of 5

**5** is the **dinuclear μ-dinitrogen complex**

    [ (PNP)Mo ← N≡N → Mo(PNP) ]      i.e.   [(PNP)Mo(μ-N₂)Mo(PNP)]

drawn with the simplified (arc) ligand as:

```
      (⌒P                    P⌒)
        \                    /
         N                  N
          \                /
           Mo — N ≡ N — Mo          (μ-η¹:η¹ end-on, near-linear Mo–N–N–Mo)
```

in words:

- **Two** (PNP)Mo units (the simplified pincer: a central N donor and the two P
  donors bound to each Mo, meridional/tridentate);
- **One** N₂ molecule bridging the two Mo centres, bound **end-on (η¹) to each**
  (μ-η¹:η¹), giving a near-linear Mo–N=N–Mo axis;
- each Mo is formally Mo(0) after the 3-electron reduction of Mo(III) in 4 and
  is coordinatively/electronically satisfied by the tridentate PNP (6e) plus
  the N₂ bridge donor (2e to each metal).

This stoichiometry (1 N₂ : 2 Mo) is exactly what the gas-uptake data require,
and it fixes the otherwise ambiguous point of the drawing: the N₂ ligand is a
**bridge between two Mo atoms**, not two separate N₂ ligands and not a cleaved
nitride.

## Source grounding

- Molecular formula of 4, M_W, the reagents (N₂, Na-Hg) and the simplified
  ligand glyph: `T7_page-2.png` (Q7-2), PDF p. 64.
- The 7.5 question text and the gas data (1.00 g, 94.97 cm³, 273.15 K, 1.0 bar):
  `T7_page-3.png` (Q7-3), PDF p. 65.
- Blank answer box labelled "5" (no template fields): A7-4, PDF p. 70.
- The 2.5 ratio and hence the dinuclear μ-N₂ assignment are *derived* by me from
  the ideal-gas law and the data above; no official solution/marking scheme was
  used.

## Caveat (semantic faithfulness)

The problem asks only for a *drawing*. The uniquely determined facts (dinuclear
complex, one bridging N₂, end-on at both Mo, Mo(0) after 3e reduction, pincer
retained) are fully grounded in the problem data plus the ideal-gas law. The
precise N–N bond order in the drawn bridge is a drawing choice; the essential,
derivable content is the **1 N₂ : 2 Mo bridging structure**.
