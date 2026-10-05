# IChO 2026 T2-A1

## Answer

With Ce(IV) written over the arrow as a catalyst, the balanced net ionic
equation is

\[
\boxed{
3\,\mathrm{CH_2(COOH)_2}
+4\,\mathrm{BrO_3^-}
\xrightarrow{\mathrm{Ce(IV)}\;\text{(cat.)}}
9\,\mathrm{CO_2}
+4\,\mathrm{Br^-}
+6\,\mathrm{H_2O}
}
\]

Equivalently, retaining the spectator potassium ions gives the molecular
form

\[
3\,\mathrm{CH_2(COOH)_2}+4\,\mathrm{KBrO_3}
\xrightarrow{\mathrm{Ce(IV)}\;\text{(cat.)}}
9\,\mathrm{CO_2}+4\,\mathrm{KBr}+6\,\mathrm{H_2O}.
\]

Ce(IV) is not included with a stoichiometric coefficient because a catalyst
is regenerated and therefore has zero net consumption in the overall
reaction.

## Derivation

The displayed formula for malonic acid expands as
\(\mathrm{CH_2(COOH)_2=C_3H_4O_4}\). In acidic solution its complete
oxidation to carbon dioxide is balanced by

\[
\mathrm{C_3H_4O_4+2H_2O\longrightarrow3CO_2+8H^++8e^-}.
\]

The stated bromate-to-bromide reduction is

\[
\mathrm{BrO_3^-+6H^++6e^-\longrightarrow Br^-+3H_2O}.
\]

Multiplying the oxidation half-reaction by 3 and the reduction half-reaction
by 4 makes both electron counts 24. Adding them cancels all electrons and
all \(\mathrm{H^+}\); cancelling six waters from opposite sides leaves the
boxed equation.

A direct check gives the same totals on both sides:

| conserved quantity | reactants | products |
|---|---:|---:|
| C atoms | 9 | 9 |
| H atoms | 12 | 12 |
| O atoms | 24 | 24 |
| Br atoms | 4 | 4 |
| total charge | \(-4\) | \(-4\) |

## Source grounding and formalization

- `TASK.json` and problem page Q2-1 (PDF page 15, also
  `icho_2026_source/image/T2_page-1.png`) supply the reactants, the formula
  of malonic acid, the oxidation product \(\mathrm{CO_2}\), the reduction
  product \(\mathrm{Br^-}\), and the statement that Ce(IV) is catalytic.
- The original PDF answer page A2-1 (PDF page 19) contains one unrestricted
  blank response box for 2.1. It adds no phase labels, numerical convention,
  or alternative species, so the net ionic equation directly answers the
  requested formula output.
- Atom conservation and charge conservation are the only general chemical
  laws used to derive the coefficients. Potassium is a spectator in the net
  ionic form; the molecular form above restores it on both sides.
- In `IChO2026Problems/problem_icho_2026_t2_a1.lean`, `SourceData.formula`
  contains only formula/charge data parsed from the problem. `Balanced`
  states atom and charge conservation. The theorem
  `balanced_overall_shape_classification` proves that every whole-number
  balanced equation using exactly the stated endpoints has coefficient
  vector \(k(3,4,9,4,6)\). `balanced_bz_equation` verifies the least positive
  vector and records Ce(IV) separately as a zero-net-coefficient catalyst.

No source gap or supplementary model assumption is needed for T2-A1.
