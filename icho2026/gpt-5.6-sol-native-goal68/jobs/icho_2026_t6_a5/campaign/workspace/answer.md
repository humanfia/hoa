# IChO 2026 T6-A5 — structures F–L

## Exact structural notation

The following compact skeletal notation makes every connection explicit.

- `P` is a *para*-connected phenylene unit, `p-C6H4`.
- `D_R` is the masked phenylene unit
  `C1(OR)(X)C=CC(OR)(Y)C=C1`: a 1,4-cyclohexadiene whose saturated
  carbons C1 and C4 each bear `OR` and, respectively, the neighboring groups
  `X` and `Y`.
- `Q(X)` is `C1(OH)(X)C=CC(=O)C=C1`, the
  4-hydroxycyclohexa-2,5-dien-1-one motif (the numbering direction is
  immaterial).
- `OTBS` is `O–Si(CH3)2C(CH3)3`; `OTES` is `O–Si(CH2CH3)3`.
- Every dash between `P`, `D`, or `Q` is a C–C single bond at the indicated
  para or saturated-ring attachment carbon. `cyclic{...}` additionally means
  that the two displayed ends are joined by a C–C bond.

With that notation, the requested structures are:

```text
F   Br–P–D_OH–P–P–OTBS

G   Br–P–D_TES–P–P–OTBS

H   Br–P–D_TES–P–P–OH

I   Br–P–D_TES–P–Q

J   Br–P–D_TES–P–D_OH–P–Br

K   Br–P–D_TES–P–D_TES–P–Br

L   cyclic{P–D_TES–P–D_TES–P}
```

Thus, for example, `D_TES` has an `OTES` group on each of its two saturated
1,4-carbons, whereas `D_OH` has an OH on each. In I, the left attachment of
`Q` is its saturated C–OH carbon and its opposite carbon is C=O. In L, the
new bond made in the nickel step joins the two aryl carbons that bore Br in K;
neither bromine remains.

The molecular-formula audit is:

| Compound | Formula |
|---|---|
| F | C30H33BrO3Si |
| G | C42H61BrO3Si3 |
| H | C36H47BrO3Si2 |
| I | C36H47BrO4Si2 |
| J | C42H52Br2O4Si2 |
| K | C54H80Br2O4Si4 |
| L | C54H80O4Si4 |

In particular, the formulas for H and L reproduce the two formulas printed in
the problem.

## Derivation

1. NaH prevents the starting OH from quenching the organolithium. Addition of
   the printed OTBS-biaryllithium to the cyclohexadienone carbonyl, followed by
   protonation on work-up, changes that C=O into C–OH and installs the biaryl
   group there. The pre-existing para C–OH is retained, giving the 1,4-diol F.
2. Two equivalents of TESCl/imidazole convert those two alcohols to OTES,
   giving G.
3. LiOH cleaves the terminal aryl OTBS ether to the phenol H while the two OTES
   groups on the masked ring remain. This assignment is also forced by the
   following step: oxidative dearomatization requires the terminal phenol. The
   resulting formula is exactly the printed C36H47BrO3Si2.
4. PhI(OAc)2 is specified as a two-electron oxidant. In water, oxidative
   dearomatization of that para-substituted phenol gives the
   para-hydroxycyclohexadienone Q, hence I. The phenolic oxygen becomes the
   carbonyl oxygen and water supplies the new para OH.
5. NaH and the printed para-bromophenyllithium repeat the carbonyl-addition
   logic, converting Q into a second 1,4-diol masked phenylene and furnishing
   the dibromide J.
6. Two equivalents of TESCl protect just the two newly formed OH groups, so K
   contains four OTES groups in total.
7. Ni(COD)2/2,2'-bipyridine reductively couples the two terminal aryl bromides.
   Their C–Br bonds are replaced by the ring-closing aryl–aryl C–C bond, giving
   macrocycle L. As a downstream check, removal of its four TES groups followed
   by SnCl2 aromatizes its two masked rings and gives the five-phenylene hoop
   C30H20 drawn as [5]CPP.

No wedge/dash, E/Z, or R/S information is present in the problem drawing or in
the blank F–L answer boxes, so no stereochemical assignment is invented. All
shown intermediates are neutral, closed-shell structures; no radical or formal
charge is needed.

## Source grounding

- [`TASK.json`](TASK.json) identifies the requested outputs as structures F–L
  and points to printed page Q6-3.
- [`T6_page-3.png`](icho_2026_source/image/T6_page-3.png) supplies the starting
  cyclohexadienone, both organolithium structures, reagent order, the printed H
  and L formulas, and the downstream [5]CPP product.
- [`T6_page-2.png`](icho_2026_source/image/T6_page-2.png) was inspected as the
  preceding page of the same problem; it introduces the context but adds no
  constraint on F–L.
- [`theory_problem.pdf`](icho_2026_source/raw/theory_problem.pdf) was inspected
  at PDF page 54 (original Q6-3) and at PDF pages 59–60 (blank student sheets
  A6-3 and A6-4). The sheets contain only empty boxes labelled F–L, so they add
  no partial skeleton or stereochemical convention.

The only non-figure chemistry used is the standard reaction meaning of
organolithium carbonyl addition/work-up, silyl-ether formation and cleavage,
aqueous hypervalent-iodine oxidative phenol dearomatization, and nickel(0)
aryl-halide coupling. There is no dependency on an earlier subquestion and no
source gap needed to determine the seven constitutional structures.
