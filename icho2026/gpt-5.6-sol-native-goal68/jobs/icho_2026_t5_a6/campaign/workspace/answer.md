# IChO 2026 T5.6

Let the following diacylglycerol fragment denote one chosen tetrahedral
configuration.  The solid wedge is toward the viewer and the hashed bond to H
is away from the viewer.

```text
                         O-C(=O)-R
                            ▲  solid wedge
R-C(=O)-O-CH2 ----------- C* ----------- CH2-O-
                            ▽  hashed bond
                            H

                              D⁺
```

Thus `D⁺` contains two fatty-acid residues and ends in the glycerol oxygen
which is to be joined to phosphorus.  `D⁻` denotes its mirror image.  The `+`
and `-` signs specify opposite tetrahedral parities; they are not electric
charges.

## PL2

A structure satisfying all the data is

```text
             O                                      O
             ||                                     ||
D⁺-P(OH)-O-CH2-CH2-CH2-O-P(OH)-D⁺
```

Here each `D⁺-P` bond is specifically `D⁺-O-P`, so each phosphorus is
`P(=O)(OH)(O-D⁺)(O-CH2...)`.  Both phosphate groups are protonated in this
non-ionised drawing.  The two copies of `D⁺` have the **same** tetrahedral
configuration (the right-hand copy is rotated, not reflected).  Consequently
this is a chiral, left-right-symmetric `(+, +)` structure; its enantiomer is
obtained by replacing both copies by `D⁻`, giving `(-, -)`.

The central hydrolysis fragment is therefore

```text
Z = HO-CH2-CH2-CH2-OH       (1,3-propanediol)
```

Hydrolysis cleaves four carboxylate ester linkages and four phosphate ester
linkages.  It therefore consumes eight water molecules and gives four
`RCOOH`, two `H3PO4`, two glycerols, and one `Z`, exactly as printed.

Why `Z` works: glycerol, `C3H8O3`, has

```text
(3·4 + 8·1 + 3·2)/2 = 13
```

total sigma-plus-pi bond orders.  PL2 has one fewer total bond order than PL1,
while their hydrolysis equations differ only by replacing the third glycerol
with `Z`.  Hence `Z` must contribute 12 bond orders.  Symmetric
1,3-propanediol, `C3H8O2`, gives

```text
(3·4 + 8·1 + 2·2)/2 = 12.
```

Its O-C-C-C-O skeleton contains only single bonds, so it also satisfies the
stated catalytic-H2 nonreaction clue.  Replacing glycerol by this fragment
therefore changes the PL1 count from `255` to `255 - 13 + 12 = 254`.

## PL3

At physiological pH, one enantiomer is

```text
                         O-C(=O)-R
                            ▲  solid wedge
R-C(=O)-O-CH2 ----------- C* ----------- CH2-O-P(=O)(O⁻)-O-CH2-CH3
                            ▽  hashed bond
                            H
```

The other enantiomer has the solid and hashed bonds interchanged.  There are
two carboxylate ester bonds and two phosphate ester bonds, so the coefficient
in the source hydrolysis equation is `m = 4`.  Complete hydrolysis gives two
`RCOOH`, one `H3PO4`, ethanol, and glycerol.  The phosphate is a diester with
one remaining acidic oxygen; its deprotonated `O⁻` accounts for the charge at
physiological pH.  The glycerol C2 atom is stereogenic because its two carbon
arms are different (`CH2-O-C(=O)-R` versus
`CH2-O-P(=O)(O⁻)-O-CH2CH3`), giving the stated enantiomeric pair.

## Source grounding and scope

The structural inputs are on problem page Q5-4 (PDF page 47; also
`T5_page-4.png`): the two balanced hydrolysis equations, PL2's 254-bond count,
its chirality/symmetry clue, the composition and hydrogenation behavior of
`Z`, and PL3's charge/enantiomer clue.  Q5-1 to Q5-3 establish the PL1
fragment inventory and the common `RCOOH`; the corresponding blank student
sheet is A5-4 (PDF page 51), with separate boxes for PL2 and PL3.

The opening instruction says to be creative and build molecules, and the
problem does not state a uniqueness criterion or define a numerical ordering
of “more symmetrical”.  Accordingly, the answer above is a fully checked
constructive witness.  Its symmetry is the explicit nontrivial involution
that swaps the two identical phosphatidyl arms and reverses the central
O-CH2-CH2-CH2-O path; no uniqueness beyond the printed constraints is
claimed.
