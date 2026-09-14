# IChO 2026 T5-A2

## Answer

Choose the enantiomer in which both stereogenic carbon atoms of the two
peripheral glycerol units have configuration $R$.  A complete condensed
structure, written as one continuous chain, is

```text
R-C(=O)-O-CH2-[C*H(O-C(=O)-R)]_(R)-CH2-O-P(=O)(OH)-O-CH2-
CH(OH)-CH2-O-P(=O)(OH)-O-CH2-[C*H(O-C(=O)-R)]_(R)-CH2-O-C(=O)-R
```

The `_(R)` labels specify the absolute configurations of the starred carbons;
they are not extra substituents.  Both peripheral stereocentres are therefore
$R$; the $(S,S)$ mirror image
is the other valid enantiomer.  The middle carbon of the central glycerol is
not stereogenic because its two arms are identical, and phosphorus chirality
is disregarded as instructed.  The mixed $(R,S)$ and $(S,R)$ assignments are
meso: reflection exchanges the identical halves and leaves each structure
unchanged.

For one proton-localized drawing of monoanion **Y**, retain the same
stereochemistry and deprotonate the left phosphate:

```text
R-C(=O)-O-CH2-[C*H(O-C(=O)-R)]_(R)-CH2-O-P_L(=O)(O^-)-O-CH2-
CH(OH)-CH2-O-P_R(=O)(OH)-O-CH2-[C*H(O-C(=O)-R)]_(R)-CH2-O-C(=O)-R
```

Fold the central headgroup so that the following two intramolecular hydrogen
bonds are visible (`...` denotes a hydrogen bond and `O_c-H` is the central
glycerol hydroxyl):

```text
P_L-O^- ... H-O_c ... H-O-P_R
```

The first contact is $P_L-O^-\cdots H-O_c$: the central OH donates to the
anionic phosphate oxygen.  The second is
$O_c\cdots H-O-P_R$: the same central oxygen accepts from the still-protonated
phosphate.  Together with the covalent segment

```text
P_L-O-CH2-CH(O_c-H)-CH2-O-P_R
```

these contacts make the bicyclic hydrogen-bonded headgroup.  The equivalent
proton-localized form has left and right exchanged:

```text
P_L-O-H ... O_c-H ... O^--P_R
```

Thus the monoanion has one remaining phosphate proton, one formal negative
charge, and two symmetry-related proton-localization forms.  Removing the
second acidic proton destroys this cyclic hydrogen-bond network.  That raises
the free-energy cost of the second deprotonation relative to the first and
therefore gives $pK_{a2}>pK_{a1}$, qualitatively the stated
$pK_{a2}\gg pK_{a1}$.

## Derivation and source grounding

The Q5-1 source figure supplies two phosphate fragments `b`, three glycerol
fragments `c`, and four acyl fragments `d`.  The three glycerols expose nine
oxygen attachment sites.  Four are esterified by the four
$R-C(=O)-$ fragments and four form the two phosphate diester linkages, leaving
one oxygen to receive the type-`a` hydrogen cap.  Hence $n=1$, consistently
deriving the preceding part rather than assuming it.  The OH already drawn on
each `b` fragment supplies the two equivalent acidic groups.  Connecting two
oxygen sites to each other would create the expressly forbidden peroxide bond;
none occurs in the structure above.

The cardiolipin connectivity places two diacylated peripheral glycerols on the
two phosphates and uses the third glycerol as their bridge.  With four
identical `R` groups, equal peripheral configurations give the chiral
$(R,R)/(S,S)$ pair stated in the problem; opposite configurations give the
mirror-plane-containing meso cases.

The molecular drawings and wording were checked directly against
[`T5_page-1.png`](icho_2026_source/image/T5_page-1.png),
[`T5_page-2.png`](icho_2026_source/image/T5_page-2.png), and the corresponding
Q5-1/Q5-2 pages in
[`theory_problem.pdf`](icho_2026_source/raw/theory_problem.pdf), including the
blank Q5-2 student answer area.  Their SHA-256 values match `TASK.json`.

The source itself stipulates that special stabilization of Y explains the
large pKa separation.  The specific cyclic intramolecular-hydrogen-bond model
is also the model tested by Kates, Syz, Gosser and Haines,
[*pH-dissociation characteristics of cardiolipin and its 2'-deoxy analogue*
(1993)](https://pubmed.ncbi.nlm.nih.gov/8246687/): removal of the central OH in
the deoxy analogue removed the unusually separated dissociations.  That paper
is used only as ordinary chemical grounding, not as a competition answer.
Later literature debates whether real cardiolipin membranes always have this
protonation behaviour; the answer above formalizes the model explicitly
stipulated by this problem and does not claim broader experimental consensus.

## Formalization correspondence

The Lean file represents all atoms outside the four permitted `R`
abbreviations, including carbon-bound hydrogens; every covalent bond and bond
order; formal charges; zero radical electrons; both peripheral configurations;
and the two noncovalent hydrogen bonds separately.  It proves the atom and
fragment inventories, neutral and monoanionic charges, valid valences, absence
of O-O bonds, closed-shell character, enantiomerism, achirality of the mixed
diastereomers, reflection-equivalence of the two Y drawings, and the pKa
ordering from a positive monoanion stabilization energy and
ΔG° = RT ln(10) pKa.

Because the source gives no numerical meaning or threshold for the symbol
“≫”, neither the prose nor the Lean theorem invents one: the formal
thermodynamic conclusion is the source-justified strict ordering
$pK_{a2}>pK_{a1}$, with the displayed two-bond network providing the requested
qualitative explanation of the large separation.
