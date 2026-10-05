# IChO 2026 T9-A2

## Answer

Tick the **right-hand chair**, i.e. the inverted **`¹C₄`** conformation.

`K` is **heptakis(3,6-anhydro)-β-cyclodextrin**, also called
**per-3,6-anhydro-β-cyclodextrin**. On every one of the seven repeat units,
draw a single ether oxygen between C3 and C6 (`C3–O–C6`) and retain the C2
hydroxyl. Thus the completed repeat has the following exact connectivity:

```text
pyranose ring:       O5–C1–C2–C3–C4–C5–O5
side bond:                            C5–C6
3,6-anhydro bridge:             C3–O36–C6
only free alcohol:                  C2–OH
macrocyclic link:    C1(i)–Og(i)–C4(i+1), cyclically for i = 1,...,7
```

All displayed bonds are single bonds. The molecule is neutral and has no
radicals. Its molecular formula, as a cross-check of the completed structure,
is `C42H56O28` (seven `C6H8O4` repeats).

### How to complete the printed right-hand template

In that template, follow the pyranose ring from its upper-right anomeric carbon
C1 through the heavy lower edge as C2, C3, C4; the upper-left carbon is C5 and
the oxygen at the top is O5.

- Draw `OH` **axial down from C2**.
- Draw the C5–C6 bond **axial up from C5**.
- Draw the C3–O bond **axial up from C3**, and join that same oxygen to C6.
  This is the intramolecular `3,6-anhydro` ether bridge.
- Leave the printed α-(1→4) glycosidic macrocycle in place and repeat the
  completed unit seven times.

The stereochemical face assignments, in the standard Haworth orientation, are
unambiguous as follows:

| Stereocentre | Face-defining bond | Face in `K` | Position in `¹C₄` |
|---|---|---|---|
| C1 | C1–O(glycosidic, outgoing) | down (α relative to C5–C6) | equatorial |
| C2 | C2–OH | down | axial |
| C3 | C3–O36 | up | axial |
| C4 | C4–O(glycosidic, incoming) | down | axial |
| C5 | C5–C6 | up (D series) | axial |

No carbon stereocentre is broken in either reaction step, so these are the
retained α-D-gluco configurations; only the chair changes from `⁴C₁` to
`¹C₄`.

## Derivation

1. Seven equivalents of TsCl correspond to one equivalent for each of the
   seven glucopyranosyl units. Tosylation in pyridine occurs at the accessible
   primary C6 hydroxyls, giving the per-6-O-tosyl intermediate; C2–OH and
   C3–OH remain.
2. In warm aqueous NaOH, C3 alkoxide attacks the primary C6 carbon
   intramolecularly and displaces tosylate. C6 is a methylene carbon, so this
   substitution introduces no new stereocentre. The oxygen originally at C3
   now supplies the `C3–O–C6` bridge.
3. Consequently C3–OH and C6–OH are consumed in the bridge and C2–OH is the
   sole free hydroxyl per repeat, exactly matching the condition stated for
   `K`. The 3,6 bridge constrains each glucopyranosyl ring to `¹C₄`, which is
   the right-hand printed chair.

## Source grounding

Problem-provided facts were taken from [TASK.json](TASK.json),
[T9_page-2.png](icho_2026_source/image/T9_page-2.png), and PDF page 85 of
[theory_problem.pdf](icho_2026_source/raw/theory_problem.pdf): β-CD has seven
α-D-glucopyranosyl units; the scheme uses TsCl (7 equiv.) in pyridine followed
by aqueous NaOH at 60 °C; and `K` has one free OH per repeat. PDF page 89 was
also inspected: it is the blank student answer sheet containing the left and
right chair/CD templates, not a solution.

The reaction-specific general chemistry is grounded independently in the
original scientific literature, not in any competition answer. Ashton,
Ellwood, Staton, and Stoddart report conversion of per-6-O-tosyl α- and β-CDs
by warm aqueous NaOH to the corresponding per-3,6-anhydro products
([J. Org. Chem. 1991, 56, 7274–7280](https://doi.org/10.1021/jo00026a017)).
Their accompanying communication identifies the glucopyranosyl conformation
of these products as `¹C₄`
([Angew. Chem. Int. Ed. Engl. 1991, 30, 80–81](https://doi.org/10.1002/anie.199100801)).

The Lean development separates the printed inputs (`ProblemInput`), the two
general reaction operations (`TrustedChemistry`), and the computed product
(`Derived`). The final molecular graph has 70 explicit heavy-atom vertices,
an implicit-hydrogen count at each vertex, an exact all-single-bond adjacency
predicate, formal charge and radical fields, and explicit stereochemical-face
predicates for C1–C5 of every repeat.
