# IChO 2026 T9-A4

## Answer

`Y` is the sixfold primary-silylated manno-epoxide of α-cyclodextrin:

\[
\boxed{
Y=\left[\to4)-\alpha\text{-D-(6-}O\text{-TBS-2,3-anhydro-
mannopyranosyl)-(1}\to\right]_6
}
\]

Equivalently, it is **hexakis(2,3-anhydro-6-\(O\)-tert-butyldimethylsilyl)-α-cyclomannin**, where

\[
\mathrm{TBS}=\mathrm{Si(CH_3)_2C(CH_3)_3}.
\]

Complete every one of the six copies of the supplied CD template as follows:

- At C6, draw the primary substituent **up** as
  \(\mathrm{CH_2-O-Si(CH_3)_2C(CH_3)_3}\) (that is, \(\mathrm{CH_2OTBS}\)).
- Delete both the C2-OH and C3-OH groups. Connect one oxygen to both C2 and C3, making the three-membered C2-C3-O epoxide. Both C2-O(epoxide) and C3-O(epoxide) bonds are on the **upper face** of the supplied template.
- Retain the α-(1→4) macrocycle: the C1 glycosidic oxygen is down (α), the incoming C4 glycosidic oxygen is down, and the C5-\(\mathrm{CH_2OTBS}\) bond is up. There are no charges or radicals.

The essential template addition can be represented schematically as

```text
                             CH2-O-Si(CH3)2-C(CH3)3
                                      up
                                       |
        α-(1→4) pyranose skeleton:     C5

                         O(epoxide; upper face)
                              /       \
                            C3---------C2
                            up         up

        C1-O(glycosidic): down (α)     C4-O(glycosidic): down
```

This repeating-unit specification fixes the atom connectivity and all stereochemical information that must be added to the blank template.

## Derivation

The starting α-CD contains six α-D-glucopyranosyl units. Cyclizing six glucoses makes six glycosidic bonds and eliminates six waters, giving \(6\,\mathrm{C_6H_{12}O_6}-6\,\mathrm{H_2O}=\mathrm{C_{36}H_{60}O_{30}}\). Six equivalents of TBSCl then protect one primary 6-OH per unit. The first-stage formula is

\[
\mathrm{C_{36}H_{60}O_{30}}
  +6\times(\mathrm{C_6H_{14}Si})
  =\mathrm{C_{72}H_{144}O_{30}Si_6}.
\]

After NaH, selective activation of O2 by TsCl followed by intramolecular displacement by O3 makes one 2,3-epoxide in every unit. Each closure removes the elements of one water molecule from the 2,3-diol, so

\[
\mathrm{C_{72}H_{144}O_{30}Si_6}
  -6\,\mathrm{H_2O}
  =\mathrm{C_{72}H_{132}O_{24}Si_6},
\]

exactly the formula printed for `Y` on the problem figure and blank answer sheet.

Stereochemically, O3 attacks the activated C2 by intramolecular SN2. C2 is inverted from the glucose configuration, whereas C3 is retained, so the epoxide oxygen is up at both C2 and C3: a 2,3-anhydro-D-manno unit. The subsequent steps shown in the problem independently check this assignment. Fluoride removes all O6-TBS groups, and hot-water opening of the epoxide at C3 inverts C3, giving the displayed D-altrose pattern of α-cycloaltrin (C2-OH up and C3-OH down).

## Source grounding

- `TASK.json` identifies T9-A4 and the required output as the complete stereochemical structure of `Y`.
- Original `theory_problem.pdf`, PDF page 85 (`Q9-2`), supplies the six-unit α-CD starting template, the reagents and equivalents, the formula \(\mathrm{C_{72}H_{132}O_{24}Si_6}\), and the stereochemically drawn α-cycloaltrin product. PDF page 90 (`A9-2`) supplies the blank six-repeat student template and repeats the formula. The designated extracted images `T9_page-1.png` and `T9_page-2.png` were also inspected.
- As an independent ordinary-chemistry cross-check, Immel *et al.* describe 2,3-anhydro-α-cyclomannin as six α-(1→4)-linked 2,3-anhydro-D-mannopyranose residues and report the epoxide oxygens on the outer side of the macrocycle: [Chemistry—A European Journal 6 (2000) 2327–2333](https://doi.org/10.1002/1521-3765(20000703)6:13%3C2327::AID-CHEM2327%3E3.0.CO;2-V). A second primary paper states the exact key sequence: 6-O-TBS blocking, selective sulfonation of the more acidic 2-OH, then displacement by the vicinal 3-OH to form the oxirane: [Tetrahedron: Asymmetry 11 (2000) 27–36](https://doi.org/10.1016/S0957-4166(99)00583-2).

No official solution, marking scheme, answer repository, or historical competition answer was used.
