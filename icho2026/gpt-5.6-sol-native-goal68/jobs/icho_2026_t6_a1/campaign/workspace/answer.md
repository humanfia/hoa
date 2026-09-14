# IChO 2026 T6-A1

The completed table is:

| π-system type | C₁₈ | C₁₆ | ³C₁₃ | ¹C₁₃ |
|---|---:|---:|---:|---:|
| aromatic (A) | **2** | **0** | **0** | **1** |
| anti-aromatic (AA) | **0** | **2** | **0** | **1** |

## Reasoning

An sp-hybridized cyclocarbon has two distinct, mutually orthogonal conjugated
π systems: one in the molecular plane and one perpendicular to it. Apply
Hückel's rule separately to their π-electron populations: a `4k + 2` system is
aromatic, a positive `4k` system is anti-aromatic, and an odd population is
neither under this rule.

- **C₁₈:** each π system has 18 electrons, and
  `18 = 4(4) + 2`. Both systems are aromatic: A = 2, AA = 0.
- **C₁₆:** each π system has 16 electrons, and `16 = 4(4)`.
  Both systems are anti-aromatic: A = 0, AA = 2.
- **³C₁₃:** the two unpaired carbene electrons occupy the two orthogonal
  manifolds separately. Each manifold therefore has 13 electrons. Since
  `13 mod 4 = 1`, neither is a Hückel aromatic nor a Hückel anti-aromatic
  system: A = 0, AA = 0.
- **¹C₁₃:** in the conventional closed-shell singlet-carbene electron
  accounting intended by this Hückel exercise, the two carbene electrons are
  paired in one manifold and the corresponding orbital in the other manifold
  is empty. The populations are consequently 14 and 12. Since
  `14 = 4(3) + 2` and `12 = 4(3)`, there is one aromatic and one
  anti-aromatic system: A = 1, AA = 1. Which manifold is named in-plane does
  not affect the requested counts.

## Source grounding and model boundary

The problem-only sources were inspected directly. `TASK.json` requests eight
exact integers. [`T6_page-1.png`](icho_2026_source/image/T6_page-1.png) and PDF
page 52 of [`theory_problem.pdf`](icho_2026_source/raw/theory_problem.pdf) give
the four species, the two spin labels, and the instruction to use Hückel's
rule. Blank student answer sheet A6-1 on PDF page 57 confirms that the intended
layout has A and AA rows against those four columns. Their SHA-256 values match
the hashes recorded in `TASK.json`:

- `T6_page-1.png`:
  `29fff91c704c94f9e4e9fddba3ab61896375763880aff114baef9318cbdbe6ba`
- `theory_problem.pdf`:
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`

The printed page does not include the orbital diagram needed for the electron
accounting. The standard two-manifold model is corroborated by the primary
cyclocarbon literature: the C₁₆ study describes the in-plane and out-of-plane
π systems and the double `4k + 2`/`4k` classification
([Nature 623, 977–981 (2023)](https://doi.org/10.1038/s41586-023-06566-8));
the C₁₃ study reports 13 electrons in each π system for the open-shell triplet
and also analyzes the paired/empty closed-shell singlet configuration
([Science 384, 677–682 (2024)](https://doi.org/10.1126/science.ado1399)).
No competition solution, marking scheme, or answer repository was used.

Spin `S = 0` alone can also describe an open-shell singlet in a more elaborate
multireference treatment. The `¹C₁₃` entry above therefore makes explicit the
ordinary closed-shell singlet-carbene interpretation required for this
elementary Hückel table; an open-shell `13/13` singlet would instead be neither
class in both manifolds. This modeling boundary is represented explicitly by
`piElectronCount` in the Lean file rather than hidden as an unchecked axiom.
