# IChO 2026 T5.5

## Answer

Tick **(d) inverse hexagonal**.

## Reasoning

The problem states that, under physiological conditions, PL1 is a **dianion**
and forms a **lamellar** phase. In the charged state, electrostatic repulsion
between the two negatively charged acidic head-group sites enlarges the
effective area occupied by the polar head group. This balances the
hydrophobic-chain cross-section and permits essentially zero-curvature,
lamellar packing.

When both acidic sites are protonated, those two negative charges—and hence
that electrostatic head-group expansion—are removed. The effective polar-head
area decreases while the hydrophobic part is unchanged. PL1 therefore has the
packing tendency of an inverted cone: its preferred interfacial curvature is
negative. Of the four structures pictured in the question, the structure with
negative curvature is the inverse hexagonal (`H_II`) phase, option **(d)**.

Equivalently, in the usual qualitative packing-parameter expression

\[
P = \frac{v}{a_0\ell},
\]

protonation decreases the effective head-group area \(a_0\), so \(P\)
increases from the lamellar regime toward the inverse-aggregate regime. No
detailed structural reconstruction of PL1 is needed.

## Source grounding

- `TASK.json`, [the supplied question image](icho_2026_source/image/T5_page-3.png),
  and page 46 of [the original problem PDF](icho_2026_source/raw/theory_problem.pdf)
  provide the actual problem inputs: PL1 is diprotic, its physiological form is
  a dianion in a lamellar phase, and the four labelled phase choices are
  (a) micellar, (b) lamellar, (c) hexagonal, and (d) inverse hexagonal.
- Page 50 of the original PDF is the blank A5-3 student answer sheet. It contains
  only empty boxes labelled (a)–(d), so it supplies the response format but no
  answer information.
- The only source-independent chemistry premise used is the standard
  electrostatic packing principle that neutralizing an anionic lipid head group
  reduces its effective cross-sectional area and favours more negative
  curvature. This is independently supported by Seddon, Kaye, and Marsh's
  X-ray study, which observed a cardiolipin transition from lamellar \(L_\alpha\)
  to inverse hexagonal \(H_{II}\) on lowering pH
  ([DOI 10.1016/0005-2736(83)90134-7](https://doi.org/10.1016/0005-2736(83)90134-7)),
  and by coarse-grained simulations in which reducing cardiolipin head-group
  charge produced aggregates with more negative curvature
  ([DOI 10.1021/jp071954f](https://doi.org/10.1021/jp071954f)). These are
  ordinary scientific references, not competition answer material.

## Formalization correspondence

The Lean file does not postulate the requested option. It models a positive
electrostatic contribution to effective head area, takes the problem-stated
dianion/lamellar observation as an explicit hypothesis, and proves:

1. lamellar packing implies balanced effective head and hydrophobic areas;
2. removing both charges makes the fully protonated head area strictly smaller;
3. this gives negative packing curvature; and
4. among the four printed choices, exactly (d), inverse hexagonal, has negative
   curvature.

