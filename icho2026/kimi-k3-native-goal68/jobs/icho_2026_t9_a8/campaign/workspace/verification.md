# Verification record — icho_2026_t9_a8

## Sources inspected (problem-only, answer-blind)

* `icho_2026_source/image/T9_page-4.png` — problem page Q9-4 with the scheme
  `N → O → P → Q → R → S`, all reagent arrows, the structure of N, and the 9.8
  question text ("1,2-unit modification happens clockwise, 1,3-unit
  modification counterclockwise; protic groups have stronger directing effects
  than alkenes").
* `icho_2026_source/image/T9_page-3.png` — problem page Q9-3 with the Sinay
  protic-direction rule (1,4 fall back to 1,3 if not available) and the Bn
  legend.
* `icho_2026_source/image/T9_page-1.png`, `T9_page-2.png`, `T9_page-5.png` —
  introductory context (α-CD = 6 units), earlier template conventions
  ((OH)14, (Obn)14 legend on Q9-1/Q9-2), and question 9.9 (no further input).
* `icho_2026_source/raw/theory_problem.pdf` (93 PDF pages) — including the
  **blank student answer sheets** A9-4 (PDF page 92, templates O, P, Q, R with
  six boxes numbered 1–6 and preprinted `(OBn)12`) and A9-5 (PDF page 93,
  template S and question 9.9). Rendered with PyMuPDF for inspection.
* Zoomed crops were made of the dichloride reagent (`ClCH2–C(=CH2)–CH2Cl`, a
  2-methylallyl dichloride) and of the N template text to fix connectivity.

No official solutions, marking schemes, or answer repositories were consulted;
`official_answer_seen` in TASK.json is `false`.

## Structural reasoning used (trusted general chemistry, not competition answers)

* Swern oxidation `(COCl)2, DMSO` of the sole primary OH of N, then Wittig
  methylenation `Ph3P=CH2`, install the vinyl group on unit 1 (structure O).
* DIBAL-H directed reductive debenzylation; the alkene directs to the ortho
  unit (1,2-clockwise = unit 2) in O → P; MsCl/NaN3 convert the freed CH2OH to
  CH2N3 (structure P).
* 2 equiv. DIBAL-H in P → Q both reduce the unit-2 azide to the primary amine
  (standard DIBAL-H chemoselectivity; the only reading compatible with the
  downstream Boc2O step, which needs an N–H) and perform a directed
  debenzylation: the protic NH2 (stronger than the alkene) directs to its
  1,4-unit, freeing unit 5. NaH + ClCH2–C(=CH2)–CH2Cl doubly alkylate OH(5)
  and NH2(2), forming the –CH2–NH–CH2–C(=CH2)–CH2–O– bridge (structure Q).
* Q → R: the bridge NH (protic) directs; its 1,4-unit (unit 5) is not
  available, so the stated 1,3-counterclockwise fallback frees unit 6;
  Boc2O protects the bridge nitrogen; MsCl/NaN3 install CH2N3 at unit 6
  (structure R).
* R → S: TFA removes Boc; NaH/BnI N-benzylates the regenerated bridge N–H;
  2 equiv. DIBAL-H reduce the unit-6 azide to CH2NH2 and debenzylate once
  more; the acting director is the new amine at unit 6 (the rival
  NHBn@2 has both its 1,4 (unit 5, bridge) and 1,3-ccw (unit 6, amine) targets
  occupied), so its 1,4-unit = unit 3 is freed to CH2OH; unit 4 keeps CH2OBn
  (structure S). S is hexadifferentiated (all six boxes pairwise different).

## Lean verification

File: `IChO2026Problems/problem_icho_2026_t9_a8.lean`

Command (run from the workspace root):

```
lake env lean IChO2026Problems/problem_icho_2026_t9_a8.lean
```

Result: exit code 0, no errors, no `sorry`/`admit`.  The `#print axioms`
commands embedded at the end of the file printed:

```
'ICho2026T9A8.structure_o_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ICho2026T9A8.structure_p_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ICho2026T9A8.structure_q_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ICho2026T9A8.structure_r_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ICho2026T9A8.structure_s_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ICho2026T9A8.step_o_to_p_regiochemistry' depends on axioms: [propext, Quot.sound]
'ICho2026T9A8.step_p_to_q_regiochemistry' depends on axioms: [propext, Quot.sound]
'ICho2026T9A8.step_q_to_r_regiochemistry' depends on axioms: [propext, Quot.sound]
'ICho2026T9A8.step_r_to_s_regiochemistry' depends on axioms: [propext, Quot.sound]
'ICho2026T9A8.structure_s_hexadifferentiated' depends on axioms: [propext, Quot.sound]
'ICho2026T9A8.bridge_units_fixed' depends on axioms: [propext, Quot.sound]
'ICho2026T9A8.bridge_caps' depends on axioms: [propext, Quot.sound]
```

Only the standard Lean logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) appear; no custom axioms and no `sorryAx`.

## Semantic faithfulness self-check

* The Lean model encodes the template boxes explicitly: each `AlphaCD` carries
  the six template entries as a function `Fin 6 → PrimSubst`, with explicit
  constructors for CH=CH2, CH2OBn, CH2OH, CH2N3, CH2NH2 and the two bridge
  arms (N-arm with N-cap H/Boc/Bn, O-arm); the bridge's connectivity
  (nUnit = 2, oUnit = 5, 0-based indices 1 and 4) is part of the datum.
* The derivation theorems (`structure_o_derivation` …) equate each claimed
  structure with the result of applying the printed reagents' semantics
  (Swern/Wittig, alkene-directed debenzylation via `oneTwoCW`, protic-directed
  debenzylation via `oneFour`/fallback `oneThreeCCW`, mesylate/azide, azide
  reduction, bridge installation, Boc/Bn capping) to the problem-given
  starting material `substrateN` — the structures are derived, not assumed.
* Regiochemistry theorems prove the concrete target of every directed step,
  including the "1,4 blocked → 1,3-ccw" fallback in Q → R, and the director
  switch NHBn@2 → NH2@6 in R → S.
* `structure_s_hexadifferentiated` proves the six boxes of S are pairwise
  distinct, matching the "hexadifferentiated α-CD S" statement in the problem.
* One trusted general law beyond the printed text is required and is recorded
  here and in `answer.md`/`result.json`: DIBAL-H reduces alkyl azides to
  primary amines (needed for the "2 equiv." steps and forced by the Boc2O
  step).  All directional rules used are printed in the problem.
