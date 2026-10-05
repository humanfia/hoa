# IChO 2026 — Problem 9 (Cyclodextrin Chemistry), subquestion 9.2 (6.0 pt)

**Task (answer sheet A9-1).** Tick the favorable chair conformation and draw
the structure of K by completing the CD template. Show stereochemistry
unambiguously.

---

## Part 1 — Which chair to tick

**Tick the LEFT chair (the ⁴C₁ chair).**

The answer sheet prints two chair templates under the `[ ]₇` bracket of the
β-CD formula: the left one is the normal ⁴C₁ chair used in every figure of
the problem (ring oxygen at the upper right of the ring, glycosidic O of the
next unit leaving C4 to the right), and the right one is the ring-flipped
¹C₄ chair.

Reasoning: every glucopyranoside unit of β-CD is an α-D-glucose unit.
Placing the α-D-gluco substitution pattern (C1–OR down, C2–OH down,
C3–OH up, C4–OR down, C5–CH₂OH up) on the two chairs:

- **⁴C₁ (left template):** only the anomeric C1–OR bond is axial — and an
  axial anomeric OR is exactly what defines the α-configuration and is
  stabilised by the anomeric effect. All four other substituents are
  equatorial. Axial-substituent count = **1**.
- **¹C₄ (right template):** the axial/equatorial pattern inverts, putting
  the C2–OH, C3–OH, the C4 glycosidic bond and — worst of all — the bulky
  CH₂OH group into axial 1,3-diaxial clash positions; only the anomeric
  bond stays pseudoequatorial. Axial-substituent count = **4**.

So ⁴C₁ costs one (anomerically compensated) axial OR while ¹C₄ pays four
genuine axial clashes including the CH₂OH group. The left chair is clearly
favoured (proved in Lean as `favourable_chair_is_4C1`, with
position-by-position tables `axial_positions_4C1`/`axial_positions_1C4` and
counts `clashes_4C1 = 1 < 4 = clashes_1C4`).

## Part 2 — Structure of K (complete the template with a 2,6-anhydro bridge)

**K = heptakis-(2,6-anhydro)-β-cyclodextrin ("per-2,6-anhydro-β-CD"): every
glucopyranoside unit carries an intramolecular 2,6-epoxide bridge between O2
and C6, and the ONLY free hydroxy group of each unit is the 3-OH** (seven
free OH groups in the whole molecule, exactly as the problem states: "only
one OH group remained free per glucopyranoside unit").

### Derivation (nothing assumed; trusted chemistry applied to printed data)

1. **Stoichiometry.** The scheme (T9_page-1/2) gives β-CD --(1) TsCl
   (7 equiv.), pyridine; (2) NaOH, H₂O, 60 °C--> K. Seven equivalents of
   TsCl for a heptamer = **exactly one equivalent per glucose unit**
   (`tosyl_equiv_lemma`). TsCl esterifies alcohols; with one equivalent per
   unit the most reactive — least hindered, most nucleophilic — **primary
   6-OH** is tosylated selectively (the problem itself primes this:
   "Primary and secondary hydroxy groups show different reactivity"). Each
   unit is now 6-O-tosylated.
2. **Base treatment.** Aqueous NaOH deprotonates the secondary OH groups,
   and the alkoxide displaces the primary tosylate in an intramolecular
   Williamson ether synthesis. This consumes the 6-OTs and one secondary
   O–H proton, so per unit 3 − 1(capped) − 1(cyclised) = **1 free OH
   remains** (`oh_budget_per_unit`), matching the printed statement.
3. **Which oxygen closes the ring — regioselectivity.** An intramolecular
   SN2 on a pyranose CH₂–OTs needs the attacking C–O⁻ bond and the C6–O
   bond **antiperiplanar (trans-diaxial)**. The C5–C6 bond of the D-gluco
   ⁴C₁ unit is equatorial (`c6_up_bond_equatorial`), so the CH₂OTs arm can
   rotate about C5–C6. In the rotamer that puts the C6–O bond anti to the
   axial C2–H, the **equatorial C2–O⁻ is exactly trans-diaxial to it**
   (`trans_diaxial_O2_CH2OTs_present`); the C3–O bond can never be aligned
   antiperiplanar to C6–O in any C5–C6 rotamer (`no_trans_diaxial_C3O`;
   together: `cyclization_regioselective`). Hence **only O2 attacks**: the
   bridge is 2,6-, not 3,6-, and the surviving OH is the 3-OH. This is also
   the unique assignment consistent with the follow-up question 9.3, where
   X is obtained by HIO₄ cleavage of the remaining vicinal diol of K — that
   requires a free 3,4-trans-diol, so the free OH must sit at C3.
4. **Uniqueness.** In Lean, all candidate closures of the β-CD skeleton
   (secondary attacking oxygen X ∈ {2,3}, free OH at Y) are enumerated;
   only the trans-diaxial-competent one with a proper degree-2 bridging
   ether oxygen and the free OH at a secondary alcoholic position survives:
   `unique_bridge_structure` proves every valid competent candidate
   *equals* the 2,6-anhydro unit `kUnit`. The 3,6-anhydro alternative is a
   distinct molecule (`kUnit_ne_mUnit`) and is excluded.

### How to complete each unit of the CD template (what to draw)

On the ticked ⁴C₁ template, for every glucopyranoside unit:

- keep all printed ring bonds, the α-1,4 glycosidic bonds (C1–O–C4′,
  axial-down at C1 / equatorial at C4) and their stereobonds unchanged;
- the C6 arm (the substituted CH₂ at the upper-left ring position, former
  CH₂OH) is drawn bonded to **O2** by a new bold single bond: the O2
  substituent at C2 (drawn down from C2) and the C6 arm together close a
  five-membered **2,6-anhydro (2,6-epoxide) ring** fused to the pyranose —
  O2 is now a diether oxygen bonded to C2 and C6
  (`kUnit_has_bridge`, `kUnit_o2_nbrs`, `kUnit_deg_o2`);
- at C3 draw the single remaining **3-OH** (equatorial up, plain bond to a
  full –OH); no OH remains at C2 or C6
  (`kUnit_free_OH_at_C3`, `kUnit_no_free_OH_at_C2`,
  `kUnit_has_one_free_OH`);
- C6 keeps its two H's (`kUnit_c6_nbrs`);
- one unit therefore has the compact connectivity of 20 bonds
  (`card_kUnit`) and the whole molecule has 7 free OH groups
  (`kCD_total_free_OH`).

### Stereochemistry (unambiguous)

No stereocentre is touched: the SN2 displacement occurs at C6 (a CH₂, not a
stereocentre), and every C–O bond at the stereocentres is retained — so the
geometry of the α-D-gluco units is preserved. Expressed as CIP labels on
the **product**, the five centres of each unit of K are:

| centre | β-CD unit | K unit | note |
|--------|-----------|--------|------|
| C1 | S | **S** | unchanged ranking |
| C2 | S | **R** | geometry retained; label flips because the CIP ranking changes: O2 becomes a diether oxygen and the C3-side ring path (via O2→C6) outranks the C1-side path (`c2_label_flips`) |
| C3 | R | **R** | unchanged |
| C4 | R | **R** | unchanged |
| C5 | R | **R** | unchanged |

(`stereo_labels_k`, `stereoK_ranks_are_bonded` — every ranked neighbour is
verified to be genuinely bonded to its centre in the completed structure;
`other_labels_retained`.)

In D-series language: all units remain **D-gluco α-anomers**; the
2,6-anhydro bridge locks C2 and C6 into the epoxide ring without inverting
any centre (the apparent S→R change at C2 is a relabelling artifact of the
CIP priority swap, not a configurational inversion).

---

## Source grounding

- Problem pages `T9_page-1.png`, `T9_page-2.png` (theory_problem.pdf p. 85):
  Q9-1 gives β-CD as the cyclic α-1,4 heptamer of α-D-glucose; the Q9-2
  scheme gives TsCl (7 equiv.), Py then NaOH, H₂O, 60 °C; the prose states
  exactly one OH free per glucopyranoside unit of K.
- Blank student answer sheet A9-1 (theory_problem.pdf p. 89): two chair
  templates with tick boxes under `[ ]₇`; the remaining template area is to
  be completed with the structure of K.
- General chemistry used (trusted laws, no competition answers): selectivity
  of tosylation for primary alcohols; Williamson ether synthesis;
  trans-diaxial/antiperiplanar requirement of intramolecular SN2 on
  pyranoses; anomeric effect; chair flip keeps up/down but swaps
  axial/equatorial; CIP priority rules. No official solutions, marking
  schemes or historical answers were consulted.

## Verification artefacts

- Lean formalization: `IChO2026Problems/problem_icho_2026_t9_a2.lean`
  (theorems quoted above; master statement `K_characterization`).
- Compile + axiom audit records: `verification.md`.
- Machine-readable summary: `result.json`.
