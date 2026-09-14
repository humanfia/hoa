# Verification record — target `icho_2026_t5_a2`

## Environment

* Workspace: `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t5_a2/campaign/workspace`
* Toolchain: Lean 4.31.0 (`lean-toolchain`), via `lake env`
* Dependencies (prebuilt under `.lake/packages`): Mathlib v4.31.0, Physlib,
  crnt-lean (only `Mathlib` is imported by the deliverable file).
* Inputs read: `TASK.json`, `GOAL.txt`, `icho_2026_source/image/T5_page-1.png`
  ... `T5_page-4.png`, and `icho_2026_source/raw/theory_problem.pdf`
  (pages Q5-1–Q5-4 = PDF pages 44–47, and the blank answer sheet A5-2 = PDF
  page 49 were rendered and inspected).

## Commands run and results

### 1. Final compilation

```bash
cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t5_a2/campaign/workspace
lake env lean IChO2026Problems/problem_icho_2026_t5_a2.lean
```

Result: **exit code 0, no errors, no warnings**, only the `#print axioms`
informational outputs listed below.

### 2. Axiom audit (`#print axioms` output, verbatim)

```
'IChO2026T5A2.structure_pl1_certificate' depends on axioms: [propext]
'IChO2026T5A2.structure_y_certificate' depends on axioms: [propext]
'IChO2026T5A2.number_of_a_fragments' depends on axioms: [propext, Quot.sound]
'IChO2026T5A2.n_parity_of_stub_evenness' depends on axioms: [propext, Quot.sound]
'IChO2026T5A2.pl1_connected' depends on axioms: [propext]
'IChO2026T5A2.pl1_valences_ok' depends on axioms: [propext]
'IChO2026T5A2.permute_is_automorphism' depends on axioms: [propext]
'IChO2026T5A2.rr_is_chiral' depends on axioms: [propext]
'IChO2026T5A2.rs_is_meso' depends on axioms: [propext]
'IChO2026T5A2.y_stabilisation_network' depends on axioms: [propext]
'IChO2026T5A2.second_deprotonation_destroys_network' depends on axioms: [propext]
'IChO2026T5A2.hydrolysis_water_count' depends on axioms: [propext]
```

Only the standard Lean logical axioms `propext` and `Quot.sound` appear.
**No `sorryAx`, no custom/unchecked axioms.** (`Classical.choice` does not
even appear.)

### 3. Umbrella

`IChO2026Problems/All.lean` contains `import IChO2026Problems.problem_icho_2026_t5_a2`,
keeping the deliverable inside the fixed umbrella namespace of the run.

## Semantic-faithfulness checklist (manual, against the problem text)

* **structure_pl1 (requested output 1):** the theorem bundle states a concrete
  42-atom/41-bond (R,R) structure assembled from exactly fragments
  a×6/b×2/c×3/d×4 (n = 6 derived, not assumed), acyclic, no peroxides,
  valence-complete, diprotic with identical P–OH groups, with the exactly two
  stereocentres CIP-labelled and mirror/chirality relationships proved
  ((R,S) meso). — matches the request "structure of one enantiomer of PL1".
* **structure_y (requested output 2):** Y is the monoanion (charge −1, one
  fewer atom and bond), drawn with two explicit intramolecular H–bonds
  (free central 2-OH → O(–), remaining P–OH → O(–)), and the theorem
  `second_deprotonation_destroys_network` exhibits that the second
  deprotonation removes the bridge donor — matching "the stabilisation that
  explains the difference between pK_a1 and pK_a2".
* Abbreviation R used for the fatty-acid residues, as instructed.

## Source gaps

None blocking. The (R,R)-vs-(S,S) correspondence to "prokaryotes and
eukaryotes vs archaea" is a standard biochemical fact; the problem requests
*one* enantiomer, so the choice does not affect validity (recorded in
`assumptions` of `result.json`).
