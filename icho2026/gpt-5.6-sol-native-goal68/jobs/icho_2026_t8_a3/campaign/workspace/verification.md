# Verification for `icho_2026_t8_a3`

Verification was run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t8_a3/campaign/workspace`

## 1. Lean compilation and axiom inspection

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a3.lean
```

Exit code: `0`

Exact output:

```text
'IChO2026Problems.T8A3.CoordinationModel.ligand8_leaves_two_trans_sites' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T8A3.derived_profile_of_complex1' does not depend on any axioms
'IChO2026Problems.T8A3.geometry_1' depends on axioms: [propext]
'IChO2026Problems.T8A3.geometry_1_unique' depends on axioms: [propext]
```

The output is produced by four `#print axioms` commands in the final Lean
file. All reported dependencies are standard Lean logical/library axioms;
there is no custom axiom and no `sorryAx`.

## 2. Forbidden proof shortcuts

Command:

```text
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t8_a3.lean
```

Exit code: `1`; output was empty. For `grep`, this means there were no
matching whole words in the file.

## 3. Result manifest syntax

Command:

```text
python3 -m json.tool result.json
```

Exit code: `0`. The command emitted the formatted JSON object without an
error, so `result.json` is valid JSON.

## 4. Source identity

Command:

```text
sha256sum TASK.json icho_2026_source/image/T8_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Exit code: `0`

Exact output:

```text
008bb0a6b64625086f2f04a97a00b04bcf35972b2b2320c3d94ee86b4575d9dc  TASK.json
3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843  icho_2026_source/image/T8_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

The image and PDF hashes agree with the source records in `TASK.json`.

## Semantic coverage audit

- Requested output `geometry_1`: represented by `geometry_1`, which proves a
  choice fits the independently derived profile iff it is `bottomRight`.
- Exact classification/uniqueness: represented by `geometry_1_unique`.
- Chemistry behind the classification: `derived_profile_of_complex1` proves
  the N₄Cl₂, coordination-number-6, octahedral, trans profile; the finite-site
  lemma `ligand8_leaves_two_trans_sites` proves the residual axial sites are
  opposite.
- Source/derived separation: printed counts and answer-sheet profiles are in
  `ProblemInput`; the general octahedral site reasoning is in
  `CoordinationModel`; derived output theorems are outside both namespaces.
- Source gap: none. The problem supplies four N atoms, synthesis from `FeCl₂`,
  and the later loss of two chloride ions; the only bridge is the standard
  κ⁴ quaterpyridine/octahedral coordination interpretation stated in both
  `answer.md` and the Lean module.
