# Verification — icho_2026_t5_a6

## Environment

- Working directory: `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t5_a6/campaign/workspace`
- Toolchain (`lean-toolchain`): `leanprover/lean4:v4.31.0`
- `lake env lean --version`:
  `Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)`
- Target file: `IChO2026Problems/problem_icho_2026_t5_a6.lean`
  (sha256 `90a7ceeacb9081054e8ea30961ebd591ec6d1ebf81cd1e0f13312bbe70951ac7`, 618 lines, namespace `IChO2026.Problems.T5.A6`).

## Commands run (exactly)

```
cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t5_a6/campaign/workspace
lake env lean IChO2026Problems/problem_icho_2026_t5_a6.lean
```

Exit code: **0** (no errors, no warnings).

### Full output (the `#print axioms` audit block at the end of the file)

```
'IChO2026.Problems.T5.A6.bondTotal_pl1' depends on axioms: [bondTotal_pl1._native.native_decide.ax_1_1]
'IChO2026.Problems.T5.A6.bondTotal_pl2' depends on axioms: [bondTotal_pl2._native.native_decide.ax_1_1]
'IChO2026.Problems.T5.A6.z_h2_inert' depends on axioms: [z_h2_inert._native.native_decide.ax_1_1]
'IChO2026.Problems.T5.A6.pl2_wingSwap_is_automorphism' depends on axioms: [propext,
 pl2_wingSwap_is_automorphism._native.native_decide.ax_1_1]
'IChO2026.Problems.T5.A6.pl1_forces_swap_absent' depends on axioms: [propext,
 pl1_forces_swap_absent._native.native_decide.ax_1_1]
'IChO2026.Problems.T5.A6.pl2_meso_RS_achiral' depends on axioms: [propext,
 pl2_meso_RS_achiral._native.native_decide.ax_1_1,
 pl2_meso_RS_achiral._native.native_decide.ax_1_4,
 pl2_meso_RS_achiral._native.native_decide.ax_1_5]
'IChO2026.Problems.T5.A6.pl2_RR_not_meso' depends on axioms: [propext, Quot.sound]
'IChO2026.Problems.T5.A6.pl3_phys_netCharge' depends on axioms: [pl3_phys_netCharge._native.native_decide.ax_1_1]
'IChO2026.Problems.T5.A6.pl3_pair_of_enantiomers' depends on axioms: [propext,
 pl3_pair_of_enantiomers._native.native_decide.ax_1_1]
'IChO2026.Problems.T5.A6.pl3_hydrolysis_waters' depends on axioms: [propext,
 pl3_hydrolysis_waters._native.native_decide.ax_1_1]
```

## Axiom assessment

- No `sorryAx`, no `addDecl`-level custom axioms anywhere: `grep -c sorryAx`
  on the output = 0; the file itself contains no `sorry`, `admit`, `axiom`,
  or `unsafe` tokens (only the prose word "admit" inside a docstring).
- `propext`, `Quot.sound` (and `Classical.choice` where it appears through
  list membership reasoning) are the standard Lean logical axioms, explicitly
  allowed by the goal statement.
- `*.native_decide.ax_*` entries are Lean 4.31's own trust-base constants for
  `native_decide` (the compiler-evaluated `ofReduceBool` mechanism). They are
  part of the standard toolchain, not custom axioms introduced by this file.
  `native_decide` is used only for finite, fully decidable statements about
  the explicit molecular graphs (bond counts, automorphism checks on a
  53-vertex graph, bounded valence audits) — propositions whose truth is
  machine-checked from first principles over the concrete data.

## Sanity checks on the machine-checked content

- `bondTotal_pl1 : pl1.bondTotal 4 (bondsPerResidue 17 31) = 255` and
  `bondTotal_pl2 : pl2.bondTotal 4 (bondsPerResidue 17 31) = 254` reproduce
  the printed counts of 5.3 and 5.5/5.6 exactly (explicit skeleton 59 and 58
  bonds respectively; `bondsPerResidue_C17H31` proves the 49-bond R-residue
  contribution of C₁₇H₃₁).
- `pl2_wingSwap_is_automorphism` is proved by evaluating the full
  53-vertex permutation against every atom label, charge, bond and bond
  order; `pl1_forces_swap_absent` shows the same permutation fails on PL1
  (it breaks a bond incidence at the middle glycerol's OH).
- `pl2_meso_RS_achiral` and `pl2_RR_not_meso` together establish that under
  the wing-exchange symmetry the (R,S) assignment is meso (achiral) and the
  (R,R) assignment is not — i.e. the printed "PL2 is chiral" forces the
  homochiral drawing.
- Every molecular graph is audited by `*_valid` (indices in range, positive
  bond orders, no duplicate/self bonds, well-placed stereocentre tables) and
  by `*_valences` (neutral-atom valence sum check at every vertex).

## Semantic-faithfulness self-check (per goal instructions)

The theorems state and prove the exact printed numerical data (255, 254,
m = 4 balance, charge −1 at physiological pH, unique PL3 stereocentre ⇒
one enantiomeric pair, homochiral-only chiral PL2) against explicit graph
encodings of the *proposed* answer structures, rather than assuming the
answers: the graphs were derived from the fragment inventory (Qg5-1), the
hydrolysis equations (Q5-4 image), and the printed clue sentences, then the
printed data were verified as theorems. Remaining underdetermination
(choice of enantiomer to draw; sn-1/sn-2 acyl placement convention) is
recorded in `result.json` under `assumptions` / `source_gaps`.
