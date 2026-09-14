# Verification record — icho_2026_t6_a4

Toolchain: `leanprover/lean4:v4.31.0` (`lean-toolchain`), project `icho_2026_run`
with pinned Mathlib v4.31.0, Physlib, crnt-lean (`lakefile.toml`).

## Commands run

All commands were run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t6_a4/campaign/workspace`.

### 1. Compile the final problem file

```
lake env lean IChO2026Problems/problem_icho_2026_t6_a4.lean
```

Result: **exit code 0**, no errors, no warnings.
The only output is the `#print axioms` report (recorded below).

### 2. Axiom audit (`#print axioms`, emitted by the same compile)

Exact output:

```
'IChO2026T6A4.massE_value' does not depend on any axioms
'IChO2026T6A4.massC48_value' does not depend on any axioms
'IChO2026T6A4.ion591_example_matches' depends on axioms: [propext]
'IChO2026T6A4.ion783_total_mass' depends on axioms: [propext]
'IChO2026T6A4.ion783_mz' depends on axioms: [propext]
'IChO2026T6A4.ion783_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T6A4.ion879_total_mass' depends on axioms: [propext]
'IChO2026T6A4.ion879_mz' depends on axioms: [propext]
'IChO2026T6A4.ion879_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T6A4.ion1174_total_mass' depends on axioms: [propext]
'IChO2026T6A4.ion1174_mz' depends on axioms: [propext]
'IChO2026T6A4.ion1174_unique_at_charge_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T6A4.catenane_octaprotonated_mz' depends on axioms: [propext]
```

(The leading `+` markers shown here are markdown, not part of the output.)

- The two foundational mass theorems (`massE_value : massE = 590`,
  `massC48_value : massC48 = 576`) depend on **no axioms at all** — they are
  closed by pure kernel computation (`decide`; additionally re-proved by
  `rfl` in `massE_value_compute` / `massC48_value_compute`).
- Every other final theorem depends only on the standard Lean/Mathlib
  logical axiom `propext` (the exhaustive-enumeration uniqueness theorems
  additionally on `Classical.choice` and `Quot.sound`).
- **No `sorryAx`** (no `sorry`/`admit`), no `native_decide` trust axioms,
  no custom axioms, no `unsafe` declarations appear anywhere in the file.
  (An earlier draft used `native_decide` for the two mass evaluations; this
  was explicitly caught by the axiom audit — it injects a `native_decide`
  trust axiom — and replaced by kernel-checked proofs before finalization.)

### 3. No-sorry sweep

```
grep -nE "sorry|admit|axiom |unsafe|native_decide" IChO2026Problems/problem_icho_2026_t6_a4.lean
```

Result: **no matches** — no `sorry`, no `admit`, no `axiom`, no `unsafe`,
no `native_decide` anywhere in the final file.

## What was verified semantically (not just "it builds")

- `massE_value` / `massC48_value`: the formal integer masses are exactly
  those printed in the problem — macrocycle **E** is `C₄₀H₃₄N₂O₃`
  (= 590) and cyclo[48]carbon is `C₄₈` (= 576) — with the integer atomic
  masses H = 1, C = 12, N = 14, O = 16 mandated by 6.4.
- `ion591_example_matches` reproduces the planted answer-sheet example
  `[E + H]⁺` at *m/z* 591, fixing the proton-attachment convention that the
  three derived ions then follow (`ProtonCharged`: `nH = z`).
- `ion783_mz`, `ion879_mz`, `ion1174_mz` prove that each requested ion's
  total integer mass equals `m/z × z` for the observed peak, i.e. the
  identities
  3·590 + 576 + 3 = 3·783, 2·590 + 576 + 2 = 2·879,
  3·590 + 576 + 2 = 2·1174.
- `ion783_unique` and `ion879_unique` prove these are the **only**
  well-formed no-fragmentation candidates (z ≤ 3, protons ≤ z, ≤ 1 intact
  C₄₈ ring — exhaustive enumeration, no unjustified search bound: the per‑field
  bounds are *proved from the mass equation by omega*, not assumed) matching
  783 and 879.
- `ion1174_unique_at_charge_two` proves uniqueness of the planted
  `[3E + C₄₈ + 2H]²⁺` at charge state 2.
- `catenane_octaprotonated_mz` honestly records the residual integer-level
  ambiguity for 1174 (the formal possibility `[C₄₈ + E + 8H]⁺`), which is
  reported as a source gap in `answer.md` and `result.json`; chemistry
  (two basic N atoms in E; the multiply protonated aggregate pattern forced
  by 783/879) selects the doubly charged planted answer.

## Cross-check of the arithmetic (independent of Lean)

Plain-integer check (Python) of the assignments:

```
E=590; C48=576
3*E + C48 + 3 = 2349 = 3*783
2*E + C48 + 2 = 1758 = 2*879
3*E + C48 + 2 = 2348 = 2*1174
E + 1 = 591
```

and an exhaustive bounded scan (z ∈ {1,2,3}, counts of E/C₄₈ small,
proton-only charging) returning exactly the candidates
`591:[E+H]⁺`, `783:[3E+C₄₈+3H]³⁺`, `879:[2E+C₄₈+2H]²⁺`,
`1174:[3E+C₄₈+2H]²⁺` (with the noted z = 1, 8-proton formal shadow for
1174).
