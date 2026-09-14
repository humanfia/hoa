# Verification — IChO 2026 T7-A1 (`icho_2026_t7_a1`)

## Deliverables checked

* `answer.md` — natural-language answer + source-grounding explanation.
* `IChO2026Problems/problem_icho_2026_t7_a1.lean` — Lean 4 formalization.
* `result.json` — status metadata.

## Commands run

All commands were executed in the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t7_a1/campaign/workspace`
with the pinned toolchain `leanprover/lean4:v4.31.0` (see `lean-toolchain`).

### 1. Compile the formalization

```
$ lake env lean IChO2026Problems/problem_icho_2026_t7_a1.lean
```

Result: **exit code 0**, no errors, no warnings. (First `import Mathlib`
takes ~2 minutes on this machine.)

### 2. Axiom audit (`#print axioms`)

The same compile produced the following output:

```
'IChO2026T7A1.composition_M1' depends on axioms: [propext, Quot.sound]
'IChO2026T7A1.M1_complete' depends on axioms: [propext, Quot.sound]
'IChO2026T7A1.M1_mem_CO' depends on axioms: [propext, Quot.sound]
'IChO2026T7A1.composition_M2' depends on axioms: [propext, Quot.sound]
'IChO2026T7A1.M2_complete' depends on axioms: [propext, Quot.sound]
'IChO2026T7A1.M2_mem_NH3' depends on axioms: [propext, Quot.sound]
'IChO2026T7A1.xy_relation_from_balances' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T7A1.xy_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All axioms are the standard Lean logical axioms (`propext`,
`Classical.choice`, `Quot.sound`). There is **no** `sorryAx`, no custom
unchecked axiom, no `unsafe` proof.

### 3. Theorem inventory

| Theorem | Content |
|---------|---------|
| `composition_M1` | `M1 = {N2, CO, H2}` |
| `M1_mem_N2`, `M1_mem_CO`, `M1_mem_H2` | membership of each gas |
| `M1_complete` | `g ∈ M1 ↔ g = N2 ∨ g = CO ∨ g = H2` (no other species) |
| `composition_M2` | `M2 = {N2, H2, NH3}` |
| `M2_mem_N2`, `M2_mem_H2`, `M2_mem_NH3` | membership of each gas |
| `M2_complete` | `g ∈ M2 ↔ g = N2 ∨ g = H2 ∨ g = NH3` |
| `xy_relation_from_balances` | from `b = c/2`, `4a + 3b = 3c`, `x = a + b`, `y = a` derives `x > y ∧ x = 7c/8 ∧ y = 3c/8` |
| `xy_relation` | existence of the above balance data forces `x > y` |

### 4. Source-faithfulness checks (done while solving)

* Cropped renders of `theory_problem.pdf` page 63 confirmed the printed
  reactions: `(I) CH₄+H₂O→CO+3H₂`, `(II) 2CH₄+O₂→2CO+4H₂`,
  `(III) CO+H₂O→CO₂+H₂` (i.e. *one* H₂O on the left, *not* `2H₂O`), the
  `4N₂ + 1O₂` air feed, the `CH₄, CO, H₂` stream between reactors I and II,
  and the `N₂, H₂` recycle around the ammonia loop.
* No separate T7 answer-sheet page exists in the provided PDF (grep for
  "Tick" found Q8/Q9 answer boxes but none for Q7; the PDF ends at Q9).

### 5. What is *not* claimed

* The strict identity `2x = 3y` is **not** claimed; the problem inputs for
  T7-A1 ground only the order relation `x > y` (see `answer.md` → "Source
  gaps").
-/
