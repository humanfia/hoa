# Verification record — icho_2026_t7_a4

Exact commands run from the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t7_a4/campaign/workspace`)
with the pinned toolchain (`lean-toolchain`: leanprover/lean4:v4.31.0).

## 1. Compile the deliverable

```
lake env lean IChO2026Problems/problem_icho_2026_t7_a4.lean
```

Result: exit code 0, no errors, no warnings.  The `#print axioms` command at the end of
the file printed:

```
'IChO2026.mdeaCO2Reaction_answer' depends on axioms: [propext]
```

## 2. Axiom audit of every exported theorem

```
cp IChO2026Problems/problem_icho_2026_t7_a4.lean /tmp/t7a4_axcheck.lean
cat >> /tmp/t7a4_axcheck.lean <<'EOF'
#print axioms IChO2026.mdeaCO2Reaction_stoichiometry
#print axioms IChO2026.mdeaCO2Reaction_nontrivial
#print axioms IChO2026.mdeaCO2Reaction_element_balance_C
#print axioms IChO2026.mdeaCO2Reaction_element_balance_H
#print axioms IChO2026.mdeaCO2Reaction_element_balance_N
#print axioms IChO2026.mdeaCO2Reaction_element_balance_O
#print axioms IChO2026.mdeaCO2Reaction_charge_balance
EOF
lake env lean /tmp/t7a4_axcheck.lean
```

Result: exit code 0.  Full output:

```
'IChO2026.mdeaCO2Reaction_answer' depends on axioms: [propext]
'IChO2026.mdeaCO2Reaction_stoichiometry' does not depend on any axioms
'IChO2026.mdeaCO2Reaction_nontrivial' depends on axioms: [propext]
'IChO2026.mdeaCO2Reaction_element_balance_C' does not depend on any axioms
'IChO2026.mdeaCO2Reaction_element_balance_H' does not depend on any axioms
'IChO2026.mdeaCO2Reaction_element_balance_N' does not depend on any axioms
'IChO2026.mdeaCO2Reaction_element_balance_O' does not depend on any axioms
'IChO2026.mdeaCO2Reaction_charge_balance' does not depend on any axioms
```

`propext` is one of Lean's three standard logical axioms (propositional extensionality)
and is explicitly permitted; it enters only through the `simp`-free but `decide`-free
string-reasoning step and through the `congrFun` usage.  No custom axioms, no `sorry`,
no `admit`, no `unsafe` (confirmed by `grep -n "sorry\|admit\|unsafe"
IChO2026Problems/problem_icho_2026_t7_a4.lean`, no matches).

## 3. Semantic audit (theorem ↔ chemistry)

The theorems state and prove, for the equation
C₅H₁₃NO₂ + CO₂ + H₂O → [C₅H₁₄NO₂]⁺ + [HCO₃]⁻:

| theorem                                       | chemical content proved                                        |
|-----------------------------------------------|----------------------------------------------------------------|
| `mdeaCO2Reaction_stoichiometry`               | coefficients are 1·C₅H₁₃NO₂ + 1·CO₂ + 1·H₂O → 1·MDEAH⁺ + 1·HCO₃⁻ |
| `mdeaCO2Reaction_nontrivial`                  | products genuinely differ from reactants (a real reaction)     |
| `mdeaCO2Reaction_element_balance_C`           | 5+1+0 = 5+1 (carbon conserved)                                 |
| `mdeaCO2Reaction_element_balance_H`           | 13+0+2 = 14+1 (hydrogen conserved)                             |
| `mdeaCO2Reaction_element_balance_N`           | 1+0+0 = 1+0 (nitrogen conserved)                               |
| `mdeaCO2Reaction_element_balance_O`           | 2+2+1 = 2+3 (oxygen conserved)                                 |
| `mdeaCO2Reaction_charge_balance`              | 0 = (+1) + (−1) (charge conserved)                             |
| `mdeaCO2Reaction_answer`                      | conjunction of all of the above                                |

This exactly matches the natural-language answer in `answer.md`.

## 4. Source material consulted (problem-only)

* `icho_2026_source/image/T7_page-1.png` (Q7-1: Fig. 1 with box "Z − CO₂ scrubber")
* `icho_2026_source/image/T7_page-2.png` (Q7-2: "An aqueous solution of 3 is being used
  to remove CO₂ from the mixture", printed structure of 3 = MeN(CH₂CH₂OH)₂, box 7.4)
* `icho_2026_source/questions_only.jsonl` (entry `icho_2026_t7_a4`: requested output
  `reaction_equation`, kind `formula`, exact symbolic)

No official solutions, marking schemes, grading reports, archived answers, or external
solver outputs were used.
