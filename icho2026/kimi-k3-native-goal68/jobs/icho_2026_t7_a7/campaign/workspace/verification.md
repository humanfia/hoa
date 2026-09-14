# Verification record — `icho_2026_t7_a7`

## Deliverables

- `answer.md` — natural-language answer and source grounding.
- `IChO2026Problems/problem_icho_2026_t7_a7.lean` — Lean 4 (Mathlib v4.31.0 profile) formalization.
- `result.json` — target metadata; `verification.md` — this record.

## Commands run

From `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t7_a7/campaign/workspace`:

```
lake env lean IChO2026Problems/problem_icho_2026_t7_a7.lean
```

Result (final run):

```
'IChO2026T7A7.icho_2026_t7_a7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit code 0, no errors and no warnings.  `#print axioms icho_2026_t7_a7` (also `#print axioms` for every lemma
through the master theorem transitively) shows only the three standard Lean logical axioms — no `sorryAx`,
no custom or unchecked axioms.

## What is proved

| Theorem | Content |
|---|---|
| `wN_consistency` | Printed w(N) 9.16 %, 18.90 %, 39.94 % lie within ±0.005 % of the theoretical mass fractions of LaN, Ca₃N₂, Si₃N₄ (exact rational arithmetic on printed atomic masses). |
| `massRatio_consistency` | The stoichiometry 10 LaN : 6 Ca₃N₂ : 7 Si₃N₄ : 5 SiO₂ reproduces the printed ratio 5.09 : 2.96 : 3.27 : 1.00 within ±0.005 (3 sf half quantum), each conjunct proved by `norm_num` over `Rat`. |
| `atom_balance` | For every element in {La, Ca, Si, N, O}, `reactantInventory e = 2 * unit10 e` — i.e., `10 LaN + 6 Ca₃N₂ + 7 Si₃N₄ + 5 SiO₂ → 2 La₅Ca₉O₂[SiNO₃][Si₁₂N₂₄]` balances exactly. |
| `charge_balance` | 5(+3) + 9(+2) + 2(−2) + (4−3−6) + (48−72) = 0 — compound 10 is neutral with S = O²⁻, T = [SiNO₃]⁵⁻, framework [Si₁₂N₂₄]²⁰⁻. |
| `anionS_inventory`, `anionT_inventory` | Definitionally S = single O atom, T = Si₁N₁O₃. |
| `icho_2026_t7_a7` | Master theorem bundling all the above as a single conjunction. |

## Independent semantic audit

- The theorem *states* the requested chemistry: nitride identities via the printed mass fractions; the
  six requested formulae (7, 8, 9, 10, S, T) appear as exact element inventories; atom and charge
  conservation hold for the stated stoichiometry; measured-value tolerances are derived from the source
  measurement intervals (half quantum of each printed decimal), not fitted.
- Cross-check outside Lean: an independent full-periodic-table scan of binary nitrides E_cN_n (c, n ≤ 4)
  confirms Si₃N₄ is the unique match of w(N)₉ = 39.94 %, Ca₃N₂ of 18.90 %, LaN of 9.16 %, and a
  Diophantine sweep over (x, y, z, u) with S monoatomic and T tetrahedral gives the batch
  10 : 6 : 7 : 5 and the anions S = O²⁻, T = [SiNO₃]⁵⁻ as the unique solution compatible with charge
  neutrality, atom conservation, and the printed ratio windows.
- No official answers, marking schemes, solution repositories, or external solver agents were used;
  the only external inputs are the standard printed atomic masses and general laws of stoichiometry
  and charge neutrality.
