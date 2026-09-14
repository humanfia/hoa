# Verification — icho_2026_t4_a6

## Build command

```
lake build IChO2026Run
```

## Actual result

Build completed successfully (8581 jobs).

## Axiom inspection

Command:

```
lake env lean /tmp/check_axioms.lean
```

Output:

```
'IChO2026.Problem.reactionEnthalpy298_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.Problem.reactionEnthalpy298_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.Problem.submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three theorems depend only on the standard Lean logical axioms
(`propext`, `Classical.choice`, `Quot.sound`).  No custom or unchecked
axioms are used.

## Semantic check

- `reactionEnthalpy298` encodes Hess's law: Δ_rH = Σ Δ_fH(products) − Σ Δ_fH(reactants).
- Stoichiometry CH₄ + 2 O₂ → CO₂ + 2 H₂O is encoded literally: one CO₂, two H₂O, one CH₄, two O₂.
- Values match the problem table exactly: −74.8, −241.8, −393.5 kJ mol⁻¹; O₂ taken as 0 (element standard state).
- Result −802.3 kJ mol⁻¹ is reported at 0.1 kJ mol⁻¹ quantum, i.e. three significant figures as required by the blind-evaluation protocol.
