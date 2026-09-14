# IChO 2026, Problem T7, Part 7.7 (target `icho_2026_t7_a7`)

## Requested outputs

"Identify the empirical formulae of **7**–**10**. Specify the composition of anions **S** and **T**."

## Answers

| Output | Answer |
|---|---|
| **7** | **LaN** (lanthanum nitride) |
| **8** | **Ca₃N₂** (calcium nitride) |
| **9** | **Si₃N₄** (silicon nitride) |
| **10** | **La₅Ca₉O₂[SiNO₃][Si₁₂N₂₄]** — minimal formula Q_αR_βS₂T[Si₁₂N₂₄] with Q = La (α = 5), R = Ca (β = 9), S₂ = O₂ (two oxide anions), T = [SiNO₃]⁵⁻, on an intact [Si₁₂N₂₄]²⁰⁻ oxo(nitrido)silicate framework |
| **S** | **O²⁻** — oxide; monoatomic |
| **T** | **[SiNO₃]⁵⁻** — tetrahedrally coordinated silicon (SiN₁O₃ tetrahedron); charge −5 |

Balanced, quantitative formation (single product), per two minimal formula units of 10:

    10 LaN + 6 Ca₃N₂ + 7 Si₃N₄ + 5 SiO₂ → 2 La₅Ca₉O₂[SiNO₃][Si₁₂N₂₄]

## Source grounding (problem-only inputs used)

From the problem text (T7 page 4 of `theory_problem.pdf`, image `T7_page-4.png`), nothing else:

1. **7, 8, 9** are binary nitrides (contain N³⁻) obtained **from pure elements**.
2. w(N)₇ = 9.16 %, w(N)₈ = 18.90 %, w(N)₉ = 39.94 %.
3. Compound **10** has minimal structural formula **Q_αR_βS₂T[Si₁₂N₂₄]**; Q, R are metal cations in their **highest** oxidation state; **S** monoatomic; **T** tetrahedral.
4. Quantitative mass ratio 7 : 8 : 9 : SiO₂ = 5.09 : 2.96 : 3.27 : 1.00.

Periodic-table atomic masses exactly as printed (IChO 2026 table; stored as exact rationals in
the Lean file): N 14.007, La 138.9055, Ca 40.078, Si 28.085, O 15.999.

General chemical laws used (allowed as `trusted_general_law`): stoichiometric mass conservation
(single quantitative product), charge neutrality of a stable compound, the chemistry of binary
nitrides (lanthanide mononitrides; alkaline-earth M₃N₂ where Ca, but not Be/Mg/Zn/Cd, belongs
to the soluble-reactive class), and the tetrahedral coordination of silicon in
oxo(nitrido)silicate anions.

## Reasoning (no external competition data)

**Step 1 — nitride 9.**  w(N) = 39.94 % has a unique match over all binary nitrides
E_cN_n (c, n ≤ 4, full periodic table): Si₃N₄, theoretical
4·14.007/(3·28.085 + 4·14.007) = 0.3993927 → 39.94 %.  So **9 = Si₃N₄**, and its interior
mass fraction of nitride nitrogen to silicon, w/(1−w), is essentially 2 : 3 by atoms.

**Step 2 — nitride 8.**  w(N) = 18.90 % matches Ca₃N₂ (theoretical 18.8967 %, within the
±0.005 % half-quantum) and no other realistic binary nitride.  **8 = Ca₃N₂.**

**Step 3 — nitride 7.**  w(N) = 9.16 % matches LaN (mononitride: 14.007/(138.9055+14.007)
= 9.16014 %, well inside ±0.005 %).  The alternative Nb₃N₂ (9.133 %) is excluded because the
mass-ratio data (next step) can then not be reproduced with integer stoichiometry; LaN is the
only identification consistent with every number in the problem.  **7 = LaN.**
(Across the whole answer-blind analysis only printed inputs were used; no candidate was
selected to fit a guessed product.)

**Step 4 — molar inventory of the reaction.**  Interpreting each printed decimal by its
half-quantum interval (±0.005), the mass ratio converts directly to molar amounts (per 1.00
mass unit of SiO₂):

- LaN: 5.09/152.9125 = 3.3287·10⁻² mol  → ×60.083 ≈ 2.000·M(LaN)/M(SiO₂)
- Ca₃N₂: 2.96/148.248  = 1.9966·10⁻² mol
- Si₃N₄: 3.27/140.283 = 2.3310·10⁻² mol

So per `u` SiO₂ units, x(LaN) : y(Ca₃N₂) : z(Si₃N₄) : u = 2 : 1.1996 : 1.4005 : 1, and the
unique small-integer scaling that keeps every atom count integral is `u = 5`, giving the
batch **10 LaN : 6 Ca₃N₂ : 7 Si₃N₄ : 5 SiO₂**; the Lean proof
`massRatio_consistency` shows all three implied ratios reproduce the printed 5.09, 2.96,
3.27 strictly inside the ±0.005 windows.

**Step 5 — atom inventory of 10.**  The batch supplies La₁₀ Ca₁₈ Si₂₆ N₅₀ O₁₀.  With an
intact **[Si₁₂N₂₄]** per minimal formula unit, exactly two minimal units are formed (Si and N
budgets force 2 units), so per minimal unit:

La₅ Ca₉ + [Si₁₂N₂₄] + (2 S + 1 T = Si₁ N₁ O₅).

**Step 6 — the anions.**  Q = La³⁺ and R = Ca²⁺ (highest oxidation states, as stated).  The
framework [Si₁₂N₂₄] carries charge 12·(+4) + 24·(−3) = **−20**.  Charge neutrality:
5·(+3) + 9·(+2) + 2·q(S) + q(T) − 20 = 0, i.e. 2q(S) + q(T) = −9.

- S is **monoatomic**; the only monoatomic anions formable from the reacting element set
  {La, Ca, Si, N, O} are N³⁻ and O²⁻.  S = N³⁻ would inject 2 N into just the anion budget,
  exceeding the single spare nitrogen, so **S = O²⁻** (monoatomic oxide), q(S) = −2.
- Then q(T) = −5 and T receives the remaining Si₁ N₁ O₃: **T = [SiNO₃]⁵⁻**, a silicon
  centre tetrahedrally coordinated by 1 N + 3 O — satisfying the tetrahedral condition.

The Lean proofs `atom_balance`, `charge_balance`, `anionS_inventory`, `anionT_inventory`
verify all of these element and charge counts definitionally.

## Faithfulness notes

- No official answers, marking schemes, external solver, or competition repository were
  consulted; only the problem pages (T7 pages 2–4 images / theory_problem.pdf), the printed
  periodic-table masses, and general chemical laws were used.
- Printed decimals are reproduced as exact rational numerals (centi-percent / centi-gram);
  no intermediate rounding was used.  Every numerical identification claim is proved within
  the half-quantum interval of the corresponding printed value.
- The one condition not decidable from the problem text alone is the *intactness* of the
  [Si₁₂N₂₄] structural unit during formation.  This is stated by the problem itself
  ("minimal possible formula, describing the structure"), and is used exactly as a problem
  input, not as an extra modelling assumption.  No other unsupported premise was needed:
  atoms, charge, and the printed mass numbers uniquely force the answers above.
