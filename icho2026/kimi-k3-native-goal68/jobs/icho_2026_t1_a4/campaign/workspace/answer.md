# IChO 2026, Theory T1 — subquestion 1.4 (answer)

## Answer (as requested on the answer sheet)

* **Q : aluminium (Al)**, relative atomic mass 26.98 (atomic number 13).
* **C ⋅ xH₂O : AlF₃·3H₂O** (aluminium fluoride trihydrate; x = 3), so C = AlF₃.
* **D : Na₃AlF₆** (cryolite) — the ore/solvent of the Hall–Héroult process used in the
  industrial production of aluminium, matching the problem's closing hint
  "…and is used in the industrial production of Q".

All three printed percentages are reproduced exactly:

| datum | computation | value | printed (±0.005 %) |
|---|---|---|---|
| w(H₂O) in C·xH₂O | 3·18.016 / (26.98 + 3·19 + 3·18.016) = 54.048/138.028 | 39.1577…% | 39.16 % ✓ |
| w(Na) in D | 3·22.99 / 209.94 = 68.97/209.94 | 32.8523…% | 32.85 % ✓ |
| w(Q) in D | 26.98 / 209.94 | 12.8513…% | 12.85 % ✓ |

(Atomic masses are read from the periodic table printed on page G1-5 of the same paper:
F = 19, Na = 22.99, Al = 26.98; M(H₂O) = 2·1.008 + 16 = 18.016.)

## Derivation (source-grounded, exact rational arithmetic)

The three printed percentages are measured values displayed to two decimals; per the
measurement policy each is the centre of a half-quantum window of width 0.01 %
(39.155–39.165 %, etc.). All inequalities below are over ℚ, so nothing is lost to rounding.

1. **Model.** Reading the data in the standard chemical way (assumptions M-A4-1..4, declared
   in the Lean file): the precipitate is a metal fluoride hydrate C·xH₂O = QFᵥ·xH₂O with
   v ∈ {2,3}, x ≥ 1, and D = NaₙQF_{v+n}, n ≥ 1 (NaF adduct). The metal datum in D then
   constrains Ar(Q) strongly, with 0 < Ar(Q) ≤ 294 (oganesson, the heaviest table entry).

2. **Finite search bounds, derived — not assumed.** From the upper end of the hydration
   window, (1−0.39165)·x·18.016 < 0.39165·(ArQ + 19v) ≤ 0.39165·370, giving **x ≤ 37**.
   From the upper end of the sodium window, **n ≤ 13** (same envelope, 370 = 294 + 4·19).

3. **Mass envelopes.** Clearing denominators in all three data and sweeping
   1 ≤ x ≤ 37, 1 ≤ n ≤ 13 for each valence shows that *every* surviving candidate obeys:
   * v = 2: 17.9725 < Ar(Q) < 17.997 — but the periodic table prints **no** mass in
     (17.9675, 18.002): oxygen is 16.00 and fluorine 19.00. Hence v = 2 is impossible.
   * v = 3: 26.945 < Ar(Q) < 26.9943 — whose half-quantum neighbourhood contains exactly
     **one** printed table mass: 26.98, the entry at atomic number 13, **aluminium**
     (neighbours: Mg 24.30, Si 28.09).

4. **Stoichiometry.** Knowing the metal prints as 26.98 re-tightens the true mass to the
   open half-quantum 26.975 < Ar(Q) < 26.985. Substituting v = 3: the hydration datum
   alone kills every x ≠ 3 in 1..37 (only x = 3 survives), and the sodium datum alone
   kills every n ≠ 3 in 1..13 (only n = 3 survives). Hence C = AlF₃, the hydrate is
   AlF₃·3H₂O, and D = Na₃AlF₆.

5. **Chemistry cross-check.** Cryolite Na₃AlF₆ is precisely the industrial aluminium
   compound (electrolyte solvent in the Hall–Héroult process), AlF₃·3H₂O is the known
   sparingly-soluble aluminium fluoride trihydrate precipitated near pH ~4, and the
   NaF-driven conversion AlF₃ → Na₃AlF₆ is the classical complex-fluoride formation.

## Declared modelling assumptions (reported honestly)

* **M-A4-1** C = QFᵥ with v ∈ {2, 3} — the common metal-fluoride stoichiometries.
  Widening to v ≤ 5 numerically admits one spurious self-similar triple (v,x,n)=(5,5,5)
  near scandium's printed mass 44.96, but ScF₅ does not exist (Sc is exclusively +3), so
  the chemical answer is unchanged; the restriction v ∈ {2,3} is the chemically meaningful
  family and is declared, not derived.
* **M-A4-2** D = C ⬝ n NaF = NaₙQF_{v+n}, n ≥ 1 (adduct, as in cryolite = AlF₃ ⬝ 3 NaF).
* **M-A4-3** 0 < Ar(Q) ≤ 294.
* **M-A4-4** after identification, the true Ar(Q) lies within half a quantum (±0.005) of
  the matched printed table value — used only to re-tighten the window before re-deriving
  x and n; no answer is assumed (Ar = 26.98 is derived from the v = 3 envelope + table).

## Formalization

The complete argument above is machine-checked in
`IChO2026Problems/problem_icho_2026_t1_a4.lean` (namespace `IChO2026Problems.T1A4`):
`main_answer` proves that any candidate satisfying the three measured data, the mass
range, and the periodic-table match must have v = 3, x = 3, n = 3, z = 13, Ar = 26.98;
`theAnswer_correct` binds this to the submitted formulas Al / AlF₃·3H₂O / Na₃AlF₆.
See `verification.md` for the exact commands and axiom audit (standard axioms only).
