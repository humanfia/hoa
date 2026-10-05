# IChO 2026, T4-A1 (item 4.1): Atomic abundance of ²³⁵U in natural uranium

## Final answer

**Atomic abundance of ²³⁵U ≈ 0.664 %** (three significant figures).

Raw (unrounded) result: abundance = 200/301 % = 0.6644518… % of atoms.
(Blank answer sheet A4-1 asks: "4.1 (2.0 pt) ²³⁵U : ______ %".)

## Solution

Let `x` be the atomic (mole) fraction of ²³⁵U; the fraction of ²³⁸U is `1 − x`
because natural uranium is assumed to consist only of these two isotopes.
The average atomic mass of the mixture is the abundance-weighted sum of the
isotopic masses:

    A(U) = x·(235.04 a.u.) + (1 − x)·(238.05 a.u.)

The average atomic weight of natural uranium, read from the official periodic
table distributed with the examination, is A(U) = 238.03. Hence

    235.04·x + 238.05·(1 − x) = 238.03
    (238.05 − 235.04)·x = 238.05 − 238.03
    3.01·x = 0.02
    x = 0.02/3.01 = 2/301 ≈ 0.0066445

so the atomic abundance in percent is

    100·x = 200/301 % ≈ 0.66445… % → **0.664 %** (3 s.f.).

No intermediate rounding is used anywhere; the rounding to three significant
figures is applied only to the final value. The raw value 0.6644518… lies
strictly inside the reporting interval (0.6635, 0.6645) of 0.664, so no
rounding tie occurs.

## Source grounding

All inputs come from the problem-only materials in this workspace:

1. **Problem statement** (theory_problem.pdf, source page 37, header "Q4-1";
   page image `icho_2026_source/image/T4_page-1.png`): "4.1 Calculate the
   atomic abundance of ²³⁵U in natural uranium, assuming it consists only of
   isotopes ²³⁵U (235.04 a.u.) and ²³⁸U (238.05 a.u.)" — supplies the isotopic
   masses and the two-isotope assumption. These are stipulated constants,
   exact as printed.
2. **Average atomic weight A(U) = 238.03**: printed under the symbol `U` in
   the official "Periodic Table of Elements" bound into the same examination
   booklet (theory_problem.pdf, page header "G1-5", fifth page of the PDF).
   The examination booklet provides no other value for the atomic weight of
   uranium. (Cross-check: page index 30 mentions uranium only as UO₂²⁺;
   no other page of the PDF contains an atomic weight for U.) Any isotopic
   abundance problem of identical structure with any tabulated atomic weight
   would be solved by the same equation proved in the Lean file.
3. **Blank student answer sheet** (theory_problem.pdf, header "A4-1", PDF page
   index 39): "4.1 (2.0 pt) ²³⁵U : ______ %" — confirms the requested output
   is the abundance of ²³⁵U as a percentage.
4. **Reporting precision**: the problem requests no specific precision; the
   project's answer-blind default for this target (TASK.json
   `reporting_policy`) is three significant figures, ties half away from zero.

The result 0.664 % is physically sensible: it is below the well-known natural
²³⁵U abundance ≈ 0.72 % only because the printed isotopic masses (235.04,
238.05) and the printed atomic weight (238.03) carry only two decimal places;
the computation follows exactly the printed figures.

## Lean formalization

`IChO2026Problems/problem_icho_2026_t4_a1.lean` proves, for any real `x`
consistent with the model, that `x = 2/301`, gives the exact percentage
`100·x = 200/301 %`, and proves that 0.664 is the correct three-significant
figure report of that value under the project's `ReportsAtQuantum` relation
(quantum 0.001 %, ties away from zero). See `verification.md` for the exact
build commands and the `#print axioms` output (only the standard logical
axioms `propext`, `Classical.choice`, `Quot.sound` are used — no `sorry`,
no custom axioms).
