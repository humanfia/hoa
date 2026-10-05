# IChO 2026, Problem T8, Part 8.6 — Quantum yield for CO formation

**Answer: φ(CO) = 1.86 %** (raw value 1.8594101613683625… %, reported to three significant figures per the uniform blind-evaluation default).

## What the problem gives (source grounding)

From the official English problem statement for Question 8, page Q8-2
(`T8_page-2.png`, printed page 2 / source page 73 of `theory_problem.pdf`), the text immediately before question 8.6 states:

- TOF definition: "The Turnover Frequency of a catalyst (TOF) is the number of product molecules formed per active catalyst molecule per hour."
- Experiment: "Under LED illumination (λ = 390 nm) with power of 50 mW, there was a TOF of 8 h⁻¹ for 10 mg of C₃N₄, loaded with 1 with ω_cat = 3.8%."
- The values M_cat = 557.21 g mol⁻¹ and ω_cat = 3.8 % come from part 8.5 at the top of the same page (Q8-2) and are restated in the experiment line.
- The formula printed directly above 8.6:

  φ = (number of reacted electrons / number of incident photons) · 100 %

Chemistry used (trusted general law, not competition-answer material):

- Each CO formed from CO₂ is a **2-electron reduction**: from part 8.1 the half-equation in acidic medium is CO₂ + 2H⁺ + 2e⁻ → CO + H₂O, i.e. 2 reacted electrons per CO molecule formed.
- Energy of one photon of wavelength λ: E = h c / λ (Planck relation).
- Rate of incident photons from a source of power P: P / (h c / λ) photons per second.
- Exact (SI-defined, stipulated) constants: h = 6.62607015 × 10⁻³⁴ J·s, c = 2.99792458 × 10⁸ m s⁻¹, N_A = 6.02214076 × 10²³ mol⁻¹.

All printed experimental numbers (390 nm, 50 mW, 8 h⁻¹, 10 mg, 3.8 %, 557.21 g mol⁻¹) are used as the exact printed values.

## Calculation

**1. Catalyst molecules present.** The sample is 10 mg of C₃N₄ loaded with mass fraction ω_cat = 3.8 % of catalyst 1:

n_cat = (10 × 10⁻³ g × 0.038) / 557.21 g mol⁻¹ = 6.8196… × 10⁻⁷ mol

**2. CO molecules produced per hour (TOF = 8 h⁻¹).**

N_CO = 8 × n_cat × N_A = 8 × (6.8196… × 10⁻⁷) × 6.02214076 × 10²³ ≈ 3.2855 × 10¹⁸ molecules per hour.

**3. Reacted electrons.** Each CO costs 2 electrons (8.1 half-equation):

N_e = 2 × N_CO ≈ 6.5711 × 10¹⁸ electrons per hour.

**4. Photons incident during the same hour.** Photon energy at λ = 390 nm:

E_photon = h c / λ = (6.62607015 × 10⁻³⁴ × 2.99792458 × 10⁸) / (390 × 10⁻⁹) ≈ 5.0935 × 10⁻¹⁹ J.

At power P = 50 mW = 0.050 W over t = 3600 s, total incident energy is 180 J, so

N_photons = P · t · λ / (h c) ≈ 3.5339 × 10²⁰ photons per hour.

**5. Quantum yield.**

φ = N_e / N_photons × 100 %
  = [2 × 8 × (0.010 × 0.038 / 557.21) × N_A] × [h c / (0.050 × 3600 × 390 × 10⁻⁹)] × 100 %
  = 1.8594101613683625… %

**Reported: φ(CO) = 1.86 %** (three significant figures).

Using per-second rates instead of per-hour totals gives the identical value; the time basis cancels as long as numerator and denominator use the same period.

## Source-grounding notes and dependency check

- The 2-electron stoichiometry is grounded in the problem itself: part 8.1 asks for the half-equation for the reduction of CO₂ to CO in acidic medium, whose answer is CO₂ + 2H⁺ + 2e⁻ → CO + H₂O (derivable from charge and mass balance alone; carbon is +4 in CO₂ and +2 in CO). This is a derived prerequisite, stated and used inline rather than imported from any answer key.
- The result of part 8.5 (N_cat per nm²) is **not** needed for 8.6: the specific surface area only concerns catalyst dispersion per unit area, whereas the quantum yield depends on the total number of active catalyst molecules in the 10 mg sample, which follows directly from the mass fraction and molar mass printed in 8.5 and restated with the experiment. No previous-part numerical result is imported.
- The photon-counting physics (E = hc/λ, photon rate = power/photon energy), the SI-exact constants h, c, N_A, and the 2-electron reduction stoichiometry are the only non-printed scientific inputs. All are ordinary general physics/chemistry laws (permitted "trusted_general_law" sources).
- No official solution, marking scheme, grading report, historical answer, or answer repository was consulted; `official_answer_seen` is false and the computation was done independently from the problem page alone.

## Lean formalization

The Lean file `IChO2026Problems/problem_icho_2026_t8_a6.lean` defines the exact real-valued quantum-yield expression from the printed data and the SI-exact constants, proves its raw numerical value matches the hand derivation, and proves the final reported value 1.86 % satisfies the project-wide rounding contract (`IChO2026Chem.Reporting.ReportsAtQuantum` with quantum 0.01 %, i.e. the raw value lies in [1.855, 1.865) and rounds half-away-from-zero to 1.86 at three significant figures). See `verification.md` for the exact build commands and `#print axioms` output.
