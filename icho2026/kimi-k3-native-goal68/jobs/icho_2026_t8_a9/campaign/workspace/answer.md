# IChO 2026, Theory Problem 8.9 (target `icho_2026_t8_a9`) — Answer

## Requested outputs

Calculate the percentage of quenching η_q (in %) of the S₁ and T₁ states of the
photosensitiser when [Red] = 0.1 M, given k_S = 2.7 × 10⁹ M⁻¹ s⁻¹,
k_T = 1.5 × 10⁸ M⁻¹ s⁻¹ and the unquenched emission lifetimes
τ₀(S₁) = 2.9 ns, τ₀(T₁) = 84 μs (all values printed on the official page Q8‑5).
Note given in the problem: k_F >> k_ISC.

## Answers (three significant figures, per requested precision)

**η_q(S₁) = 43.9 %**  (raw value 783/1783 × 100 % = 43.9147… %)

**η_q(T₁) = 99.9 %**  (raw value 1260/1261 × 100 % = 99.9207… %)

## Derivation

With the quencher at fixed concentration [Red], reductive quenching acts as a
pseudo-first-order channel competing with all intrinsic (unimolecular) decay
channels of the excited state.  The intrinsic channels add up to
k₀ = 1/τ₀ (τ₀ is defined as the lifetime *without* quencher), and the quenching
channel has rate constant kq = k_Q·[Red]:

* S₁: k₀(S₁) = 1/(2.9 ns) = 3.448… × 10⁸ s⁻¹ (= 10¹⁰/29 s⁻¹),
      kq(S₁) = 2.7 × 10⁹ × 0.1 = 2.7 × 10⁸ s⁻¹.
* T₁: k₀(T₁) = 1/(84 μs) = 1.190… × 10⁴ s⁻¹ (= 250000/21 s⁻¹),
      kq(T₁) = 1.5 × 10⁸ × 0.1 = 1.5 × 10⁷ s⁻¹.

The excited population then decays monoexponentially,
N(t) = N₀·exp[−(k₀ + kq)t], and the probability of ending up quenched is the
integral of the quenching channel's rate over the whole decay (proved in Lean
by FTC-2 on (0, ∞), theorem `fractionQuenched_of_competingChannels`):

  η_q = ∫₀^∞ kq·N₀·exp[−(k₀+kq)t] dt / N₀ = kq / (k₀ + kq).

Because the note k_F >> k_ISC makes intersystem crossing negligible relative to
fluorescence, essentially no T₁ population is generated out of the S₁
competition, so S₁ and T₁ behave as two independent excited populations, each
quenching with its own τ₀ and its own k_Q — exactly the quantities given.

### S₁ state

  η_q(S₁) = kq(S₁) / (k₀(S₁) + kq(S₁))
          = 2.7×10⁸ / (10¹⁰/29 + 2.7×10⁸)
          = 2.7×10⁸ × 29 / (10¹⁰ + 78.3×10⁸)
          = 783 / 1783
          = 0.439147… → **43.9 %**

(equivalently, with the Stern–Volmer product kq·τ₀ = 2.7×10⁸ × 2.9×10⁻⁹ = 0.783,
 η_q = 0.783/(1 + 0.783))

### T₁ state

  η_q(T₁) = kq(T₁) / (k₀(T₁) + kq(T₁))
          = 1.5×10⁷ / (250000/21 + 1.5×10⁷)
          = 3.15×10⁸ / 3.1525×10⁸
          = 1260 / 1261
          = 0.999207… → **99.9 %**

(equivalently, kq·τ₀ = 1.5×10⁷ × 84×10⁻⁶ = 1260, so η_q = 1260/1261)

## Source grounding

* All numerical inputs come verbatim from the question page
  `icho_2026_source/image/T8_page-5.png` (58th IChO theory paper, Q8‑5,
  English official): k_S = 2.7×10⁹ M⁻¹ s⁻¹, k_T = 1.5×10⁸ M⁻¹ s⁻¹,
  τ₀(S₁) = 2.9 ns, τ₀(T₁) = 84 μs, [Red] = 0.1 M, note k_F >> k_ISC.
* The Jablonski diagram on the same page assigns to S₁ the intrinsic channels
  k_F (fluorescence) and k_IC (internal conversion), plus intersystem crossing
  k_ISC, and assigns to T₁ the intrinsic channels k_P (phosphorescence) and k_N
  (non-radiative decay).  τ₀ is explicitly defined as "the emission lifetime in
  the absence of the quencher", which is exactly why 1/τ₀ equals the total
  unimolecular decay rate used above.
* The piece of trusted general law used is the standard competing-first-order
  (Stern–Volmer) quenching kinetics: for parallel first-order/pseudo-first-order
  channels the fraction following the quenching channel equals its rate constant
  divided by the sum of all rate constants.  This is *derived* in the Lean file
  from the monoexponential decay model rather than assumed.
* No external competition materials (official solutions, marking schemes,
  repositories, solver agents) were used.

## Verification

The Lean 4 formalization in
`IChO2026Problems/problem_icho_2026_t8_a9.lean` proves:

* the kinetic derivation lemma `fractionQuenched_of_competingChannels`
  (fraction quenched = kq/(k₀+kq), via the improper integral of the
  monoexponential decay, using only Mathlib);
* the exact rational values `quenchingPercentage_S1 : η_q(S₁) = 78300/1783 %`
  and `quenchingPercentage_T1 : η_q(T₁) = 126000/1261 %`;
* ordering facts (`η_q(S₁) < 100`, `η_q(T₁) > 99`, `η_q(T₁) > η_q(S₁)`);
* the answer-blind reporting of both values at the three-significant-figure
  quantum 0.1 % (43.9 % and 99.9 %) against the shared
  `IChO2026Chem.Reporting` contract.

`#print axioms` for every final theorem lists only
`propext`, `Classical.choice`, `Quot.sound` (standard Lean logical axioms;
no `sorryAx`, no custom axioms).  See `verification.md` for exact commands.
