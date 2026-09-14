Answer record for IChO 2026 problem T4, part 4.5 (target `icho_2026_t4_a5`).

## Answer

**n_c ≈ 20 collisions**, more precisely **n_c ≈ 19.97 ≈ 20.0 (to three
significant figures)**.

## Source statement

Theory problem T4 ("The nuclear past of Uzbekistan"), source page 38,
printed page Q4-2, part 4.5:

> 4.5 **Determine** the average number of collisions required, n_c, to slow a
> neutron from 2 MeV to 0.012 eV, using water as the moderator.
> ξ(water) = 0.948

The shared context (printed page Q4-2, directly above part 4.5) defines the
logarithmic energy decrement,

    ξ = ln (E_initial / E_final),

where E_initial and E_final are the initial and final neutron energies *per
collision*, and states:

> ξ is a constant for each type of material and does not depend on the
> initial neutron energy.

The shared context also fixes that fission neutrons are produced with an
average energy of 2 MeV.

## Solution

Because ξ is the average decrease of `ln E` per collision and is independent
of the energy, after n collisions the average log-energy has fallen by n·ξ.
To slow from E₀ to E_target we therefore need

    n_c · ξ = ln(E₀ / E_target)     ⟹     n_c = (1/ξ) · ln(E₀ / E_target).

With both energies expressed in eV (1 MeV = 10⁶ eV):

    E₀           = 2 MeV    = 2·10⁶ eV
    E_target     = 0.012 eV
    E₀/E_target  = 2·10⁶/0.012 = (5/3)·10⁸ ≈ 1.6667·10⁸
    ln(E₀/E_target) = ln(1.6667·10⁸) ≈ 18.93151
    n_c          = 18.93151 / 0.948 ≈ 19.9699 ≈ 19.97 collisions.

All intermediate quantities are kept as exact real expressions; rounding
happens only at the final reporting boundary. At the answer-blind default of
three significant figures the reported value is **20.0 collisions**; phrased
physically, a neutron makes on average about **20 collisions** with the water
nuclei before reaching 0.012 eV.

## Formalization

The full development is in
`IChO2026Problems/problem_icho_2026_t4_a5.lean`:

- `logEnergyAfter_eq` — iterates the printed per-collision definition of ξ
  to the closed form `logEnergyAfter n logE₀ ξ = logE₀ − n·ξ` (induction
  on n).
- `averageCollisions`, `averageCollisions_spec`, `averageCollisions_unique` —
  the average collision count `L/ξ` is the unique n with `ξ·n = L`.
- `ncRaw` — the exact raw answer `log (2·10⁶/0.012)/0.948`, with
  `ncRaw_spec : ξWater * ncRaw = log (Einitial / Etarget)`.
- Certified rational bounds with no floating point:
  `log(Einitial/Etarget) = log(5/3) + 8·log 10` and
  `log 10 = 2·log 2 + log(5/2)`, and each of `log 2`, `log(5/2)`,
  `log(5/3)` is bounded by exact rationals using the artanh power series
  (`Real.sum_range_le_log_div`, `Real.log_div_le_sum_range_add`), giving

      18.93150572… ≤ log (Einitial/Etarget) ≤ 18.93151689…
      19.96 ≤ ncRaw < 19.98.

- `submission_valid` — the `IChO2026Chem.Reporting` contract is satisfied:
  the raw value is kept exact and the reported value `20.0` uses quantum
  `0.1` (three-significant-figure default); the raw value lies strictly
  inside the half-quantum cell `[19.95, 20.05)`, so no tie-breaking arises.

Axioms used by all final theorems: only Lean's standard `propext`,
`Classical.choice`, `Quot.sound` (see verification.md).
