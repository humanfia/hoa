# IChO 2026 T8-A10

Tick **b) decreases**.

- The emission lifetime of the **S1 state decreases** as `[Red]` increases.
- The emission lifetime of the **T1 state decreases** as `[Red]` increases.

## Derivation

For either excited state, write `tau0` for its lifetime without reductant and
`kq` for its bimolecular reductive-quenching constant. At reductant
concentration `c = [Red]`, bimolecular quenching supplies the additional
pseudo-first-order decay rate `kq c`. The standard dynamic-quenching lifetime
law is therefore

`1/tau(c) = 1/tau0 + kq c`,

or equivalently

`tau(c) = tau0 / (1 + kq tau0 c)`.

Both printed quenching constants are strictly positive:

- `kS = 2.7 × 10^9 M^-1 s^-1` for S1;
- `kT = 1.5 × 10^8 M^-1 s^-1` for T1.

The printed unquenched lifetimes, `tau0(S1) = 2.9 ns` and
`tau0(T1) = 84 microseconds`, are also positive. Consequently, if
`c2 > c1 >= 0`, then

`1 + kq tau0 c2 > 1 + kq tau0 c1 > 0`,

so `tau(c2) < tau(c1)`. This establishes strict decrease for each state. For
reference, the Stern--Volmer coefficients are positive in both cases:
`kS tau0(S1) = 7.83 M^-1` and `kT tau0(T1) = 1.26 × 10^4 M^-1`.

## Source grounding

- `TASK.json` identifies the two requested outputs as the lifetime trends of
  S1 and T1.
- `T8_page-5.png` and the original problem PDF, Q8-5 (PDF page 76), print the
  two reductive-quenching reactions, their positive rate constants, both
  unquenched lifetimes, and question 8.10 with choices (a)--(c).
- The preceding `T8_page-4.png` was checked for continuity of the problem; it
  introduces the irradiation context but adds no premise needed here.
- The blank student answer sheet A8-7 (PDF page 83) has a single row of boxes
  `a`, `b`, and `c` for 8.10. Thus the shared tick is `b`, applying to both S1
  and T1 as the question asks.
- The only general scientific law used is the standard addition of independent
  first-order loss rates for dynamic bimolecular quenching at fixed quencher
  concentration. No result from 8.9 is assumed or needed.

There is no source gap affecting the classification: the problem explicitly
specifies dynamic bimolecular quenching and positive `kS` and `kT`; the
lifetime trend then follows from the standard kinetic law.

