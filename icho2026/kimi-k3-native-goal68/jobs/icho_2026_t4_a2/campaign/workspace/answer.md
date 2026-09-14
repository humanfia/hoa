# IChO 2026 — T4 The nuclear past of Uzbekistan, part 4.2 (target `icho_2026_t4_a2`)

## Question as printed (source: `theory_problem.pdf`, printed page Q4-1, source page 37; also `T4_page-1.png`)

"The main reaction occurring in nuclear power plants is the reaction where
²³⁵U absorbs a neutron and undergoes fission, releasing energy and producing
three additional neutrons, thus sustaining a chain reaction.

  ²³⁵₉₂U + ¹₀n → … + 3 ¹₀n

Neutrons that induce the chain reaction are produced by several ways:
a) Reaction of ¹¹B with α-particles inside the reactor core
b) Interaction of γ rays with ²D nuclei present in the reactor coolant water
c) Reaction of ⁹Be with α-particles produced in an externally installed neutron source.

**Write** the nuclear reaction equations for (a), (b), and (c). (3.0 pt)"

## Answers

**(a)** ¹¹B + α → ¹⁴N + n, i.e.

$$^{11}_{5}\mathrm{B} + {}^{4}_{2}\mathrm{He} \;\longrightarrow\; {}^{14}_{7}\mathrm{N} + {}^{1}_{0}\mathrm{n}$$

**(b)** ²D + γ → ¹H + n (photodisintegration of the deuteron), i.e.

$$^{2}_{1}\mathrm{D} + \gamma \;\longrightarrow\; {}^{1}_{1}\mathrm{H} + {}^{1}_{0}\mathrm{n}$$

**(c)** ⁹Be + α → ¹²C + n, i.e.

$$^{9}_{4}\mathrm{Be} + {}^{4}_{2}\mathrm{He} \;\longrightarrow\; {}^{12}_{6}\mathrm{C} + {}^{1}_{0}\mathrm{n}$$

## Reasoning

Every nuclear equation is balanced by conserving the mass number A (top index)
and the atomic number Z (bottom index) separately; the photon γ carries
A = 0, Z = 0, the α-particle is ⁴₂He (A = 4, Z = 2), and the neutron is ¹₀n.

Moreover, the problem text dictates the nature of each channel: the
introductory sentence states that these are the ways in which the
**chain-reaction neutrons are produced**, so each reaction must have a free
neutron among its products. With one neutron as the dictated light product,
conservation of (A, Z) *uniquely* forces the residual heavy product:

* **(a)** reactants carry (A, Z) = (11 + 4, 5 + 2) = (15, 7). The neutron
  takes away (1, 0), leaving (14, 7): nitrogen-14, ¹⁴N. This is the classic
  (α, n) reaction on boron-11, the inverse of the reaction
  (¹⁴N + α → ¹⁷O + p) used for the discovery of the proton.
* **(b)** the deuteron (2, 1) absorbs a γ photon (0, 0); the neutron takes
  (1, 0), leaving (1, 1): a proton, ¹H. This is the well-known
  photodisintegration of deuterium, γ + d → p + n, the same channel that
  operates in heavy-water-moderated reactors.
* **(c)** reactants carry (9 + 4, 4 + 2) = (13, 6); the neutron takes (1, 0),
  leaving (12, 6): carbon-12, ¹²C. This is the historically first artificial
  (α, n) neutron source, ⁹Be(α, n)¹²C, still used in laboratory neutron
  sources — exactly matching "an externally installed neutron source".

All three equations balance exactly:

| channel | A balance | Z balance |
|---------|-----------|-----------|
| (a) | 11 + 4 = 14 + 1 = 15 | 5 + 2 = 7 + 0 = 7 |
| (b) | 2 + 0 = 1 + 1 = 2 | 1 + 0 = 1 + 0 = 1 |
| (c) | 9 + 4 = 12 + 1 = 13 | 4 + 2 = 6 + 0 = 6 |

## Source grounding

The reactants (¹¹B + α, ²D + γ, ⁹Be + α) are given verbatim by the problem
text above. The requirement that a **neutron is produced** is given by the
surrounding prose ("Neutrons that induce the chain reaction are produced by
several ways"). Nothing beyond conservation of mass number A and atomic
number Z — a trusted general law of nuclear reactions — is needed: each
balanced equation is then forced, as proved formally in
`IChO2026Problems/problem_icho_2026_t4_a2.lean`
(theorems `reaction_*_balanced` verify the balances and
`reaction_*_residual_forced` prove that the residual product nucleus is
uniquely determined given the single-neutron output). No official solution,
marking scheme, or answer repository was consulted.

## Formalization

See `IChO2026Problems/problem_icho_2026_t4_a2.lean`. Nuclear species are
modeled by their (A, Z) labels in `Fin 2 → ℤ`; `Balanced` is conservation of
both labels, and the six theorems cover balance and uniqueness for all three
channels. Verification details are in `verification.md`.
