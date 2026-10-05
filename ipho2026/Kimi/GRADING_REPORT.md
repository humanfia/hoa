# IPhO 2026 Kimi K3 Max grading audit

Date: 2026-08-21 UTC

## Verdict

Estimated score: **29.90 / 50.00 = 59.8%**.

This is a conservative source-level estimate against the official IPhO
answers and point allocations, not an official jury adjudication. Lean
compilation establishes that the submitted propositions are proved; it does
not establish that those propositions faithfully encode every requested
physical or experimental result. Credit below therefore follows what each
formal theorem actually entails.

Summary:

- All 41 Lean answer files compile.
- 14 parts receive full credit, 22 partial credit, and 5 zero credit.
- The theory submission often proves useful identities, but several target
  predicates omit the official closed form or allow arbitrary interface data.
- The experimental submission mostly formalizes generic graphing or fitting
  infrastructure. It usually does not supply the requested measurements,
  numerical estimates, or uncertainties.

## Official sources and grading basis

- [Theory 1 official solution](https://cdn.phoxiv.org/olympiads/ipho/2026/T1/solution.pdf)
- [Theory 2 official solution](https://cdn.phoxiv.org/olympiads/ipho/2026/T2/solution.pdf)
- [Theory 3 official solution](https://cdn.phoxiv.org/olympiads/ipho/2026/T3/solution.pdf)
- [Experimental official solution](https://cdn.phoxiv.org/olympiads/ipho/2026/E1/solution.pdf)
- [Experimental problem and final point allocation](https://cdn.phoxiv.org/olympiads/ipho/2026/E1/problem.pdf)
- Official text marking schemes: [T1](https://huggingface.co/datasets/humanfia-lab/IPHO2026/resolve/main/ipho_2026_source/text/T1_marking_scheme.txt), [T2](https://huggingface.co/datasets/humanfia-lab/IPHO2026/resolve/main/ipho_2026_source/text/T2_marking_scheme.txt), and [T3](https://huggingface.co/datasets/humanfia-lab/IPHO2026/resolve/main/ipho_2026_source/text/T3_marking_scheme.txt)

Full credit requires the submitted predicate to entail the official requested
result for the stated inputs. Partial credit is awarded for a correct central
law or method that omits a requested branch, orientation, numerical
specialization, data product, or uncertainty. A theorem receives zero where
its assumptions are inconsistent, its result is vacuous, or it constructs
arbitrary data unrelated to the requested observation.

## Detailed ledger

### Theory problem 1 — 7.20 / 10.00

| Part | Pts | Official result | Submitted result and assessment | Grade |
|---|---:|---|---|---:|
| 1-A1 | 3.0 | `a = Δh/(2√2) = 0.50 m` | Derives the equivalent exact formula and numerical value. | 3.0 |
| 1-B1 | 1.0 | `r_max = (1600/9)a₀` | Proves the correct maximum distance. | 1.0 |
| 1-B2 | 2.5 | Signed deflection `−16.60°` | Correct energy, eccentricity, scale, and `16.60°` magnitude, but loses the official negative/below-axis orientation. | **2.3** |
| 1-C1 | 2.5 | Piecewise minimum photon energy, including the nonacute backscatter branch | Establishes conservation identities only; it does not derive the physical infimum or the official piecewise formula. | **0.4** |
| 1-C2 | 1.0 | Ozone excess energy `2.03×10⁻¹¹ eV` | Selects the smaller algebraic root but gives neither the requested second-order approximation nor the numerical result and unit. | **0.5** |

### Theory problem 2 — 5.40 / 10.00

| Part | Pts | Official result | Submitted result and assessment | Grade |
|---|---:|---|---|---:|
| 2-A1 | 1.5 | `x_N = R cos(π/(2N+1))` | Proves the official threshold formula. | 1.5 |
| 2-B1 | 2.0 | `α=R`, `β=−R/2` | Proves the official coefficient pair. | 2.0 |
| 2-B2 | 1.5 | `P/P₀ = 1/(1−cos θ_max)` | Correctly identifies `P₀` and relevant flux pieces, but combines direct and reflected power incorrectly and never proves the official ratio. | **0.6** |
| 2-B3 | 0.5 | `a=12 cm` for `R=1 m`, `P=5P₀` | Constructs an arbitrary constant power profile and a radius near `5 cm`, so the requested value is not derived. | **0.0** |
| 2-C1 | 0.5 | `m_A=cot(2θ)`, `b_A=R/(2cos θ)` | Proves the official reflected-line coefficients. | 0.5 |
| 2-C2 | 2.0 | Evaluated first-order expansions for `m_B` and `b_B` | Supplies a generic Taylor framework but does not evaluate it to the official coefficients. | **0.4** |
| 2-C3 | 1.0 | `(X_C,Y_C)=(R sin³θ,(R/2)cosθ(2−cos2θ))` | Sets up an envelope relation but gives no official coordinates; moreover the unnormalized direction `(1,m)` is forced to have the incident ray's unit norm, making the global reflected-ray context inconsistent. | **0.2** |
| 2-C4 | 1.0 | `u=R/2`, `v=(3/4)R^(1/3)`, `p/q=2/3` | Proves `p/q=2/3`, but assumes the wrong apex `Y_C→R` and does not recover the official `u` and `v`. | **0.2** |

### Theory problem 3 — 9.40 / 10.00

| Part | Pts | Official result | Submitted result and assessment | Grade |
|---|---:|---|---|---:|
| 3-A1 | 0.2 | `H=NIA/V` | Proves the official field law. | 0.2 |
| 3-A2 | 0.6 | `dW_emf=VH dB` | Proves the official work relation. | 0.6 |
| 3-A3 | 0.2 | `dW=μ₀VH dM` | `SourceWorkLaw` only asserts an unrelated flux witness; the final result follows from an underconstrained premise rather than deriving the material-work law. | **0.0** |
| 3-B1 | 1.5 | `Q=−μ₀nK(H_f²−H_i²)/(2T)` | Proves the official isothermal heat formula. | 1.5 |
| 3-B2 | 1.5 | Official square-root adiabatic temperature law | Proves an analytically equivalent endpoint relation. | 1.5 |
| 3-C1 | 0.2 | Correct process labels and heat directions | Supplies the official cycle annotation. | 0.2 |
| 3-C2 | 1.5 | `M₁=√(M₂²−M₃²+M₄²)` | Proves the official positive-root relation. | 1.5 |
| 3-C3 | 0.8 | `T_f≈0.99008 K` | Establishes the symbolic energy balance, but key numerical inputs remain comments or unconstrained fields and no numerical temperature is proved. | **0.4** |
| 3-C4 | 2.0 | Official logarithmic cooling-time formula | Proves the official formula. | 2.0 |
| 3-C5 | 1.5 | Official coefficient-of-performance formula | Proves the equivalent official result. | 1.5 |

### Experimental problem — 7.90 / 20.00

The official solution's tables are representative measurements, but each
question still asks the contestant to record or graph an actual run and then
extract numerical estimates. A formal interface for arbitrary external data
earns method credit; an invented constant/exponential record does not earn the
recording point.

| Part | Pts | Official result or method | Submitted result and assessment | Grade |
|---|---:|---|---|---:|
| 4-A1 | 0.4 | Determine sample mass, amount, and molecule count with uncertainties | Correct symbolic conversion laws, without numerical values or uncertainties. | **0.20** |
| 4-A2 | 1.0 | Record a `P(T)` table | No experimental table is supplied. | **0.00** |
| 4-A3 | 0.9 | Plot `P` against `T` | Encodes qualitative linear behavior but supplies no graph from measured data. | **0.30** |
| 4-A4 | 1.0 | Determine `R≈8.4±0.4 J mol⁻¹ K⁻¹` | Gives the slope formula, but no fitted numerical value or uncertainty. | **0.50** |
| 4-A5 | 0.7 | Determine `β₀≈0.0034±0.0007 K⁻¹` | Gives the coefficient formula, but no numerical value or uncertainty. | **0.40** |
| 4-B1 | 1.0 | Record an `H(T)` table | Constructs a degenerate constant two-row record rather than experimental measurements. | **0.00** |
| 4-B2 | 1.0 | Plot `H` against `T` | Supplies generic graph/OLS infrastructure, not the requested measured plot. | **0.30** |
| 4-B3 | 0.5 | Extrapolate `H₀≈5.9 cm` at `273.15 K` | Encodes extrapolation but proves no value for `H₀`. | **0.20** |
| 4-B4 | 1.0 | `P_v=P_atm(1−H₀T/(HT₀))` | Proves exactly the official height formula. | 1.00 |
| 4-B5 | 4.0 | Transformed plot, slope `−4700±200 K`, `ΔH_v≈39±2 kJ/mol` | Correct transformed variables, linear-fit method, and `ΔH_v=−R·slope`, but no experimental graph, numerical fit, or uncertainty. | **2.00** |
| 4-B6 | 0.5 | `L_v≈2190±110 kJ/kg` | Correct molar-to-mass conversion formula, without a numerical result or uncertainty. | **0.25** |
| 4-C1 | 1.0 | Record `(t,T_IC,T_OC)` | Invents a convenient exponential/constant temperature record rather than recording observations. | **0.00** |
| 4-C2 | 1.0 | Plot both temperature traces | Encodes the two-trace plot structure, with no experimental plot. | **0.25** |
| 4-C3 | 0.7 | Plot temperature difference against each temperature | Provides a generic graph relation, not the requested measured plots. | **0.20** |
| 4-C4 | 1.1 | Infer equilibrium temperature `T_eq≈53°C` | Gives a weighted-mean relation but no numerical equilibrium temperature. | **0.40** |
| 4-C5 | 1.0 | Plot finite-difference cooling rate against adjacent average gap | Uses the right derived quantities, but chooses an arbitrarily large tolerance from the residual itself, making the claimed linear fit vacuous. | **0.30** |
| 4-C6 | 1.6 | `R_Th≈1.17±0.03 K/W` | Gives the reciprocal-slope formula, but no numerical fit or uncertainty. | **0.80** |
| 4-C7 | 1.6 | `λ≈0.25±0.01 W/(m·K)` | Gives the radial-conduction formula, but no numerical value or uncertainty. | **0.80** |

## Totals

| Section | Score |
|---|---:|
| Theory 1 | 7.20 / 10.00 |
| Theory 2 | 5.40 / 10.00 |
| Theory 3 | 9.40 / 10.00 |
| Experiment | 7.90 / 20.00 |
| **Overall** | **29.90 / 50.00 (59.8%)** |

## Highest-impact formalization defects

- `problem_IPhO_2026_2_B_3.lean:158-160` chooses a freely defined radius
  law and constant fivefold power profile, so the official `12 cm` answer is
  not constrained by B.1/B.2.
- `problem_IPhO_2026_2_C_3.lean:115-119` models the reflected direction as
  `(1,m)` while requiring it to have the same squared norm as `(0,−1)`. This
  forces `m=0` and makes the proposed law across the physical angle interval
  uninhabited.
- `problem_IPhO_2026_2_C_4.lean:162` assumes `Y_C→R`, whereas the official
  caustic has apex `u=R/2`.
- `problem_IPhO_2026_3_A_3.lean:124-126` defines a weak
  `SourceWorkLaw` that does not state the source-work equation needed for the
  official derivation.
- `problem_IPhO_2026_3_C_3.lean:177-224` leaves the numerical source data as
  unconstrained structure fields, so the requested `0.99008 K` does not
  follow.
- `problem_IPhO_2026_4_B_1.lean:178-184` constructs a constant record;
  `problem_IPhO_2026_4_C_1.lean:269-270` constructs an invented analytic
  record; and `problem_IPhO_2026_4_C_5.lean:311-318` selects its plotting
  tolerance after seeing the total residual.

## Verification and reviewer provenance

The answer set was produced by Kimi K3 at maximum reasoning effort. The 41
modules and aggregate import were compiled after completion. The numerical
grade is a direct audit of the formal theorem statements and hypotheses
against the official answers and point allocations; a separate model review
was not required for this submission.

The grading pass did not alter the submitted Lean answers. It compared their
actual theorem statements and hypotheses with the official requested results;
commentary alone was not counted as a proof.
