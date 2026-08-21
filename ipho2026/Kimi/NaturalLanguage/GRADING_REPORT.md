# IPhO 2026 Kimi K3 Max natural-language theory grading audit

Date: 2026-08-21 UTC

## Verdict

Estimated theory score: **30.00 / 30.00 = 100%**.

This is a source-level audit against the official IPhO 2026 solutions and
itemized marking schemes, not an official jury adjudication. Credit was
assigned only for reasoning and results actually present in the submitted
Markdown files.

| Problem | Score | Accuracy |
|---|---:|---:|
| Theory 1 | 10.00 / 10.00 | 100% |
| Theory 2 | 10.00 / 10.00 | 100% |
| Theory 3 | 10.00 / 10.00 | 100% |
| **Theory total** | **30.00 / 30.00** | **100%** |

## Official grading sources

- [Theory 1 official solution](https://cdn.phoxiv.org/olympiads/ipho/2026/T1/solution.pdf)
- [Theory 2 official solution](https://cdn.phoxiv.org/olympiads/ipho/2026/T2/solution.pdf)
- [Theory 3 official solution](https://cdn.phoxiv.org/olympiads/ipho/2026/T3/solution.pdf)
- [Theory 1 marking scheme](https://huggingface.co/datasets/humanfia-lab/IPHO2026/resolve/main/ipho_2026_source/text/T1_marking_scheme.txt)
- [Theory 2 marking scheme](https://huggingface.co/datasets/humanfia-lab/IPHO2026/resolve/main/ipho_2026_source/text/T2_marking_scheme.txt)
- [Theory 3 marking scheme](https://huggingface.co/datasets/humanfia-lab/IPHO2026/resolve/main/ipho_2026_source/text/T3_marking_scheme.txt)

## Detailed ledger

### Theory problem 1 — 10.00 / 10.00

| Part | Pts | Assessment | Grade |
|---|---:|---|---:|
| 1-A1 | 3.0 | Correctly identifies weight, buoyancy, the uniform excess pressure, face areas and centroids; balances the two pressure torques against the effective-weight torque; obtains `a = Δh/(2√2) = 0.4985 m ≈ 0.50 m` with units. Every marking-scheme element is present. | 3.0 |
| 1-B1 | 1.0 | Uses the correct two-body energy and angular momentum, recognizes the initial point as an apsis, selects the second turning point, and obtains `r_max = (1600/9)a₀ ≈ 178a₀`. | 1.0 |
| 1-B2 | 2.5 | Finds positive energy, eccentricity `ε=3.5`, semi-latus rectum `450a₀`, and the asymptote angle `16.6°`. The official solution writes the corresponding directed deflection as `−16.60°`; the question asks for the angle *between* two vectors, for which the submitted unsigned magnitude is the conventional answer, so no credit is deducted. | 2.5 |
| 1-C1 | 2.5 | Gives momentum and energy conservation, the quadratic in fragment momentum, the discriminant condition, the quadratic in photon energy, the physical low-energy root, and the correct exact and expanded threshold. It also correctly identifies that for `θ>π/2` the threshold is the `p→0` boundary (the same boundary reached at `θ=π/2`), satisfying the marking scheme's small backscattering item. | 2.5 |
| 1-C2 | 1.0 | Expands through the required recoil correction and obtains `ℏω_min−ΔU = 2.03×10⁻¹¹ eV`, with the correct unit and an exact-expression cross-check. | 1.0 |

### Theory problem 2 — 10.00 / 10.00

| Part | Pts | Assessment | Grade |
|---|---:|---|---:|
| 2-A1 | 1.5 | Correctly derives the constant angular step between reflections, the escape condition, and `x_N = R cos(π/(2N+1))`, including low-`N` and limiting checks. | 1.5 |
| 2-B1 | 2.0 | Applies reflection geometry and the tangent-ray condition to obtain `a = R sinθ_max − (R/2)sin(2θ_max)`, hence `α=R`, `β=−R/2`. | 2.0 |
| 2-B2 | 1.5 | Correctly computes `P₀=2aLI`, accounts for direct and once-reflected flux without double counting, obtains `P=2RLI sinθ_max`, and hence `P/P₀=1/(1−cosθ_max)`. | 1.5 |
| 2-B3 | 0.5 | Uses `P/P₀=5` to get `cosθ_max=4/5` and `a=0.12 m=12 cm`, with correct units. | 0.5 |
| 2-C1 | 0.5 | Obtains the official line coefficients `m_A=cot(2θ)` and `b_A=R/(2cosθ)`. | 0.5 |
| 2-C2 | 2.0 | Correctly constructs ray B and expands both slope and intercept to first order in `Δθ`, with all official coefficients. | 2.0 |
| 2-C3 | 1.0 | Sets up the intersection and takes the neighboring-ray limit correctly, obtaining `X_c=R sin³θ` and `Y_c=(R/2)(3cosθ−2cos³θ)`, algebraically identical to the official form. | 1.0 |
| 2-C4 | 1.0 | Performs the small-angle expansion and identifies `u=R/2`, `v=(3/4)R^(1/3)`, and `p/q=2/3`. The additional next-order audit is also correct. | 1.0 |

### Theory problem 3 — 10.00 / 10.00

| Part | Pts | Assessment | Grade |
|---|---:|---|---:|
| 3-A1 | 0.2 | Uses Ampère's law and `V=2πRA` to obtain `H=NIA/V`. | 0.2 |
| 3-A2 | 0.6 | Uses the linked flux and opposing induced emf to derive `dW_emf=VH dB`, with the correct sign interpretation. | 0.6 |
| 3-A3 | 0.2 | Subtracts the vacuum-field work and uses `dB=μ₀(dH+dM)` to obtain `dW=μ₀VH dM`. | 0.2 |
| 3-B1 | 1.5 | Applies the first law, constant-temperature internal energy, the equation of state and the field integral to obtain `Q=−μ₀nK(H_f²−H_i²)/(2T)`. | 1.5 |
| 3-B2 | 1.5 | Correctly treats the process as adiabatic, separates and integrates the differential relation, and obtains the official square-root temperature law. | 1.5 |
| 3-C1 | 0.2 | Correctly labels `T_c`, `T_h`, both isotherms and both adiabats, including the directions of `Q_c` and `Q_h`. | 0.2 |
| 3-C2 | 1.5 | Uses the two adiabatic relations (and independently the Carnot heat identity) to derive `M₁=√(M₂²+M₄²−M₃²)`. | 1.5 |
| 3-C3 | 0.8 | Computes the helium mass and heat capacity, the cold-isotherm heat `Q_c≈0.129 J`, and `T_final≈0.990 K`, agreeing with the official `0.99008 K` well within the `0.001 K` tolerance and with correct units. | 0.8 |
| 3-C4 | 2.0 | Writes the differential Carnot work relation, uses constant input power, separates variables, integrates with the correct limits and obtains the official logarithmic cooling-time formula. | 2.0 |
| 3-C5 | 1.5 | Relates total work to `Pt`, total extracted heat to `C_c(T₀−T)`, and obtains the official cumulative COP expression. | 1.5 |

## Review notes

- All 23 theory subparts are answered, and every official requested final
  result is present with an adequate derivation.
- The earlier RLCR review correction in T2-C4 is reflected in the submitted
  file: the exact `θ⁴` coefficient and the leading eliminated-series error
  are now correct. These checks are beyond what is required for full credit.
- The earlier RLCR review correction in T3-C4 changes only a positivity
  cross-check; the final cooling-time formula was already correct and the
  repaired inequality is valid.
- This post-completion grading pass did not modify the submitted answers.
  Official answer material was introduced only for grading after the three
  answer-blind Humanize runs had completed.
