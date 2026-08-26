# IPhO 2026 GPT-5.6 Sol natural-language theory grading audit

Date: 2026-08-26 UTC

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
| 1-A1 | 3.0 | Identifies weight, buoyancy, the uniform pressure difference, the opening area and lever arms; balances the signed pressure and effective-weight torques; obtains `a = Δh/(2√2) = 0.4985 m ≈ 0.499 m` with units and a threshold-direction check. | 3.0 |
| 1-B1 | 1.0 | Reduces the equal-mass problem correctly, evaluates the negative energy, recognizes the initial point as a turning point, solves for both roots, and selects `r_max = (1600/9)a₀ ≈ 177.8a₀`. | 1.0 |
| 1-B2 | 2.5 | Finds positive energy, `L = 15ℏ`, eccentricity `ε = 7/2`, and semi-latus rectum `450a₀`; selects the future clockwise asymptote and reports the requested angle magnitude `16.6°` while retaining the signed direction `−16.6°`. | 2.5 |
| 1-C1 | 2.5 | Uses momentum and energy conservation and an equivalent constrained-minimization/completing-the-square argument to obtain the threshold condition. It derives both photon-energy roots, selects the lower physical branch by its infinite-mass limit, checks the discriminant and dimensions, and handles the forward, right-angle, and backward-angle domains. | 2.5 |
| 1-C2 | 1.0 | Expands through the required recoil correction, controls the omitted order, and obtains `ℏω_min−ΔU = 2.03×10⁻¹¹ eV`, with correct units and a cancellation-safe exact check. | 1.0 |

### Theory problem 2 — 10.00 / 10.00

| Part | Pts | Assessment | Grade |
|---|---:|---|---:|
| 2-A1 | 1.5 | Derives the constant angular step between reflections and the limiting escape condition, obtaining `x_N = R cos[π/(2N+1)]` with low-`N` and limiting checks. | 1.5 |
| 2-B1 | 2.0 | Applies the reflection geometry and tangent condition to obtain `a = R sinθ_max − (R/2)sin(2θ_max)`, hence `α=R` and `β=−R/2`. | 2.0 |
| 2-B2 | 1.5 | Computes `P₀`, accounts for direct and reflected flux without double counting, obtains `P`, and derives `P/P₀ = 1/(1−cosθ_max)`. | 1.5 |
| 2-B3 | 0.5 | Uses the previous result to get `cosθ_max=4/5` and `a=0.12 m=12.0 cm`, with correct units. | 0.5 |
| 2-C1 | 0.5 | Obtains the official reflected-line coefficients `m_A=cot(2θ)` and `b_A=R/(2cosθ)`. | 0.5 |
| 2-C2 | 2.0 | Constructs the neighboring reflected ray and correctly expands both its slope and intercept to first order in `Δθ`. | 2.0 |
| 2-C3 | 1.0 | Solves the finite neighboring-line intersection before taking the limit, obtaining `X_c=R sin³θ` and `Y_c=(R/2)cosθ(1+2sin²θ)`, including the symmetric branch. | 1.0 |
| 2-C4 | 1.0 | Performs the controlled small-angle expansion and identifies `u=R/2`, `v=(3/4)R^(1/3)`, and `p/q=2/3`, with correct dimensions and remainder order. | 1.0 |

### Theory problem 3 — 10.00 / 10.00

| Part | Pts | Assessment | Grade |
|---|---:|---|---:|
| 3-A1 | 0.2 | Uses Ampère's law and `V=2πRA` to obtain `H=NIA/V`. | 0.2 |
| 3-A2 | 0.6 | Uses the opposing induced emf and Faraday's law to derive the source work `dW_emf=VH dB`, with the correct sign convention. | 0.6 |
| 3-A3 | 0.2 | Subtracts the vacuum-field work and uses `dB=μ₀(dH+dM)` to obtain the material work `dW=μ₀VH dM`. | 0.2 |
| 3-B1 | 1.5 | Applies the first law, the isothermal internal-energy condition, and the equation of state to obtain `Q=μ₀nK(H_i²−H_f²)/(2T)`. | 1.5 |
| 3-B2 | 1.5 | Treats the process as adiabatic, derives and separates the differential relation, and obtains the official square-root temperature law with limiting checks. | 1.5 |
| 3-C1 | 0.2 | Correctly labels `T_c`, `T_h`, both isotherms and both adiabats, including the directions of `Q_c` and `Q_h`. | 0.2 |
| 3-C2 | 1.5 | Uses the two adiabatic invariants and the cycle relations to derive `M₁=√(M₂²+M₄²−M₃²)`. | 1.5 |
| 3-C3 | 0.8 | Computes the salt volume, helium mass and heat capacity, `Q_c≈0.12935 J`, and `T_final≈0.99005 K`, within the official tolerance and with correct units. | 0.8 |
| 3-C4 | 2.0 | Writes the differential Carnot work balance, relates work to constant input power and heat to the changing cold temperature, separates variables, and integrates to the official logarithmic cooling-time formula. | 2.0 |
| 3-C5 | 1.5 | Relates total work to `Pt` and total extracted heat to `C_c(T₀−T)`, then obtains the official cumulative COP expression with differential and zero-drop checks. | 1.5 |

## Review notes

- All 23 theory subparts are answered, and every marking-scheme result is
  supported by an adequate derivation.
- The answer-blind RLCR review corrected one T1-C2 presentation detail before
  terminal approval: a ten-digit cross-check had used a more precise atomic
  mass conversion than the rounded value printed in the solution. The final
  file reports the reproducible `2.02967×10⁻¹¹ eV`; the boxed
  three-significant-figure answer was unchanged.
- T2 and T3 required no physics corrections after their complete drafts.
- Official solution and marking material was available only to this separate
  grading audit, never to the answer-generating worker environments. The
  grading pass did not modify the submitted answers.
