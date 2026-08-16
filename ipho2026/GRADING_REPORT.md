# IPhO 2026 official-solution grading audit

Date: 2026-08-16 UTC

## Verdict

Estimated score: **47.45 / 50.00 = 94.9%**.

This is a source-level grading estimate, not an official jury adjudication. The
rubric gives full credit when the proved Lean predicate entails the official
formula/result for the same physical inputs, even if the answer-blind target
signature leaves the witness implicit. Partial credit is used when the central
derivation is correct but the submitted formal result omits a requested
orientation, numerical specialization, or experimental uncertainty treatment.

Summary:

- 32 of 41 parts: full agreement.
- T1-B2: correct scattering magnitude, but the final predicate discards the
  orientation and returns the unsigned angle instead of the official signed
  angle.
- T3-C3: correct energy-balance formula, but the source predicate leaves
  vacuum permeability unconstrained, so it does not force the official
  numerical temperature.
- E-A1, E-A4, E-A5, E-B5, E-B6, E-C6, and E-C7: correct central-value
  inference, but no formal uncertainty propagation/enclosure corresponding to
  the uncertainty reported in the official solution.

## Official documents and scoring basis

- [Official theory solution PDF](https://ipho.physics.bme.hu/pdfs/ipho_probs/2026/T_solution.pdf),
  SHA-256 `df68b4deb23c26b88cd697dd47d3df38c0dfd5f69201de38ef9baf7a5dd1a7a6`.
- [Official experimental problem PDF](https://ipho.physics.bme.hu/pdfs/ipho_probs/2026/E.pdf).
- [Official experimental solution PDF](https://ipho.physics.bme.hu/pdfs/ipho_probs/2026/E_solution.pdf),
  SHA-256 `544def93580d3691f488347f44a3eade20f777379ddade4fb50905e11d8663f9`.
- [Japanese Physics Olympiad official experimental-solution mirror](https://www.jpho.jp/international/media-download/1043/f97342cc1889ce9a/PDF/).
  Its extracted seven-page text is byte-identical to the BME-hosted solution.

The experimental solution PDF retains an earlier ordering/point allocation in
several labels. Part identities and point values below follow the final official
experimental exam paper—the same mapping used by the 18 project source
records—while expected values and methods come from the solution PDF. These
final exam weights sum to 20 points.

## Detailed ledger

### Theory problem 1 — 9.50 / 10.00

| Part | Pts | Official result | Lean result | Grade |
|---|---:|---|---|---:|
| 1-A1 | 3.0 | `a = Δh/(2√2) = 0.50 m` for `Δh=1.41 m` | The torque proof derives `a = Δh·√2/4`, exactly equivalent. | 3.0 |
| 1-B1 | 1.0 | `r_max = (1600/9) a₀` | The turning polynomial is explicitly factored with roots `100` and `1600/9`, and the larger attained root is proved maximal. | 1.0 |
| 1-B2 | 2.5 | Signed angle `−16.60°` relative to the initial positron direction | The orbit derivation fixes the correct future direction and hence the correct magnitude `16.60°`, but `CanonicalUnsignedAngle` retains only cosine and constrains the answer to `[0,π]`; the signed cross component is not used in `AsymptoticAngleDegreesSolution`. | **2.0** |
| 1-C1 | 2.5 | Lower physical root of the official quadratic, with the `θ≥90°` saturation | The conservation boundary is the same quadratic; `max(cos θ,0)` implements the official acute/nonacute branch split. | 2.5 |
| 1-C2 | 1.0 | `ℏω_min−ΔU = 2.03×10⁻¹¹ eV` | Exact ozone specialization and the same lower-root excess are proved; the theorem additionally gives a tight interval from the printed atomic-mass precision. | 1.0 |

Required correction: replace the unsigned final-angle predicate in
`problem_IPhO_2026_1_B_2.lean` by an oriented-angle relation using both the dot
and planar-cross components. The official signed answer is negative in the
source orientation.

### Theory problem 2 — 10.00 / 10.00

| Part | Pts | Official result | Lean result | Grade |
|---|---:|---|---|---:|
| 2-A1 | 1.5 | `x_N = R cos(π/(2N+1))` | The unique threshold witness is exactly `R * cos (π/(2N+1))`. | 1.5 |
| 2-B1 | 2.0 | `α=R`, `β=−R/2` | The canonical coefficient pair is explicitly constructed with these values. | 2.0 |
| 2-B2 | 1.5 | `P/P₀ = 1/(1−cos θ_max)` | The direct/one-reflection aperture partition proves the same ratio. | 1.5 |
| 2-B3 | 0.5 | `a=12 cm` for `R=1 m` and `P=5P₀` | The fivefold residual is `1/(1−cos θ)−5`; the tangent relation uniquely fixes the same `0.12 m` radius and centimetre report. | 0.5 |
| 2-C1 | 0.5 | `m_A=cot(2θ)`, `b_A=R/(2cos θ)` | The unique reflected-line coefficients reduce to exactly these expressions. | 0.5 |
| 2-C2 | 2.0 | `m_B=cot(2θ)−2csc²(2θ)Δθ+o(Δθ)` and `b_B=(R/(2cos θ))(1+tan θ·Δθ)+o(Δθ)` | The canonical coefficient derivative jet proves these first-order expansions with explicit little-o remainders. | 2.0 |
| 2-C3 | 1.0 | `(X_C,Y_C)=(R sin³θ, (R/2)cosθ(2−cos2θ))` | The unique forward differential-caustic point has the same coordinates. | 1.0 |
| 2-C4 | 1.0 | `u=R/2`, `v=(3/4)R^(1/3)`, `p/q=2/3` | The normalized asymptotic has offset `R/2`, amplitude `3/4` at radius scales, and exponent `2/3`; unnormalizing gives the official `v`. | 1.0 |

### Theory problem 3 — 9.80 / 10.00

| Part | Pts | Official result | Lean result | Grade |
|---|---:|---|---|---:|
| 3-A1 | 0.2 | `H=NIA/V` | Ampère balance plus `V=Aℓ` proves the same field. | 0.2 |
| 3-A2 | 0.6 | `dW_emf=VH dB` | The linked-flux, Faraday–Lenz, source-emf, and Ampère equations reduce to the same work increment. | 0.6 |
| 3-A3 | 0.2 | `dW=μ₀VH dM` | Vacuum work is subtracted from total source work and the constitutive derivative gives the official material work. | 0.2 |
| 3-B1 | 1.5 | `Q=−μ₀nK(H_f²−H_i²)/(2T)` | The fixed-temperature path-independent heat integral is exactly this expression. | 1.5 |
| 3-B2 | 1.5 | `ΔT=T_i(√((λ+μ₀KH_f²)/(λ+μ₀KH_i²))−1)` | The proved logarithmic endpoint potential is analytically equivalent to the official square-root relation. | 1.5 |
| 3-C1 | 0.2 | Correct `T_h,T_c,Q_h,Q_c` process annotation | The unique diagram annotation fixes the two isotherms, two adiabats, and heat directions. | 0.2 |
| 3-C2 | 1.5 | `M₁=√(M₂²−M₃²+M₄²)` | The composed adiabatic invariant proves the same squared relation and selects the unique positive magnetization. | 1.5 |
| 3-C3 | 0.8 | `T_f≈0.99008 K` (official rounding) | The exact cold-heat and helium energy-balance relation is correct, but `OneCycleSourceData.MatchesStatement` intentionally places no coordinate condition on `vacuumPermeability`. Thus the theorem does not determine the official numerical value until an external `μ₀` is supplied. | **0.6** |
| 3-C4 | 2.0 | `t=(C_cT_h/P)(ln(T₀/T)−(T₀−T)/T_h)` | The proved integral evaluates directly to the same formula. | 2.0 |
| 3-C5 | 1.5 | `COP=(T_h ln(T₀/T)/(T₀−T)−1)⁻¹` | The unique cumulative heat/work ratio is equivalent to this expression. | 1.5 |

Required correction: constrain the C3 source vacuum permeability to the stated
SI value (or introduce and bind a shared physical constant), then prove the
requested numerical enclosure/rounding result.

### Experimental problem — 18.15 / 20.00

For record/graph questions, the official tables are representative measurements,
not universal constants. Parameterizing an externally supplied run is therefore
accepted as full credit when the occurrence-preserving table or graph is exactly
constructed. Deductions below concern missing uncertainty treatment, not the
absence of hard-coded sample readings.

| Part | Pts | Official result/method | Lean result | Grade |
|---|---:|---|---|---:|
| 4-A1 | 0.4 | Representative inventory `m=0.94±0.02 g`, `n=3.24±0.7 mmol`, `N=(1.95±0.05)×10²¹` | Correct typed density→mass→amount→molecule chain for the measured geometry; no uncertainty propagation. | **0.30** |
| 4-A2 | 1.0 | Record `P(T)` | Exact same-occurrence pressure–temperature table from calibrated observations. | 1.0 |
| 4-A3 | 0.9 | Plot `P` against `T` | Exact indexed graph, preserving order and multiplicity. | 0.9 |
| 4-A4 | 1.0 | OLS/graph result `R=8.4±0.4 J mol⁻¹ K⁻¹` | Correct OLS slope law `nR=V·slope`; no uncertainty result. | **0.80** |
| 4-A5 | 0.7 | `β₀=0.0034±0.0007 K⁻¹` | Correct fitted relation `β₀=slope/P₀`; no uncertainty result. | **0.50** |
| 4-B1 | 1.0 | Record `H(T)` | Exact typed record from the external run. | 1.0 |
| 4-B2 | 1.0 | Plot `H(T)` | Exact occurrence-preserving graph. | 1.0 |
| 4-B3 | 0.5 | OLS extrapolation `H₀≈5.9 cm` at `273.15 K` | Exactly the unweighted OLS evaluation at `273.15 K`. | 0.5 |
| 4-B4 | 1.0 | `P_v=P_atm(1−H₀T/(HT₀))` | The per-observation theorem proves exactly this height formula with calibrated SI quantities. | 1.0 |
| 4-B5 | 4.0 | Plot `ln(P_v/P_ref)` vs `1/T`; slope `−4700±200 K`; `ΔH_v=39±2 kJ/mol` | Correct transformed graph, negative OLS slope, and `ΔH_v=−R·slope`; no slope/latent-heat uncertainty. | **3.50** |
| 4-B6 | 0.5 | `L_v=ΔH_v/M_w=2190±110 kJ/kg`, with explicit uncertainty | Correct typed molar-to-mass conversion with `M_w=18.02 g/mol`; no uncertainty propagation. | **0.35** |
| 4-C1 | 1.0 | Record `(t,T_IC,T_OC)` | Exact strictly time-ordered paired record. | 1.0 |
| 4-C2 | 1.0 | Plot both temperature traces | Exact two-trace indexed graph. | 1.0 |
| 4-C3 | 0.7 | Plot `T_OC−T_IC` against each temperature | Exact two occurrence-matched difference graphs. | 0.7 |
| 4-C4 | 1.1 | Extrapolated equilibrium `T_eq≈53°C` | Correct common-zero inference from the two OLS traces and the stated energy conservation. | 1.1 |
| 4-C5 | 1.0 | Plot inner finite-difference rate against adjacent average temperature difference | Exact forward-difference graph with the official adjacency convention. | 1.0 |
| 4-C6 | 1.6 | `R_Th=1/(c₀m·slope)=1.17±0.03 K/W` | Correct raw-rate OLS, full inner-water heat capacity, and reciprocal resistance law; no uncertainty result. | **1.30** |
| 4-C7 | 1.6 | `λ=ln(r₂/r₁)/(2πhR_Th)=0.25±0.01 W/(m·K)`, with uncertainty propagation | Correct integrated radial Fourier law, sign convention, geometry bridge, and unique conductivity; no uncertainty propagation. | **1.20** |

Experimental uncertainty completion would require typed uncertain inputs or
certified intervals for measured lengths, masses, temperatures, and fitted
coefficients, followed by enclosure/error-propagation theorems for the seven
flagged outputs.

## Totals

| Section | Score |
|---|---:|
| Theory 1 | 9.50 / 10.00 |
| Theory 2 | 10.00 / 10.00 |
| Theory 3 | 9.80 / 10.00 |
| Experiment | 18.15 / 20.00 |
| **Overall** | **47.45 / 50.00 (94.9%)** |

## Trust and mutation boundary

This audit was read-only with respect to all Lean submissions and the immutable
blank `Original` archive. It used the already verified completion state (all
57 modules elaborating, all proof closures free of `sorryAx`) and compared the
mathematical content against the official solution documents. No Lean source,
blueprint, contract, or `Original` file was changed by this grading pass.
