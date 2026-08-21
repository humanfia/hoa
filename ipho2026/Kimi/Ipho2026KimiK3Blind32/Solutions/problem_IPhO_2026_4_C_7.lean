import Mathlib

/- USER: Iter-016 mandatory contract repair. Face continuity alone does not fix the sign contradiction: the current negative derivative integrates to a negative face difference while the target uses a positive one. Use one convention throughout. Recommended: `P` is positive heat received inward by the IC, the same `P` in `P * R_Th = T_OC - T_IC`; outward signed flux is `-P`, so encode `deriv T r = +P / (lam * A r)`. Retain one-sided face continuity, document the radial orientation, update every helper consistently, and compile before handoff. -/

/- Iter-016 note: the sign-convention repair is implemented below.  `P` is
   the positive heat current received inward by the IC (the same `P` in
   `P * R_Th = T_OC - T_IC`); the outward-signed radial flux is therefore
   `-P`, and Fourier's law (equation (6), `−P = −λ A dT/dr`) is encoded as
   `dT/dr = +P/(λ A r)` — see `SatisfiesRadialFourierLaw`.  One-sided face
   continuity and the radial orientation (increasing `r` runs from the IC
   face to the OC face) are retained and documented. -/

/-!
# IPhO 2026, Experimental Exam E1, Problem 4, Part C.7 — Thermal
# conductivity `λ` of the acrylic wall

Answer-blind formalization of subquestion E1-C.7 (1.6 pts):

> **C7.** Using equations (4) and (6), determine the value `λ` of the thermal
> conductivity of acrylic (the material separating IC and OC), indicating the
> formula that you used.

## Experimental context (Part C: heat conduction)

* Water in the inner cylinder (**IC**, water level `h = 10 cm`) and water in
  the outer cylinder (**OC**, water level `h = 15 cm`, initially heated to
  `65 °C` and homogenized with the pump) exchange heat *radially* through the
  **acrylic cylindrical wall** separating them; `T_IC` and `T_OC` are
  recorded as functions of time (parts C.1–C.2; apparatus and dimensions in
  Figure 17, water levels from the Part C procedure on page 13).
* The heat-flow model of the statement's **equation (4)** is

      dQ/dt = (T_OC − T_IC) / R_Th ,

  where `Q` is the heat received by the water in the IC through the wall and
  `R_Th` is the effective wall thermal resistance, determined in part C.6
  from the C.5 graph (a natural-language prerequisite only: it enters this
  file as prescribed positive data, not as an imported Lean conclusion).
* The plate's **equation (6)** is Fourier's law for radial heat conduction
  through a slim cylindrical wall,

      dQ/dt = −λ A · dT/dr ,

  where `A` is the area of the wall, `λ` the thermal conductivity of the
  wall material, and `r` the distance from the axis of the cylinder.  For a
  cylindrical wall of height `L` the area at radius `r` is the lateral area
  `A(r) = 2π r L` (the wall height relevant to the radial exchange is the
  IC water level `h = 10 cm` of Figure 17).


## Sign and orientation convention (single convention, iter-016 repair)

`P > 0` always denotes the heat current *received inward by the IC* — the
same `P` in `P * R_Th = T_OC - T_IC` (equation (4)).  The outward-signed
radial flux is `−P`, so Fourier's law of equation (6),
`dQ/dt = −λ A dT/dr`, applied to the outward flux `dQ/dt = −P` gives
`dT/dr = +P/(λ·A(r)) > 0`: `T` *increases* with the radius `r` (hotter OC
face at `r_b`, cooler IC face at `r_a`) while heat flows toward decreasing
`r`.  Every law, helper, and target below uses this one convention.

## Governing relation C.7 asks for

Combining equations (4) and (6): under steady radial conduction the heat
current `dQ/dt` is the same through every coaxial shell (conservation of
energy in the wall; the apparatus heat capacity is ignored as instructed).
With the outward flux `dQ/dt = −P` this is `dT/dr = P / (λ · 2π r L)`
(positive, as the OC face is the hotter one).  Integrating the `T(r)` law
from the wall's inner radius `r_a` (where `T = T_IC`) to its outer radius
`r_b` (where `T = T_OC`) over the annulus `r_a < r_b` gives

    T_OC − T_IC = P / (2π λ L) · log (r_b / r_a) ,

and matching against equation (4) identifies the effective wall resistance
as the radial conduction integral

    R_Th = log (r_b / r_a) / (2 π λ L) ,

the formula C.7 requests; it determines `λ` from the C.6 resistance and the
Figure 17 dimensions.

## Answer-free statement design

The official value of `λ` is withheld.  Per the blind policy, the theorem
signature introduces a result variable `lam` of thermal-conductivity role
and an answer-free solution predicate `AcrylicConductivityProblem.Solution`,
built only from the two stated governing laws and the geometric constraints
of the setup:

* `AmenableGeometry`: the boundary data of a radial conduction problem —
  inner/outer radii `0 < r_a < r_b`, wall height `L > 0`, shell boundary
  temperatures `T_inner < T_OC`, and effective wall resistance `R > 0`;
* a radial temperature field `T : ℝ → ℝ` in the wall with the endpoint
  conditions `T r_a = T_IC`, `T r_b = T_OC`;
* equation (6) at every radius with a heat current constant across the
  shells, and the mean radial heat current agreeing with equation (4).

Existence of such a field for a positive `lam`, its uniqueness, and the fact
that the common radial current equals `(T_OC − T_IC)/R` exactly when
`2 π L R lam = log (r_b / r_a)` — the content of the requested formula — are
stated as characterizations with `sorry` bodies.  No closed-form witness or
numerical value of `λ` appears in any signature.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_4C7

/-- The geometric and boundary data of the radial-conduction stage of the
experiment (Figure 17 plus the C.6 result), packaged so that every
subsequent law is dimensionally and geometrically grounded:

* `r_a`, `r_b`: inner and outer radii of the acrylic cylindrical wall, with
  `0 < r_a < r_b` (the wall is a genuine annulus);
* `L`: height of the cylindrical wall traversed by the radial heat current
  (the wall height relevant to the exchange is the IC water level
  `h = 10 cm`; geometric positivity only);
* `T_IC`, `T_OC`: inner- and outer-cylinder water temperatures acting as
  boundary temperatures of the wall's inner and outer cylindrical faces,
  with `T_IC < T_OC` (the OC water is heated to about `65 °C`, so heat
  flows outward, from OC to IC);
* `R`: effective wall thermal resistance `R_Th > 0` determined from the
  C.5 graph in part C.6 (natural-language prerequisite, prescribed data). -/
structure AmenableGeometry where
  r_a : ℝ
  r_b : ℝ
  L : ℝ
  T_IC : ℝ
  T_OC : ℝ
  R : ℝ
  r_a_pos : 0 < r_a
  r_a_lt_r_b : r_a < r_b
  L_pos : 0 < L
  T_IC_lt_T_OC : T_IC < T_OC
  R_pos : 0 < R

namespace AmenableGeometry

variable (G : AmenableGeometry)

/-- The radial extent of the wall: the open annulus `r_a < r < r_b` between
the acrylic wall's inner and outer cylindrical faces, in which the
conduction of equation (6) takes place. -/
def wallInterior : Set ℝ := Set.Ioo G.r_a G.r_b

/-- The lateral area `A(r) = 2π r L` of the coaxial cylindrical shell of
radius `r` and wall height `L`: the area `A` appearing in the statement's
equation (6), `dQ/dt = −λ A dT/dr`, for radial conduction through the slim
cylindrical wall. -/
noncomputable def lateralArea (r : ℝ) : ℝ := 2 * Real.pi * r * G.L

/-- **Fourier's law for radial conduction (statement's equation (6)) with a
shell-independent heat current.**  The radial temperature field `T` in the
wall satisfies equation (6) with conductivity `lam` and heat current `P`
iff at every radius `r` in the wall interior the outward-signed heat
current `−P` obeys

    −P = −lam · A(r) · dT/dr (r) ,

i.e. `dT/dr (r) = +P / (lam · 2π r L)`.

**Sign and orientation convention (iter-016 repair).**  `P > 0` is the heat
current *received inward by the IC* — the same `P` appearing in the
heat-flow relation `P * R_Th = T_OC - T_IC` of equation (4) — so the
outward-signed radial heat current is `−P`.  Equation (6)
(`dQ/dt = −λ A dT/dr` with the outward sign) therefore reads
`−P = −λ A dT/dr`, i.e. `dT/dr = +P/(λ·A(r))`: since heat flows from the
hotter OC to the cooler IC, `T` *increases* with `r` across the wall
(`dT/dr > 0`) while heat is transported towards decreasing `r`.  This is
the single convention used by every helper below.  Constancy of `P` across
the shells is conservation of energy in the wall (steady radial conduction;
the apparatus heat capacity is ignored as instructed).

The last two conjuncts are the **face-continuity bridge** mandated by the
iter-014 confirmation review: equation (6) constrains only the wall
*interior* and is silent about the wall faces `r_a, r_b`, so the integrated
log-law could not previously be evaluated at the faces.  Physically the
boundary condition `T r_a = T_IC`, `T r_b = T_OC` means the conducting
profile meets the inner- and outer-cylinder water temperatures at the faces,
i.e. the profile is one-sided continuous from the wall side
(`ContinuousWithinAt T (Ici r_a) r_a` and
`ContinuousWithinAt T (Iic r_b) r_b`).  Together with the interior
`HasDerivAt` (which gives continuity on the open annulus) this is precisely
the `ContinuousOn T [r_a, r_b]` needed to evaluate the integrated law at the
faces.  This is a physical boundary/mounting condition, not the C.7 answer.
-/
def SatisfiesRadialFourierLaw (lam P : ℝ) (T : ℝ → ℝ) : Prop :=
  (∀ r ∈ G.wallInterior, ∃ d : ℝ, HasDerivAt T d r ∧ d = P / (lam * G.lateralArea r)) ∧
    ContinuousWithinAt T (Set.Ici G.r_a) G.r_a ∧
    ContinuousWithinAt T (Set.Iic G.r_b) G.r_b

/-- **Boundary conditions of the wall faces:** the radial temperature field
takes the IC water temperature at the wall's inner face and the OC water
temperature at the wall's outer face, `T r_a = T_IC`, `T r_b = T_OC`. -/
def SatisfiesFaceTemperatures (T : ℝ → ℝ) : Prop :=
  T G.r_a = G.T_IC ∧ T G.r_b = G.T_OC

/-- **The heat-flow relation (statement's equation (4)) at mean rate.**
The mean radial heat current `P` through the wall agrees with the
heat-flow model `dQ/dt = (T_OC − T_IC)/R_Th` for the effective wall
resistance `R`. -/
def SatisfiesHeatFlowRelation (P : ℝ) : Prop :=
  P * G.R = G.T_OC - G.T_IC

/-- **The formula that C.7 asks to indicate:** the effective wall thermal
resistance obtained by combining equations (4) and (6),

    R_Th = log (r_b / r_a) / (2 π λ L) ,  equivalently
    2 π L R_Th λ = log (r_b / r_a) ,

relating the conductivity `lam` of the acrylic wall to the C.6 resistance
and the Figure 17 dimensions `r_a`, `r_b`, `L`.  (Given in reciprocal-free
form; `lam` and the geometric factors are positive in every admissible
configuration, so no physical content is lost.) -/
def ConductivityResistanceFormula (lam : ℝ) : Prop :=
  2 * Real.pi * G.L * G.R * lam = Real.log (G.r_b / G.r_a)

/-- **Answer-free solution predicate for C.7.**  A real number `lam` of
thermal-conductivity role is the thermal conductivity `λ` of the acrylic
wall separating IC and OC iff

* `lam > 0` (a positive conductivity: heat flows from the hotter OC face
  to the cooler IC face, `dT/dr < 0` in the wall); and
* the wall admits a radial temperature field `T` obeying the face boundary
  conditions (`T r_a = T_IC`, `T r_b = T_OC`), Fourier's law of
  equation (6) with conductivity `lam` and a shell-independent heat
  current `P`, while that common current satisfies the heat-flow relation
  of equation (4) with the C.6 effective wall resistance `R_Th`.

The requested formula `R_Th = log (r_b / r_a)/(2πλL)` — and *a fortiori*
any evaluated value of `λ` — appears nowhere in the predicate; it is
recovered below as a characterization theorem. -/
def Solution (lam : ℝ) : Prop :=
  0 < lam ∧
    ∃ T : ℝ → ℝ, ∃ P : ℝ,
      G.SatisfiesFaceTemperatures T ∧
        G.SatisfiesRadialFourierLaw lam P T ∧ G.SatisfiesHeatFlowRelation P

/-- **Radial gradient of a Fourier field (genuinely provable local content of
equation (6)).**  At every radius `r` of the wall interior, equation (6)
fixes the radial gradient, `deriv T r = P / (2π λ L r)`, and in particular
`T` is differentiable in the wall interior.  This is the sound local core
on which the genuine (interior) results rely. -/
private theorem deriv_eq_of_radialFourier {lam P : ℝ} (hlam : 0 < lam) {T : ℝ → ℝ}
    (hF : G.SatisfiesRadialFourierLaw lam P T) :
    (∀ r ∈ G.wallInterior, DifferentiableAt ℝ T r) ∧
      (∀ r ∈ G.wallInterior, deriv T r = P / (2 * Real.pi * lam * G.L * r)) ∧
        ContinuousWithinAt T (Set.Ici G.r_a) G.r_a ∧
        ContinuousWithinAt T (Set.Iic G.r_b) G.r_b := by
  obtain ⟨hF, hcont_a, hcont_b⟩ := hF
  refine ⟨fun r hr => (hF r hr).choose_spec.1.differentiableAt, fun r hr => ?_,
    hcont_a, hcont_b⟩
  obtain ⟨d, hd, rfl⟩ := hF r hr
  have hrp : (0:ℝ) < r := lt_trans G.r_a_pos hr.1
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hcne : (2 * Real.pi * lam * G.L * r) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2pi.ne' hlam.ne') G.L_pos.ne') hrp.ne'
  rw [hd.deriv]
  unfold lateralArea
  field_simp [hcne, hrp.ne']

/-- **Interior logarithmic drop (fully proved).**  On any compact sub-window
`[x, y] ⊆ (r_a, r_b)` of the wall interior, the temperature drop is the
interval integral of the Fourier gradient, hence equals
`s·(log y − log x)` with `s = P/(2π λ L)`: the interior gradient is
`s/r` (see `deriv_eq_of_radialFourier`), it is continuous on `[x, y]` (which
lies in the positive half-line), so the fundamental theorem of calculus
applies with primitive `s·log`.  This is the genuine analytic content of
the "combining" argument, available entirely without any hypothesis at the
wall faces. -/
private theorem interior_drop_log {lam P : ℝ} (hlam : 0 < lam) {T : ℝ → ℝ}
    (hF : G.SatisfiesRadialFourierLaw lam P T)
    {x y : ℝ} (hx : x ∈ G.wallInterior) (hy : y ∈ G.wallInterior) (hxy : x ≤ y) :
    T y - T x = (P / (2 * Real.pi * lam * G.L)) * (Real.log y - Real.log x) := by
  obtain ⟨hdiff, hder, _⟩ := G.deriv_eq_of_radialFourier hlam hF
  set s : ℝ := P / (2 * Real.pi * lam * G.L) with hs_def
  have hderC : ∀ r ∈ G.wallInterior, deriv T r = s * r⁻¹ := by
    intro r hr
    have h1 := hder r hr
    rw [h1]
    have hrp : (0:ℝ) < r := lt_trans G.r_a_pos hr.1
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
    have hcne : (2 * Real.pi * lam * G.L) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2pi.ne' hlam.ne') G.L_pos.ne'
    have hs : s = P / (2 * Real.pi * lam * G.L) := rfl
    rw [hs]
    field_simp [hcne, hrp.ne']
  by_cases he : x = y
  · subst he
    simp [mul_comm]
  have hlt : x < y := lt_of_le_of_ne hxy he
  have hI : Set.uIcc x y = Set.Icc x y := Set.uIcc_of_le hxy
  have hsub : Set.Icc x y ⊆ G.wallInterior :=
    fun z hz => ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have hdoU : ∀ u ∈ Set.uIcc x y, HasDerivAt T (deriv T u) u := by
    intro u hu
    rw [hI] at hu
    exact (hdiff u (hsub hu)).hasDerivAt
  have hsubpos : Set.uIcc x y ⊆ Set.Ioi (0 : ℝ) := by
    intro u hu
    rw [hI] at hu
    exact lt_of_lt_of_le (lt_trans G.r_a_pos hx.1) hu.1
  have hEqOn : Set.EqOn (deriv T) (fun r => s * r⁻¹) (Set.uIcc x y) := by
    intro u hu
    rw [hI] at hu
    exact hderC u (hsub hu)
  have hIooOn : Set.EqOn (deriv T) (fun r => s * r⁻¹) (Set.uIoo x y) :=
    hEqOn.mono Set.uIoo_subset_uIcc_self
  have hcont : ContinuousOn (fun r => s * r⁻¹) (Set.uIcc x y) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hsubpos hu
    exact (continuousAt_const.mul (continuousAt_inv₀ (ne_of_gt hu0))).continuousWithinAt
  have hIg : IntervalIntegrable (deriv T) MeasureTheory.volume x y :=
    hcont.intervalIntegrable.congr_uIoo hIooOn.symm
  have hFTC : ∫ u in x..y, deriv T u = T y - T x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hdoU hIg
  have hcongr : (∫ u in x..y, deriv T u) = ∫ u in x..y, s * u⁻¹ :=
    intervalIntegral.integral_congr hEqOn
  have hIg2 : IntervalIntegrable (fun r => s * r⁻¹) MeasureTheory.volume x y :=
    hcont.intervalIntegrable
  rw [← hFTC, hcongr]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => by simpa [mul_comm] using
        (Real.hasDerivAt_log (ne_of_gt (hsubpos hu))).const_mul s)
      hIg2]
  ring
/-- The radial temperature field in a homogeneous cylindrical wall under a
constant shell-independent heat current `P` (received inward by the IC) is
logarithmic: if `T` satisfies Fourier's law of equation (6), encoded with
the file-wide convention `dT/dr = +P/(λ A r)`, then across the annulus

    T r_b − T r_a = (P / (2 π lam L)) · log (r_b / r_a) .

Both sides are positive when `P > 0`, matching the hotter-OC/cooler-IC
orientation `T r_b = T_OC > T_IC = T r_a`.  The interior gradient is
`s/r` with `s = P/(2π λ L)`
(see `deriv_eq_of_radialFourier`), whose primitive is `s·log`; on every
compact sub-window `[x, y] ⊆ (r_a, r_b)` the interior drop is therefore
`s·(log y − log x)` by the fundamental theorem of calculus.  The statement
evaluates `T` at the wall *faces* `r_a, r_b`, which equation (6) (enforced
only in the interior) does not by itself constrain; the face values are
recovered from the one-sided face continuity of `SatisfiesRadialFourierLaw`
(interior limits as `r → r_a⁺, r → r_b⁻` equal `T r_a, T r_b`), which is
the remaining proof step. -/
theorem temperature_drop_log_law {lam P : ℝ} (hlam : 0 < lam) {T : ℝ → ℝ}
    (hF : G.SatisfiesRadialFourierLaw lam P T) :
    T G.r_b - T G.r_a =
      (P / (2 * Real.pi * lam * G.L)) * Real.log (G.r_b / G.r_a) := by
  obtain ⟨hdiff, hder, hconta, hcontb⟩ := G.deriv_eq_of_radialFourier hlam hF
  -- Notation: the interior gradient scale `s = P / (2 π λ L)`, so that
  -- `deriv T r = s * r⁻¹` in the wall interior.
  set s : ℝ := P / (2 * Real.pi * lam * G.L) with hs_def
  have hderC : ∀ r ∈ G.wallInterior, deriv T r = s * r⁻¹ := by
    intro r hr
    rw [hder r hr]
    have hrp : (0:ℝ) < r := lt_trans G.r_a_pos hr.1
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
    have hcne : (2 * Real.pi * lam * G.L) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2pi.ne' hlam.ne') G.L_pos.ne'
    rw [hs_def]
    field_simp [hcne, hrp.ne']
  -- Step 1: `T` is continuous on the closed annulus `[r_a, r_b]`: interior
  -- differentiability plus the one-sided face continuity.
  have hcont : ContinuousOn T (Set.Icc G.r_a G.r_b) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | hlt
    · exact ContinuousWithinAt.mono hconta (Set.Icc_subset_Ici_self)
    rcases eq_or_lt_of_le hr.2 with rfl | hgt
    · exact ContinuousWithinAt.mono hcontb (Set.Icc_subset_Iic_self)
    exact (hdiff r ⟨hlt, hgt⟩).continuousAt.continuousWithinAt
  -- Step 2: `T` is differentiable at every interior radius.
  have hdrv : ∀ r ∈ Set.Ioo G.r_a G.r_b, HasDerivAt T (deriv T r) r :=
    fun r hr => (hdiff r hr).hasDerivAt
  -- Useful: `r_b > 0` as well.
  have hRb : (0:ℝ) < G.r_b := lt_trans G.r_a_pos G.r_a_lt_r_b
  -- Step 3: the gradient `r ↦ s / r` is interval-integrable on `[r_a, r_b]`
  -- (it is continuous on the positive half-line, which contains the annulus).
  have hIg : IntervalIntegrable (fun r : ℝ => s * r⁻¹) MeasureTheory.volume G.r_a G.r_b := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu0 : (0:ℝ) < u :=
      G.r_a_pos.trans_le (Set.uIcc_of_le (le_of_lt G.r_a_lt_r_b) ▸ hu |>.1)
    exact (continuousAt_const.mul (continuousAt_inv₀ (ne_of_gt hu0))).continuousWithinAt
  -- Step 4: FTC-2 on the closed annulus for both `deriv T` (which agrees with
  -- `s * r⁻¹` inside the integration range) and the primitive `s * log`.
  have hIooSub : Set.uIoo G.r_a G.r_b ⊆ G.wallInterior :=
    Set.uIoo_of_lt G.r_a_lt_r_b ▸ Set.Subset.rfl
  have hcongr : (∫ u in G.r_a..G.r_b, deriv T u) = ∫ u in G.r_a..G.r_b, s * u⁻¹ :=
    intervalIntegral.integral_congr_uIoo fun r hr => hderC r (hIooSub hr)
  have hFTC : (∫ u in G.r_a..G.r_b, deriv T u) = T G.r_b - T G.r_a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (le_of_lt G.r_a_lt_r_b) hcont hdrv
      ((intervalIntegrable_congr_uIoo
        (Set.EqOn.symm fun r hr => hderC r (hIooSub hr))).mp hIg)
  have hF2 : (∫ u in G.r_a..G.r_b, s * u⁻¹) = s * Real.log G.r_b - s * Real.log G.r_a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => by
        have hu0 : (0:ℝ) < u :=
          lt_of_lt_of_le G.r_a_pos ((Set.uIcc_of_le (le_of_lt G.r_a_lt_r_b) ▸ hu).1)
        simpa [mul_comm] using (Real.hasDerivAt_log (ne_of_gt hu0)).const_mul s)
      hIg
  rw [← hFTC, hcongr, hF2, Real.log_div hRb.ne' G.r_a_pos.ne']
  ring

/-- **Uniqueness of the radial temperature field.**  Two Fourier fields with
the same `lam`, the same shell-independent current `P`, and the same
wall-face boundary values agree on the whole closed annulus.  On the open
annulus their difference has gradient `0`
(`deriv_eq_of_radialFourier` applied to both), hence is constant by the
mean value theorem; and the shared face values force that constant to be
zero; the one-sided face continuity of `SatisfiesRadialFourierLaw`
propagates that interior constant also to `r_a, r_b`, where the fields need
not satisfy equation (6) itself. -/
theorem temperature_profile_unique {lam P : ℝ} (hlam : 0 < lam)
    {T₁ T₂ : ℝ → ℝ}
    (h₁ : G.SatisfiesRadialFourierLaw lam P T₁)
    (h₂ : G.SatisfiesRadialFourierLaw lam P T₂)
    (hb₁ : G.SatisfiesFaceTemperatures T₁) (hb₂ : G.SatisfiesFaceTemperatures T₂) :
    Set.EqOn T₁ T₂ (Set.Icc G.r_a G.r_b) := by
  intro r hr
  obtain ⟨hd1, hgrad1, hconta1, hcontb1⟩ := G.deriv_eq_of_radialFourier hlam h₁
  obtain ⟨hd2, hgrad2, hconta2, hcontb2⟩ := G.deriv_eq_of_radialFourier hlam h₂
  have hd0 : ∀ x ∈ G.wallInterior, deriv (T₁ - T₂) x = 0 := by
    intro x hx
    rw [deriv_sub (hd1 x hx) (hd2 x hx), hgrad1 x hx, hgrad2 x hx, sub_self]
  -- The difference `T₁ - T₂` is some constant `c` throughout the open wall,
  -- by the mean value theorem (`deriv` vanishes there).
  have hcd : DifferentiableOn ℝ (T₁ - T₂) G.wallInterior :=
    fun y hy => ((hd1 y hy).sub (hd2 y hy)).differentiableWithinAt
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioo hcd (fun y hy => by simp only [Pi.zero_apply]; exact hd0 y hy)
  -- Pin the constant through the one-sided face continuity of both fields:
  -- the shared face values force `c = 0` (already at the outer face).
  have hx0 : ((G.r_a + G.r_b) / 2 : ℝ) ∈ G.wallInterior :=
    ⟨by linarith [G.r_a_lt_r_b], by linarith [G.r_a_lt_r_b]⟩
  have hx0b : ((G.r_a + G.r_b) / 2 : ℝ) ∈ Set.Iic G.r_b := by
    simp only [Set.mem_Iic]; linarith [G.r_a_lt_r_b]
  have hfb : (T₁ - T₂) G.r_b = 0 := by
    simp [Pi.sub_apply, hb₁.2, hb₂.2]
  have hc0 : c = 0 := by
    have e2 := ContinuousWithinAt.sub hcontb1 hcontb2
    have e2' : ContinuousWithinAt (T₁ - T₂) (Set.Ioo G.r_a G.r_b) G.r_b :=
      e2.mono (fun _ hx => le_of_lt hx.2)
    have hrbcl : G.r_b ∈ closure (Set.Ioo G.r_a G.r_b) := by
      rw [closure_Ioo (ne_of_lt G.r_a_lt_r_b)]
      exact ⟨le_of_lt G.r_a_lt_r_b, le_rfl⟩
    have heq : (T₁ - T₂) G.r_b = c :=
      e2'.eq_const_of_mem_closure hrbcl (fun y hy => hc y hy)
    linarith
  -- Conclusion on the whole closed annulus.
  rcases eq_or_lt_of_le hr.1 with rfl | hlt
  · rw [hb₁.1, hb₂.1]
  rcases eq_or_lt_of_le hr.2 with rfl | hgt
  · rw [hb₁.2, hb₂.2]
  have h : (T₁ - T₂) r = 0 := by rw [hc r ⟨hlt, hgt⟩, hc0]
  exact sub_eq_zero.mp h

/-- **The requested formula, as a characterization.**  Matching equation (4)
against the integrated Fourier law identifies the wall resistance with the
radial-conduction integral: `SatisfiesHeatFlowRelation P` is equivalent to
`2π L R_Th λ = log (r_b / r_a)`.  Both directions reduce, via
`temperature_drop_log_law` and the face boundary conditions, to arithmetic
over `R > 0` and `log (r_b / r_a) > 0`. -/
theorem heatFlowRelation_iff_formula {lam P : ℝ} (hlam : 0 < lam)
    {T : ℝ → ℝ} (hF : G.SatisfiesRadialFourierLaw lam P T)
    (hb : G.SatisfiesFaceTemperatures T) :
    G.SatisfiesHeatFlowRelation P ↔ G.ConductivityResistanceFormula lam := by
  have hdrop := G.temperature_drop_log_law hlam hF
  obtain ⟨hTa, hTb⟩ := hb
  rw [hTb, hTa] at hdrop
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hRb : (0:ℝ) < G.r_b := lt_trans G.r_a_pos G.r_a_lt_r_b
  have hLog : (0:ℝ) < Real.log (G.r_b / G.r_a) := by
    apply Real.log_pos
    rw [one_lt_div G.r_a_pos]
    exact G.r_a_lt_r_b
  have hRne : G.R ≠ 0 := ne_of_gt G.R_pos
  have hLamNe : lam ≠ 0 := ne_of_gt hlam
  have h2piLne : (2:ℝ) * Real.pi * G.L ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi.ne') G.L_pos.ne'
  have hKne : (2:ℝ) * Real.pi * G.L * G.R ≠ 0 := mul_ne_zero h2piLne hRne
  constructor
  · -- Equation (4) `P * R = T_OC - T_IC` implies the combined formula
    -- `2 π L R λ = log (r_b / r_a)` by cancelling the common current `P`.
    intro h4
    simp only [SatisfiesHeatFlowRelation] at h4
    have hP : P ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at h4
      linarith [G.T_IC_lt_T_OC]
    -- Clear the denominator in the integrated drop:
    -- `G.T_OC - G.T_IC = P * Real.log (G.r_b / G.r_a) / (2 * π * λ * L)`.
    have h2pilam_ne : (2:ℝ) * Real.pi * lam ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hpi.ne') hLamNe
    have hK' : (2:ℝ) * Real.pi * lam * G.L ≠ 0 :=
      mul_ne_zero h2pilam_ne G.L_pos.ne'
    have hdrop2 : (2 * Real.pi * lam * G.L) * (G.T_OC - G.T_IC)
        = P * Real.log (G.r_b / G.r_a) := by
      calc
        (2 * Real.pi * lam * G.L) * (G.T_OC - G.T_IC)
            = (2 * Real.pi * lam * G.L) *
                ((P / (2 * Real.pi * lam * G.L)) *
                  Real.log (G.r_b / G.r_a)) := by rw [hdrop]
        _ = P * Real.log (G.r_b / G.r_a) := by
          field_simp [hK', G.L_pos.ne']
    exact mul_left_cancel₀ hP (calc
      P * (2 * Real.pi * G.L * G.R * lam)
          = (2 * Real.pi * lam * G.L) * (P * G.R) := by ring
      _ = (2 * Real.pi * lam * G.L) * (G.T_OC - G.T_IC) := by rw [h4]
      _ = P * Real.log (G.r_b / G.r_a) := hdrop2)
  · -- Conversely the combined formula identifies the C.6 resistance, so the
    -- common current satisfies equation (4).
    intro hform
    -- Same clearing, then cancel the positive constant `2 π L λ`.
    have h2pilam_ne : (2:ℝ) * Real.pi * lam ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hpi.ne') hLamNe
    have hK' : (2:ℝ) * Real.pi * lam * G.L ≠ 0 :=
      mul_ne_zero h2pilam_ne G.L_pos.ne'
    have hdrop2 : (2 * Real.pi * lam * G.L) * (G.T_OC - G.T_IC)
        = P * Real.log (G.r_b / G.r_a) := by
      calc
        (2 * Real.pi * lam * G.L) * (G.T_OC - G.T_IC)
            = (2 * Real.pi * lam * G.L) *
                ((P / (2 * Real.pi * lam * G.L)) *
                  Real.log (G.r_b / G.r_a)) := by rw [hdrop]
        _ = P * Real.log (G.r_b / G.r_a) := by
          field_simp [hK', G.L_pos.ne']
    exact mul_left_cancel₀ hK' (calc
      (2 * Real.pi * lam * G.L) * (P * G.R)
          = P * (2 * Real.pi * G.L * G.R * lam) := by ring
        _ = P * Real.log (G.r_b / G.r_a) := by rw [hform]
        _ = (2 * Real.pi * lam * G.L) * (G.T_OC - G.T_IC) := hdrop2.symm)

/-- **E1-C7, answer-free existence-and-uniqueness characterization.**  Under
the combined equation-(4)+equation-(6) model, there is a unique positive
conductivity `λ`.  Existence is witnessed by the logarithmic radial profile
(taking `P` from equation (4) and `λ` from the combined formula), and
uniqueness follows from `heatFlowRelation_iff_formula`. -/
theorem acrylic_conductivity_exists_unique : ∃! lam : ℝ, G.Solution lam := by
  /- USER: Preserve the existing logarithmic witness and fix errors top-down;
  do not rebuild this tail again.  Boundary continuity follows from the
  ordinary `ContinuousAt` chain for `x ↦ log (x / G.r_a)` at the positive
  endpoints, then `.continuousWithinAt`.  For uniqueness, use the already
  proved `heatFlowRelation_iff_formula` on each candidate and cancel the
  positive coefficient `2 * π * G.L * G.R`; avoid a second FTC derivation. -/
  -- Geometric positivity data used throughout.
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hRb : (0:ℝ) < G.r_b := lt_trans G.r_a_pos G.r_a_lt_r_b
  have hratio : (1:ℝ) < G.r_b / G.r_a := by
    rw [one_lt_div G.r_a_pos]; exact G.r_a_lt_r_b
  have hLog : (0:ℝ) < Real.log (G.r_b / G.r_a) := Real.log_pos hratio
  have hLogNe : Real.log (G.r_b / G.r_a) ≠ 0 := ne_of_gt hLog
  -- The candidate: the C.6 current `P₀` from equation (4), the logarithmic
  -- radial profile `T₀` with the wall-face boundary values, and the
  -- conductivity `lam₀` singled out by the combined formula.
  set P₀ : ℝ := (G.T_OC - G.T_IC) / G.R with hP₀_def
  have hP₀ : (0:ℝ) < P₀ := div_pos (sub_pos.mpr G.T_IC_lt_T_OC) G.R_pos
  set σ : ℝ := (G.T_OC - G.T_IC) / Real.log (G.r_b / G.r_a) with hσ_def
  have hσ : (0:ℝ) < σ := div_pos (sub_pos.mpr G.T_IC_lt_T_OC) hLog
  set T₀ : ℝ → ℝ := fun r => G.T_IC + σ * Real.log (r / G.r_a) with hT₀_def
  set lam₀ : ℝ := Real.log (G.r_b / G.r_a) / (2 * Real.pi * G.L * G.R) with hlam₀_def
  have h2piLne : (2:ℝ) * Real.pi * G.L ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi.ne') G.L_pos.ne'
  have hDenNe : (2:ℝ) * Real.pi * G.L * G.R ≠ 0 := mul_ne_zero h2piLne G.R_pos.ne'
  have hLRNe : G.L * G.R ≠ 0 := mul_ne_zero G.L_pos.ne' G.R_pos.ne'
  have hlam₀ : (0:ℝ) < lam₀ := by
    rw [hlam₀_def]
    have h2pi : (0:ℝ) < 2 * Real.pi := mul_pos (by norm_num) hpi
    exact div_pos hLog (mul_pos (mul_pos h2pi G.L_pos) G.R_pos)
  -- `lam₀` satisfies the combined formula.
  have hform₀ : G.ConductivityResistanceFormula lam₀ := by
    rw [ConductivityResistanceFormula, hlam₀_def]
    exact mul_div_cancel₀ _ hDenNe
  -- The boundary values of the witness profile.
  have hb₀ : G.SatisfiesFaceTemperatures T₀ := by
    constructor
    · simp [hT₀_def]
    · rw [hT₀_def, hσ_def]
      field_simp [hLogNe]
      ring
  -- The scale identity: the Fourier slope `P₀ / (2 π lam₀ L)` equals `σ`.
  have hs₀ : P₀ / (2 * Real.pi * lam₀ * G.L) = σ := by
    rw [hlam₀_def, hP₀_def, hσ_def]
    field_simp [hDenNe, hLRNe, hLogNe, G.R_pos.ne', G.L_pos.ne', hpi.ne']
  -- The logarithmic witness profile is continuous at every nonzero radius,
  -- and differentiable wherever the ratio `r / r_a` is nonzero.
  have hcore : ∀ {x : ℝ}, x / G.r_a ≠ 0 →
      HasDerivAt (fun x => Real.log (x / G.r_a)) ((x / G.r_a)⁻¹ * G.r_a⁻¹) x := by
    intro x hx
    simpa only [Function.comp_def, id_eq, one_div] using
      (Real.hasDerivAt_log hx).comp x ((hasDerivAt_id x).div_const G.r_a)
  have hcontlog : ∀ {x : ℝ}, x / G.r_a ≠ 0 →
      ContinuousWithinAt T₀ (Set.Ici x) x ∧ ContinuousWithinAt T₀ (Set.Iic x) x := by
    intro x hx
    have hdiv : ContinuousAt (fun r : ℝ => r / G.r_a) x :=
      continuousAt_id.div_const G.r_a
    have hc : ContinuousAt (fun r => Real.log (r / G.r_a)) x := by
      exact ContinuousAt.comp' (f := fun r : ℝ => r / G.r_a) (x := x)
        (Real.continuousAt_log hx) hdiv
    have hcT : ContinuousAt T₀ x := by
      have : T₀ = fun r => G.T_IC + σ * Real.log (r / G.r_a) := rfl
      rw [this]
      exact (hc.const_mul σ).const_add _
    exact ⟨hcT.continuousWithinAt, hcT.continuousWithinAt⟩
  -- Fourier's law, equation (6), for the witness profile.
  have hFour : G.SatisfiesRadialFourierLaw lam₀ P₀ T₀ := by
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · -- At interior radius `r`, the logarithmic profile has derivative
      -- `σ / r`, here in the un-normalised form `σ * (r / r_a)⁻¹ * r_a⁻¹`.
      have hrp : (0:ℝ) < r := lt_trans G.r_a_pos hr.1
      have harg : r / G.r_a ≠ 0 := (div_pos hrp G.r_a_pos).ne'
      refine ⟨σ / r, ?_, ?_⟩
      · -- Assemble `HasDerivAt T₀` from the primitive and the constants.
        have h' := ((hcore harg).const_mul σ).const_add G.T_IC
        have hscale : σ * ((r / G.r_a)⁻¹ * G.r_a⁻¹) = σ / r := by
          field_simp [G.r_a_pos.ne', hrp.ne']
        rw [hT₀_def]
        rw [← hscale]
        exact h'
      · -- `σ / r = P₀ / (lam₀ * A(r))` via `hs₀` and algebra.
        have hA : lam₀ * G.lateralArea r = 2 * Real.pi * lam₀ * G.L * r := by
          unfold lateralArea; ring
        rw [hA]
        have hrne : r ≠ 0 := ne_of_gt hrp
        rw [← hs₀]
        field_simp
    · -- Face continuity at `r_a` from within `Ici r_a`.
      have harg : G.r_a / G.r_a ≠ 0 := by
        rw [div_self G.r_a_pos.ne']; exact one_ne_zero
      exact (hcontlog harg).1
    · -- Face continuity at `r_b` from within `Iic r_b`.
      have harg : G.r_b / G.r_a ≠ 0 := (div_pos hRb G.r_a_pos).ne'
      exact (hcontlog harg).2
  -- Equation (4), the heat-flow relation, holds for `P₀`.
  have h4₀ : G.SatisfiesHeatFlowRelation P₀ := by
    rw [SatisfiesHeatFlowRelation, hP₀_def]
    field_simp [G.R_pos.ne']
  -- Assemble the existential half.
  refine ⟨lam₀, ⟨hlam₀, T₀, P₀, hb₀, hFour, h4₀⟩, ?_⟩
  -- Uniqueness: any solution conductivity satisfies the combined formula,
  -- whose positive coefficient pins it to `lam₀`.
  intro lam' hlam'
  obtain ⟨hlam'pos, T', P', hb', hF', h4'⟩ := hlam'
  have hform' : G.ConductivityResistanceFormula lam' :=
    (G.heatFlowRelation_iff_formula hlam'pos hF' hb').mp h4'
  have hform'₂ : 2 * Real.pi * G.L * G.R * lam' = Real.log (G.r_b / G.r_a) :=
    hform'
  have key := mul_left_cancel₀ hDenNe (by
    calc (2 * Real.pi * G.L * G.R) * lam'
        = Real.log (G.r_b / G.r_a) := hform'₂
      _ = (2 * Real.pi * G.L * G.R) * lam₀ := by
        have : (2 * Real.pi * G.L * G.R) * lam₀
            = Real.log (G.r_b / G.r_a) := by
          rw [hlam₀_def]
          exact mul_div_cancel₀ _ hDenNe
        exact this.symm)
  exact key

end AmenableGeometry

end Ipho2026KimiK3Blind32.ProblemIPhO2026_4C7
