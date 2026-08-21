import Mathlib

/-!
# IPhO 2026, Problem T1, Part B.1 — answer-blind formalization

## Source (official paper, translated)

At a certain instant of time, a positron `e⁺` is located at a distance of
`100 a₀` from an electron `e⁻`.  The particles are moving in such a way that
their velocities are antiparallel at that instant, perpendicular to their
separation (figure 1b of the source page, referred to from part A).  Each
particle has an angular momentum of magnitude `μħ` with respect to the
system's center of mass, with `μ` a dimensionless numerical factor.  The
only interaction between `e⁺` and `e⁻` is electrostatic (both particles have
the same mass `m` and equal magnitude of the charge but of opposite sign),
the system remains isolated, and its dynamics are classical and
non-relativistic.  The Bohr radius is `a₀ = 4πε₀ħ²/(m e²)` and
`k = 1/(4πε₀)`.

**Subquestion B.1.**  If `μ = 4`, the system is bound, meaning that the
particles move in a closed orbit around the system's center of mass.  Find
the maximum separation distance between `e⁺` and `e⁻` in terms of `a₀`.

The source page states two hints, both grounded here as definitions:

* Hint 1: the eccentricity of a conic trajectory is
  `ε = √(1 + 4 L² E / (k² e⁴ m))`, where `E` and `L` are the total energy
  and the magnitude of the total angular momentum;
* Hint 2: the equation of a conic in polar coordinates is
  `r(θ) = a / (1 − ε cos θ)`.

## Physics model (center-of-mass reduction)

Equal masses make the center of mass the midpoint; with the reduced mass
`m_red = m/2` and the relative separation `r`, the motion is the planar
Kepler problem with total energy
```
E = (m/4) * (radial speed)² + L² / (m * r²) − k * e² / r,
```
where `L = |r × p|` is the total conserved angular momentum about the
center of mass.  Because the two particles move symmetrically about the
center of mass, each particle's angular momentum about it has the same
magnitude, namely `L / 2`; the statement "each particle has angular momentum
of magnitude `μħ`" therefore fixes `L = 2 μ ħ`.  Measuring `r` in units of
`a₀` (using `ħ²/(m a₀) = k e²`, the definition of `a₀`), the squared radial
speed `v_r²` in units of `ħ²/(m² a₀²)`, and the energy in units of
`ħ²/(m a₀²)`, the energy law becomes
```
Ê = v_r² / 4 + 4 μ² / r² − 1 / r.
```
The initial velocities being perpendicular to the separation means the
radial speed vanishes at the initial separation `r₀ = 100` (in units of
`a₀`), so the conserved energy `Ê₀ = 4μ²/100² − 1/100` is negative at
`μ = 4` — the "bound" hypothesis of the statement.  The attained
separations of a bound planar motion form the full closed interval between
the two turning points (zeros of the radial speed), and the requested
answer is its right endpoint.

## Answer-free policy

The official answer is withheld: `problem_IPhO_2026_1_B_1` states existence
and uniqueness of a dimensionless separation characterised by a physically
meaningful solution predicate.  No closed-form witness or numerical value
appears in the signature; the uniqueness half of the target is proved
unconditionally from the predicate (see `unique_solution`).

## Review history (iteration 004 → this redraft)

The previous draft existentially quantified the attained-separation set `s`
over ranges *contained in* the admissible interval with no maximality
requirement, so the inner turning point (and the initial separation
`r₀ = 100`) satisfied the predicate via the degenerate singleton
`s = {100}`, while the true outer turning point satisfied it via the full
interval — uniqueness failed.  This redraft adds the maximality clause:
the range must be **complete**, i.e. every positive scalar `r` admitting a
nonnegative radial contribution at the conserved energy must lie in `s`.
That forces the range to be the full admissible interval; its maximal
element, if any, is its supremum (proved unconditionally as
`solution_eq_csSup`), which restores uniqueness (`unique_solution`).
-/

namespace IPhO_2026_1_B_1

/-!
### Physical constants and the Bohr radius -/

/-- The physical constants appearing in the statement, as positive real
dimensional data: the common particle mass `m`, the elementary-charge
magnitude `e` (the charges have equal magnitude and opposite sign, so only
`e` enters the potential energy), the reduced Planck constant `ħ` (the
statement's angular-momentum unit), and Coulomb's constant
`k = 1/(4πε₀)`; `ε₀` appears only through `k`, including inside the Bohr
radius. -/
structure Constants where
  m : ℝ
  e : ℝ
  ħ : ℝ
  k : ℝ
  m_pos : 0 < m
  e_pos : 0 < e
  ħ_pos : 0 < ħ
  k_pos : 0 < k

/-- The Bohr radius `a₀ = ħ² / (k m e²)` (equivalently
`4πε₀ħ²/(m e²)`), the length unit in which the answer is requested.
Positivity is used only to keep the dimensionless reductions meaningful. -/
noncomputable def Constants.bohrRadius (C : Constants) : ℝ :=
  C.ħ ^ 2 / (C.k * C.m * C.e ^ 2)

theorem Constants.bohrRadius_pos (C : Constants) : 0 < C.bohrRadius := by
  unfold Constants.bohrRadius
  have hm : 0 < C.m := C.m_pos
  have he : 0 < C.e := C.e_pos
  have hħ : 0 < C.ħ := C.ħ_pos
  have hk : 0 < C.k := C.k_pos
  exact div_pos (pow_pos hħ 2) (mul_pos (mul_pos hk hm) (pow_pos he 2))

/-- The value `μ = 4` prescribed by subquestion B.1: each particle's angular
momentum about the center of mass has magnitude `4 ħ`. -/
def muValue : ℝ := 4

/-- The stated initial separation `100 * a₀`, expressed in units of `a₀`. -/
def initialSeparationInBohrRadii : ℝ := 100

/-!
### Conserved quantities of the center-of-mass motion -/

/-- The conserved radial-energy law of the center-of-mass motion, written in
the problem's natural units: with the separation `r` measured in units of
`a₀` and `v2` the squared radial speed `v_r²` measured in units of
`ħ²/(m² a₀²)`, `radialEnergyFun μ v2 r` is the total energy
`E = (m/4) v_r² + (2μħ)²/(m r²) − k e²/r` in units of `ħ²/(m a₀²)`,
i.e. `Ê = v_r²/4 + 4μ²/r² − 1/r`.  It uses only the stated governing laws
(Newtonian kinetic energy with reduced mass `m/2`, total angular momentum
`L = 2μħ` fixed by the statement, Coulomb attraction `−k e²/r`) and the
definition of `a₀`; no evaluated quantity is built in. -/
noncomputable def radialEnergyFun (μ v2 r : ℝ) : ℝ :=
  v2 / 4 + 4 * μ ^ 2 / r ^ 2 - 1 / r

/-- The total angular momentum `L = 2 μ ħ` about the center of mass fixed by
the statement "each particle has angular momentum of magnitude `μħ` about
the center of mass": in the symmetric equal-mass motion the two angular
momenta about the center of mass are parallel and of equal magnitude
`L / 2`, so `L / 2 = μħ`.  Used by Hint 1. -/
noncomputable def totalAngularMomentum (C : Constants) (μ : ℝ) : ℝ :=
  2 * μ * C.ħ

/-- The total energy of the pair in dimensional form,
`E = (m/4) v_r² + L²/(m r_phys²) − k e²/r_phys`, evaluated from the stated
initial data: at the initial separation `r_phys = 100 a₀` the velocities are
perpendicular to the separation, so the radial speed vanishes and only the
centrifugal barrier and the Coulomb attraction contribute.  Used by Hint 1. -/
noncomputable def totalEnergy (C : Constants) (μ : ℝ) : ℝ :=
  totalAngularMomentum C μ ^ 2 / (C.m * (100 * C.bohrRadius) ^ 2) -
    C.k * C.e ^ 2 / (100 * C.bohrRadius)

/-- **Hint 1** of the source page: the eccentricity of the conic trajectory
is `ε = √(1 + 4 L² E / (k² e⁴ m))`, where `E` and `L` are the total energy
and the magnitude of the total angular momentum and `k = 1/(4πε₀)`.
Grounded as stated; the subquestion's dynamics determine `E` and `L` through
`totalEnergy` and `totalAngularMomentum`. -/
noncomputable def conicEccentricity (C : Constants) (E L : ℝ) : ℝ :=
  Real.sqrt (1 + 4 * L ^ 2 * E / (C.k ^ 2 * C.e ^ 4 * C.m))

/-- **Hint 2** of the source page: the polar equation `r = a/(1 − ε cos θ)`
of a conic.  Grounded as stated; a bound trajectory of the problem
(eccentricity from Hint 1, `0 < ε < 1`) attains every separation between its
perihelion `a/(1 + ε)` and aphelion `a/(1 − ε)`, which is the geometric fact
behind the completeness requirement of the solution predicate. -/
noncomputable def conicRadius (a ε : ℝ) (θ : ℝ) : ℝ :=
  a / (1 - ε * Real.cos θ)

/-- The effective potential of the dimensionless radial energy law at zero
radial speed, `r ↦ 4μ²/r² − 1/r`, in units of `ħ²/(m a₀²)`.  A scalar
energy `Ê` is realised at separation `r` with a nonnegative radial
contribution iff `Ê ≤ effectivePotential μ r`. -/
noncomputable def effectivePotential (μ r : ℝ) : ℝ :=
  4 * μ ^ 2 / r ^ 2 - 1 / r

/-- Splitting of the radial energy into the radial-kinetic part `v2/4` and
the effective potential. -/
theorem radialEnergyFun_eq (μ v2 r : ℝ) :
    radialEnergyFun μ v2 r = v2 / 4 + effectivePotential μ r := by
  unfold radialEnergyFun effectivePotential; ring

/-- The conserved energy of the stated initial configuration, in units of
`ħ²/(m a₀²)`: the radial speed vanishes at the initial separation
`r₀ = 100` (initial velocities perpendicular to the separation), so the
energy equals the effective potential there.  No numerical evaluation is
built into the solution predicate below. -/
noncomputable def initialEnergy (μ : ℝ) : ℝ :=
  effectivePotential μ initialSeparationInBohrRadii

/-!
### The admissible (radially reachable) scalar interval -/

/-- A positive scalar separation `r` (in units of `a₀`) is *admitted* at the
scalar energy `Ê` iff it is radially reachable, i.e. some nonnegative
squared radial speed `v2` realises `Ê` at `r`: the radial kinetic
contribution cannot be negative. -/
def admittedScalars (E : ℝ) : Set ℝ :=
  {r : ℝ | 0 < r ∧ ∃ v2 : ℝ, 0 ≤ v2 ∧ radialEnergyFun muValue v2 r = E}

/-!
### Separation ranges and the solution predicate -/

/-- A *separation range* of the bound motion: a nonempty bounded set of
positive dimensionless separations (in units of `a₀`) that is closed,
connected (hence a compact interval, as expected for bound planar radial
motion bounded by two turning points), contains the stated initial
separation `r₀ = 100`, and shares the conserved scalar energy set by the
stated initial data: every attained `r ∈ s` admits a nonnegative squared
radial speed `v2` with `radialEnergyFun μ v2 r = Ê₀`.  Boundedness is the
statement's "the system is bound" hypothesis, internalised. -/
structure IsSeparationRange (s : Set ℝ) : Prop where
  nonempty : s.Nonempty
  pos_of_mem : ∀ r ∈ s, 0 < r
  closed : IsClosed s
  connected : IsConnected s
  initial_mem : initialSeparationInBohrRadii ∈ s
  bddAbove : BddAbove s
  energy : ∀ r ∈ s, ∃ v2 : ℝ, 0 ≤ v2 ∧
    radialEnergyFun muValue v2 r = initialEnergy muValue

/-- **Solution predicate (answer-free).**  A dimensionless separation
`r_over` (in units of `a₀`) solves subquestion B.1 iff it is the maximum of
a *complete* separation range of the bound `μ = 4` motion: there is a
separation range `s` (per `IsSeparationRange`) such that

* `r_over` is attained by the motion (`r_over ∈ s`);
* `r_over` bounds every attained separation from above
  (`IsMaxOn id s r_over`, i.e. `∀ r ∈ s, r ≤ r_over`); and
* the range is **complete** (maximal): every positive scalar separation
  admitting a nonnegative radial contribution at the conserved energy
  (`r ∈ admittedScalars (initialEnergy muValue)`) lies in `s`.

Completeness forces `s` to be the full admissible radial interval, whose
right endpoint is the outer turning point of the stated energy law; the
inner turning point and the degenerate singletons of the iteration-004
review countermodel are excluded.  No derived value appears anywhere in the
predicate. -/
def Solution (r_over : ℝ) : Prop :=
  ∃ s : Set ℝ,
    IsSeparationRange s ∧
      r_over ∈ s ∧
        IsMaxOn id s r_over ∧
          admittedScalars (initialEnergy muValue) ⊆ s

/-!
### Interplay lemmas -/

/-- Every separation range is contained in the admissible scalar interval:
its positivity and energy clauses are exactly the admission conditions. -/
theorem IsSeparationRange.subset_admittedScalars {s : Set ℝ}
    (h : IsSeparationRange s) :
    s ⊆ admittedScalars (initialEnergy muValue) :=
  fun _ hr => ⟨h.pos_of_mem _ hr, h.energy _ hr⟩

/-- **Uniqueness pin (proved).**  Any solution equals the supremum of the
admissible scalar interval: boundedness plus `IsMaxOn` identifies `r_over`
with `sSup` of its range, and completeness plus the inclusion of the range
in the admissible set identifies that supremum with the supremum of the
admissible interval. -/
theorem solution_eq_csSup {r_over : ℝ} (h : Solution r_over) :
    r_over = sSup (admittedScalars (initialEnergy muValue)) := by
  obtain ⟨s, hr, hmem, hmax, hcomplete⟩ := h
  have hbdd : BddAbove s := hr.bddAbove
  have hle : ∀ r ∈ s, r ≤ r_over := by
    intro r hrmem
    rw [isMaxOn_iff] at hmax
    exact hmax r hrmem
  have h1 : sSup s ≤ r_over := csSup_le hr.nonempty hle
  have h2 : r_over ≤ sSup s := le_csSup hbdd hmem
  have hsup : sSup s = r_over := le_antisymm h1 h2
  have hset : s = admittedScalars (initialEnergy muValue) :=
    Set.Subset.antisymm hr.subset_admittedScalars hcomplete
  rw [← hset, hsup]

/-- **Uniqueness (the repaired clause, proved).**  Any two solutions
coincide, since both equal the supremum of the admissible interval. -/
theorem unique_solution {r s : ℝ} (hr : Solution r) (hs : Solution s) :
    r = s := by
  rw [solution_eq_csSup hr, solution_eq_csSup hs]

/-- **Explicit admissible interval at the stated energy.**  With `μ = 4` the
conserved dimensionless energy of the stated configuration is
`Ê₀ = 64/100² − 1/100 = −9/2500`, and the energy law
`v_r²/4 + 9 (r − 100)(r − 1600/9)/(2500 r²) = 0` shows that a positive scalar
`r` is radially admissible iff it lies between the two turning points `100`
and `1600/9`.  Hence the admissible scalar set is literally the closed
interval `[100, 1600/9]`; the witness `1600/9` (the requested maximum
separation, in units of `a₀`) appears only inside this proof body, never in
any signature. -/
theorem admittedScalars_eq :
    admittedScalars (initialEnergy muValue) = Set.Icc 100 (1600 / 9) := by
  have hrad : ∀ v2 r : ℝ,
      radialEnergyFun muValue v2 r = v2 / 4 + 64 / r ^ 2 - 1 / r := by
    intro v2 r; unfold radialEnergyFun muValue; norm_num
  have hpot : effectivePotential muValue 100 = -(9 / 2500) := by
    unfold effectivePotential muValue; norm_num
  have hinitE : initialEnergy muValue = -(9 / 2500) := by
    unfold initialEnergy initialSeparationInBohrRadii; simpa using hpot
  ext r
  rw [hinitE]
  simp only [admittedScalars, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨hrpos, v2, hv2, hE⟩
    rw [hrad] at hE
    have hE2 : v2 * r ^ 2 * 2500 + 640000 - 10000 * r + 36 * r ^ 2 = 0 := by
      have hrn : (r : ℝ) ≠ 0 := ne_of_gt hrpos
      field_simp at hE
      linear_combination hE
    have hnn : (0 : ℝ) ≤ v2 * r ^ 2 * 2500 := by positivity
    have hcore : (r - 100) * (r - 1600 / 9) ≤ 0 := by nlinarith [hE2, hnn]
    constructor
    · by_contra hlt
      push Not at hlt
      have hA : (0 : ℝ) < (r - 100) * (r - 1600 / 9) := by nlinarith
      nlinarith
    · by_contra hgt
      push Not at hgt
      have hA : (0 : ℝ) < (r - 100) * (r - 1600 / 9) := by nlinarith
      nlinarith
  · rintro ⟨h1, h2⟩
    have hrp : (0 : ℝ) < r := by nlinarith
    have hrn : (r : ℝ) ≠ 0 := ne_of_gt hrp
    have hcore : (r - 100) * (r - 1600 / 9) ≤ 0 := by nlinarith
    refine ⟨hrp, -36 * (r - 100) * (r - 1600 / 9) / (2500 * r ^ 2), ?_, ?_⟩
    · have hnum : (0 : ℝ) ≤ -36 * ((r - 100) * (r - 1600 / 9)) := by nlinarith
      have hnum2 : (0 : ℝ) ≤ -36 * (r - 100) * (r - 1600 / 9) := by
        nlinarith [hcore]
      have hden : (0 : ℝ) < 2500 * r ^ 2 := by positivity
      exact div_nonneg hnum2 (le_of_lt hden)
    · rw [hrad]
      field_simp
      ring_nf

/-- Any solution is a turning point of the stated energy law: the radial
speed vanishes there.  (The maximal admissible separation lies on the
outer, strictly decreasing branch of the effective potential, so the
nonnegative radial contribution must be zero.) -/
theorem isTurningPoint_of_solution {r_over : ℝ} (h : Solution r_over) :
    radialEnergyFun muValue 0 r_over = initialEnergy muValue := by
  rw [solution_eq_csSup h, admittedScalars_eq]
  have hs : sSup (Set.Icc 100 (1600 / 9 : ℝ)) = 1600 / 9 :=
    csSup_Icc (by norm_num)
  have hinitE : initialEnergy muValue = -(9 / 2500) := by
    unfold initialEnergy initialSeparationInBohrRadii effectivePotential muValue
    norm_num
  rw [hs, hinitE]
  unfold radialEnergyFun muValue
  norm_num

/-- The admissible interval is bounded above: at the conserved energy
`Ê₀ < 0` of the stated `μ = 4` configuration the Coulomb term dominates the
centrifugal barrier for large `r`, so no sufficiently large separation is
admitted. -/
theorem admittedScalars_boundedAbove :
    BddAbove (admittedScalars (initialEnergy muValue)) := by
  rw [admittedScalars_eq]
  exact bddAbove_Icc

/-- The full admissible interval is a separation range; its energy clause
and positivity hold by construction, it contains the initial separation
(with `v2 = 0`), and closedness/connectedness follow from the interval
structure of `admittedScalars`. -/
theorem isSeparationRange_admittedScalars :
    IsSeparationRange (admittedScalars (initialEnergy muValue)) := by
  have hlt : (100 : ℝ) ≤ 1600 / 9 := by norm_num
  have h100 : (100 : ℝ) ∈ Set.Icc 100 (1600 / 9) :=
    ⟨le_rfl, hlt⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [admittedScalars_eq]
    exact ⟨100, h100⟩
  · intro r hr
    rw [admittedScalars_eq] at hr
    have hrIcc := Set.mem_Icc.mp hr
    linarith [hrIcc.left]
  · rw [admittedScalars_eq]
    exact isClosed_Icc
  · rw [admittedScalars_eq]
    exact isConnected_Icc hlt
  · rw [admittedScalars_eq]
    exact h100
  · exact admittedScalars_boundedAbove
  · intro r hr
    exact hr.2

/-- **Existence.**  The full admissible interval witnesses the predicate:
being closed, connected, bounded and admitting each of its points with a
nonnegative radial contribution, its supremum is attained and maximal. -/
theorem exists_solution : ∃ r_over : ℝ, Solution r_over := by
  refine ⟨sSup (admittedScalars (initialEnergy muValue)), ?_⟩
  have hrange : IsSeparationRange (admittedScalars (initialEnergy muValue)) :=
    isSeparationRange_admittedScalars
  refine ⟨admittedScalars (initialEnergy muValue), hrange, ?_, ?_, ?_⟩
  · rw [admittedScalars_eq]
    have hlt : (100 : ℝ) ≤ 1600 / 9 := by norm_num
    have hs : sSup (Set.Icc 100 (1600 / 9 : ℝ)) = 1600 / 9 :=
      csSup_Icc hlt
    rw [hs]
    exact ⟨hlt, le_rfl⟩
  · rw [admittedScalars_eq]
    have hlt : (100 : ℝ) ≤ 1600 / 9 := by norm_num
    have hs : sSup (Set.Icc 100 (1600 / 9 : ℝ)) = 1600 / 9 :=
      csSup_Icc hlt
    rw [isMaxOn_iff, hs]
    intro x hx
    exact hx.2
  · exact Set.Subset.rfl

/-!
### Target theorem -/

/-- **Target theorem (answer-free).**  For any admissible positive values of
the physical constants, the stated `μ = 4` bound configuration — equal
masses `m`, charge magnitudes `e`, initial separation `100 a₀`, initial
velocities antiparallel and perpendicular to the separation, isolated
classical non-relativistic purely Coulomb dynamics — determines a unique
dimensionless maximum electron–positron separation in units of `a₀`. -/
theorem problem_IPhO_2026_1_B_1 (_C : Constants) :
    ∃! r_over : ℝ, Solution r_over :=
  let ⟨r, hr⟩ := exists_solution
  ⟨r, hr, fun _ hs => unique_solution hs hr⟩

end IPhO_2026_1_B_1
