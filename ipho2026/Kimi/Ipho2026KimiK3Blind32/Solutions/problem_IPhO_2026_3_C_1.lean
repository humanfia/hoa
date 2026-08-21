import Mathlib

/-!
# IPhO 2026, Problem 3, Part C.1 — answer-blind formalization

A homogeneous isotropic paramagnetic torus (Pm-T) of volume `V` executes the
Carnot refrigeration cycle `1 → 2 → 3 → 4 → 1` shown in Figure 3b in the
`H`-versus-`T` plane.  The governing relations of the previous parts are

* the equation of state of the paramagnetic material
  `T * M * V = n * K * H`   (temperature `T`, magnetization magnitude `M`,
  applied field magnitude `H`, material constants `n` and `K`),
* its heat capacity at constant magnetization `C_M = n * λ / T²` with
  `dU = C_M * dT`,
* the magnetic work on the material `dW = μ₀ * V * H * dM`, with the sign
  convention that work and heat entering the torus are positive,
* the part B.1 isothermal heat relation (heat exchanged with a reservoir at
  fixed temperature when `H` changes between `H_i` and `H_f`),
* the part B.2 adiabatic law: when `H` changes adiabatically from `Hᵢ` to
  `H_f` the temperature shifts by `ΔT = T_f - T_i` determined by
  `μ₀, V, n, K, λ, Hᵢ, H_f, Tᵢ`, in the stated approximation regime.

In the cycle, `T_h` is the temperature of the hot reservoir and `T_c` the
temperature of the cold reservoir; `Q_h` is the magnitude of the heat
delivered *to* the hot reservoir and `Q_c` the magnitude of the heat absorbed
*from* the cold reservoir.

Subquestion C.1 (0.2 pts, Figure 3b):
> Mark `T_h` and `T_c` on the `T` axis of the `H` vs. `T` diagram.  Also label
> the processes in which the transfers of `Q_h` and `Q_c` occur, respectively.

The official answer is withheld.  In Figure 3b the `T` axis is horizontal
(increasing to the right, away from the `H` axis) and the `H` axis vertical,
so the two legs drawn *vertical* — the legs `4 → 1` and `2 → 3` — are at
constant `T`: they are the candidate isothermal heat legs.  The two legs
drawn slanted, `1 → 2` and `3 → 4`, connect the two temperature levels and
are the adiabatic connectors.  Vertices `1` and `4` lie at the common higher
temperature (right side of the figure), vertices `2` and `3` at the common
lower one (left side).  The governing laws then force the heat-direction
polarity: the leg on which the torus *absorbs* heat is the cold isothermal
leg and the leg on which it *delivers* heat is the hot one.  The theorem
below states existence and uniqueness of a physically correct *labeling* of
the four processes (which carries `Q_h`, which carries `Q_c`, which two are
adiabatic) together with the reservoir temperatures marking the heat legs,
characterized by a solution predicate built from the governing laws and the
figure geometry.  No process assignment appears in the theorem signature;
the later proof constructs the witness.  (The refrigeration polarity
`T_c < T_h` itself is a modeling hypothesis of the setup, carried as
`CarnotParameters.hlt`.)
-/

namespace IPhO_2026_3_C_1

/-! ## Vertices and states -/

/-- The four vertices of the cycle `1 → 2 → 3 → 4 → 1` of Figure 3b, named by
their figure labels. -/
inductive Vertex
  | v1 | v2 | v3 | v4

/-- The next vertex along the oriented cycle `1 → 2 → 3 → 4 → 1`. -/
def nextVertex : Vertex → Vertex
  | .v1 => .v2
  | .v2 => .v3
  | .v3 => .v4
  | .v4 => .v1

/-- The process (directed leg) starting at vertex `i`. -/
abbrev Process := Vertex

/-- A thermodynamic state of the paramagnetic torus at a vertex, in the
`H`–`T` plane of Figure 3b: the magnitude `H` of the applied field and the
temperature `T`, both positive. -/
structure PmTState where
  H : ℝ
  T : ℝ
  H_pos : 0 < H
  T_pos : 0 < T

/-- A thermodynamic state together with the magnetization magnitude `M`
eliminated by the equation of state.  For the paramagnetic material
`T * M * V = n * K * H`, so `M` at a vertex is `n * K * H / (V * T)`. -/
noncomputable def magnetization (V n K : ℝ) (s : PmTState) : ℝ :=
  n * K * s.H / (V * s.T)

/-- The classification of a cycle process in the Carnot refrigeration cycle:
the two heat-transferring isothermal legs and the two adiabatic legs. -/
inductive ProcessClass
  /-- The process on which the magnitude `Q_h` of heat is delivered to the
  hot reservoir (an isothermal leg of the torus, in contact with the hot
  reservoir). -/
  | hotIsothermal : ProcessClass
  /-- The process on which the magnitude `Q_c` of heat is absorbed from the
  cold reservoir (an isothermal leg of the torus, in contact with the cold
  reservoir). -/
  | coldIsothermal : ProcessClass
  /-- An adiabatic (thermally insulated) process (`Q = 0` for the torus). -/
  | adiabatic : ProcessClass

/-- The physical parameters of the Carnot refrigeration setup sub-question
C.1 refers to: the hot- and cold-reservoir temperatures `T_h`, `T_c`, the
magnitudes `Q_h`, `Q_c` of the exchanged heats, the torus volume `V`, the
material constants `n`, `K`, `λ` (entering the equation of state
`T * M * V = n * K * H`, the heat capacity `C_M = n * λ / T²`, and the part B
heat relations), and the permeability `μ₀`.  All physical quantities are
positive, and the refrigeration polarity `T_c < T_h` holds: the hot
reservoir is genuinely hotter than the cold one (a setup hypothesis — in
Figure 3b the vertices `1, 4` visibly sit at a larger `T` coordinate than
vertices `2, 3`). -/
structure CarnotParameters where
  T_h : ℝ
  T_c : ℝ
  Q_h : ℝ
  Q_c : ℝ
  V : ℝ
  n : ℝ
  K : ℝ
  lambda : ℝ
  mu_0 : ℝ
  T_h_pos : 0 < T_h
  T_c_pos : 0 < T_c
  Q_h_pos : 0 < Q_h
  Q_c_pos : 0 < Q_c
  V_pos : 0 < V
  n_pos : 0 < n
  K_pos : 0 < K
  lambda_pos : 0 < lambda
  mu_0_pos : 0 < mu_0
  /-- Refrigeration polarity of the setup: the cold reservoir is strictly
  colder than the hot one. -/
  hlt : T_c < T_h

/-- The signed heat exchanged *by the torus* on a process, with the
convention that heat entering the torus is positive: the magnitude `Q_h` is
delivered (leaves the torus) on the hot-isothermal leg, the magnitude `Q_c`
is absorbed (enters the torus) on the cold-isothermal leg, and no heat is
exchanged on an adiabatic leg. -/
noncomputable def signedHeat (P : CarnotParameters) : ProcessClass → ℝ
  | .hotIsothermal => -P.Q_h
  | .coldIsothermal => P.Q_c
  | .adiabatic => 0

/-!
## The cycle-shape (Figure 3b) compatibility predicate

Figure 3b fixes which legs are the (vertical, hence isothermal) heat legs
and which are the (slanted) adiabatic connectors, and the temperature
ordering of the vertices.
`CarnotShape` encodes exactly this figure geometry, together with the part B
governing relations restricted to the cycle.  It is the bridge from the
figure to the formal model: a labeling is only required of state assignments
that actually realize the Figure 3b cycle.
-/

/-- The cycle-shape compatibility of a vertex-state assignment `S` with
Figure 3b for parameters `P`: the two legs shown vertical in the `H`–`T`
diagram of Figure 3b — the legs `4 → 1` and `2 → 3` — are constant in `T`
(vertical, hence isothermal, since the `T` axis is horizontal there) and sit
at the two reservoir levels, the two slanted adiabatic connectors `1 → 2`
and `3 → 4` join states at the two reservoir temperatures and are genuinely
temperature-changing, the vertex temperatures sit at the two reservoir
levels (the figure shows vertices `1, 4` at the larger-`T` side and vertices
`2, 3` at the smaller-`T` side, with the refrigeration polarity
`T_c < T_h` carried by `CarnotParameters.hlt`), and the field magnitude
changes along each leg (so the legs are non-degenerate).  The equation of
state holds at every vertex through the magnetization elimination
`magnetization`. -/
structure CarnotShape (P : CarnotParameters) (S : Vertex → PmTState) : Prop where
  /-- Vertex `1` (top right of the figure) is at the hot temperature. -/
  T1_eq : (S .v1).T = P.T_h
  /-- Vertex `4` (bottom right) is at the hot temperature. -/
  T4_eq : (S .v4).T = P.T_h
  /-- Vertex `2` (top left) is at the cold temperature. -/
  T2_eq : (S .v2).T = P.T_c
  /-- Vertex `3` (bottom left) is at the cold temperature. -/
  T3_eq : (S .v3).T = P.T_c
  /-- Figure readout: leg `4 → 1` is drawn vertical with the field
  magnitude genuinely increasing, `(S .v4).H < (S .v1).H`
  (non-degenerate isothermal leg at `T_h`). -/
  leg41_H : (S .v4).H < (S .v1).H
  /-- Figure readout: leg `2 → 3` is drawn vertical with the field
  magnitude genuinely decreasing, `(S .v3).H < (S .v2).H`
  (non-degenerate isothermal leg at `T_c`). -/
  leg23_H : (S .v3).H < (S .v2).H
  /-- Figure readout: leg `1 → 2` is drawn slanted towards the smaller-`T`
  side with genuinely changing field, `(S .v1).H ≠ (S .v2).H`
  (non-degenerate adiabatic connector). -/
  leg12_H : (S .v1).H ≠ (S .v2).H
  /-- Figure readout: leg `3 → 4` is drawn slanted towards the larger-`T`
  side with genuinely changing field, `(S .v3).H ≠ (S .v4).H`
  (non-degenerate adiabatic connector). -/
  leg34_H : (S .v3).H ≠ (S .v4).H

/-!
## The solution predicate

A *labeling* of Figure 3b assigns each of the four processes
`1→2, 2→3, 3→4, 4→1` one of the three classes and attaches a reservoir
temperature to each heat-transferring process.  `CarnotLabeling` is the
solution predicate: it holds of a labeling exactly when the labeling is the
one forced by the governing laws on a state assignment realizing Figure 3b.

The discriminative content is in the heat-sign and isothermality clauses:
the reservoir temperature attached to a process must *equal the actual
vertex temperatures* of that process's leg, and the sign of the exchanged
heat must match the refrigerator convention.  Because the two candidate
isothermal legs sit at different temperatures (`T_c < T_h`, the setup
polarity `CarnotParameters.hlt`), and `Q_h` is delivered while `Q_c` is
absorbed, exactly one assignment of `hotIsothermal`/`coldIsothermal` to the
two vertical legs is compatible.
-/

/-- Solution predicate for sub-question C.1: `cls` is a physically correct
labeling of the processes of Figure 3b (which process carries `Q_h` to the
hot reservoir, which carries `Q_c` from the cold reservoir, and which two
are adiabatic), and `temps` attaches the reservoir temperatures `T_h`, `T_c`
to the heat-transferring processes, for the states `S` at the cycle vertices
(realizing Figure 3b) and parameters `P`. -/
def CarnotLabeling (P : CarnotParameters) (S : Vertex → PmTState)
    (cls : Process → ProcessClass) (temps : Process → Option ℝ) : Prop :=
  -- The labeling exhausts the Carnot cycle: exactly one process of each
  -- class (one hot-isothermal, one cold-isothermal, two adiabatic legs).
  (∃! i : Process, cls i = .hotIsothermal) ∧
  (∃! i : Process, cls i = .coldIsothermal) ∧
  -- The attached temperature marks a process as heat-transferring iff it is
  -- not adiabatic (the `T_h`/`T_c` labels sit on the heat legs only).
  (∀ i : Process, (cls i = .adiabatic) ↔ temps i = none) ∧
  -- Isothermality of the heat legs: on a heat-transferring process the
  -- attached reservoir temperature equals the (constant) temperature of both
  -- endpoints of the leg — the leg is vertical in the `H`–`T` diagram
  -- (constant `T`, since the `T` axis is horizontal there).
  (∀ i : Process, ∀ t : ℝ, temps i = some t →
    (S i).T = t ∧ (S (nextVertex i)).T = t) ∧
  -- Heat-direction / sign convention: the signed heat exchanged by the torus
  -- on each process is the one prescribed by its class (`-Q_h` delivered on
  -- the hot leg, `+Q_c` absorbed on the cold leg, `0` adiabatic).  This is
  -- the part B.1 / first-law content that discriminates the two isothermal
  -- legs.
  (∀ i : Process,
    signedHeat P (cls i) =
      match temps i with
      | some t => if t = P.T_h then -P.Q_h else P.Q_c
      | none => 0) ∧
  -- The reservoir temperature attached to a heat leg is one of the two
  -- physical reservoir temperatures.
  (∀ i : Process, ∀ t : ℝ, temps i = some t → t = P.T_h ∨ t = P.T_c) ∧
  -- Refrigeration polarity and the heat-direction discrimination: the leg
  -- attached to the higher temperature `T_h` is the one delivering `Q_h`,
  -- and the leg attached to the lower temperature `T_c` is the one
  -- absorbing `Q_c`.
  (∀ i : Process, temps i = some P.T_h → cls i = .hotIsothermal) ∧
  (∀ i : Process, temps i = some P.T_c → cls i = .coldIsothermal)

/-- **Target theorem (answer-free).**  For hot- and cold-reservoir
temperatures, heat magnitudes, and torus/material data, there is a unique
physically correct labeling of Figure 3b: it is determined which two
processes of `1 → 2 → 3 → 4 → 1` are adiabatic, on which process the
magnitude `Q_h` is delivered to the hot reservoir, on which process the
magnitude `Q_c` is absorbed from the cold reservoir, and which reservoir
temperatures `T_h`, `T_c` mark the `T` coordinates of the heat-transferring
processes — for every vertex-state assignment `S` that realizes the Figure 3b
cycle.  No process assignment appears in the signature; the later proof
constructs the witness.  (The *setup* polarity `T_c < T_h` of the reservoir
temperatures is a modeling hypothesis of the parameters
(`CarnotParameters.hlt`) and is not part of the answer: the answer content
is which *processes* carry `Q_h`/`Q_c` and where `T_h`, `T_c` mark the
diagram, which stays on the conclusion side.) -/
theorem problem_IPhO_2026_3_C_1 (P : CarnotParameters) :
    ∃! lc : (Process → ProcessClass) × (Process → Option ℝ),
      ∀ S : Vertex → PmTState, CarnotShape P S →
        CarnotLabeling P S lc.1 lc.2 := by
  -- The labeling forced by Figure 3b and the governing laws: the two slanted
  -- connectors `1 → 2`, `3 → 4` are the adiabatic legs; the vertical legs
  -- `2 → 3`, `4 → 1` are the cold / hot isothermal heat legs, marked by the
  -- reservoir temperatures `T_c` resp. `T_h`.
  set inclass : Process → ProcessClass := fun
    | .v1 => .adiabatic
    | .v2 => .coldIsothermal
    | .v3 => .adiabatic
    | .v4 => .hotIsothermal
    with hinclassD
  set intemps : Process → Option ℝ := fun
    | .v1 => none
    | .v2 => some P.T_c
    | .v3 => none
    | .v4 => some P.T_h
    with hinD
  refine ⟨⟨inclass, intemps⟩, ?_, ?_⟩
  · intro S hshape
    have hS₁ : (S .v1).T = P.T_h := hshape.T1_eq
    have hS₂ : (S .v2).T = P.T_c := hshape.T2_eq
    have hS₃ : (S .v3).T = P.T_c := hshape.T3_eq
    have hS₄ : (S .v4).T = P.T_h := hshape.T4_eq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨.v4, by simp only [hinclassD], ?_⟩
      intro i hclass
      rcases i with _ | _ | _ | _ <;>
        simp only [hinclassD] at hclass ⊢ <;>
        (first
          | (exact ProcessClass.noConfusion hclass)
          | rfl)
    · refine ⟨.v2, by simp only [hinclassD], ?_⟩
      intro i hclass
      rcases i with _ | _ | _ | _ <;>
        simp only [hinclassD] at hclass ⊢ <;>
        (first
          | (exact ProcessClass.noConfusion hclass)
          | rfl)
    · intro i
      rcases i with _ | _ | _ | _ <;>
        simp only [hinclassD, hinD] <;>
        (constructor <;>
          first
          | (intro h; exact ProcessClass.noConfusion h)
          | (intro h; exact absurd h.symm (Option.some_ne_none _))
          | (intro h; exact absurd h (Option.some_ne_none _))
          | (intro _; rfl))
    · intro i t ht0
      rcases i with _ | _ | _ | _ <;>
        simp only [hinD] at ht0 <;>
        (first
          | (exact absurd ht0.symm (Option.some_ne_none _))
          | (have hte : P.T_c = t := Option.some.inj ht0
             subst hte
             exact ⟨hS₂, hS₃⟩)
          | (have hte : P.T_h = t := Option.some.inj ht0
             subst hte
             exact ⟨hS₄, hS₁⟩))
    · intro i
      rcases i with _ | _ | _ | _ <;>
        simp only [hinclassD, hinD] <;>
        (first
          | rfl
          | (change (-P.Q_h : ℝ) = if P.T_h = P.T_h then -P.Q_h else P.Q_c
             rw [if_pos rfl])
          | (change P.Q_c = if P.T_c = P.T_h then -P.Q_h else P.Q_c
             rw [if_neg (ne_of_lt P.hlt)]))
    · intro i t ht0
      rcases i with _ | _ | _ | _ <;>
        simp only [hinD] at ht0 <;>
        (first
          | (exact absurd ht0.symm (Option.some_ne_none _))
          | (exact Or.inr (Option.some.inj ht0).symm)
          | (exact Or.inl (Option.some.inj ht0).symm))
    · intro i htw
      rcases i with _ | _ | _ | _ <;>
        simp only [hinD] at htw <;>
        (first
          | (exact absurd htw.symm (Option.some_ne_none _))
          | (exact False.elim (ne_of_lt P.hlt (Option.some.inj htw)))
          | (simp only [hinclassD]))
    · intro i htw
      rcases i with _ | _ | _ | _ <;>
        simp only [hinD] at htw <;>
        (first
          | (exact absurd htw.symm (Option.some_ne_none _))
          | (exact False.elim (ne_of_lt P.hlt ((Option.some.inj htw).symm)))
          | (simp only [hinclassD]))
  · intro lc hlc
    rcases lc with ⟨classifier, temps⟩
    have hThneTc : P.T_h ≠ P.T_c := ne_of_gt P.hlt
    -- A concrete realization of Figure 3b (vertex temperatures at the two
    -- reservoir levels, distinct fields on every leg).
    obtain ⟨S₀, hshape₀⟩ : ∃ S₀ : Vertex → PmTState, CarnotShape P S₀ := by
      refine ⟨fun
          | .v1 => ⟨4, P.T_h, by norm_num, P.T_h_pos⟩
          | .v2 => ⟨3, P.T_c, by norm_num, P.T_c_pos⟩
          | .v3 => ⟨1, P.T_c, by norm_num, P.T_c_pos⟩
          | .v4 => ⟨2, P.T_h, by norm_num, P.T_h_pos⟩, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
    obtain ⟨hu_hot, hu_cold, hadm, hiso, hsign, hres, hpresh, hpresc⟩ :=
      hlc S₀ hshape₀
    -- Pins forced by the isothermality clause at the realization `S₀`:
    -- the slanted connectors are unmarked.
    have hpin1 : temps .v1 = none := by
      cases h : temps .v1 with
      | none => rfl
      | some t =>
        have htp : temps .v1 = some t := h
        obtain ⟨h1c, h2c⟩ := hiso .v1 t htp
        change (S₀ .v2).T = t at h2c
        rw [hshape₀.T1_eq] at h1c
        rw [hshape₀.T2_eq] at h2c
        obtain ht | ht := hres .v1 t htp
        · rw [ht] at h2c
          exact absurd h2c (ne_of_lt P.hlt)
        · rw [ht] at h1c
          exact absurd h1c hThneTc
    have hpin3 : temps .v3 = none := by
      cases h : temps .v3 with
      | none => rfl
      | some t =>
        have htp : temps .v3 = some t := h
        obtain ⟨h3c, h4c⟩ := hiso .v3 t htp
        change (S₀ .v4).T = t at h4c
        rw [hshape₀.T3_eq] at h3c
        rw [hshape₀.T4_eq] at h4c
        obtain ht | ht := hres .v3 t htp
        · rw [ht] at h3c
          exact absurd h3c (ne_of_lt P.hlt)
        · rw [ht] at h4c
          exact absurd h4c hThneTc
    -- The hot and cold witnesses sit at the two vertical legs `4 → 1` and
    -- `2 → 3`: they cannot sit at the slanted connectors (which are unmarked
    -- and hence adiabatic by admissibility), and they are distinct.
    obtain ⟨ih, hclassih, huniqih⟩ := hu_hot
    obtain ⟨ic, hclassic, huniqic⟩ := hu_cold
    change classifier ih = .hotIsothermal at hclassih
    change classifier ic = .coldIsothermal at hclassic
    change (∀ i : Process, (classifier i = .adiabatic) ↔ temps i = none) at hadm
    have hnotadi_h : classifier ih ≠ .adiabatic := by
      intro hcadi
      rw [hcadi] at hclassih
      exact ProcessClass.noConfusion hclassih
    have hnotadi_c : classifier ic ≠ .adiabatic := by
      intro hcadi
      rw [hcadi] at hclassic
      exact ProcessClass.noConfusion hclassic
    have hmark_ih : temps ih ≠ none := fun hnone => hnotadi_h ((hadm ih).mpr hnone)
    have hmark_ic : temps ic ≠ none := fun hnone => hnotadi_c ((hadm ic).mpr hnone)
    have hih_not13 : ih ≠ .v1 ∧ ih ≠ .v3 := by
      constructor
      · intro hv1; rw [hv1] at hmark_ih; exact hmark_ih hpin1
      · intro hv3; rw [hv3] at hmark_ih; exact hmark_ih hpin3
    have hic_not13 : ic ≠ .v1 ∧ ic ≠ .v3 := by
      constructor
      · intro hv1; rw [hv1] at hmark_ic; exact hmark_ic hpin1
      · intro hv3; rw [hv3] at hmark_ic; exact hmark_ic hpin3
    have hih_ne_ic : ih ≠ ic := by
      intro heq
      rw [heq] at hclassih
      exact ProcessClass.noConfusion (hclassih.symm.trans hclassic)
    have hih_cases : ih = .v2 ∨ ih = .v4 := by
      rcases ih with _ | _ | _ | _
      · exact absurd rfl hih_not13.1
      · exact Or.inl rfl
      · exact absurd rfl hih_not13.2
      · exact Or.inr rfl
    have hic_cases : ic = .v2 ∨ ic = .v4 := by
      rcases ic with _ | _ | _ | _
      · exact absurd rfl hic_not13.1
      · exact Or.inl rfl
      · exact absurd rfl hic_not13.2
      · exact Or.inr rfl
    have hmark4 : temps .v4 ≠ none := by
      rcases hih_cases with hv2 | hv4
      · rcases hic_cases with hc2 | hc4
        · exact absurd (hv2.trans hc2.symm) hih_ne_ic
        · rw [← hc4]; exact hmark_ic
      · rw [← hv4]; exact hmark_ih
    have hmark2 : temps .v2 ≠ none := by
      rcases hih_cases with hv2 | hv4
      · rw [← hv2]; exact hmark_ih
      · rcases hic_cases with hc2 | hc4
        · rw [← hc2]; exact hmark_ic
        · exact absurd (hv4.trans hc4.symm) hih_ne_ic
    cases h4 : temps .v4 with
    | none => exact absurd h4 hmark4
    | some t₄ =>
      cases h2 : temps .v2 with
      | none => exact absurd h2 hmark2
      | some t₂ =>
        -- The marked legs carry the reservoir at the leg temperature.
        have h4c : (S₀ .v4).T = t₄ := (hiso .v4 t₄ h4).1
        have h2c : (S₀ .v2).T = t₂ := (hiso .v2 t₂ h2).1
        rw [hshape₀.T4_eq] at h4c
        rw [hshape₀.T2_eq] at h2c
        subst h4c
        subst h2c
        -- Now temps = intemps and classifier = inclass pointwise.
        have htemps : temps = intemps := by
          funext i
          rcases i with _ | _ | _ | _ <;>
            simp only [hinD] <;>
            first
            | exact hpin1
            | exact hpin3
            | exact h2
            | exact h4
        have hclassh4 : classifier .v4 = .hotIsothermal := hpresh .v4 h4
        have hclassh2 : classifier .v2 = .coldIsothermal := hpresc .v2 h2
        have hclass1 : classifier .v1 = .adiabatic := by
          -- The leftover legs `.v1`, `.v3` are adiabatic: the hot- and
          -- cold-isothermal classes are each pinned to a unique leg by the
          -- `∃!` clauses, and the prescriptions already sit at `.v4`/`.v2`.
          rcases hc1 : classifier .v1 with _|_|_
          · have h4eq : .v4 = ih := huniqih .v4 hclassh4
            have h1eq : .v1 = ih := huniqih .v1 hc1
            exact
              absurd (h1eq.trans h4eq.symm)
                (by intro h; exact Vertex.noConfusion h)
          · have h2eq : .v2 = ic := huniqic .v2 hclassh2
            have h1eq : .v1 = ic := huniqic .v1 hc1
            exact
              absurd (h1eq.trans h2eq.symm)
                (by intro h; exact Vertex.noConfusion h)
          · rfl
        have hclass3 : classifier .v3 = .adiabatic := by
          rcases hc3 : classifier .v3 with _|_|_
          · have h4eq : .v4 = ih := huniqih .v4 hclassh4
            have h3eq : .v3 = ih := huniqih .v3 hc3
            exact
              absurd (h3eq.trans h4eq.symm)
                (by intro h; exact Vertex.noConfusion h)
          · have h2eq : .v2 = ic := huniqic .v2 hclassh2
            have h3eq : .v3 = ic := huniqic .v3 hc3
            exact
              absurd (h3eq.trans h2eq.symm)
                (by intro h; exact Vertex.noConfusion h)
          · rfl
        have hclass : classifier = inclass := by
          funext i
          rcases i with _ | _ | _ | _ <;>
            simp only [hinclassD] <;>
            first
            | exact hclass1
            | exact hclassh2
            | exact hclass3
            | exact hclassh4
        exact Prod.ext_iff.mpr ⟨hclass, htemps⟩

end IPhO_2026_3_C_1
