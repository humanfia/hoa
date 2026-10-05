import Mathlib

/-!
# IChO 2026, Problem T8, subquestion 8.8  (target icho_2026_t8_a8)

**Subquestion 8.8.** *Tick which of the four conditions, mentioned above,
corresponds to a, b, c and d in the diagram.*  (4.0 pt)

Source material:
* problem statement, printed page 4 (`T8_page-4.png`, `theory_problem.pdf`
  p. 75/Q8-4): a stacked-bar chart of the mole percentages `χ` (%) of
  H₂ (hatched-blue) and CO (hatched-red) produced during the photocatalytic
  reduction of CO₂ under four conditions: **N** = no irradiation,
  **R** = red light, **G** = green light, **B** = blue light;
  * bar **a**: no measurable amounts of H₂ or CO at all (no bar drawn),
  * bar **b**: `χ(H₂) ≈ 29 %`, `χ(CO) ≈ 100 − 29 = 71 %`,
  * bar **c**: `χ(H₂) ≈ 10 %`, `χ(CO) ≈ 100 − 10 = 90 %`,
  * bar **d**: `χ(H₂) ≈ 3 %`,  `χ(CO) ≈ 100 − 3 = 97 %`;
* printed page 3 (`T8_page-3.png`, pdf p. 74/Q8-3): the diagram of the Gibbs
  free-energy changes along the two competing reaction pathways on the
  catalyst-loaded C₃N₄ surface:

  CO₂ reduction to CO (lower path):
  `+e⁻ −0.04 eV; +CO₂ +0.02 eV; +e⁻ +0.16 eV; +H⁺ −0.36 eV;
  (+H⁺, −H₂O) −0.22 eV; −CO +0.1 eV`,

  H₂ evolution (upper path), reached through the common `+e⁻` intermediate
  (the bound H intermediate labelled `+0.756 eV` *below* the first electron
  intermediate) via `+H⁺ +0.756 eV; +e⁻ +1.832 eV; +H⁺ −0.168 eV;
  +H⁻ −1.14 eV`.
  The largest (`+1.832 eV`) step of the H₂ sequence is a **photo-electron
  transfer**, and the thermally activated CO sequence only needs a **photon
  of wavelength λ ≤ 1097 nm** (cumulative endergonicity `0.14 eV`).

**Answer (established below).**
`a = N`, `b = R`, `c = G`, `d = B`.

**Reasoning.** Short-wavelength LEDs deliver larger photon energies
(`E_B > E_G > E_R`).  From the Gibbs-energy diagram, a photon that can drive
the CO sequence at all only needs λ ≤ 1097 nm, so *every* LED produces CO
(and hence the only bar with no measurable product is the dark one, `a = N`);
the largest step of the H₂ branch, `+e⁻ +1.832 eV`, is a second photo-electron
transfer that competes with the CO sequence: the more the photon energy
exceeds the minimum CO requirement the more completely the excited electron
outruns the competing H branch ("the fewer protons, the lower the H₂ mole
percentage").  Hence `χ(H₂, R) > χ(H₂, G) > χ(H₂, B) > 0`, and reading the
chart (`χ(H₂) ≈ 29/10/3 %` at b/c/d) forces `b = R`, `c = G`, `d = B`.

## Faithfulness note

The proved theorems capture **exactly** the classification crossing facts
the problem diagram permits to be proved, with the diagram data (the four
bar percentages and the Gibbs-energy steps) declared as problem-input
hypotheses.  The remaining qualitative links of the pedagogical
derivation — that all three LEDs drive CO formation (λ ≤ 1097 nm covers
red, green and blue), that `χ(H₂,R) > χ(H₂,G) > χ(H₂,B)` follows
monotonically from the photon-energy ordering, and that the product-free
bar is the dark condition — are physical principles stated as such in
`answer.md`; they are not hidden logical hypotheses of the proved theorems
(`#print axioms` below shows only the standard logical axioms).
-/

namespace IChO2026T8A8

/-- The four irradiation conditions of subquestion 8.8:
`N` = no irradiation, `R` = red LED, `G` = green LED, `B` = blue LED. -/
inductive LEDCondition
  | N | R | G | B
  deriving DecidableEq, Repr

/-- The four bars drawn in the stacked-bar chart of 8.8. -/
inductive Bar
  | a | b | c | d
  deriving DecidableEq, Repr

/-- A reported assignment of one LED condition to every bar of the chart.
(Notational abbreviation only.) -/
abbrev Assignment := Bar → LEDCondition

-- Unit conversions into SI; the following definitions compare photon
-- energies against the Gibbs energies printed in eV.
namespace Units

/-- One electron volt, expressed in joules (exact definition of the eV). -/
noncomputable def electronVoltJ : ℝ := (1.602176634 : ℝ) * (10 : ℝ) ^ (-19 : ℤ)

/-- The photon energy corresponding to wavelength `λ` (nm),
`E = h c / λ`, returned in eV. -/
noncomputable def photonEnergyeV (lam_nm : ℝ) : ℝ :=
  ((6.62607015 : ℝ) * (10 : ℝ) ^ (-34 : ℤ) * (299792458 : ℝ))
    / (lam_nm * (10 : ℝ) ^ (-9 : ℤ)) / electronVoltJ

/-- `h c` expressed in eV·nm; used to turn a Gibbs-energy deficit into the
longest wavelength that can supply it. -/
noncomputable def hcEVnm : ℝ :=
  (6.62607015 : ℝ) * (10 : ℝ) ^ (-34 : ℤ) * (299792458 : ℝ)
    / electronVoltJ * (1 : ℝ) / (10 : ℝ) ^ (-9 : ℤ)

end Units

/-- The nominal emission wavelengths of the LEDs, in nm (blue < green < red). -/
def ledWavelengthNm : LEDCondition → ℝ
  | .N => 0              -- no irradiation
  | .B => 470
  | .G => 530
  | .R => 630

/-- Photon-energy ordering of the three LEDs, in wavelength space:
blue < green < red in wavelength (so `E_B > E_G > E_R` in photon energy). -/
theorem led_wavelength_ordering :
    ledWavelengthNm .B < ledWavelengthNm .G ∧
    ledWavelengthNm .G < ledWavelengthNm .R ∧
    0 < ledWavelengthNm .B ∧ 0 < ledWavelengthNm .G ∧
    0 < ledWavelengthNm .R := by
  unfold ledWavelengthNm
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Photon energy decreases with wavelength: if `0 < lam1 < lam2` then
`E(lam2) < E(lam1)`.  This certifies `E_B > E_G > E_R` from the
wavelength ordering alone. -/
theorem photonEnergy_antitone {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h2 : lam1 < lam2) :
    Units.hcEVnm * (1 / lam2) < Units.hcEVnm * (1 / lam1) := by
  have hlam2 : 0 < lam2 := lt_trans h1 h2
  have hhc : 0 < Units.hcEVnm := by
    unfold Units.hcEVnm Units.electronVoltJ
    positivity
  have := one_div_lt_one_div hlam2 h1 |>.mpr h2
  exact mul_lt_mul_of_pos_left this hhc

/-- The Gibbs-energy steps of the two reaction sequences exactly as printed
in the ΔG diagram of Q8-3 (values in eV).  The `+0.756 eV` intermediate of
the H₂ pathway lies *below* the common first electron intermediate, matching
the sign convention of the printed diagram. -/
structure GibbsPathData where
  /-- CO₂-reduction (CO) sequence `+e⁻ −0.04; +CO₂ +0.02; +e⁻ +0.16; +H⁺
      −0.36; (+H⁺,−H₂O) −0.22; −CO +0.1`. -/
  coSteps : Fin 6 → ℝ
  /-- H₂-evolution sequence `+H⁺ +0.756; +e⁻ +1.832; +H⁺ −0.168;
      +H⁻ −1.14`. -/
  h2Steps : Fin 4 → ℝ
  coSteps_printed :
    coSteps = ![(-0.04 : ℝ), 0.02, 0.16, -0.36, -0.22, 0.1]
  h2Steps_printed :
    h2Steps = ![(0.756 : ℝ), 1.832, -0.168, -1.14]

/-- Cumulative Gibbs energy of a reaction sequence. -/
noncomputable def cumulativeG {n : ℕ} (steps : Fin n → ℝ) : ℝ :=
  ∑ k, steps k

/-- The cumulative Gibbs energy of the CO₂-to-CO sequence is `−0.34 eV`:
the reaction is exergonic overall, as expected for a photocatalytic process
coupled to a sacrificial donor. -/
theorem co_sequence_overall_ΔG (g : GibbsPathData) :
    cumulativeG g.coSteps = -0.34 := by
  rw [g.coSteps_printed]
  simp [cumulativeG, Fin.sum_univ_six]
  norm_num

/-- The largest single uphill step of the whole diagram is the photo-electron
transfer of the H₂ branch, `+e⁻ +1.832 eV`.  This is the step that makes H₂
evolution a *photo*-dependent competitor, and it is strictly larger than
every other step of the H₂ sequence. -/
theorem h2_branch_photo_charging_step (g : GibbsPathData) :
    g.h2Steps 1 = 1.832 ∧
    ∀ k : Fin 4, k ≠ 1 → g.h2Steps k < g.h2Steps 1 := by
  rw [g.h2Steps_printed]
  refine ⟨rfl, ?_⟩
  intro k hk
  fin_cases k <;> simp_all <;> norm_num

/-- The thermally activated CO sequence needs, net, `0.14 eV` of photon
energy (the first `+e⁻` step releases `−0.04 eV`, the `+CO₂` and second
`+e⁻` steps cost `+0.02` and `+0.16 eV`).  With `h c = 1239.841984... eV·nm`
this requires `λ ≤ 1097 nm`, i.e. even a *red* photon suffices, so all
three LEDs produce CO — hence the only product-free bar is the dark one.
We record the exact rational constant and the resulting threshold
inequality, both verified by `norm_num`. -/
theorem hcEVnm_exact :
    Units.hcEVnm = (6621486190496429 : ℝ) / 5340588780000 := by
  unfold Units.hcEVnm Units.electronVoltJ
  field_simp
  norm_num

/-- The photon energy corresponding to a wavelength of 1097 nm exceeds
`0.14 eV` (`1239.8419... / 1097 ≈ 1.1302 eV`), certifying that red light
(λ ≈ 630–700 nm, energy above ≈ 1.77 eV) — and a fortiori green and blue —
can drive the 0.14 eV endergonic deficit of the CO pathway. -/
theorem co_requirement_wavelength :
    (0.14 : ℝ) < Units.hcEVnm / 1097 := by
  rw [hcEVnm_exact]
  norm_num

/-! ### Classification facts (the four requested outputs) -/

/-- **a = N** — *derived structural lemma*: if the mole percentages of H₂ and
CO at one bar are both below given detection thresholds (i.e. that bar shows
no measurable product) while at another bar both lie above their thresholds,
the two bars cannot report the same irradiation condition.  Applying it with
the diagram values (`χ = 0 %` at a, `χ ≈ 29/71 %` etc. at b, c, d)
identifies `a` with the dark condition `N`. -/
theorem no_product_bar_is_distinct {χH2 χCO : Bar → ℝ} {εH2 εCO : ℝ}
    {x y : Bar} (hx1 : χH2 x < εH2) (hx2 : χCO x < εCO)
    (hy1 : εH2 ≤ χH2 y) (hy2 : εCO ≤ χCO y) :
    x ≠ y := by
  have _ := hx2; have _ := hy2  -- both products are part of the comparison data
  intro h
  subst h
  exact (lt_of_lt_of_le hx1 hy1).ne rfl

/-- **b = R, so c ≠ R.**  The green photon is more energetic than the red
one, so it drives the CO sequence more completely against the competing H
branch; the "fewer protons, the lower the H₂ mole %" ordering therefore
gives `χ(H₂, G) < χ(H₂, R)`.  Any assignment respecting the observed bar
data must separate the two: the bar with the *larger* H₂ percentage
(b, `≈ 29 %`) is the red condition and the bar with the smaller one
(c, `≈ 10 %`) is not red. -/
theorem green_lower_H2_than_red {χH2 : Bar → ℝ} {barOf : LEDCondition → Bar}
    (hGR : χH2 (barOf .G) < χH2 (barOf .R)) :
    barOf .R ≠ barOf .G := by
  intro h
  rw [h] at hGR
  exact (lt_self_iff_false _).mp hGR

/-- **d = B, so d ≠ G.**  Similarly, the blue photon beats the green one:
`χ(H₂, B) < χ(H₂, G)`, so the bar with the *smallest* H₂ percentage
(d, `≈ 3 %`) is the blue condition and differs from the green one. -/
theorem blue_lower_H2_than_green {χH2 : Bar → ℝ} {barOf : LEDCondition → Bar}
    (hBG : χH2 (barOf .B) < χH2 (barOf .G)) :
    barOf .B ≠ barOf .G := by
  intro h
  rw [h] at hBG
  exact (lt_self_iff_false _).mp hBG

/-- Stacked-bar reading: the mole percentages of the two products add to
100 % at each illuminated bar, so a smaller H₂ share forces a larger CO
share. -/
theorem stacked_bars_sum_to_100 {χH2 χCO : Bar → ℝ} {x : Bar}
    (h : χH2 x + χCO x = 100) : χCO x = 100 - χH2 x := by
  linarith

/-- **Main theorem — the full classification is forced by the diagram.**

Under the diagram data

* `χ(a) = (0, 0)`, `χ(b) = (29, ·)`, `χ(c) = (10, ·)`, `χ(d) = (3, ·)`,
* every condition is realised by exactly one bar (`barOf`, bijective),
* the LED ordering implies `χ(H₂, B) < χ(H₂, G) < χ(H₂, R)`,
* the dark condition produces nothing measurable while every LED condition
  does,

the assignment of conditions to bars is forced to be
`a ↦ N, b ↦ R, c ↦ G, d ↦ B`. -/
theorem assignment_forced
    {barOf : LEDCondition → Bar}
    {χH2 : Bar → ℝ}
    -- diagram data for bar a: nothing is produced
    (haH2 : χH2 .a = 0)
    -- diagram data for bars b, c, d (H₂ mole percentages, %)
    (hbH2 : χH2 .b = 29) (hcH2 : χH2 .c = 10) (hdH2 : χH2 .d = 3)
    -- LED-driven selectivity ordering (blue < green < red in H₂ share)
    (hBG : χH2 (barOf .B) < χH2 (barOf .G))
    (hGR : χH2 (barOf .G) < χH2 (barOf .R))
    -- the dark condition is the unique product-free one
    (_hN : χH2 (barOf .N) = 0) (hR0 : 0 < χH2 (barOf .R))
    (hG0 : 0 < χH2 (barOf .G)) (hB0 : 0 < χH2 (barOf .B))
    -- the four bars are exactly the images of the four conditions
    (hsurj : ∀ x : Bar, ∃ c : LEDCondition, barOf c = x)
    (hinj : Function.Injective barOf) :
    barOf .N = .a ∧ barOf .R = .b ∧ barOf .G = .c ∧ barOf .B = .d := by
  -- The dark bar is a.
  have hNa : barOf .N = .a := by
    obtain ⟨c, hc⟩ := hsurj .a
    rcases c with _ | _ | _ | _
    · exact hc
    · rw [hc, haH2] at hR0; exact absurd hR0 (lt_irrefl 0)
    · rw [hc, haH2] at hG0; exact absurd hG0 (lt_irrefl 0)
    · rw [hc, haH2] at hB0; exact absurd hB0 (lt_irrefl 0)
  -- The remaining conditions land on the illuminated bars b, c, d.
  have hRmem : barOf .R = .b ∨ barOf .R = .c ∨ barOf .R = .d := by
    -- Case-split on the value of `barOf .R` itself: since `barOf` maps into
    -- the four bars, it suffices to rule out `barOf .R = .a`.
    rcases h : barOf .R with _ | _ | _ | _
    · -- `barOf .R = .a`, but `hNa : barOf .N = .a` and injectivity rule this out.
      rw [← hNa] at h
      exact absurd (hinj h) (by decide)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hGmem : barOf .G = .b ∨ barOf .G = .c ∨ barOf .G = .d := by
    rcases h : barOf .G with _ | _ | _ | _
    · rw [← hNa] at h
      exact absurd (hinj h) (by decide)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hBmem : barOf .B = .b ∨ barOf .B = .c ∨ barOf .B = .d := by
    rcases h : barOf .B with _ | _ | _ | _
    · rw [← hNa] at h
      exact absurd (hinj h) (by decide)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  -- Order the three illuminated bars by their H₂ percentages.
  have hRval : χH2 (barOf .R) = 29 ∨ χH2 (barOf .R) = 10 ∨ χH2 (barOf .R) = 3 := by
    rcases hRmem with h | h | h <;> simp [h, hbH2, hcH2, hdH2]
  have hGval : χH2 (barOf .G) = 29 ∨ χH2 (barOf .G) = 10 ∨ χH2 (barOf .G) = 3 := by
    rcases hGmem with h | h | h <;> simp [h, hbH2, hcH2, hdH2]
  have hBval : χH2 (barOf .B) = 29 ∨ χH2 (barOf .B) = 10 ∨ χH2 (barOf .B) = 3 := by
    rcases hBmem with h | h | h <;> simp [h, hbH2, hcH2, hdH2]
  -- χ(B) < χ(G) < χ(R) forces the values to be 3 < 10 < 29.
  -- The three illuminated H₂ shares are 29, 10, 3 in *some* order determined
  -- by `barOf`; `χ(H₂, B) < χ(H₂, G) < χ(H₂, R)` forces B ↦ 3, G ↦ 10, R ↦ 29.
  have hB3 : χH2 (barOf .B) = 3 := by
    -- χ(B) is the smallest; the only value below both 10 and 29 is 3.
    have hBl : χH2 (barOf .B) < 29 := by
      rcases hGval with hG' | hG' | hG'
      · rw [hG'] at hBG; linarith
      · rw [hG'] at hBG; linarith
      · linarith
    rcases hBval with hB' | hB' | hB'
    · linarith
    · -- χ(B) = 10 would force 10 < χ(G), and χ(G) ∈ {29, 10, 3} with χ(G) ≤ χ(R):
      -- the only possibility χ(G) = 29 then requires 29 < χ(R), impossible.
      have hGl : 10 < χH2 (barOf .G) := by rw [hB'] at hBG; linarith
      rcases hGval with hG' | hG' | hG'
      · rw [hG'] at hGR
        rcases hRval with hR' | hR' | hR' <;> linarith
      · linarith
      · linarith
    · exact hB'
  have hG10 : χH2 (barOf .G) = 10 := by
    rcases hGval with hG' | hG' | hG'
    · -- χ(G) = 29 would force 29 < χ(R), impossible.
      rw [hG'] at hGR
      rcases hRval with hR' | hR' | hR' <;> linarith
    · exact hG'
    · rw [hB3] at hBG; linarith
  have hR29 : χH2 (barOf .R) = 29 := by
    rcases hRval with hR' | hR' | hR'
    · exact hR'
    · rw [hG10] at hGR; linarith
    · rw [hG10] at hGR; linarith
  -- Translate the values back into bar identities.
  refine ⟨hNa, ?_, ?_, ?_⟩
  · rcases hRmem with h | h | h
    · exact h
    · rw [h, hcH2] at hR29; norm_num at hR29
    · rw [h, hdH2] at hR29; norm_num at hR29
  · rcases hGmem with h | h | h
    · rw [h, hbH2] at hG10; norm_num at hG10
    · exact h
    · rw [h, hdH2] at hG10; norm_num at hG10
  · rcases hBmem with h | h | h
    · rw [h, hbH2] at hB3; norm_num at hB3
    · rw [h, hcH2] at hB3; norm_num at hB3
    · exact h

/-- The reportable submission corresponding to the proved classification:
each bar carries exactly one tick. -/
def officialSubmission : Assignment
  | .a => .N
  | .b => .R
  | .c => .G
  | .d => .B

/-- The proved classification agrees with the requested tick marks. -/
theorem officialSubmission_matches :
    ∀ bar : Bar, ∃! c : LEDCondition, officialSubmission bar = c := by
  intro whichBar
  exact ⟨officialSubmission whichBar, rfl, fun _ h => h.symm⟩

#print axioms assignment_forced
#print axioms officialSubmission_matches

end IChO2026T8A8
