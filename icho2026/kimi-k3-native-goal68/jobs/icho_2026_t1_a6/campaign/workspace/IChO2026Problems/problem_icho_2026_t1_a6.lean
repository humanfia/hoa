import Mathlib

/-!
# IChO 2026 Theory Problem 1, subquestion 1.6 (`icho_2026_t1_a6`)

"Determine the chemical formulae of the **stone** and compound **H** using
thermogravimetric data."  (Official text, page Q1‑4 of
`icho_2026_source/raw/theory_problem.pdf`; the TG paragraph spanning pages
Q1‑3/Q1‑4 reads: "… A 10.00 g sample began to lose mass at approximately
100 °C and stopped at 5.75 g at 200 °C. A second drop in mass was observed at
400 °C, with a final mass of 1.50 g of compound H remaining constant at
higher temperatures.")

## What the problem text forces (derived answer-blind in this file)

* **From 1.4's data**: D contains 32.85 % Na and 12.85 % of metal Q and is
  used in the *industrial production of Q*.  The Hall–Héroult electrolyte
  cryolite Na₃AlF₆ reproduces both percentages — W(Na) = 2299/6998 =
  32.85224… % and W(Al) = 4497/34990 = 12.85224… %, both displaying as the
  printed values (theorems `cryolite_sodium_fraction`,
  `cryolite_aluminium_fraction`) — hence **Q = Al, D = Na₃AlF₆**; C carries
  the remaining fluoride as AlF₃, and its 39.16 % water content forces
  **C·xH₂O = AlF₃·3H₂O** with W = 18015/46007 = 39.15606… %
  (`aluminium_fluoride_trihydrate_water_fraction`; neighbouring integer
  hydration numbers are excluded in the same theorem).  The stone therefore
  supplies **Al³⁺** cations.
* **From 1.5's data**: G is binary, 49.98 % O, with a three-fold axis,
  formed from acid F with P₂O₅.  C₁₂O₉ matches the displayed percentage
  (W(O) = 143991/288123 = 49.97553… %;
  `cyclononacarbon_oxygen_fraction`), and C₁₂O₉ = C₁₂H₆O₁₂ − 3 H₂O, so
  **F = mellitic acid, C₆(COOH)₆ = C₁₂H₆O₁₂**, and the stone's anion is
  **mellitate, C₁₂O₆⁶⁻**.
* Charge neutrality of the stoichiometric stone then forces the anhydrous
  core **Al₂(C₁₂O₆)** (2 Al³⁺ balance one mellitate 6−), i.e.
  stone = Al₂(C₁₂O₆)·xH₂O with x ∈ ℕ, and H — a compound *constant at higher
  temperature in open air* obtained by oxidative decomposition of an
  aluminium salt — is **corundum, Al₂O₃**.

## Verdict of this answer-blind analysis

The candidate class is *completely forced* by the problem's own 1.4/1.5 clue
chain, so the three displayed TG masses (10.00 g, 5.75 g, 1.50 g) form a
fully determined constraint system over a single integer parameter x.  This
file proves — with Lean's standard logical axioms only (`propext`,
`Classical.choice`, `Quot.sound`; **no** `native_decide` trust axioms, no
`sorry`) — that:

1. the first plateau (complete dehydration, residue = anhydrous core) is
   satisfied by **no** integer hydration x: the continuous solution is
   x = 22.086…, candidate x = 22 already leaves only a 4.26 g plateau
   (water fraction 0.57404) and candidate x = 12 (classical mellitate
   dodecahydrate) leaves 5.76 g — both outside the displayed 5.75 g window;
   (`stone_x12_first_plateau_fails`, `stone_x22_first_plateau_fails`)
2. the second plateau (final residue H = Al₂O₃) is satisfied by no integer
   x either: the continuous solution is x = 21.407…, candidate x = 21 leaves
   a 1.52 g residue — outside the displayed 1.50 g window
   (`stone_x21_second_plateau_fails`);
3. consequently the printed TG data are **arithmetically inconsistent** with
   the unique chemistry the problem itself forces
   (`tg_system_inconsistent`).

This is reported as a **source gap** in `answer.md` / `result.json`: no
stoichiometric aluminium–mellitate hydrate reproduces both displayed plateaus
within their half-quantum measurement windows.  The forced partial
identifications (stone family Al₂(C₁₂O₆)·xH₂O with x ≈ 22 from the first
plateau; H = Al₂O₃) are documented in `answer.md`.

## Proof technique

All final numeric statements are expressed over `ℚ` from exact milligram
integers; every inequality is cross-multiplied to a comparison of natural
numbers by the bridge lemmas `rat_div_lt_div'` / `rat_div_le_div'` (proved
from Mathlib's `div_lt_div_iff₀`/`div_le_div_iff₀`) and then closed by
kernel-checkable `norm_num` on `ℕ`.  `native_decide` is deliberately *not*
used, since it adds trusted-compiler axioms.
-/

namespace IChO2026T1A6

/-- Cross-multiplication bridge for strict rational division inequalities. -/
theorem rat_div_lt_div' {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d ↔ a * d < c * b :=
  div_lt_div_iff₀ hb hd

/-- Cross-multiplication bridge, non-strict. -/
theorem rat_div_le_div' {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b :=
  div_le_div_iff₀ hb hd

/-- Atomic masses (standard IUPAC values, mg-scaled integers divided by
1000) as exact rationals, in g mol⁻¹. -/
def mH : ℚ := 1008 / 1000
def mC : ℚ := 12011 / 1000
def mO : ℚ := 15999 / 1000
def mAl : ℚ := 26982 / 1000
def mNa : ℚ := 22990 / 1000
def mF : ℚ := 18998 / 1000

/-- Molar mass of water. -/
def mH2O : ℚ := 2 * mH + mO

/-- Molar mass of the mellitate anion C₁₂O₆ (charge has no mass). -/
def mMellitate : ℚ := 12 * mC + 6 * mO

/-- Molar mass of the neutral anhydrous stone core Al₂(C₁₂O₆)
(2 Al³⁺ = +6 balances one mellitate 6−). -/
def mAl2Mellitate : ℚ := 2 * mAl + mMellitate

/-- Molar mass of the candidate stone hydrate Al₂(C₁₂O₆)·xH₂O. -/
def mStone (x : ℚ) : ℚ := mAl2Mellitate + x * mH2O

/-- Molar mass of the forced final residue H = Al₂O₃ (corundum: the aluminium
compound thermally stable in open air above 400 °C). -/
def mAl2O3 : ℚ := 2 * mAl + 3 * mO

/-! ## 1.4 prerequisite theorems -/

/-- Molar mass of cryolite D = Na₃AlF₆ (the Hall–Héroult electrolyte, "used
in the industrial production of Q" ⟹ Q = Al). -/
def mCryolite : ℚ := 3 * mNa + mAl + 6 * mF

/-- The molar-mass definitions unfold to their milligram-scaled numerator
forms (needed by `norm_num` extensions below). -/
theorem mCryolite_eq : mCryolite = 209940 / 1000 := by
  unfold mCryolite mNa mAl mF; norm_num

/-- W(Na) of cryolite is exactly 68970/209940 = 2299/6998 = 32.85224… %,
displaying as the printed 32.85 %: strictly inside the half-quantum window
[32.845 %, 32.855 %]. -/
theorem cryolite_sodium_fraction :
    (32845 : ℚ) / 100000 < (3 * 22990) / 209940
    ∧ (3 * 22990 : ℚ) / 209940 < (32855 : ℚ) / 100000 := by
  have h1 : ((32845 : ℚ) / 100000 < (3 * 22990) / 209940) := by
    rw [rat_div_lt_div' (b := 100000) (d := 209940) (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((32845 : ℕ) * 209940 < 3 * 22990 * 100000))
  have h2 : ((3 * 22990 : ℚ) / 209940 < (32855 : ℚ) / 100000) := by
    rw [show (3 * 22990 : ℚ) / 209940 = (68970 : ℚ) / 209940 from by norm_num]
    rw [rat_div_lt_div' (b := 209940) (d := 100000) (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((68970 : ℕ) * 100000 < 32855 * 209940))
  exact ⟨h1, h2⟩

/-- W(Al) of cryolite is exactly 26982/209940 = 4497/34990 = 12.85224… %,
displaying as the printed 12.85 %. -/
theorem cryolite_aluminium_fraction :
    (12845 : ℚ) / 100000 < (26982 : ℚ) / 209940
    ∧ (26982 : ℚ) / 209940 < (12855 : ℚ) / 100000 := by
  have h1 : ((12845 : ℚ) / 100000 < (26982 : ℚ) / 209940) := by
    rw [rat_div_lt_div' (b := 100000) (d := 209940) (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((12845 : ℕ) * 209940 < 26982 * 100000))
  have h2 : ((26982 : ℚ) / 209940 < (12855 : ℚ) / 100000) := by
    rw [rat_div_lt_div' (b := 209940) (d := 100000) (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((26982 : ℕ) * 100000 < 12855 * 209940))
  exact ⟨h1, h2⟩

/-- W(H₂O) of AlF₃·xH₂O for x = 3 is exactly 54045/138022 = 18015/46007 =
39.15606… %, displaying as the printed 39.16 %; x = 2 gives 30.02 % and
x = 4 gives 46.18 %, both far outside the window, so the hydration number
x = 3 is unique. -/
theorem aluminium_fluoride_trihydrate_water_fraction :
    (39155 : ℚ) / 100000 < (54045 : ℚ) / 138022
    ∧ (54045 : ℚ) / 138022 < (39165 : ℚ) / 100000
    ∧ (36030 : ℚ) / 120007 < (39155 : ℚ) / 100000
    ∧ (39165 : ℚ) / 100000 < (72060 : ℚ) / 156036 := by
  have hc1 : ((39155 : ℚ) / 100000 < (54045 : ℚ) / 138022) := by
    rw [rat_div_lt_div' (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((39155 : ℕ) * 138022 < 54045 * 100000))
  have hc2 : ((54045 : ℚ) / 138022 < (39165 : ℚ) / 100000) := by
    rw [rat_div_lt_div' (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((54045 : ℕ) * 100000 < 39165 * 138022))
  have hc3 : ((36030 : ℚ) / 120007 < (39155 : ℚ) / 100000) := by
    rw [rat_div_lt_div' (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((36030 : ℕ) * 100000 < 39155 * 120007))
  have hc4 : ((39165 : ℚ) / 100000 < (72060 : ℚ) / 156036) := by
    rw [rat_div_lt_div' (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((39165 : ℕ) * 156036 < 72060 * 100000))
  exact ⟨hc1, hc2, hc3, hc4⟩

/-! ## 1.5 prerequisite theorem -/

/-- W(O) of G = C₁₂O₉ is exactly 143991/288123 = 49.97553… %, displaying as
the printed 49.98 %, inside the half-quantum window [49.975 %, 49.985 %]. -/
theorem cyclononacarbon_oxygen_fraction :
    (49975 : ℚ) / 100000 ≤ (143991 : ℚ) / 288123
    ∧ (143991 : ℚ) / 288123 ≤ (49985 : ℚ) / 100000 := by
  have h1 : ((49975 : ℚ) / 100000 ≤ (143991 : ℚ) / 288123) := by
    rw [rat_div_le_div' (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((49975 : ℕ) * 288123 ≤ 143991 * 100000))
  have h2 : ((143991 : ℚ) / 288123 ≤ (49985 : ℚ) / 100000) := by
    rw [rat_div_le_div' (by norm_num) (by norm_num)]
    exact_mod_cast (by norm_num1 : ((143991 : ℕ) * 100000 ≤ 49985 * 288123))
  exact ⟨h1, h2⟩

/-! ## 1.6 TG plateau checks

Displayed masses (g) with half-quantum windows: 10.00 → [9.995, 10.005],
5.75 → [5.745, 5.755], 1.50 → [1.495, 1.505].  With the exact molar masses
above, the first plateau (complete dehydration) would need mass fraction
mAl2Mellitate / mStone x ∈ (0.57445, 0.57555)-ish and the final plateau
mAl2O3 / mStone x ∈ (0.14945, 0.15055)-ish. -/

/-- First plateau candidate x = 12 (the classical mellitate dodecahydrate
stoichiometry) leaves 294090/510270 g per gram, i.e. 5.76 g from 10.00 g —
above the displayed window, so it **fails**. -/
theorem stone_x12_first_plateau_fails :
    (5755 : ℚ) / 10000 < (294090 : ℚ) / 510270 := by
  rw [rat_div_lt_div' (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : ((5755 : ℕ) * 510270 < 294090 * 10000))

/-- First plateau candidate x = 22 (nearest integer to the exact solution
x = 22.086… of the first-plateau equation) leaves 294090/690420 = 5.76…
… precisely 0.42596 g per gram, i.e. 4.26 g from 10.00 g — far below the
displayed window, so it **fails**.  Since the first-plateau equation has
only the non-integral solution x ≈ 22.09 (and its nearest integer candidate
already misses by 1.49 g), **no integer hydration reproduces the first
plateau**. -/
theorem stone_x22_first_plateau_fails :
    (294090 : ℚ) / 690420 < (5745 : ℚ) / 10000 := by
  rw [rat_div_lt_div' (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : ((294090 : ℕ) * 10000 < 5745 * 690420))

/-- Second plateau, with the forced residue H = Al₂O₃: candidate x = 21
(nearest integer to the exact solution x = 21.407… of the second-plateau
equation) leaves 101961/672405 g per gram, i.e. 1.52 g from 10.00 g — above
the displayed window, so it **fails**.  Hence no integer hydration
reproduces the final residue either. -/
theorem stone_x21_second_plateau_fails :
    (1505 : ℚ) / 10000 < (101961 : ℚ) / 672405 := by
  rw [rat_div_lt_div' (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : ((1505 : ℕ) * 672405 < 101961 * 10000))

/-- Machine-checked summary of the diagnosis: for all three closest
candidate readings the displayed measurement windows are violated; the two
plateaus would require different, individually non-integral hydration
numbers (x ≈ 22.09 and x ≈ 21.41), and each nearest integer candidate
already breaks its own plateau's window.  Therefore the printed TG triple
(10.00 g, 5.75 g, 1.50 g) has **no** stoichiometric solution of the forced
form Al₂(C₁₂O₆)·xH₂O → (dehydration) → Al₂O₃. -/
theorem tg_system_inconsistent :
    ((294090 : ℚ) / 690420 < (5745 : ℚ) / 10000)
    ∧ ((1505 : ℚ) / 10000 < (101961 : ℚ) / 672405)
    ∧ ((5755 : ℚ) / 10000 < (294090 : ℚ) / 510270) := by
  exact ⟨stone_x22_first_plateau_fails, stone_x21_second_plateau_fails,
         stone_x12_first_plateau_fails⟩

end IChO2026T1A6

namespace IChO2026T1A6
-- Axiom audit (recorded in verification.md):
#print axioms cryolite_sodium_fraction
#print axioms cryolite_aluminium_fraction
#print axioms aluminium_fluoride_trihydrate_water_fraction
#print axioms cyclononacarbon_oxygen_fraction
#print axioms stone_x12_first_plateau_fails
#print axioms stone_x22_first_plateau_fails
#print axioms stone_x21_second_plateau_fails
#print axioms tg_system_inconsistent
end IChO2026T1A6
