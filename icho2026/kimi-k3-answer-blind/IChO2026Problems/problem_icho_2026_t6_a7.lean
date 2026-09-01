import IChO2026Chem

/-!
# IChO 2026 (58th, Uzbekistan) — Problem T6, subquestion 6.7 (`icho_2026_t6_a7`)

**Problem (T6-A7, answer-blind formalization).** P6 is the cyclic porphyrin
hexamer ("(porphyrin–alkyne)₆") printed on page Q6-4 (`T6_page-4.png`):
six Zn-porphyrin units joined into a ring by butadiyne (–C≡C–C≡C–) bridges
between opposite (trans) meso positions; the remaining two meso positions of
each porphyrin carry Ar substituents.  The linker identity is confirmed by the
printed synthesis on the same page: `Q → R` installs silyl-protected alkynes
(Pd⁰/PPh₃/CuI with (C₆H₁₃)₃Si–acetylene, then `n-Bu₄NF` deprotection) and the
final step (PdCl₂/PPh₃/CuI with a *p*-benzoquinone oxidant) is an oxidative
terminal-alkyne homocoupling, which furnishes butadiyne bridges.

Page Q6-5 (`T6_page-5.png`) states the counting convention: π electrons are
counted **only along the continuous conjugated pathway** around the
macrocycle, exemplified by [n]CPPs (bold pathway: 4 π electrons per
para-phenylene ring — only the two on-pathway double bonds of each ring are
counted, not all six benzene π electrons).

**Question 6.7.** Based on Hückel's rule, find the minimum number of
electrons n(e) that should be removed from P6 to achieve global aromaticity,
and write the total number n(t) of π electrons in that global aromatic system.

## Source-derived component ledger (problem images)

* Zn-porphyrin unit — multiplicity 6 (repeat unit; ring subscript `₆` on
  `T6_page-4.png`) — contributes 10 π electrons per unit on the global
  pathway: the trans meso→meso half-perimeter carries 4 pyrrole C=C bonds and
  1 meso–α C=C bond of the porphyrin 18π circuit.
* Butadiyne bridge –C≡C–C≡C– — multiplicity 6 (linker between trans meso
  positions) — contributes 4 π electrons per bridge: one conjugation-plane
  π pair per triple bond, two triple bonds per bridge.

Neutral P6: `6 * 10 + 6 * 4 = 84` π electrons on the global pathway
(`84 = 4 * 21`, a 4n count).  Hückel aromaticity needs `4n + 2`, so removing
`k` electrons must satisfy `84 - k = 4n + 2`; the smallest such `k` is `2`
(`k = 0` gives 84, `k = 1` gives 83), giving `n(t) = 84 - 2 = 82 = 4 * 20 + 2`.

## Answer-blind contract

This file *states* the source-faithful obligations and now carries
kernel-checked proofs for all of them.  The two `*_contract` theorems bind the
answer-blind candidate payload hashes (role digests) to the semantic specs.
-/

namespace IChO2026T6A7

/-- **Hückel's rule** (problem-stated basis of 6.7): a planar, fully
conjugated monocyclic π system is aromatic when its π-electron count equals
`4n + 2` for some natural `n`.  The problem's own context ("When P6 is
oxidised, it can exhibit global aromaticity and global anti-aromaticity")
licenses applying this count predicate to the oxidised forms of P6. -/
def HuckelAromatic (piElectrons : ℕ) : Prop :=
  ∃ n : ℕ, piElectrons = 4 * n + 2

/-- Number of porphyrin units in P6.  Source: `T6_page-4.png`, the printed
P6 structure — the repeat-unit parenthesis carries subscript 6 (cyclic
hexamer). -/
def p6PorphyrinUnitCount : ℕ := 6

/-- Number of butadiyne (–C≡C–C≡C–) bridges in P6: one bridge between each
pair of adjacent porphyrin units of the ring, hence as many bridges as
porphyrin units.  Source: `T6_page-4.png` (P6 structure and the oxidative
alkyne-coupling step of the printed synthesis). -/
def p6ButadiyneLinkerCount : ℕ := 6

/-- π electrons that one porphyrin unit contributes to the **global conjugated
pathway**.  The pathway enters and leaves each porphyrin at opposite (trans)
meso carbons and follows half of the porphyrin's 18π perimeter; on that route
lie five π bonds of the circuit (four pyrrole C=C bonds and one meso–α C=C
bond), i.e. `5 * 2 = 10` π electrons.  Source: `T6_page-4.png` structure with
the `T6_page-5.png` bold-pathway counting convention. -/
def porphyrinPathwayPiElectronCount : ℕ := 10

/-- π electrons that one butadiyne bridge contributes to the global pathway:
each triple bond contributes the one π pair lying in the conjugation plane
(the orthogonal π pair is not part of the ring's conjugated loop, exactly as
the CPP example on `T6_page-5.png` counts only the on-pathway π bonds of each
phenylene), so `2` triple bonds contribute `2 * 2 = 4` π electrons. -/
def butadiynePathwayPiElectronCount : ℕ := 4

/-- Total π-electron count of **neutral** P6 along the global conjugated
pathway: porphyrin and linker contributions. -/
def p6NeutralGlobalPiElectronCount : ℕ :=
  p6PorphyrinUnitCount * porphyrinPathwayPiElectronCount +
    p6ButadiyneLinkerCount * butadiynePathwayPiElectronCount

/-- π electrons on the global pathway of P6 after `k` electrons have been
removed by oxidation.  (Natural subtraction is harmless here: the Hückel
predicate is false at `0`, so over-oxidation indices never enter the aromatic
set.) -/
def p6GlobalPiElectronCountAfterOxidation (k : ℕ) : ℕ :=
  p6NeutralGlobalPiElectronCount - k

/-- Neutral P6 carries 84 π electrons on its global pathway
(`6 * 10 + 6 * 4 = 84 = 4 * 21`, formally a 4n, i.e. anti-aromatic, count). -/
theorem p6_neutral_global_pi_electron_count :
    p6NeutralGlobalPiElectronCount = 84 := by
  rfl

/-- **Requested output `minimum_electrons_removed`.**  The minimum number of
electrons to remove from P6 so that the remaining global-pathway count obeys
Hückel's `4n + 2` rule is `2`: removing `0` leaves `84 = 4 * 21` (4n), removing
`1` leaves `83` (odd), while removing `2` leaves `82 = 4 * 20 + 2`. -/
theorem p6_minimum_electrons_removed :
    IsLeast {k : ℕ | HuckelAromatic (p6GlobalPiElectronCountAfterOxidation k)} 2 := by
  constructor
  · -- Membership: after removing 2 electrons the count is 82 = 4 * 20 + 2.
    exact ⟨20, rfl⟩
  · -- Minimality: no smaller `k` gives a `4n + 2` count (84 is 4n, 83 is odd).
    intro k hk
    obtain ⟨n, hn⟩ := hk
    have heq : p6GlobalPiElectronCountAfterOxidation k = 84 - k := rfl
    rw [heq] at hn
    omega

/-- **Requested output `global_pi_electron_count`.**  After removing the
minimum number of electrons (2), the global aromatic system of P6²⁺ contains
`84 - 2 = 82` π electrons. -/
theorem p6_global_pi_electron_count_at_minimum_oxidation :
    p6GlobalPiElectronCountAfterOxidation 2 = 82 := by
  rfl

/-- The aromatic count is a genuine Hückel `4n + 2` number: `82 = 4 * 20 + 2`. -/
theorem p6_aromatic_count_satisfies_huckel : HuckelAromatic 82 :=
  ⟨20, rfl⟩

/-- **Raw derivation spec (both requested outputs).**  Conjunction of the
neutral-count anchor, the minimality statement for `n(e) = 2`, and the exact
aromatic count `n(t) = 82`. -/
def P6GlobalAromaticityRawSpec : Prop :=
  p6NeutralGlobalPiElectronCount = 84 ∧
    IsLeast {k : ℕ | HuckelAromatic (p6GlobalPiElectronCountAfterOxidation k)} 2 ∧
      p6GlobalPiElectronCountAfterOxidation 2 = 82

theorem p6_global_aromaticity_raw_spec : P6GlobalAromaticityRawSpec :=
  ⟨p6_neutral_global_pi_electron_count, p6_minimum_electrons_removed,
    p6_global_pi_electron_count_at_minimum_oxidation⟩

/-- **Reported spec (both requested outputs).**  Both outputs are exact
integers (`reporting_policy: exact_integer`), so each is reported at unit
quantum `1` with the raw value equal to the reported value; the raw
expressions keep the derivation visible (`2`, and `84 - 2` for the aromatic
count).  The full raw spec is included so this spec is self-contained. -/
def P6GlobalAromaticityReportedSpec : Prop :=
  P6GlobalAromaticityRawSpec ∧
    IChO2026Chem.Reporting.ReportsAtQuantum 2 2 1 ∧
      IChO2026Chem.Reporting.ReportsAtQuantum
        ((p6NeutralGlobalPiElectronCount : ℝ) - 2) 82 1

theorem p6_global_aromaticity_reported_spec : P6GlobalAromaticityReportedSpec := by
  refine ⟨p6_global_aromaticity_raw_spec, ?_, ?_⟩
  · -- `ReportsAtQuantum 2 2 1`: quantum positive, `2 = 1 * 2`, and the raw
    -- value `2` lies in the half-quantum interval `[2 - 1/2, 2 + 1/2)`.
    refine ⟨by norm_num, ⟨2, by norm_num⟩, ?_⟩
    rw [if_pos (by norm_num : (0 : ℝ) ≤ 2)]
    exact ⟨by norm_num, by norm_num⟩
  · -- `ReportsAtQuantum (84 - 2) 82 1`: the neutral count cast is `84`, so the
    -- raw value is `82`, reported exactly at unit quantum (`82 = 1 * 82`).
    rw [p6_neutral_global_pi_electron_count]
    refine ⟨by norm_num, ⟨82, by norm_num⟩, ?_⟩
    rw [if_pos (by norm_num : (0 : ℝ) ≤ ((84 : ℕ) : ℝ) - 2)]
    exact ⟨by norm_num, by norm_num⟩

/-- Answer-blind **raw-result contract**: binds the candidate's raw-role
payload digest to the raw semantic spec. -/
theorem raw_result_contract :
    ("9e20c8eab95d59409027d7e26e4adb93e0fc1c03896ba4ae269d7dc5ec6375e6" : String) =
      "9e20c8eab95d59409027d7e26e4adb93e0fc1c03896ba4ae269d7dc5ec6375e6" ∧
      IChO2026T6A7.P6GlobalAromaticityRawSpec :=
  ⟨rfl, p6_global_aromaticity_raw_spec⟩

/-- Answer-blind **reported-result contract**: binds the candidate's
reported-role payload digest to the reported semantic spec. -/
theorem reported_result_contract :
    ("fa2c266f68f482d17c340cc8ce3078937a08d9d42080bc5beefae081de85f984" : String) =
      "fa2c266f68f482d17c340cc8ce3078937a08d9d42080bc5beefae081de85f984" ∧
      IChO2026T6A7.P6GlobalAromaticityReportedSpec :=
  ⟨rfl, p6_global_aromaticity_reported_spec⟩

end IChO2026T6A7
