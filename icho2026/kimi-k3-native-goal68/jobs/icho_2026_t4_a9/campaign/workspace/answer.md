# IChO 2026 — Problem T4, subquestion 4.9 (`icho_2026_t4_a9`)

## Question (official English text, page Q4-3)

> The *Urtabulak* gas leak was ended by detonating a 30-kiloton in TNT
> equivalent underground nuclear explosion that collapsed the reservoir and
> sealed the leak. 1 ton of TNT equivalent is 4.184 GJ of energy.
>
> **4.9** Using the value from **4.4**, calculate the total number of
> fissions, TN, during the nuclear explosion. Calculate the mass, m, of
> enriched uranium used in the explosion (in kg), assuming it contained 90% by
> mass of the ²³⁵U isotope, and 33% of the ²³⁵U underwent fission.
> *If you did not get an answer for 4.4, use ΔE = 200 MeV.*

## Answer

* **Total number of fissions:** TN = 3.876 468… × 10²⁴ → **TN = 3.88 × 10²⁴ fissions**
* **Mass of enriched uranium:** m = 5.094 137… kg → **m = 5.09 kg**

(Both reported at three significant figures, per the run-wide reporting
policy; exact ties round half away from zero — no tie occurs here.)

## Solution

### Step 0 — part 4.4 value, re-derived answer-blind (no intermediate rounding)

The energy released per fission follows from the binding-energy data of part
4.4 (page Q4-2): BE(²³⁵U) = 7.59 MeV/nucleon, average BE of the fission
products BE(fis.) = 8.45 MeV/nucleon, and free-neutron binding energies are
neglected. The netted neutron appears unchanged on both sides of the fission
equation, so the 235 bound nucleons simply move to stronger-bound fragments:

ΔE = (BE(fis.) − BE(²³⁵U)) × 235 = (8.45 − 7.59) × 235 = 0.86 × 235
   = **202.1 MeV per fission**

Since this value was derived from problem-only material, the fallback
ΔE = 200 MeV is not used.

### Step 1 — energy of the explosion

E = 30 kt × 4.184 GJ/t = 30 000 × 4.184 × 10⁹ J = 1.2552 × 10¹⁴ J.

(Only problem-stated numbers are used: 30 kilotons and 1 ton TNT ≡ 4.184 GJ.)

### Step 2 — total number of fissions

Each fission releases ΔE, so

TN = E / ΔE.

Converting MeV to joules with the exact SI value 1 eV = 1.602176634 × 10⁻¹⁹ J
(1 MeV = 10⁶ eV):

ΔE = 202.1 × 10⁶ × 1.602176634 × 10⁻¹⁹ J = 3.237998977314 × 10⁻¹¹ J,

TN = 1.2552 × 10¹⁴ J / 3.237998977314 × 10⁻¹¹ J
   = **3.876468179… × 10²⁴ fissions → 3.88 × 10²⁴ fissions**.

### Step 3 — mass of enriched uranium

The mass of ²³⁵U that actually fissioned is the number of fissions times the
mass of one ²³⁵U atom. Using the ²³⁵U mass printed in part 4.1
(235.04 a.u. = 235.04 g mol⁻¹) and the exact SI Avogadro constant
N_A = 6.02214076 × 10²³ mol⁻¹:

m(²³⁵U fissioned) = TN × (0.23504 kg mol⁻¹ / N_A)
                  = 3.876468179… × 10²⁴ × 0.23504 / 6.02214076 × 10²³
                  = 1.512958792… kg.

This fissioned mass is 33% of all the ²³⁵U present, and the ²³⁵U present is
90% by mass of the enriched uranium, so

m = m(²³⁵U fissioned) / (0.33 × 0.90)
  = 1.512958792… / 0.297
  = **5.094137346… kg → 5.09 kg**.

## Source grounding

| Quantity | Value used | Source |
|---|---|---|
| Explosive yield | 30 kilotons TNT | Problem 4.9 preamble, page Q4-3 |
| TNT equivalence | 1 ton ≡ 4.184 GJ | Problem statement, page Q4-3 |
| BE(²³⁵U) | 7.59 MeV/nucleon | Part 4.4 statement, page Q4-2 |
| BE(fis.) | 8.45 MeV/nucleon | Part 4.4 statement, page Q4-2 |
| Nucleon number | 235 (neutron binding neglected) | Part 4.4 statement (isotope ²³⁵U, page Q4-1) |
| M(²³⁵U) | 235.04 a.u. → 235.04 g mol⁻¹ | Part 4.1 statement, page Q4-1 |
| Enrichment | 90% ²³⁵U by mass | Part 4.9 statement |
| Fissioned fraction | 33% of the ²³⁵U | Part 4.9 statement |
| 1 eV in joules | 1.602176634 × 10⁻¹⁹ J (exact SI) | Trusted general law — **not printed in the problem; see source gap below** |
| N_A | 6.02214076 × 10²³ mol⁻¹ (exact SI) | Trusted general law — likewise not printed |

Unit conventions 1 kt = 1000 t and 1 GJ = 10⁹ J, 1 MeV = 10⁶ eV are standard
SI prefix definitions.

### Source gap (disclosed, per protocol)

The problem statement never prints the MeV↔J conversion factor or Avogadro's
constant. Both are taken from the exact SI definitions (the electronvolt is
defined as exactly 1.602176634 × 10⁻¹⁹ J since the 2019 SI revision, and
N_A is exactly 6.02214076 × 10²³ mol⁻¹). These are ordinary scientific
constants, not competition answers; their use is recorded as an assumption in
`result.json`. All other inputs come verbatim from the printed problem.

## Formalization

The full chain above is formalized in
`IChO2026Problems/problem_icho_2026_t4_a9.lean` over the reals, with every
problem input separated as a named definition, the part-4.4 value proved
(`deltaE_MeV_value`, 202.1 MeV), the explosion energy proved
(`explosionEnergy_value`, 1.2552 × 10¹⁴ J), and tight rational bounds
(`totalFissions_bounds`, `enrichedUraniumMass_bounds`) proving that the exact
derived values round to 3.88 × 10²⁴ and 5.09 at three significant figures.
`totalFissions_reported` and `enrichedUraniumMass_reported` certify the final
rounded values against the project-wide `ValidNumericSubmission` reporting
contract (quantum 10²² fissions and 0.01 kg respectively). All proofs close
without `sorry`; `#print axioms` reports only `propext`, `Classical.choice`,
and `Quot.sound` (standard Lean logical axioms). See `verification.md`.
