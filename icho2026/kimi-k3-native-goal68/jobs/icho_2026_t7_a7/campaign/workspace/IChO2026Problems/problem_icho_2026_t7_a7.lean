import Mathlib

/-!
# IChO 2026, Problem 7 (Theory, paper T7), subquestion 7.7 - `icho_2026_t7_a7`

Formalization of:

> Nitrogen fixation can also be achieved via binary nitrides (compounds containing N3-).
> Such nitrides 7, 8, 9 were obtained from pure elements. When they are heated
> together with SiO2, red crystals of a stable compound 10 are formed as the single
> product. The minimal possible formula, describing the structure of compound 10 is
> Q_alpha R_beta S2 T [Si12 N24].  In addition:
> 1. Mass fractions of nitrogen are w(N)7 = 9.16 %, w(N)8 = 18.90 %, w(N)9 = 39.94 %.
> 2. Q and R are metal cations in their highest oxidation state.
> 3. S is a monoatomic anion.
> 4. T is an anion with tetrahedral configuration.
> 5. For the quantitative formation of 10, the mass ratio
>    7 : 8 : 9 : SiO2 = 5.09 : 2.96 : 3.27 : 1.00.
>
> 7.7 Identify the empirical formulae of 7-10. Specify the composition of
> anions S and T.

## Answers proved below

* 7 = LaN, 8 = Ca3 N2, 9 = Si3 N4;
* 10 = La5 Ca9 O2 [SiNO3] [Si12 N24], with S = O2- (oxide, monoatomic) and
  T = [SiNO3]^5- (a tetrahedral oxonitridosilicate anion, Si centre in an Si(N,O)4
  tetrahedron);
* The quantitative reaction per two minimal formula units is
  `10 LaN + 6 Ca3N2 + 7 Si3N4 + 5 SiO2 -> 2 La5Ca9 O2 [SiNO3] [Si12N24]`
  and this stoichiometry reproduces the printed mass fractions and mass ratio
  within the half-quantum rounding interval of every printed decimal.
-/

namespace IChO2026T7A7

/-- The five chemical elements relevant to problem 7.7. -/
inductive Element5 | La | Ca | Si | N | O
  deriving DecidableEq, Repr

/-- The anion identities requested by the problem. -/
inductive AnionId | S | T
  deriving DecidableEq, Repr

/-- The oxide forms of the alkaline-earth metals listed by the problem as *not*
reacting with SiO2: BeO, MgO, CaO, SrO, BaO, ZnO, CdO. -/
inductive OxideE | Be | Mg | Ca | Sr | Ba | Zn | Cd
  deriving DecidableEq, Repr

/-! ## Printed (measured) data, reproduced as exact rationals

Decimals from the problem statement are rendered as exact `Rat` numerals
(centi-percent / centi-gram); no rounding occurs at any intermediate stage. -/

/-- Printed w(N) of nitride 7: 9.16 % = 916/10000. -/
def wN7 : Rat := 916 / 10000
/-- Printed w(N) of nitride 8: 18.90 % = 1890/10000. -/
def wN8 : Rat := 1890 / 10000
/-- Printed w(N) of nitride 9: 39.94 % = 3994/10000. -/
def wN9 : Rat := 3994 / 10000
/-- Printed mass of 7 in the ratio 5.09 : 2.96 : 3.27 : 1.00. -/
def m7 : Rat := 509 / 100
/-- Printed mass of 8 in the ratio. -/
def m8 : Rat := 296 / 100
/-- Printed mass of 9 in the ratio. -/
def m9 : Rat := 327 / 100
/-- Printed mass of SiO2 in the ratio. -/
def mSiO2 : Rat := 100 / 100

/-! ## Atomic masses (IChO periodic table, exact as printed) in g mol^-1. -/

def ArN : Rat := 14007 / 1000
def ArLa : Rat := 1389055 / 10000
def ArCa : Rat := 40078 / 1000
def ArSi : Rat := 28085 / 1000
def ArO : Rat := 15999 / 1000

/-- Atomic mass resolution of every `Element5`. -/
def Element5.mass : Element5 → Rat
  | .La => ArLa
  | .Ca => ArCa
  | .Si => ArSi
  | .N  => ArN
  | .O  => ArO

/-! ## Molar masses of the identified species -/

/-- Molar mass of 7 = LaN. -/
def M7 : Rat := ArLa + ArN
/-- Molar mass of 8 = Ca3 N2. -/
def M8 : Rat := 3 * ArCa + 2 * ArN
/-- Molar mass of 9 = Si3 N4. -/
def M9 : Rat := 3 * ArSi + 4 * ArN
/-- Molar mass of SiO2. -/
def MSiO2 : Rat := ArSi + 2 * ArO

/-! ## Inventories -/

/-- Element inventory of one minimal formula unit of compound 10,
La5 Ca9 O2 [SiNO3] [Si12 N24]: Q = La (alpha = 5), R = Ca (beta = 9),
two S anions (oxide), one T anion ([SiNO3]^5-), and the intact framework [Si12 N24]. -/
def unit10 : Element5 → Rat
  | .La => 5
  | .Ca => 9
  | .Si => 12 + 1
  | .N  => 24 + 1
  | .O  => 2 + 3

/-- Anion inventories: S = O2- (monoatomic oxide); T = [SiNO3]^5-. -/
def anionS : Element5 → Rat
  | .O => 1
  | _ => 0
def anionT : Element5 → Rat
  | .Si => 1
  | .N => 1
  | .O => 3
  | _ => 0

/-- Reactant inventory for `10 LaN + 6 Ca3N2 + 7 Si3N4 + 5 SiO2`
(per two minimal formula units of 10). -/
def reactantInventory : Element5 → Rat
  | .La => 10
  | .Ca => 3 * 6
  | .Si => 3 * 7 + 5
  | .N  => 10 + 2 * 6 + 4 * 7
  | .O  => 2 * 5

/-! ## Half-quantum rounding consistency for the printed measured decimals -/

/-- Identification of 7, 8, 9.  The printed mass fractions agree with the
theoretical values of LaN, Ca3N2 and Si3N4 to within half a quantum (0.005 %)
of the last printed digit. -/
theorem wN_consistency :
    |wN7 - ArN / M7| ≤ 5 / 100000 ∧
    |wN8 - 2 * ArN / M8| ≤ 5 / 100000 ∧
    |wN9 - 4 * ArN / M9| ≤ 5 / 100000 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;>
    · norm_num [wN7, wN8, wN9, M7, M8, M9, ArN, ArLa, ArCa, ArSi]

/-- Stoichiometry of the formation of 10.  The printed mass ratio agrees with
`10 LaN : 6 Ca3N2 : 7 Si3N4 : 5 SiO2` to within half a quantum (0.005) of the
last printed digit, relative to the SiO2 mass. -/
theorem massRatio_consistency :
    |m7 - 2 * M7 / MSiO2| ≤ 5 / 1000 ∧
    |m8 - (6 : Rat) / 5 * M8 / MSiO2| ≤ 5 / 1000 ∧
    |m9 - (7 : Rat) / 5 * M9 / MSiO2| ≤ 5 / 1000 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;>
    · norm_num [m7, m8, m9, M7, M8, M9, MSiO2, ArN, ArLa, ArCa, ArSi, ArO]

/-! ## Atom and charge conservation -/

/-- Atom balances per two minimal formula units of 10:
`10 LaN + 6 Ca3N2 + 7 Si3N4 + 5 SiO2 -> 2 La5Ca9 N2 (Si7N2O5) [Si12N24]`. -/
theorem atom_balance (e : Element5) :
    reactantInventory e = 2 * unit10 e := by
  cases e <;> norm_num [reactantInventory, unit10]

/-- Charge neutrality of 10: 5 La3+, 9 Ca2+, two O2- (S), one [SiNO3]^5- (T)
and the intact framework [Si12N24]^20-. -/
theorem charge_balance :
    5 * 3 + 9 * 2 + 2 * (-2 : Int) + (1 * 4 + 1 * (-3) + 3 * (-2)) + (12 * 4 + 24 * (-3)) = 0 := by
  decide

/-- Anion S is monoatomic oxide: its inventory in a minimal unit of 10. -/
theorem anionS_inventory (e : Element5) :
    anionS e = (if e = .O then 1 else 0 : Rat) := by
  cases e <;> rfl

/-- Anion T is the tetrahedral oxonitridosilicate [SiNO3]^5-: its inventory. -/
theorem anionT_inventory (e : Element5) :
    anionT e = (if e = .Si then 1 else if e = .N then 1 else if e = .O then 3 else 0 : Rat) := by
  cases e <;> rfl

/-! ## Master theorem: every requested output of problem 7.7 -/

/-- Problem 7.7, complete.  Empirical formulae 7 = LaN, 8 = Ca3N2, 9 = Si3N4,
10 = La5Ca9 O2 [SiNO3] [Si12N24]; anions S = O2- (monoatomic) and
T = [SiNO3]^5- (tetrahedral).  The theorem packages: the nitride
identifications consistent with the three printed mass fractions; the
stoichiometry 10 : 6 : 7 : 5 consistent with the printed mass ratio; exact atom
conservation; and exact charge neutrality. -/
theorem icho_2026_t7_a7 :
    (|wN7 - ArN / M7| ≤ 5 / 100000) ∧
    (|wN8 - 2 * ArN / M8| ≤ 5 / 100000) ∧
    (|wN9 - 4 * ArN / M9| ≤ 5 / 100000) ∧
    (|m7 - 2 * M7 / MSiO2| ≤ 5 / 1000) ∧
    (|m8 - (6 : Rat) / 5 * M8 / MSiO2| ≤ 5 / 1000) ∧
    (|m9 - (7 : Rat) / 5 * M9 / MSiO2| ≤ 5 / 1000) ∧
    (∀ e : Element5, reactantInventory e = 2 * unit10 e) ∧
    (5 * 3 + 9 * 2 + 2 * (-2 : Int) + (1 * 4 + 1 * (-3) + 3 * (-2))
        + (12 * 4 + 24 * (-3)) = 0) ∧
    (∀ e : Element5, anionS e = if e = .O then 1 else 0) ∧
    (∀ e : Element5, anionT e = if e = .Si then 1 else if e = .N then 1
        else if e = .O then 3 else 0) := by
  refine ⟨wN_consistency.1, wN_consistency.2.1, wN_consistency.2.2,
    massRatio_consistency.1, massRatio_consistency.2.1, massRatio_consistency.2.2,
    atom_balance, charge_balance, anionS_inventory, anionT_inventory⟩

#print axioms icho_2026_t7_a7

end IChO2026T7A7
