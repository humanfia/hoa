import Mathlib

/-!
# IChO 2026, problem T4.2

The problem asks for three neutron-producing nuclear equations.  This file
models a nuclear species by its chemical element (where applicable), mass
number, and atomic number, and records the two conservation laws separately.

The element vocabulary below is deliberately only a vocabulary for the
species occurring in these three equations; it is not asserted to be an
exhaustive candidate domain for the periodic table.
-/

namespace IChO2026Problems.T4A2

/-- Element names needed to state the three nuclear equations in T4.2. -/
inductive Element
  | hydrogen
  | helium
  | beryllium
  | boron
  | carbon
  | nitrogen
  deriving DecidableEq, Repr

/-- Atomic numbers attached to the element symbols used in the problem and
its derived products. -/
def Element.atomicNumber : Element → ℕ
  | .hydrogen => 1
  | .helium => 2
  | .beryllium => 4
  | .boron => 5
  | .carbon => 6
  | .nitrogen => 7

/-- A nuclear species is either a named isotope, a free neutron, or a photon.
The photon constructor keeps a gamma ray distinct from a zero-number nucleus. -/
inductive NuclearSpecies
  | isotope (element : Element) (massNumber : ℕ)
  | neutron
  | photon
  deriving DecidableEq, Repr

namespace NuclearSpecies

/-- Mass number contributed by a species to a nuclear equation. -/
def massNumber : NuclearSpecies → ℕ
  | .isotope _ a => a
  | .neutron => 1
  | .photon => 0

/-- Atomic number contributed by a species to a nuclear equation. -/
def atomicNumber : NuclearSpecies → ℕ
  | .isotope element _ => element.atomicNumber
  | .neutron => 0
  | .photon => 0

end NuclearSpecies

/-- An ordered presentation of the reactant and product sides of a nuclear
equation.  Ordering is retained so the carrier mirrors the displayed answer. -/
structure NuclearEquation where
  reactants : List NuclearSpecies
  products : List NuclearSpecies
  deriving DecidableEq, Repr

namespace NuclearEquation

/-- Total mass number on one side of a nuclear equation. -/
def totalMassNumber (side : List NuclearSpecies) : ℕ :=
  (side.map NuclearSpecies.massNumber).sum

/-- Total atomic number on one side of a nuclear equation. -/
def totalAtomicNumber (side : List NuclearSpecies) : ℕ :=
  (side.map NuclearSpecies.atomicNumber).sum

/-- Conservation of nucleon (mass) number. -/
def ConservesMassNumber (equation : NuclearEquation) : Prop :=
  totalMassNumber equation.reactants = totalMassNumber equation.products

/-- Conservation of atomic (charge) number. -/
def ConservesAtomicNumber (equation : NuclearEquation) : Prop :=
  totalAtomicNumber equation.reactants = totalAtomicNumber equation.products

/-- The two conservation obligations used to check a nuclear equation. -/
def IsBalanced (equation : NuclearEquation) : Prop :=
  ConservesMassNumber equation ∧ ConservesAtomicNumber equation

end NuclearEquation

/-! ## Species printed or inferred in the three equations -/

def hydrogen1 : NuclearSpecies := .isotope .hydrogen 1
def deuterium : NuclearSpecies := .isotope .hydrogen 2
def alphaParticle : NuclearSpecies := .isotope .helium 4
def beryllium9 : NuclearSpecies := .isotope .beryllium 9
def boron11 : NuclearSpecies := .isotope .boron 11
def carbon12 : NuclearSpecies := .isotope .carbon 12
def nitrogen14 : NuclearSpecies := .isotope .nitrogen 14
def neutron : NuclearSpecies := .neutron
def gammaRay : NuclearSpecies := .photon

/-! ## Source-side reactants -/

/-- Reactants stipulated in item (a): boron-11 and an alpha particle. -/
def nuclearAReactants : List NuclearSpecies := [boron11, alphaParticle]

/-- Reactants stipulated in item (b): a gamma ray and deuterium. -/
def nuclearBReactants : List NuclearSpecies := [gammaRay, deuterium]

/-- Reactants stipulated in item (c): beryllium-9 and an alpha particle. -/
def nuclearCReactants : List NuclearSpecies := [beryllium9, alphaParticle]

/-! ## Candidate output equations -/

/-- Candidate for (a): `¹¹₅B + ⁴₂α → ¹⁴₇N + ¹₀n`. -/
def nuclearA : NuclearEquation where
  reactants := nuclearAReactants
  products := [nitrogen14, neutron]

/-- Candidate for (b): `γ + ²₁H → ¹₁H + ¹₀n`. -/
def nuclearB : NuclearEquation where
  reactants := nuclearBReactants
  products := [hydrogen1, neutron]

/-- Candidate for (c): `⁹₄Be + ⁴₂α → ¹²₆C + ¹₀n`. -/
def nuclearC : NuclearEquation where
  reactants := nuclearCReactants
  products := [carbon12, neutron]

/-! ## Derivation and output specifications

Each specification exposes the source-stated reactants, the requested exact
product side, and both independently checkable conservation ledgers.  Thus the
answer is carried in a conclusion and is not supplied as a theorem premise.
-/

/-- Exact specification for requested output `nuclear_a`. -/
def NuclearASpec (equation : NuclearEquation) : Prop :=
  equation.reactants = nuclearAReactants ∧
    equation.products = [nitrogen14, neutron] ∧
      equation.IsBalanced

/-- Exact specification for requested output `nuclear_b`. -/
def NuclearBSpec (equation : NuclearEquation) : Prop :=
  equation.reactants = nuclearBReactants ∧
    equation.products = [hydrogen1, neutron] ∧
      equation.IsBalanced

/-- Exact specification for requested output `nuclear_c`. -/
def NuclearCSpec (equation : NuclearEquation) : Prop :=
  equation.reactants = nuclearCReactants ∧
    equation.products = [carbon12, neutron] ∧
      equation.IsBalanced

/-- The mass and atomic numbers forced for a single residual nucleus in (a).
This is the arithmetic derivation behind the isotope `¹⁴₇N`. -/
theorem nuclearA_residual_numbers
    (residual : NuclearSpecies)
    (hBalanced : NuclearEquation.IsBalanced
      ⟨nuclearAReactants, [residual, neutron]⟩) :
    residual.massNumber = 14 ∧ residual.atomicNumber = 7 := by
  change 15 = residual.massNumber + 1 ∧
    7 = residual.atomicNumber at hBalanced
  omega

/-- The mass and atomic numbers forced for a single residual nucleus in (b).
This is the arithmetic derivation behind the isotope `¹₁H`. -/
theorem nuclearB_residual_numbers
    (residual : NuclearSpecies)
    (hBalanced : NuclearEquation.IsBalanced
      ⟨nuclearBReactants, [residual, neutron]⟩) :
    residual.massNumber = 1 ∧ residual.atomicNumber = 1 := by
  change 2 = residual.massNumber + 1 ∧
    1 = residual.atomicNumber at hBalanced
  omega

/-- The mass and atomic numbers forced for a single residual nucleus in (c).
This is the arithmetic derivation behind the isotope `¹²₆C`. -/
theorem nuclearC_residual_numbers
    (residual : NuclearSpecies)
    (hBalanced : NuclearEquation.IsBalanced
      ⟨nuclearCReactants, [residual, neutron]⟩) :
    residual.massNumber = 12 ∧ residual.atomicNumber = 6 := by
  change 13 = residual.massNumber + 1 ∧
    6 = residual.atomicNumber at hBalanced
  omega

/-- Carrier and balance certificate for requested output `nuclear_a`. -/
theorem nuclear_a : NuclearASpec nuclearA := by
  norm_num [NuclearASpec, nuclearA, nuclearAReactants,
    nitrogen14, boron11, alphaParticle, neutron,
    NuclearEquation.IsBalanced,
    NuclearEquation.ConservesMassNumber,
    NuclearEquation.ConservesAtomicNumber,
    NuclearEquation.totalMassNumber,
    NuclearEquation.totalAtomicNumber,
    NuclearSpecies.massNumber, NuclearSpecies.atomicNumber,
    Element.atomicNumber]

/-- Carrier and balance certificate for requested output `nuclear_b`. -/
theorem nuclear_b : NuclearBSpec nuclearB := by
  norm_num [NuclearBSpec, nuclearB, nuclearBReactants,
    hydrogen1, gammaRay, deuterium, neutron,
    NuclearEquation.IsBalanced,
    NuclearEquation.ConservesMassNumber,
    NuclearEquation.ConservesAtomicNumber,
    NuclearEquation.totalMassNumber,
    NuclearEquation.totalAtomicNumber,
    NuclearSpecies.massNumber, NuclearSpecies.atomicNumber,
    Element.atomicNumber]

/-- Carrier and balance certificate for requested output `nuclear_c`. -/
theorem nuclear_c : NuclearCSpec nuclearC := by
  norm_num [NuclearCSpec, nuclearC, nuclearCReactants,
    carbon12, beryllium9, alphaParticle, neutron,
    NuclearEquation.IsBalanced,
    NuclearEquation.ConservesMassNumber,
    NuclearEquation.ConservesAtomicNumber,
    NuclearEquation.totalMassNumber,
    NuclearEquation.totalAtomicNumber,
    NuclearSpecies.massNumber, NuclearSpecies.atomicNumber,
    Element.atomicNumber]

/-- Combined unrounded symbolic result, in the controller-specified order
`nuclear_a`, `nuclear_b`, `nuclear_c`. -/
def RawResult : Prop :=
  NuclearASpec nuclearA ∧ NuclearBSpec nuclearB ∧ NuclearCSpec nuclearC

/-- Raw solve-phase contract for all three requested equations. -/
theorem raw_result : RawResult := by
  exact ⟨nuclear_a, nuclear_b, nuclear_c⟩

/-- Exact-symbolic reporting does not round or otherwise alter the equations;
the reported contract repeats every semantic specification explicitly. -/
def ReportedResult : Prop :=
  NuclearASpec nuclearA ∧ NuclearBSpec nuclearB ∧ NuclearCSpec nuclearC

/-- Reported solve-phase contract for all three exact symbolic outputs. -/
theorem reported_result : ReportedResult := by
  exact ⟨nuclear_a, nuclear_b, nuclear_c⟩

end IChO2026Problems.T4A2
