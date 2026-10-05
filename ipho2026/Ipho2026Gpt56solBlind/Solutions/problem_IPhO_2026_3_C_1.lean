import Mathlib
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 3, part C.1

This file models the annotation requested for the `H`-versus-`T` diagram of a
four-state Carnot refrigerator.  Physical quantities use Physlib's seven-base
ISQ dimensional algebra and cross into real arithmetic only through an explicit
coherent-SI coordinate map.  Heat is signed positive when it enters the
paramagnetic torus.  Thus the named `Q_h` and `Q_c` remain positive magnitudes,
while each process carries a signed heat.

The selected axis columns and cycle legs are deliberately fields of an
existentially unique `DiagramAnnotation`; no particular selection is put in the
theorem signature.
-/

namespace Ipho2026Gpt56solBlind
namespace ProblemIPhO2026_3_C_1

/-!
## ISQ dimensions and coherent-SI coordinates

The dimension indices below are genuine `Dimension ISQDimensionBase` values.
`WithDim` is basis-parametric, so these declarations do not use the LTMCT-only
`HasDim` and `Dimensionful` interfaces.
-/

/-- ISQ thermodynamic-temperature dimension. -/
def temperatureDimension : Dimension ISQDimensionBase :=
  Dimension.single .temperature

/-- ISQ volume dimension, `length ^ 3`. -/
def volumeDimension : Dimension ISQDimensionBase :=
  Dimension.single .length ^ (3 : ℕ)

/-- ISQ amount-of-substance dimension. -/
def amountDimension : Dimension ISQDimensionBase :=
  Dimension.single .amount

/-- Dimension of the Curie parameter in `T M V = n K H`. -/
def curieParameterDimension : Dimension ISQDimensionBase :=
  temperatureDimension * volumeDimension * amountDimension⁻¹

/-- ISQ magnetic-field-strength dimension, `current / length`. -/
def magneticFieldStrengthDimension : Dimension ISQDimensionBase :=
  Dimension.single .current * (Dimension.single .length)⁻¹

/-- Magnetization has the same dimensional role as magnetic-field strength. -/
def magnetizationDimension : Dimension ISQDimensionBase :=
  magneticFieldStrengthDimension

/-- ISQ energy dimension, `mass * length ^ 2 / time ^ 2`. -/
def energyDimension : Dimension ISQDimensionBase :=
  Dimension.single .mass * Dimension.single .length ^ (2 : ℕ) *
    (Dimension.single .time ^ (2 : ℕ))⁻¹

/-- The equation-of-state dimensions agree before either side is projected to
real SI coordinates. -/
lemma equationOfState_dimension :
    temperatureDimension * magnetizationDimension * volumeDimension =
      amountDimension * curieParameterDimension * magneticFieldStrengthDimension := by
  change temperatureDimension * magneticFieldStrengthDimension * volumeDimension =
    amountDimension *
      (temperatureDimension * volumeDimension * amountDimension⁻¹) *
        magneticFieldStrengthDimension
  calc
    temperatureDimension * magneticFieldStrengthDimension * volumeDimension =
        1 * (temperatureDimension * magneticFieldStrengthDimension * volumeDimension) :=
      (one_mul _).symm
    _ = (amountDimension * amountDimension⁻¹) *
        (temperatureDimension * magneticFieldStrengthDimension * volumeDimension) := by
      rw [mul_inv_cancel]
    _ = amountDimension *
        (temperatureDimension * volumeDimension * amountDimension⁻¹) *
          magneticFieldStrengthDimension := by
      ac_rfl

/-- A quantity represented in `sourceUnits`, converted to its coherent-SI real
coordinate.  This is the explicit bridge from typed ISQ quantities to scalar
equations and inequalities. -/
noncomputable def coordinateInSI {d : Dimension ISQDimensionBase}
    (sourceUnits : SIUnitChoices) (x : WithDim d ℝ) : ℝ :=
  (SIUnitChoices.dimScale sourceUnits SIUnitChoices.SI d).val * x.val

/-- Real coordinate of a quantity already represented in coherent SI units. -/
noncomputable def siCoordinate {d : Dimension ISQDimensionBase}
    (x : WithDim d ℝ) : ℝ :=
  coordinateInSI SIUnitChoices.SI x

@[simp]
lemma siCoordinate_eq_val {d : Dimension ISQDimensionBase} (x : WithDim d ℝ) :
    siCoordinate x = x.val := by
  unfold siCoordinate coordinateInSI
  rw [SIUnitChoices.dimScale_self]
  simp

/-- A real-valued temperature carrying its ISQ dimension. -/
abbrev Temperature := WithDim temperatureDimension ℝ

/-- A real-valued volume carrying its ISQ dimension. -/
abbrev Volume := WithDim volumeDimension ℝ

/-- A real-valued amount of substance carrying its ISQ dimension. -/
abbrev AmountOfSubstance := WithDim amountDimension ℝ

/-- A real-valued Curie parameter carrying its ISQ dimension. -/
abbrev CurieParameter := WithDim curieParameterDimension ℝ

/-- A real-valued magnetic-field strength carrying its ISQ dimension. -/
abbrev MagneticFieldStrength := WithDim magneticFieldStrengthDimension ℝ

/-- A real-valued magnetization carrying its ISQ dimension. -/
abbrev Magnetization := WithDim magnetizationDimension ℝ

/-- A signed real-valued energy carrying its ISQ dimension. -/
abbrev Energy := WithDim energyDimension ℝ

/-- Fixed parameters of the paramagnetic torus. -/
structure ParamagnetParameters where
  volume : Volume
  amount : AmountOfSubstance
  curieConstant : CurieParameter

/-- The fixed torus parameters are in their physical positive domains. -/
def ParamagnetParameters.IsPhysical (p : ParamagnetParameters) : Prop :=
  0 < siCoordinate p.volume ∧
  0 < siCoordinate p.amount ∧
  0 < siCoordinate p.curieConstant

/-- One equilibrium state of the paramagnetic torus.  The field and magnetization
entries are magnitudes. -/
structure ThermodynamicState where
  temperature : Temperature
  field : MagneticFieldStrength
  magnetization : Magnetization

/-- Positivity of the three state variables used in the problem. -/
def ThermodynamicState.IsPhysical (s : ThermodynamicState) : Prop :=
  0 < siCoordinate s.temperature ∧
  0 < siCoordinate s.field ∧
  0 < siCoordinate s.magnetization

/-- The equation of state `T M V = n K H`, evaluated in the common unit system. -/
def SatisfiesEquationOfState (p : ParamagnetParameters) (s : ThermodynamicState) : Prop :=
  siCoordinate s.temperature * siCoordinate s.magnetization * siCoordinate p.volume =
    siCoordinate p.amount * siCoordinate p.curieConstant * siCoordinate s.field

/-- The four numbered vertices in Figure 3b. -/
inductive Vertex
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype

/-- The directed legs of the stated cycle `1 → 2 → 3 → 4 → 1`. -/
inductive CycleLeg
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Fintype

/-- Initial vertex of a directed cycle leg. -/
def CycleLeg.startVertex : CycleLeg → Vertex
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final vertex of a directed cycle leg. -/
def CycleLeg.finishVertex : CycleLeg → Vertex
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- The two thermodynamic process types occurring in a Carnot cycle. -/
inductive ProcessKind
  | isothermal
  | adiabatic
  deriving DecidableEq

/-- Data attached to one directed process.  `heatIntoSystem` is signed, with
positive values denoting heat received by the torus. -/
structure ProcessData where
  kind : ProcessKind
  heatIntoSystem : Energy
  reversible : Prop

/-- Four states and four directed, typed processes forming the displayed cycle. -/
structure FourStateCycle where
  state : Vertex → ThermodynamicState
  process : CycleLeg → ProcessData

/-- State at the initial endpoint of a leg. -/
def FourStateCycle.startState (cycle : FourStateCycle) (leg : CycleLeg) :
    ThermodynamicState :=
  cycle.state leg.startVertex

/-- State at the final endpoint of a leg. -/
def FourStateCycle.finishState (cycle : FourStateCycle) (leg : CycleLeg) :
    ThermodynamicState :=
  cycle.state leg.finishVertex

/-- A leg is isothermal when it has that process type and its endpoint
temperatures agree. -/
def IsIsothermal (cycle : FourStateCycle) (leg : CycleLeg) : Prop :=
  (cycle.process leg).kind = .isothermal ∧
    (cycle.startState leg).temperature = (cycle.finishState leg).temperature

/-- An adiabatic leg has the adiabatic type and no heat transfer. -/
def IsAdiabatic (cycle : FourStateCycle) (leg : CycleLeg) : Prop :=
  (cycle.process leg).kind = .adiabatic ∧
    siCoordinate (cycle.process leg).heatIntoSystem = 0

/-- The two abscissae visible in Figure 3b.  Vertices 2 and 3 represent the
left column, while vertices 1 and 4 represent the right column; the geometry
predicate below requires the two representatives of each column to agree. -/
inductive TemperatureColumn
  | left
  | right
  deriving DecidableEq, Fintype

/-- Temperature coordinate belonging to a column of the diagram. -/
def columnTemperature (cycle : FourStateCycle) : TemperatureColumn → Temperature
  | .left => (cycle.state .two).temperature
  | .right => (cycle.state .one).temperature

/-- The state coordinates shown in Figure 3b, together with the equation of
state at every vertex.  The inequalities record the orientation of each drawn
leg without assigning reservoir names to either temperature column. -/
def Figure3bGeometry (p : ParamagnetParameters) (cycle : FourStateCycle) : Prop :=
  (∀ v, (cycle.state v).IsPhysical ∧ SatisfiesEquationOfState p (cycle.state v)) ∧
  (cycle.state .two).temperature = (cycle.state .three).temperature ∧
  (cycle.state .four).temperature = (cycle.state .one).temperature ∧
  siCoordinate (cycle.state .two).temperature <
    siCoordinate (cycle.state .one).temperature ∧
  siCoordinate (cycle.state .two).field < siCoordinate (cycle.state .one).field ∧
  siCoordinate (cycle.state .three).field < siCoordinate (cycle.state .four).field ∧
  siCoordinate (cycle.state .three).field < siCoordinate (cycle.state .two).field ∧
  siCoordinate (cycle.state .four).field < siCoordinate (cycle.state .one).field

/-- Governing process laws needed to read the Carnot-refrigerator diagram.

Every leg is reversible.  Equality of endpoint temperatures exactly detects
the isothermal process type, adiabatic legs exchange no heat, and on an
isothermal paramagnetic leg increasing field rejects heat while decreasing
field absorbs it.  The last two equivalences use the positive-into-system sign
convention. -/
def IsCarnotRefrigerator (cycle : FourStateCycle) : Prop :=
  (∀ leg, (cycle.process leg).reversible) ∧
  (∀ leg,
    (cycle.process leg).kind = .isothermal ↔
      (cycle.startState leg).temperature = (cycle.finishState leg).temperature) ∧
  (∀ leg,
    (cycle.process leg).kind = .adiabatic →
      siCoordinate (cycle.process leg).heatIntoSystem = 0) ∧
  (∀ leg,
    IsIsothermal cycle leg →
      (siCoordinate (cycle.process leg).heatIntoSystem < 0 ↔
        siCoordinate (cycle.startState leg).field <
          siCoordinate (cycle.finishState leg).field) ∧
      (0 < siCoordinate (cycle.process leg).heatIntoSystem ↔
        siCoordinate (cycle.finishState leg).field <
          siCoordinate (cycle.startState leg).field))

/-- Named reservoir temperatures and the positive heat magnitudes from the
problem statement. -/
structure ReservoirData where
  hotTemperature : Temperature
  coldTemperature : Temperature
  heatDeliveredToHotMagnitude : Energy
  heatAbsorbedFromColdMagnitude : Energy

/-- Physical domains for `T_h`, `T_c`, `Q_h`, and `Q_c`. -/
def ReservoirData.IsPhysical (r : ReservoirData) : Prop :=
  0 < siCoordinate r.coldTemperature ∧
  siCoordinate r.coldTemperature < siCoordinate r.hotTemperature ∧
  0 < siCoordinate r.heatDeliveredToHotMagnitude ∧
  0 < siCoordinate r.heatAbsorbedFromColdMagnitude

/-- The two reservoir temperatures are exactly the two temperature levels of
the cycle, stated without deciding which diagram column receives which label. -/
def OperatesBetweenReservoirs (cycle : FourStateCycle) (r : ReservoirData) : Prop :=
  (r.hotTemperature = columnTemperature cycle .left ∨
    r.hotTemperature = columnTemperature cycle .right) ∧
  (r.coldTemperature = columnTemperature cycle .left ∨
    r.coldTemperature = columnTemperature cycle .right) ∧
  (columnTemperature cycle .left = r.hotTemperature ∨
    columnTemperature cycle .left = r.coldTemperature) ∧
  (columnTemperature cycle .right = r.hotTemperature ∨
    columnTemperature cycle .right = r.coldTemperature)

/-- `Q_h` and `Q_c` are the absolute magnitudes of negative and positive
process heat, respectively.  This only names magnitudes by the physical sign
convention; it does not select a cycle leg. -/
def NamedHeatMagnitudes (cycle : FourStateCycle) (r : ReservoirData) : Prop :=
  ∀ leg,
    (siCoordinate (cycle.process leg).heatIntoSystem < 0 →
      -siCoordinate (cycle.process leg).heatIntoSystem =
        siCoordinate r.heatDeliveredToHotMagnitude) ∧
    (0 < siCoordinate (cycle.process leg).heatIntoSystem →
      siCoordinate (cycle.process leg).heatIntoSystem =
        siCoordinate r.heatAbsorbedFromColdMagnitude)

/-- A process that delivers the positive magnitude `Q_h` to the hot reservoir.
The process heat is negative because heat entering the torus is positive. -/
def HeatDeliveredToHotOn (cycle : FourStateCycle) (r : ReservoirData)
    (leg : CycleLeg) : Prop :=
  IsIsothermal cycle leg ∧
  (cycle.startState leg).temperature = r.hotTemperature ∧
  (cycle.finishState leg).temperature = r.hotTemperature ∧
  siCoordinate (cycle.process leg).heatIntoSystem =
    -siCoordinate r.heatDeliveredToHotMagnitude

/-- A process that absorbs the positive magnitude `Q_c` from the cold
reservoir. -/
def HeatAbsorbedFromColdOn (cycle : FourStateCycle) (r : ReservoirData)
    (leg : CycleLeg) : Prop :=
  IsIsothermal cycle leg ∧
  (cycle.startState leg).temperature = r.coldTemperature ∧
  (cycle.finishState leg).temperature = r.coldTemperature ∧
  siCoordinate (cycle.process leg).heatIntoSystem =
    siCoordinate r.heatAbsorbedFromColdMagnitude

/-- The requested diagram annotation.  Its four finite-valued fields represent
the two labels on the `T` axis and the two heat-transfer labels on cycle legs. -/
structure DiagramAnnotation where
  hotColumn : TemperatureColumn
  coldColumn : TemperatureColumn
  heatToHotLeg : CycleLeg
  heatFromColdLeg : CycleLeg
  deriving DecidableEq

/-- A faithful answer-free solution predicate for the requested labeling.
Besides assigning both temperature labels and both heat labels, it says that
the labeled heat legs are precisely the non-adiabatic heat-transfer legs. -/
def IsCorrectAnnotation (cycle : FourStateCycle) (r : ReservoirData)
    (annotation : DiagramAnnotation) : Prop :=
  columnTemperature cycle annotation.hotColumn = r.hotTemperature ∧
  columnTemperature cycle annotation.coldColumn = r.coldTemperature ∧
  annotation.hotColumn ≠ annotation.coldColumn ∧
  HeatDeliveredToHotOn cycle r annotation.heatToHotLeg ∧
  HeatAbsorbedFromColdOn cycle r annotation.heatFromColdLeg ∧
  annotation.heatToHotLeg ≠ annotation.heatFromColdLeg ∧
  ∀ leg,
    siCoordinate (cycle.process leg).heatIntoSystem ≠ 0 ↔
      leg = annotation.heatToHotLeg ∨ leg = annotation.heatFromColdLeg

end ProblemIPhO2026_3_C_1

open ProblemIPhO2026_3_C_1

/-- The Figure 3b reservoir and heat-transfer annotation exists and is unique.
The concrete columns and legs remain outside the theorem signature. -/
theorem problem_IPhO_2026_3_C_1
    (parameters : ParamagnetParameters)
    (cycle : FourStateCycle)
    (reservoirs : ReservoirData)
    (hparameters : parameters.IsPhysical)
    (hgeometry : Figure3bGeometry parameters cycle)
    (hcarnot : IsCarnotRefrigerator cycle)
    (hreservoirs : reservoirs.IsPhysical)
    (hlevels : OperatesBetweenReservoirs cycle reservoirs)
    (hmagnitudes : NamedHeatMagnitudes cycle reservoirs) :
    ∃! annotation : DiagramAnnotation,
      IsCorrectAnnotation cycle reservoirs annotation := by
  rcases hgeometry with
    ⟨_hstates, htemperature23, htemperature41, htemperature_lt,
      _hfield21, _hfield34, hfield32, hfield41⟩
  rcases hcarnot with
    ⟨_hreversible, hkind_iff, hadiabatic_heat, hisothermal_heat⟩
  rcases hreservoirs with
    ⟨_hcold_pos, hcold_lt_hot, hhot_heat_pos, hcold_heat_pos⟩
  rcases hlevels with
    ⟨hhot_level, hcold_level, _hleft_level, _hright_level⟩

  have hcolumn_lt :
      siCoordinate (columnTemperature cycle .left) <
        siCoordinate (columnTemperature cycle .right) := by
    change siCoordinate (cycle.state .two).temperature <
      siCoordinate (cycle.state .one).temperature
    exact htemperature_lt

  have hhot_level_eq :
      reservoirs.hotTemperature = columnTemperature cycle .right := by
    rcases hhot_level with hhot_left | hhot_right
    · exfalso
      rcases hcold_level with hcold_left | hcold_right
      · have h := hcold_lt_hot
        rw [hhot_left, hcold_left] at h
        exact (lt_irrefl _ h)
      · have h := hcold_lt_hot
        rw [hhot_left, hcold_right] at h
        exact (lt_asymm hcolumn_lt h)
    · exact hhot_right

  have hcold_level_eq :
      reservoirs.coldTemperature = columnTemperature cycle .left := by
    rcases hcold_level with hcold_left | hcold_right
    · exact hcold_left
    · exfalso
      have h := hcold_lt_hot
      rw [hcold_right, hhot_level_eq] at h
      exact (lt_irrefl _ h)

  have htemperature1_hot :
      (cycle.state .one).temperature = reservoirs.hotTemperature := by
    change (cycle.state .one).temperature = reservoirs.hotTemperature
    exact hhot_level_eq.symm
  have htemperature4_hot :
      (cycle.state .four).temperature = reservoirs.hotTemperature :=
    htemperature41.trans htemperature1_hot
  have htemperature2_cold :
      (cycle.state .two).temperature = reservoirs.coldTemperature := by
    change (cycle.state .two).temperature = reservoirs.coldTemperature
    exact hcold_level_eq.symm
  have htemperature3_cold :
      (cycle.state .three).temperature = reservoirs.coldTemperature :=
    htemperature23.symm.trans htemperature2_cold

  have htemperature23' :
      (cycle.startState .twoToThree).temperature =
        (cycle.finishState .twoToThree).temperature := by
    change (cycle.state .two).temperature = (cycle.state .three).temperature
    exact htemperature23
  have htemperature41' :
      (cycle.startState .fourToOne).temperature =
        (cycle.finishState .fourToOne).temperature := by
    change (cycle.state .four).temperature = (cycle.state .one).temperature
    exact htemperature41
  have htemperature12_ne :
      (cycle.startState .oneToTwo).temperature ≠
        (cycle.finishState .oneToTwo).temperature := by
    intro htemperature12
    have hcoords := congrArg siCoordinate htemperature12
    change siCoordinate (cycle.state .one).temperature =
      siCoordinate (cycle.state .two).temperature at hcoords
    exact (ne_of_gt htemperature_lt) hcoords
  have htemperature34_ne :
      (cycle.startState .threeToFour).temperature ≠
        (cycle.finishState .threeToFour).temperature := by
    intro htemperature34
    have htemperature34' :
        (cycle.state .three).temperature = (cycle.state .four).temperature := by
      change (cycle.state .three).temperature =
        (cycle.state .four).temperature at htemperature34
      exact htemperature34
    have htemperature21 :
        (cycle.state .two).temperature = (cycle.state .one).temperature :=
      htemperature23.trans (htemperature34'.trans htemperature41)
    exact (ne_of_lt htemperature_lt) (congrArg siCoordinate htemperature21)

  have hisothermal23 : IsIsothermal cycle .twoToThree := by
    exact ⟨(hkind_iff .twoToThree).2 htemperature23', htemperature23'⟩
  have hisothermal41 : IsIsothermal cycle .fourToOne := by
    exact ⟨(hkind_iff .fourToOne).2 htemperature41', htemperature41'⟩

  have hkind12 : (cycle.process .oneToTwo).kind = .adiabatic := by
    cases hkind : (cycle.process .oneToTwo).kind with
    | isothermal =>
        exfalso
        exact htemperature12_ne ((hkind_iff .oneToTwo).1 hkind)
    | adiabatic => rfl
  have hkind34 : (cycle.process .threeToFour).kind = .adiabatic := by
    cases hkind : (cycle.process .threeToFour).kind with
    | isothermal =>
        exfalso
        exact htemperature34_ne ((hkind_iff .threeToFour).1 hkind)
    | adiabatic => rfl

  have hheat12_zero :
      siCoordinate (cycle.process .oneToTwo).heatIntoSystem = 0 :=
    hadiabatic_heat .oneToTwo hkind12
  have hheat34_zero :
      siCoordinate (cycle.process .threeToFour).heatIntoSystem = 0 :=
    hadiabatic_heat .threeToFour hkind34

  have hfield23' :
      siCoordinate (cycle.finishState .twoToThree).field <
        siCoordinate (cycle.startState .twoToThree).field := by
    change siCoordinate (cycle.state .three).field <
      siCoordinate (cycle.state .two).field
    exact hfield32
  have hfield41' :
      siCoordinate (cycle.startState .fourToOne).field <
        siCoordinate (cycle.finishState .fourToOne).field := by
    change siCoordinate (cycle.state .four).field <
      siCoordinate (cycle.state .one).field
    exact hfield41
  have hheat23_pos :
      0 < siCoordinate (cycle.process .twoToThree).heatIntoSystem :=
    ((hisothermal_heat .twoToThree hisothermal23).2).2 hfield23'
  have hheat41_neg :
      siCoordinate (cycle.process .fourToOne).heatIntoSystem < 0 :=
    ((hisothermal_heat .fourToOne hisothermal41).1).2 hfield41'

  have hheat23_magnitude :
      siCoordinate (cycle.process .twoToThree).heatIntoSystem =
        siCoordinate reservoirs.heatAbsorbedFromColdMagnitude :=
    (hmagnitudes .twoToThree).2 hheat23_pos
  have hheat41_magnitude :
      siCoordinate (cycle.process .fourToOne).heatIntoSystem =
        -siCoordinate reservoirs.heatDeliveredToHotMagnitude := by
    have h := (hmagnitudes .fourToOne).1 hheat41_neg
    linarith

  have hdelivered41 :
      HeatDeliveredToHotOn cycle reservoirs .fourToOne := by
    refine ⟨hisothermal41, ?_, ?_, hheat41_magnitude⟩
    · change (cycle.state .four).temperature = reservoirs.hotTemperature
      exact htemperature4_hot
    · change (cycle.state .one).temperature = reservoirs.hotTemperature
      exact htemperature1_hot
  have habsorbed23 :
      HeatAbsorbedFromColdOn cycle reservoirs .twoToThree := by
    refine ⟨hisothermal23, ?_, ?_, hheat23_magnitude⟩
    · change (cycle.state .two).temperature = reservoirs.coldTemperature
      exact htemperature2_cold
    · change (cycle.state .three).temperature = reservoirs.coldTemperature
      exact htemperature3_cold

  let solution : DiagramAnnotation :=
    { hotColumn := .right
      coldColumn := .left
      heatToHotLeg := .fourToOne
      heatFromColdLeg := .twoToThree }
  have hsolution : IsCorrectAnnotation cycle reservoirs solution := by
    change
      columnTemperature cycle .right = reservoirs.hotTemperature ∧
      columnTemperature cycle .left = reservoirs.coldTemperature ∧
      (TemperatureColumn.right : TemperatureColumn) ≠ .left ∧
      HeatDeliveredToHotOn cycle reservoirs .fourToOne ∧
      HeatAbsorbedFromColdOn cycle reservoirs .twoToThree ∧
      (CycleLeg.fourToOne : CycleLeg) ≠ .twoToThree ∧
      ∀ leg,
        siCoordinate (cycle.process leg).heatIntoSystem ≠ 0 ↔
          leg = .fourToOne ∨ leg = .twoToThree
    refine ⟨hhot_level_eq.symm, hcold_level_eq.symm, by decide,
      hdelivered41, habsorbed23, by decide, ?_⟩
    intro leg
    constructor
    · intro hnonzero
      cases leg with
      | oneToTwo => exact (hnonzero hheat12_zero).elim
      | twoToThree => exact Or.inr rfl
      | threeToFour => exact (hnonzero hheat34_zero).elim
      | fourToOne => exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact ne_of_lt hheat41_neg
      · exact ne_of_gt hheat23_pos

  refine ⟨solution, hsolution, ?_⟩
  intro other hother
  change
    columnTemperature cycle other.hotColumn = reservoirs.hotTemperature ∧
    columnTemperature cycle other.coldColumn = reservoirs.coldTemperature ∧
    other.hotColumn ≠ other.coldColumn ∧
    HeatDeliveredToHotOn cycle reservoirs other.heatToHotLeg ∧
    HeatAbsorbedFromColdOn cycle reservoirs other.heatFromColdLeg ∧
    other.heatToHotLeg ≠ other.heatFromColdLeg ∧
    ∀ leg,
      siCoordinate (cycle.process leg).heatIntoSystem ≠ 0 ↔
        leg = other.heatToHotLeg ∨ leg = other.heatFromColdLeg at hother
  rcases hother with
    ⟨hother_hot_temperature, _hother_cold_temperature,
      hother_columns_ne, hother_delivered, hother_absorbed,
      _hother_legs_ne, _hother_complete⟩

  have hother_hot_column : other.hotColumn = .right := by
    cases hcolumn : other.hotColumn with
    | left =>
        exfalso
        have hequal :
            columnTemperature cycle .left =
              columnTemperature cycle .right := by
          calc
            columnTemperature cycle .left = reservoirs.hotTemperature := by
              rw [hcolumn] at hother_hot_temperature
              exact hother_hot_temperature
            _ = columnTemperature cycle .right := hhot_level_eq
        exact (ne_of_lt hcolumn_lt) (congrArg siCoordinate hequal)
    | right => rfl
  have hother_cold_column : other.coldColumn = .left := by
    cases hcolumn : other.coldColumn with
    | left => rfl
    | right =>
        exfalso
        apply hother_columns_ne
        exact hother_hot_column.trans hcolumn.symm

  have hother_hot_heat_neg :
      siCoordinate (cycle.process other.heatToHotLeg).heatIntoSystem < 0 := by
    rw [hother_delivered.2.2.2]
    linarith
  have hother_cold_heat_pos :
      0 < siCoordinate (cycle.process other.heatFromColdLeg).heatIntoSystem := by
    rw [hother_absorbed.2.2.2]
    exact hcold_heat_pos

  have hother_hot_leg : other.heatToHotLeg = .fourToOne := by
    cases hleg : other.heatToHotLeg with
    | oneToTwo =>
        exfalso
        rw [hleg, hheat12_zero] at hother_hot_heat_neg
        exact (lt_irrefl 0 hother_hot_heat_neg)
    | twoToThree =>
        exfalso
        rw [hleg] at hother_hot_heat_neg
        exact (lt_asymm hheat23_pos hother_hot_heat_neg)
    | threeToFour =>
        exfalso
        rw [hleg, hheat34_zero] at hother_hot_heat_neg
        exact (lt_irrefl 0 hother_hot_heat_neg)
    | fourToOne => rfl
  have hother_cold_leg : other.heatFromColdLeg = .twoToThree := by
    cases hleg : other.heatFromColdLeg with
    | oneToTwo =>
        exfalso
        rw [hleg, hheat12_zero] at hother_cold_heat_pos
        exact (lt_irrefl 0 hother_cold_heat_pos)
    | twoToThree => rfl
    | threeToFour =>
        exfalso
        rw [hleg, hheat34_zero] at hother_cold_heat_pos
        exact (lt_irrefl 0 hother_cold_heat_pos)
    | fourToOne =>
        exfalso
        rw [hleg] at hother_cold_heat_pos
        exact (lt_asymm hother_cold_heat_pos hheat41_neg)

  cases other with
  | mk hotColumn coldColumn heatToHotLeg heatFromColdLeg =>
      dsimp only at hother_hot_column hother_cold_column hother_hot_leg hother_cold_leg
      subst hotColumn
      subst coldColumn
      subst heatToHotLeg
      subst heatFromColdLeg
      rfl

end Ipho2026Gpt56solBlind
