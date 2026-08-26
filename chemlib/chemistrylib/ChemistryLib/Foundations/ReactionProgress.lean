import ChemistryLib.Foundations.Amount
import ChemistryLib.Foundations.Stoichiometry

/-!
# Reaction progress and reaction rate

An extent change is common to every species when each signed amount change is
its stoichiometric number times that extent change.  The same identity defines
an extent rate.  Dividing either identity by a nonzero stoichiometric number
gives a normalization independent of the participating species.  At a
caller-supplied positive volume, the reaction rate is the extent rate divided
by that volume; no temporal constancy assumption is built into this definition.

Sources:

* `IUPAC-GOLDBOOK-5.0.0:E02283 definition 1 and displayed extent identity`
* `IUPAC-GOLDBOOK-5.0.0:R05156 definition 1 and displayed rate identities`
* `icho_2026_t2_a2:T2-A2`
* `icho_2026_t4_a6:T4-A6`
* `icho_2026_t7_a3:T7-A3`
-/

namespace ChemistryLib.Foundations

/-- Every species amount change is its stoichiometric number times one common
extent change. -/
def IsExtentChange {Species : Type} (ν : StoichiometricNumber Species)
    (dn : Species → AmountChange) (dξ : AmountChange) : Prop :=
  ∀ s, (dn s).value = (ν s : ℝ) * dξ.value

/-- Every species amount rate is its stoichiometric number times one common
extent rate. -/
def IsExtentRate {Species : Type} (ν : StoichiometricNumber Species)
    (dnDt : Species → ExtentRate) (dξdt : ExtentRate) : Prop :=
  ∀ s, (dnDt s).value = (ν s : ℝ) * dξdt.value

/-- Normalizing amount changes by any two participating species gives the same
extent change. -/
theorem extentChange_normalization_independent {Species : Type}
    (ν : StoichiometricNumber Species) (dn : Species → AmountChange)
    (dξ : AmountChange) (h : IsExtentChange ν dn dξ) (s t : Species)
    (hs : ν s ≠ 0) (ht : ν t ≠ 0) :
    (dn s).value / (ν s : ℝ) = (dn t).value / (ν t : ℝ) := by
  have hs' : (ν s : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hs
  have ht' : (ν t : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ht
  rw [h s, h t, mul_div_cancel_left₀ _ hs', mul_div_cancel_left₀ _ ht']

/-- Normalizing a participating species' amount change recovers the common
extent change. -/
theorem extentChange_normalized {Species : Type}
    (ν : StoichiometricNumber Species) (dn : Species → AmountChange)
    (dξ : AmountChange) (h : IsExtentChange ν dn dξ) (s : Species)
    (hs : ν s ≠ 0) :
    dξ.value = (dn s).value / (ν s : ℝ) := by
  have hs' : (ν s : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hs
  rw [h s, mul_div_cancel_left₀ _ hs']

/-- Normalizing amount rates by any two participating species gives the same
extent rate. -/
theorem extentRate_normalization_independent {Species : Type}
    (ν : StoichiometricNumber Species) (dnDt : Species → ExtentRate)
    (dξdt : ExtentRate) (h : IsExtentRate ν dnDt dξdt) (s t : Species)
    (hs : ν s ≠ 0) (ht : ν t ≠ 0) :
    (dnDt s).value / (ν s : ℝ) = (dnDt t).value / (ν t : ℝ) := by
  have hs' : (ν s : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hs
  have ht' : (ν t : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ht
  rw [h s, h t, mul_div_cancel_left₀ _ hs', mul_div_cancel_left₀ _ ht']

/-- Normalizing a participating species' amount rate recovers the common
extent rate. -/
theorem extentRate_normalized {Species : Type}
    (ν : StoichiometricNumber Species) (dnDt : Species → ExtentRate)
    (dξdt : ExtentRate) (h : IsExtentRate ν dnDt dξdt) (s : Species)
    (hs : ν s ≠ 0) :
    dξdt.value = (dnDt s).value / (ν s : ℝ) := by
  have hs' : (ν s : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hs
  rw [h s, mul_div_cancel_left₀ _ hs']

/-- Reaction rate at a fixed positive volume: extent rate divided by volume. -/
noncomputable def reactionRateAtVolume (dξdt : ExtentRate) (V : Volume) : ReactionRate :=
  Units.Quantity.div dξdt V.1

/-- The numerical value of the fixed-volume reaction rate. -/
theorem reactionRateAtVolume_value (dξdt : ExtentRate) (V : Volume) :
    (reactionRateAtVolume dξdt V).value = dξdt.value / V.1.value :=
  rfl

end ChemistryLib.Foundations
