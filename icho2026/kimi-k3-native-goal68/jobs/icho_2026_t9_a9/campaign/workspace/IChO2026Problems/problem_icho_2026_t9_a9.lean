import Mathlib

/-!
# Problem icho_2026_t9_a9 (IChO 2026, T9 – Cyclodextrin Chemistry, question 9.9)

**Statement (from `theory_problem.pdf`, page Q9-5).**
*"Determine the number of all possible arrangements of the functional groups on a
hexadifferentiated α-CD (**assume** only the CH₂OH groups have been modified)."*

## Chemistry grounding of the model

* α-Cyclodextrin is a macrocycle of **six** α-D-glucopyranoside units (problem
  text: "the three most common cyclodextrins (α-, β-, γ-cyclodextrin) contain 6,
  7, and 8 α-D-glucopyranoside units").  Each unit has exactly one primary CH₂OH
  group (C6), and 9.9 stipulates that **only the CH₂OH groups have been
  modified**.  The functionalized sites hence form a 6-site cyclic array,
  modelled as `ZMod 6`.
* "Hexadifferentiated" — the six sites carry **six different** functional groups
  (the Sollogoub sequence N → O → P → Q → R → S of Q9-8 installs six distinct
  groups on the six primary positions of α-CD).  Groups are labelled by
  `Fin 6`; an *addressed* pattern is a bijection `ZMod 6 ≃ Fin 6`.  There are
  `6! = 720` of them (`Fintype.card_perm`).
* Two addressed patterns describe the **same molecule** iff they differ by a
  pure rotation of the macrocycle.  α-CD contains only D-glucose units, hence it
  is *chiral*: a reflection-reversed assignment is the enantiomer and is counted
  as a different arrangement.  The symmetry group is therefore the cyclic
  rotation group of order 6 — formalized as `Multiplicative (ZMod 6)` acting on
  patterns by translation of the site index; there is no reflection coset.
* If a rotation `k ≠ 0` fixed a pattern `σ`, then `σ (i - k) = σ i` for every
  site `i`, and injectivity of `σ` forces `k = 0` — a contradiction.  Hence the
  action is **free** (`rotation_action_isFree`), every orbit has exactly 6
  elements (`orbit_card_eq_six`), and orbit counting gives
  `#Arrangement = 720 / 6 = 120` (`arrangement_count`).

All numerical claims (`720 = 6!`, orbit size `6`, the final count `120`) are
*proved* from the definitions below, not assumed.
-/

namespace IChO2026.T9.A9

/-- The cyclic array of the six glucopyranoside units of α-CD, positioned by
their index in the ring. -/
abbrev Ring6 := ZMod 6

/-- The cyclic rotation group of the macrocycle (order 6), written
multiplicatively so that `MulAction` results apply. -/
abbrev Rot := Multiplicative Ring6

/-- A *functionalization pattern*: a bijective assignment of the six distinct
functional groups (tagged by `Fin 6`) to the six CH₂OH sites of the addressed
α-CD ring. -/
abbrev Pattern := Ring6 ≃ Fin 6

/-- There are `6! = 720` addressed functionalization patterns (all permutations
of the six distinct groups on the six sites). -/
theorem patterns_count : Fintype.card Pattern = 720 := by
  show Fintype.card (Ring6 ≃ Fin 6) = 720
  have e : Pattern ≃ Equiv.Perm (Fin 6) := Equiv.equivCongr
    (ZMod.finEquiv 6).toEquiv.symm (Equiv.refl (Fin 6))
  rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- Rotation by `k` acts on a pattern by precomposition with the inverse site
shift on the left: since a pattern maps sites to group tags, rotating the ring
by `k` moves the group at site `i` to site `i + k`, so the rotated assignment
at site `i` is `σ ((-k) + i) = σ (i - k)`. -/
instance smulPattern : SMul Rot Pattern where
  smul k σ := (Equiv.addLeft (-k.toAdd)).trans σ

theorem smul_app (k : Rot) (σ : Pattern) (i : Ring6) :
    (k • σ) i = σ (i - k.toAdd) := by
  show σ ((-k.toAdd) + i) = σ (i - k.toAdd)
  congr 1
  rw [sub_eq_add_neg, add_comm]

instance mulActionPattern : MulAction Rot Pattern where
  one_smul σ := by
    apply Equiv.ext; intro i
    rw [smul_app]
    simp
  mul_smul k l σ := by
    apply Equiv.ext; intro i
    rw [smul_app, smul_app, smul_app]
    show σ (i - (k * l).toAdd) = σ (i - k.toAdd - l.toAdd)
    congr 1
    rw [show (k * l).toAdd = k.toAdd + l.toAdd from rfl, sub_sub,
      add_comm k.toAdd l.toAdd]

/-- The (type of) *arrangements*: functionalization patterns identified up to
rotation of the macrocycle — mathematically `Pattern / Rot`. -/
abbrev Arrangement := MulAction.orbitRel.Quotient Rot Pattern

noncomputable instance : DecidableRel (MulAction.orbitRel Rot Pattern).r :=
  fun _ _ => Classical.dec _

noncomputable instance fintypeArrangement : Fintype Arrangement :=
  Quotient.fintype (MulAction.orbitRel Rot Pattern)

noncomputable instance fintypeOrbit (σ : Pattern) :
    Fintype (MulAction.orbit Rot σ) :=
  Fintype.ofFinite _

noncomputable instance fintypeStabilizer (σ : Pattern) :
    Fintype (MulAction.stabilizer Rot σ) :=
  Fintype.ofFinite _

/-- **Free action**: no nontrivial rotation of the α-CD ring fixes any
functionalization pattern: from `k • σ = σ` one gets `σ (0 - k) = σ 0`, and
injectivity of `σ` forces `k = 0`. -/
theorem rotation_action_isFree {k : Rot} (hk : k ≠ 1) (σ : Pattern) :
    (k • σ) ≠ σ := by
  intro h
  have hfixed : (k • σ) 0 = σ 0 := congr_fun (congr_arg DFunLike.coe h) 0
  rw [smul_app, zero_sub] at hfixed
  have htoAdd : (-k.toAdd : Ring6) = 0 := σ.injective hfixed
  have hz : k.toAdd = 0 := neg_eq_zero.mp htoAdd
  exact hk (Multiplicative.ext hz)

/-- Every rotation orbit contains exactly 6 addressed patterns: the stabilizer
is trivial by `rotation_action_isFree`, and orbit–stabilizer counting gives
`#orbit * #stabilizer = #Rot = 6`. -/
theorem orbit_card_eq_six (σ : Pattern) :
    Fintype.card (MulAction.orbit Rot σ) = 6 := by
  classical
  have hstab : MulAction.stabilizer Rot σ = ⊥ := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    constructor
    · intro h
      by_contra hk
      exact rotation_action_isFree hk σ h
    · intro h
      rw [h]
      exact one_smul Rot σ
  have hbot : Fintype.card (MulAction.stabilizer Rot σ) = 1 := by
    rw [Fintype.card_eq_one_iff]
    use ⟨1, one_mem _⟩
    intro ⟨k, hk⟩
    apply Subtype.ext
    have : k = 1 := by
      have := hstab ▸ hk
      rwa [Subgroup.mem_bot] at this
    exact this
  have horb : Fintype.card (MulAction.orbit Rot σ)
      * Fintype.card (MulAction.stabilizer Rot σ) = Fintype.card Rot :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Rot) σ
  rw [hbot, mul_one] at horb
  simpa [Rot, ZMod.card] using horb

/-- There are exactly `6` rotations of the α-CD macrocycle. -/
theorem rotations_count : Fintype.card Rot = 6 := by simp [Rot, ZMod.card]

/-- **Answer to 9.9**: there are exactly `120` different arrangements of the six
different functional groups on the primary rim of α-CD, i.e.
`#Pattern / #rotations = 6! / 6 = 5! = 120`. -/
theorem arrangement_count : Fintype.card Arrangement = 120 := by
  classical
  have hdecomp := MulAction.selfEquivSigmaOrbits Rot Pattern
  have hcard : Fintype.card Pattern
      = ∑ ω : Arrangement, Fintype.card (MulAction.orbit Rot ω.out) := by
    rw [Fintype.card_congr hdecomp, Fintype.card_sigma]
  have hfib : ∀ ω : Arrangement,
      Fintype.card (MulAction.orbit Rot ω.out) = 6 :=
    fun ω => orbit_card_eq_six ω.out
  have hp := patterns_count
  rw [hcard] at hp
  have hsum : (∑ _ω : Arrangement, 6) = Fintype.card Arrangement * 6 := by
    rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  have : ∑ ω : Arrangement, Fintype.card (MulAction.orbit Rot ω.out)
      = ∑ _ω : Arrangement, 6 :=
    Finset.sum_congr rfl (fun ω _ => hfib ω)
  rw [this, hsum] at hp
  -- patterns_count : 720 = Fintype.card Arrangement * 6
  omega

/-- Reporting sanity check: `6! = 720`, `720 / 6 = 120`, consistent with the
exact-integer reporting policy of the problem. -/
theorem answer_numeric : (Nat.factorial 6 : ℕ) = 720 ∧ 720 / 6 = 120 := by
  exact ⟨by decide, by decide⟩

#print axioms patterns_count
#print axioms rotation_action_isFree
#print axioms orbit_card_eq_six
#print axioms arrangement_count

end IChO2026.T9.A9
