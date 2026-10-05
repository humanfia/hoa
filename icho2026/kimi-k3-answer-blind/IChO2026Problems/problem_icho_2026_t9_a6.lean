/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T9, subquestion 9.6 (target `icho_2026_t9_a6`)

**Problem.** (Sealed problem bundle: T9 page 3, questions 9.5–9.6, with the shared
context of T9 pages 1–2.)  β-Cyclodextrin (β-CD) is the cyclic α(1→4)-linked
heptasaccharide of α-D-glucopyranose: 7 units, hence 7 primary (C6) hydroxy groups
and 14 secondary hydroxy groups — the T9 page 3 starting-material template draws the
seven `CH2OH` boxes numbered 1–7 and one `(OH)14` box.  In the Sinay synthesis shown,
native β-CD is (1) exhaustively benzylated (NaH, 30 equiv.; BnCl, 30 equiv.) and
(2) treated with DIBAL-H (2 equiv.), which reductively debenzylates primary positions,
giving intermediate **L**.  The problem text states Sinay's directing rule: a single
protic group (NH or OH) at unit 1 directs the *next* reductive debenzylation of a
primary OH to unit 4 of the macrocyclic ring (or to unit 3 if the unit 4 position is
not available).  L is then ω-alkenylated (t-BuOK, a terminal alkenyl bromide),
dimerized by olefin metathesis (Grubbs I) and hydrogenated (H2, PtO2) to the β-CD
dimer, drawn on T9 page 3 as two macrocycles joined by one saturated linker, each
macrocycle bearing exactly one `CH2O–linker`, one free `CH2OH`, five `CH2OBn`, and
`(OBn)14`.  The dimer is obtained "as a mixture of constitutional linkage isomers".

**Requested output.** `dimer_isomer_count`: the number of constitutional (linkage)
isomers of the β-CD dimer that can form in this synthesis (exact integer).

**Derivation.**
(i) *L is the 1,4-diol.*  30 equiv. of BnCl cover all 7 + 14 = 21 hydroxy groups, so
at the DIBAL-H stage every primary site is benzylated; after the first debenzylation
at some unit `u`, the unit-4 site `u + 3` is a different site (`u + 3 ≠ u` in
`ZMod 7`), hence still benzylated and available.  The second debenzylation therefore
follows the primary directive to unit 4; the unit-3 fallback never triggers in this
synthesis.  L (the T9-A5 structure, derived inline here) is the single 1,4-diol: two
free primary OHs at directed ring distance 3, everything else benzylated.
(ii) *Two half types.*  Mono-alkenylation caps either one of L's two free primary OHs
(the dimer template shows each ring retains exactly one free `CH2OH`; the dimer forms
as a *mixture* of linkage isomers, so the capping is nonselective).  A macrocycle half
is thus decorated by a linker site and a free-OH site at directed distance ±3.  The
α(1→4)-linked all-D-glucose ring is chiral: rotations of the heptagonal template are
symmetries, reflections are not.  The rotation orbits of legal decorations are exactly
the two directed distances `+3` and `-3 = 4` in `ZMod 7`, and `3 ≠ 4`, so there are
exactly two half types (`forward`, `backward`).
(iii) *The dimer is an unordered pair of half types.*  Both monomers carry the same
terminal ω-alkenyl group from the single alkenyl-bromide reagent; cross-metathesis of
two identical terminal alkenes R–CH=CH2 gives R–CH=CH–R and H2/PtO2 reduces it to the
symmetric bridge R–CH2–CH2–R, which is invariant under exchange of its two ends.
Hence a dimer constitution is an unordered pair of half types, and the isomers are
{forward, forward}, {forward, backward}, {backward, backward}: `C(2+1, 2) = 3`.

No atomic weights or empirical-registry bridges are needed; the count follows from the
problem-stated Sinay rule, the printed reagent equivalents, the drawn dimer template,
and `ZMod 7` arithmetic.  Olefin metathesis of identical terminal alkenes followed by
hydrogenation yielding a symmetric bridge is used as a trusted general law.
-/

namespace IChO2026Problems.Icho2026T9A6

/-! ## The β-CD macrocycle as a directed 7-site ring -/

/-- Primary-site positions on the β-CD macrocycle.  β-CD has 7 α-D-glucopyranose
units (shared problem context) joined by α(1→4)-glycosidic bonds, so the sites form a
directed 7-cycle: translations `x ↦ x + t` are exactly the rotational symmetries of
the uniformly protected template, while reflections are not symmetries because the
all-D-glucose ring is chiral.  Index `k` models printed unit `k + 1`; in particular
the Sinay "unit 4" relative to a first site `u` is `u + 3`, and "unit 3" is `u + 2`. -/
abbrev Site := ZMod 7

/-! ## Hydroxy inventory and reagent ledger (problem image, T9 page 3) -/

/-- Primary hydroxy groups of native β-CD: one `CH2OH` per unit; the seven numbered
boxes of the T9 page 3 template. -/
def betaCDprimaryOH : ℕ := 7

/-- Secondary hydroxy groups of native β-CD: the `(OH)14` box of the T9 page 3
template (two per unit). -/
def betaCDsecondaryOH : ℕ := 14

/-- Benzyl chloride charge of the benzylation step (problem image: BnCl, 30 equiv.;
NaH, 30 equiv.). -/
def bnClEquiv : ℕ := 30

/-- The 30 equivalents of BnCl cover all 21 hydroxy groups, so the first step
perbenzylates β-CD: at the DIBAL-H stage every primary site is benzylated.  This is
what makes the unit-4 primary position *available* for the directed second
debenzylation (problem text, T9 page 3). -/
theorem benzylation_is_exhaustive :
    betaCDprimaryOH + betaCDsecondaryOH ≤ bnClEquiv := by decide

/-- DIBAL-H charge of the second step (problem image: DIBAL-H, 2 equiv.): exactly two
primary benzyl groups are removed per molecule of L. -/
def dibahEquiv : ℕ := 2

/-! ## Sinay's directed debenzylation and the structure of L (T9-A5, derived inline) -/

/-- Sinay's directing rule (problem text, T9 page 3): with a first free protic group
at unit `u`, the next primary debenzylation is directed to unit `u + 3` ("unit 4"),
or to unit `u + 2` ("unit 3") only when the unit-4 position is not available. -/
def sinaySecondSite (u : Site) (unitFourAvailable : Bool) : Site :=
  if unitFourAvailable then u + 3 else u + 2

/-- In this synthesis the unit-4 site is always available: after one primary
debenzylation at `u`, the site `u + 3` is a different site, hence still benzylated. -/
theorem unit_four_available (u : Site) : u + 3 ≠ u := by
  intro h
  have h3 : (3 : Site) = 0 := by
    have h' := congrArg (fun x : Site => x - u) h
    simpa using h'
  exact absurd h3 (by decide)

/-- The deprotected pair of L: the Sinay sequence frees the primary sites `u` and
`u + 3` (the 1,4-relation) for some first site `u`; because `unit_four_available`
discharges the rule's availability condition, the `unitFourAvailable = true` branch
applies and the unit-3 fallback never occurs in this synthesis. -/
def sinayPair (u : Site) : Site × Site := (u, u + 3)

/-- L is the 1,4-diol: the two deprotected sites of a Sinay pair are at directed
ring distance 3. -/
theorem sinayPair_dist (u : Site) :
    (sinayPair u).2 - (sinayPair u).1 = 3 := by
  simp [sinayPair]

/-- Structure inventory of L (the T9-A5 answer, derived inline from problem-only
material): 2 free primary OHs, 5 benzylated primary sites, all 14 secondary sites
benzylated, matching the per-ring inventory drawn for each macrocycle of the dimer
(`CH2OH` × 1, `CH2O–linker` × 1 in place of one formerly free OH, `CH2OBn` × 5,
`(OBn)14`). -/
theorem l_inventory : 5 + 2 = betaCDprimaryOH ∧ 14 = betaCDsecondaryOH := ⟨rfl, rfl⟩

/-! ## Half decorations: the mono-functionalized macrocycles of the dimer -/

/-- A legal primary-site decoration of one macrocycle half of the dimer: the ordered
pair `(linker site, free-OH site)`.  Both sites lie in L's deprotected pair — the
dimer template (T9 page 3) shows each macrocycle bearing exactly one `CH2O–linker`
and one free `CH2OH` — so the directed ring distance between them is ±3 (the Sinay
1,4-relation). -/
abbrev HalfDecoration : Type :=
  { p : Site × Site // p.2 - p.1 = 3 ∨ p.1 - p.2 = 3 }

/-- Rotating the template by `t` units maps decorations to decorations: the uniformly
benzylated ring has the full C₇ rotational symmetry. -/
def HalfDecoration.rotate (d : HalfDecoration) (t : Site) : HalfDecoration :=
  ⟨(d.val.1 + t, d.val.2 + t), by
    rcases d.property with h | h
    · refine Or.inl ?_
      have hr : d.val.2 + t - (d.val.1 + t) = d.val.2 - d.val.1 := by abel
      rw [hr]; exact h
    · refine Or.inr ?_
      have hr : d.val.1 + t - (d.val.2 + t) = d.val.1 - d.val.2 := by abel
      rw [hr]; exact h⟩

/-- Two decorations represent the same constitution of a macrocycle half iff they are
related by a rotation of the template (the only symmetries of the chiral ring). -/
def SameOrbit (d e : HalfDecoration) : Prop :=
  ∃ t : Site, e = d.rotate t

/-- The directed linker→OH distance of a legal decoration is `+3` or `-3 = 4` in
`ZMod 7`. -/
theorem HalfDecoration.dist_mem (d : HalfDecoration) :
    d.val.2 - d.val.1 = 3 ∨ d.val.2 - d.val.1 = 4 := by
  rcases d.property with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hneg : d.val.2 - d.val.1 = -(d.val.1 - d.val.2) := by abel
    rw [hneg, h]
    decide

/-- Decorations with the same directed linker→OH distance lie in one rotation orbit:
translate by the difference of the linker sites. -/
theorem sameOrbit_of_dist_eq {d e : HalfDecoration}
    (hd : d.val.2 - d.val.1 = e.val.2 - e.val.1) : SameOrbit d e := by
  refine ⟨e.val.1 - d.val.1, ?_⟩
  apply Subtype.ext
  rw [Prod.ext_iff]
  constructor
  · show e.val.1 = d.val.1 + (e.val.1 - d.val.1)
    abel
  · show e.val.2 = d.val.2 + (e.val.1 - d.val.1)
    calc e.val.2 = e.val.1 + (e.val.2 - e.val.1) := by abel
      _ = e.val.1 + (d.val.2 - d.val.1) := by rw [← hd]
      _ = d.val.2 + (e.val.1 - d.val.1) := by abel

/-- Capping the first site of a Sinay pair (linker at `u`, free OH at `u + 3`). -/
def HalfDecoration.mkFirst (u : Site) : HalfDecoration :=
  ⟨(u, u + 3), Or.inl (by show u + 3 - u = 3; abel)⟩

/-- Capping the second site of a Sinay pair (linker at `u + 3`, free OH at `u`). -/
def HalfDecoration.mkSecond (u : Site) : HalfDecoration :=
  ⟨(u + 3, u), Or.inr (by show u + 3 - u = 3; abel)⟩

/-! ## The two half types -/

/-- The constitution type of one macrocycle half of the dimer: the rotation orbit of a
legal decoration.  Because the α(1→4)-linked all-D-glucose ring is chiral, the orbit
is captured exactly by the directed linker→OH distance: `forward` (distance +3:
linker at unit 1, free OH at unit 4) or `backward` (distance −3: linker at unit 4,
free OH at unit 1). -/
inductive HalfType
  | forward
  | backward
deriving DecidableEq, Repr, Fintype

/-- The orbit label of a decoration, read off its directed linker→OH distance. -/
def halfTypeOf (d : HalfDecoration) : HalfType :=
  if d.val.2 - d.val.1 = 3 then .forward else .backward

theorem halfTypeOf_eq_forward (d : HalfDecoration) :
    halfTypeOf d = .forward ↔ d.val.2 - d.val.1 = 3 := by
  unfold halfTypeOf
  by_cases h : d.val.2 - d.val.1 = 3
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun hf => HalfType.noConfusion hf, fun hd => absurd hd h⟩

theorem halfTypeOf_eq_backward (d : HalfDecoration) :
    halfTypeOf d = .backward ↔ d.val.2 - d.val.1 = 4 := by
  unfold halfTypeOf
  by_cases h : d.val.2 - d.val.1 = 3
  · rw [if_pos h]
    constructor
    · intro hf; exact HalfType.noConfusion hf
    · intro h4; exact absurd (h.symm.trans h4) (by decide)
  · rw [if_neg h]
    rcases d.dist_mem with h3 | h4
    · exact absurd h3 h
    · exact ⟨fun _ => h4, fun _ => rfl⟩

/-- Rotation invariance: the orbit label is unchanged by rotating the template. -/
theorem halfTypeOf_rotate (d : HalfDecoration) (t : Site) :
    halfTypeOf (d.rotate t) = halfTypeOf d := by
  have hr : d.val.2 + t - (d.val.1 + t) = d.val.2 - d.val.1 := by abel
  rcases d.dist_mem with h3 | h4
  · rw [(halfTypeOf_eq_forward d).mpr h3]
    apply (halfTypeOf_eq_forward _).mpr
    show d.val.2 + t - (d.val.1 + t) = 3
    rw [hr]; exact h3
  · rw [(halfTypeOf_eq_backward d).mpr h4]
    apply (halfTypeOf_eq_backward _).mpr
    show d.val.2 + t - (d.val.1 + t) = 4
    rw [hr]; exact h4

/-- The orbit label is a complete invariant: decorations with the same label lie in
the same rotation orbit. -/
theorem sameOrbit_of_halfTypeOf_eq {d e : HalfDecoration}
    (h : halfTypeOf d = halfTypeOf e) : SameOrbit d e := by
  apply sameOrbit_of_dist_eq
  by_cases hd : d.val.2 - d.val.1 = 3
  · have he : e.val.2 - e.val.1 = 3 := by
      have hf := (halfTypeOf_eq_forward d).mpr hd
      rw [h] at hf
      exact (halfTypeOf_eq_forward e).mp hf
    rw [hd, he]
  · have hd4 : d.val.2 - d.val.1 = 4 := d.dist_mem.resolve_left hd
    have hb := (halfTypeOf_eq_backward d).mpr hd4
    rw [h] at hb
    have he4 := (halfTypeOf_eq_backward e).mp hb
    rw [hd4, he4]

/-- Both half types are chemically realized: the mono-alkenylation of L is
nonselective between the two free primary OHs (the dimer is obtained "as a mixture of
constitutional linkage isomers", problem text T9 page 3), so capping the first site of
a Sinay pair gives the forward half and capping the second gives the backward half. -/
theorem halfType_realized : ∀ t : HalfType, ∃ d : HalfDecoration, halfTypeOf d = t := by
  intro t
  cases t with
  | forward =>
      exact ⟨HalfDecoration.mkFirst 0,
        (halfTypeOf_eq_forward _).mpr (by decide)⟩
  | backward =>
      exact ⟨HalfDecoration.mkSecond 0,
        (halfTypeOf_eq_backward _).mpr (by decide)⟩

/-- The directed linker→OH distance of a half type: `+3` for `forward`, `-3 = 4` for
`backward`. -/
def HalfType.toDist : HalfType → { d : Site // d = 3 ∨ d = 4 }
  | .forward => ⟨3, Or.inl rfl⟩
  | .backward => ⟨4, Or.inr rfl⟩

/-- The half type of a directed distance. -/
def HalfType.ofDist : { d : Site // d = 3 ∨ d = 4 } → HalfType :=
  fun d => if d.val = 3 then .forward else .backward

/-- The two half types are exactly the two directed distances `+3` and `-3 = 4` in
`ZMod 7`; there are exactly two because `3 ≠ 4` in `ZMod 7`. -/
def halfTypeEquivDist : HalfType ≃ { d : Site // d = 3 ∨ d = 4 } where
  toFun := HalfType.toDist
  invFun := HalfType.ofDist
  left_inv := by
    intro t
    cases t with
    | forward =>
        show HalfType.ofDist ⟨3, Or.inl rfl⟩ = HalfType.forward
        exact if_pos rfl
    | backward =>
        show HalfType.ofDist ⟨4, Or.inr rfl⟩ = HalfType.backward
        exact if_neg (by decide)
  right_inv := by
    intro d
    obtain ⟨v, hv⟩ := d
    by_cases h3 : v = 3
    · show HalfType.toDist (HalfType.ofDist ⟨v, hv⟩) = ⟨v, hv⟩
      rw [show HalfType.ofDist ⟨v, hv⟩ = HalfType.forward from if_pos h3]
      apply Subtype.ext
      show (3 : Site) = v
      exact h3.symm
    · have h4 : v = 4 := hv.resolve_left h3
      show HalfType.toDist (HalfType.ofDist ⟨v, hv⟩) = ⟨v, hv⟩
      rw [show HalfType.ofDist ⟨v, hv⟩ = HalfType.backward from if_neg h3]
      apply Subtype.ext
      show (4 : Site) = v
      exact h4.symm

/-- There are exactly two half types. -/
theorem card_halfType : Fintype.card HalfType = 2 := by
  rw [Fintype.card_congr halfTypeEquivDist]
  decide

/-! ## The dimer constitutions -/

/-- The constitutional isomers of the β-CD dimer: unordered pairs of half types.  The
saturated linker is symmetric — both macrocycles receive the same terminal ω-alkenyl
group from the single alkenyl-bromide reagent (problem image, T9 page 3), olefin
metathesis of two identical terminal alkenes R–CH=CH2 gives R–CH=CH–R, and H2/PtO2
reduces it to R–CH2–CH2–R (trusted general law) — so exchanging the two halves of a
dimer gives the same constitution. -/
inductive DimerIsomer
  /-- Both halves forward: on each ring the linker is at unit 1 and the free OH at
  unit 4. -/
  | forwardForward
  /-- One forward half and one backward half. -/
  | forwardBackward
  /-- Both halves backward: on each ring the linker is at unit 4 and the free OH at
  unit 1. -/
  | backwardBackward
deriving DecidableEq, Repr, Fintype

/-- Map a dimer isomer to the unordered pair of half types it comprises. -/
def DimerIsomer.toSym2 : DimerIsomer → Sym2 HalfType
  | .forwardForward => s(.forward, .forward)
  | .forwardBackward => s(.forward, .backward)
  | .backwardBackward => s(.backward, .backward)

/-- Map an unordered pair of half types to the dimer isomer it constitutes. -/
def DimerIsomer.ofSym2 : Sym2 HalfType → DimerIsomer :=
  Sym2.lift ⟨fun
    | .forward, .forward => .forwardForward
    | .forward, .backward => .forwardBackward
    | .backward, .forward => .forwardBackward
    | .backward, .backward => .backwardBackward,
    fun a b => by cases a <;> cases b <;> rfl⟩

/-- The dimer constitutions are exactly the unordered pairs of half types. -/
def dimerIsomerEquivSym2 : DimerIsomer ≃ Sym2 HalfType where
  toFun := DimerIsomer.toSym2
  invFun := DimerIsomer.ofSym2
  left_inv := by
    intro d
    cases d <;> rfl
  right_inv := by
    intro s
    induction s using Sym2.ind with
    | _ a b => cases a <;> cases b <;> first | rfl | exact Sym2.eq_swap

/-- The number of constitutional isomers of the β-CD dimer: the number of unordered
pairs of half types joined by the symmetric saturated linker. -/
def dimerIsomerCount : ℕ := Fintype.card (Sym2 HalfType)

/-- The multiset counting formula: the number of unordered pairs drawn from the two
half types is `C(2 + 1, 2)`. -/
theorem dimerIsomerCount_eq_choose :
    dimerIsomerCount = (Fintype.card HalfType + 1).choose 2 := by
  rw [dimerIsomerCount, Fintype.card_congr dimerIsomerEquivSym2.symm, card_halfType]
  decide

/-- The requested count: exactly 3 constitutional linkage isomers. -/
theorem dimerIsomerCount_eq : dimerIsomerCount = 3 := by
  rw [dimerIsomerCount, Fintype.card_congr dimerIsomerEquivSym2.symm]
  decide

/-! ## Raw and reported result specifications -/

/-- The raw derived quantity as a real number: the exact integer count of dimer
constitutions, exposed as the cardinality of the unordered-pair type (the governing
combinatorial relation), not as a stipulated decimal. -/
def dimerIsomerCountReal : ℝ := (dimerIsomerCount : ℝ)

theorem dimerIsomerCountReal_eq : dimerIsomerCountReal = 3 := by
  rw [dimerIsomerCountReal, dimerIsomerCount_eq]
  norm_num

/-- Certified non-degenerate enclosure of the raw count: the cell `(2, 4)` contains
exactly one integer, the raw count 3. -/
theorem dimerIsomerCountReal_interval :
    (2 : ℝ) < dimerIsomerCountReal ∧ dimerIsomerCountReal < 4 := by
  rw [dimerIsomerCountReal_eq]
  exact ⟨by norm_num, by norm_num⟩

/-- Exact-integer reporting of the count on the unit lattice (reporting quantum 1;
the source reporting policy for `dimer_isomer_count` is `exact_integer`). -/
theorem reportsAtQuantum_dimerIsomerCount :
    IChO2026Chem.Reporting.ReportsAtQuantum dimerIsomerCountReal 3 1 := by
  rw [dimerIsomerCountReal_eq]
  refine ⟨one_pos, ⟨3, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 3)]
  exact ⟨by norm_num, by norm_num⟩

/-- Raw derivation spec for the requested output `dimer_isomer_count`, before any
reporting rounding: the assumption chain (exhaustive benzylation, unit-4
availability, the Sinay 1,4-pattern of L), the orbit analysis (the directed distance
is a complete rotation-orbit invariant, both half types are realized, there are
exactly two half types), the symmetric-linker unordered-pair model, the multiset
counting formula `C(2+1, 2)`, the exact count 3, and its certified non-degenerate
enclosure `(2, 4)`. -/
def RawResultSpec : Prop :=
  betaCDprimaryOH + betaCDsecondaryOH ≤ bnClEquiv
  ∧ (∀ u : Site, u + 3 ≠ u)
  ∧ (∀ u : Site, (sinayPair u).2 - (sinayPair u).1 = 3)
  ∧ (∀ d : HalfDecoration, d.val.2 - d.val.1 = 3 ∨ d.val.2 - d.val.1 = 4)
  ∧ (∀ d e : HalfDecoration, halfTypeOf d = halfTypeOf e → SameOrbit d e)
  ∧ (∀ t : HalfType, ∃ d : HalfDecoration, halfTypeOf d = t)
  ∧ Nonempty (HalfType ≃ { d : Site // d = 3 ∨ d = 4 })
  ∧ Fintype.card HalfType = 2
  ∧ Nonempty (DimerIsomer ≃ Sym2 HalfType)
  ∧ dimerIsomerCount = (Fintype.card HalfType + 1).choose 2
  ∧ dimerIsomerCount = 3
  ∧ ((2 : ℝ) < dimerIsomerCountReal ∧ dimerIsomerCountReal < 4)

/-- Reported (final) spec: the count reported as the exact integer 3 (integer lattice,
reporting quantum 1; `exact_integer` policy for this output), equal to the raw count. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum dimerIsomerCountReal 3 1
  ∧ dimerIsomerCountReal = 3
  ∧ dimerIsomerCount = 3

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("e2408287ffff808cee35758dea99594393172e56ea6b3ab1df1582916deba9ae" : String)
      = "e2408287ffff808cee35758dea99594393172e56ea6b3ab1df1582916deba9ae"
      ∧ RawResultSpec :=
  ⟨rfl, benzylation_is_exhaustive, unit_four_available, sinayPair_dist,
    HalfDecoration.dist_mem, fun _ _ h => sameOrbit_of_halfTypeOf_eq h,
    halfType_realized, ⟨halfTypeEquivDist⟩, card_halfType, ⟨dimerIsomerEquivSym2⟩,
    dimerIsomerCount_eq_choose, dimerIsomerCount_eq, dimerIsomerCountReal_interval⟩

/-- Reported result certificate: binds the answer-blind reported-role payload digest
to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("168e638e39b23df88784ec36cd1de2c1e55c53a6af3180fdaf5c26c8a0ec07f1" : String)
      = "168e638e39b23df88784ec36cd1de2c1e55c53a6af3180fdaf5c26c8a0ec07f1"
      ∧ ReportedResultSpec :=
  ⟨rfl, reportsAtQuantum_dimerIsomerCount, dimerIsomerCountReal_eq, dimerIsomerCount_eq⟩

end IChO2026Problems.Icho2026T9A6
