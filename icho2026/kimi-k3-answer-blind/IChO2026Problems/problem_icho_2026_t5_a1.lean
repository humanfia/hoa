/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T5, subquestion 5.1 (target `icho_2026_t5_a1`)

**Problem.** (Sealed problem bundle: T5 page 1 — header, fragment figure and
question 5.1 box.)  Cardiolipins are a family of *acyclic* phospholipids
differing in fatty acid residues; **PL1** belongs to this family.  Molecules
are built from structural fragments by joining their free-valence ("wavy")
ends into covalent bonds, as demonstrated on T5 page 1 by the worked example
of the chiral phospholipid **W** assembled from one copy each of fragments
a (∿–H), b ((HO)(O)P(∿)₂), c (∿O–CH₂–CH(O∿)–CH₂–O∿), d (∿–C(=O)–R) and
e (∿–OH).  For PL1 only fragments **a–d** are used, in the stated quantities

  a : b : c : d  =  n : 2 : 3 : 4      (n unknown),

and "it is possible to assemble the **non-ionised** form of PL1" from exactly
these fragments (problem_text).  R is a hydrocarbon substituent in the fatty
acid structure, and PL1 does not contain any peroxide (O–O) bonds.

**Requested output.**  Tick one correct statement regarding n:
(a) n is an even number, (b) n is an odd number, (c) n can be either an odd
or an even number.

**Derivation (parity/handshake argument).**  Every covalent bond formed during
assembly consumes exactly two free valences, and a completely assembled
molecule has no dangling wavy ends, so the total number of free valences must
be even.  From the drawn fragments (problem_image): a = ∿–H carries 1 free
valence, b = (HO)(O)P(∿)₂ carries 2, c = ∿O–CH₂–CH(O∿)–CH₂–O∿ carries 3,
d = ∿–C(=O)–R carries 1.  The inventory therefore supplies

  n·1 + 2·2 + 3·3 + 4·1 = n + 17

free valences, so `n + 17` must be even, i.e. `n` must be **odd** — statement
(b).  Since the source stipulates that an assembly exists, (a) is refuted;
since no even `n` admits an assembly, (c) is refuted.  (For orientation: the
tree count `2·bonds = n + 17` with `bonds = instances − 1 = n + 8` would even
force `n = 1`, the cardiolipin skeleton — two phosphate bridges linking three
glycerols with four acyl esters and one free central 2-OH — but the question
asks only for the parity statement.)

The two result contracts at the end are the answer-blind certificates binding
the payload digests to the semantic specifications.
-/

namespace IChO2026Problems.Icho2026T5A1

/-! ## Fragment inventory (problem_image, `T5_page-1.png`, lower fragment row) -/

/-- The four structural element types from which PL1 is assembled
(problem_image, lower fragment row of T5 page 1). -/
inductive FragmentKind
  | /-- a: ∿–H — a hydrogen cap with one free valence -/ a
  | /-- b: (HO)(O)P(∿)₂ — phosphate fragment with two free valences -/ b
  | /-- c: ∿O–CH₂–CH(O∿)–CH₂–O∿ — glyceryl fragment with three free valences -/ c
  | /-- d: ∿–C(=O)–R — fatty-acyl fragment with one free valence -/ d
deriving DecidableEq, Fintype

/-- Free valences ("wavy ends") of one fragment of each kind, read off the
drawn fragment structures (problem_image): a = ∿–H has 1, b = (HO)(O)P(∿)₂
has 2, c = ∿O–CH₂–CH(O∿)–CH₂–O∿ has 3, d = ∿–C(=O)–R has 1. -/
def FragmentKind.freeValences : FragmentKind → ℕ
  | .a => 1
  | .b => 2
  | .c => 3
  | .d => 1

/-- Stated quantities of the four fragment types for the assembly of PL1
(problem_image, lower fragment row: `n ×` a, `2 ×` b, `3 ×` c, `4 ×` d). -/
def FragmentKind.quantity (n : ℕ) : FragmentKind → ℕ
  | .a => n
  | .b => 2
  | .c => 3
  | .d => 4

/-- The chemical element whose atom carries the free valence(s) of each
fragment kind; used to state the peroxide (O–O) exclusion.  Fragment a bonds
through its hydrogen atom, b through phosphorus, c through its glyceryl
oxygens, d through the carbonyl carbon (problem_image). -/
inductive ValenceAtom
  | hydrogen
  | phosphorus
  | oxygen
  | carbonylCarbon
deriving DecidableEq

/-- The atom label of the free valence(s) of each fragment kind. -/
def FragmentKind.valenceAtom : FragmentKind → ValenceAtom
  | .a => .hydrogen
  | .b => .phosphorus
  | .c => .oxygen
  | .d => .carbonylCarbon

/-- Total number of free valences ("wavy ends") supplied by the stated
fragment inventory for PL1. -/
def totalFreeValences (n : ℕ) : ℕ :=
  FragmentKind.quantity n .a * FragmentKind.freeValences .a
    + FragmentKind.quantity n .b * FragmentKind.freeValences .b
    + FragmentKind.quantity n .c * FragmentKind.freeValences .c
    + FragmentKind.quantity n .d * FragmentKind.freeValences .d

/-- The valence inventory is `n + 17` (valence counts from the drawn
fragments; pure arithmetic). -/
theorem totalFreeValences_eq (n : ℕ) : totalFreeValences n = n + 17 := by
  change n * 1 + 2 * 2 + 3 * 3 + 4 * 1 = n + 17
  omega

/-! ## Fragment instances, valence ends, and assemblies -/

/-- One fragment instance in an assembly of PL1: its kind and its copy index
(reducible alias so that typeclass structure on the sigma type is found
automatically). -/
abbrev FragmentInstance (n : ℕ) : Type :=
  (k : FragmentKind) × Fin (FragmentKind.quantity n k)

/-- One free valence ("wavy end") of one fragment instance: the fragment kind,
the copy index, and which of the fragment's valence slots (reducible alias so
that the `Fintype` and `DecidableEq` instances are found automatically). -/
abbrev ValenceEnds (n : ℕ) : Type :=
  (k : FragmentKind) × (Fin (FragmentKind.quantity n k) ×
    Fin (FragmentKind.freeValences k))

/-- The fragment instance carrying a valence end. -/
def ValenceEnds.instanceOf {n : ℕ} (e : ValenceEnds n) : FragmentInstance n :=
  ⟨e.1, e.2.1⟩

/-- The number of valence ends equals the valence inventory:
`card (ValenceEnds n) = n·1 + 2·2 + 3·3 + 4·1 = totalFreeValences n`. -/
theorem card_valenceEnds (n : ℕ) :
    Fintype.card (ValenceEnds n) = totalFreeValences n := by
  have hcard : ∀ (p q : ℕ) [inst : Fintype (Fin p × Fin q)],
      @Fintype.card _ inst = p * q := by
    intro p q inst
    rw [Subsingleton.elim inst (instFintypeProd _ _), Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  rw [Fintype.card_sigma]
  have huniv : (Finset.univ : Finset FragmentKind) = {.a, .b, .c, .d} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hcard, FragmentKind.quantity, FragmentKind.freeValences,
    totalFreeValences]
  omega

/-- The fragment-instance bonding graph induced by a bond-partner map: two
distinct fragment instances are adjacent when a valence end of one is bonded
to a valence end of the other. -/
def instanceGraph {n : ℕ} (partner : ValenceEnds n → ValenceEnds n)
    (hinv : ∀ e, partner (partner e) = e) : SimpleGraph (FragmentInstance n) where
  Adj v w := v ≠ w ∧ ∃ e : ValenceEnds n,
    e.instanceOf = v ∧ (partner e).instanceOf = w
  symm := by
    refine ⟨fun {v w} h => ?_⟩
    obtain ⟨hvw, e, hev, hew⟩ := h
    exact ⟨hvw.symm, partner e, hew, by rw [hinv e]; exact hev⟩
  loopless := by
    refine ⟨fun {v} h => ?_⟩
    obtain ⟨hvv, -⟩ := h
    exact hvv rfl

/-- A complete assembly of (a candidate) PL1 from the stated fragment
inventory (problem_text: "Using only the structural elements a–d in the
quantities stated below, it is possible to assemble the non-ionised form of
PL1").

* `partner` pairs every free valence end with its bond partner — in a complete
  molecule every wavy end is consumed, two ends per covalent bond (the
  handshake content; the worked example W on T5 page 1 shows this semantics);
* `no_peroxide` — no bond joins two oxygen valence ends: PL1 contains no
  peroxide (O–O) bonds (problem_text);
* `no_parallel_bonds` — distinct ends of one fragment instance have partners
  in distinct fragment instances, ruling out intra-instance bonds and double
  bonds between one pair of instances, both of which would create molecular
  rings invisible to the simple `instanceGraph`;
* `acyclic`/`connected` — the assembled fragments form a single acyclic
  molecule: cardiolipins are a family of *acyclic* phospholipids and PL1 is
  one molecule (problem_text).  The non-ionised form is embedded in the
  fragment choice: every phosphate fragment b keeps its –OH. -/
structure Assembly (n : ℕ) where
  /-- The bond-partner map on free valence ends. -/
  partner : ValenceEnds n → ValenceEnds n
  /-- Bonding is mutual: the partner of the partner is the original end. -/
  partner_involutive : ∀ e, partner (partner e) = e
  /-- A bond joins two distinct valence ends. -/
  partner_ne_self : ∀ e, partner e ≠ e
  /-- No peroxide (O–O) bonds: no bond joins two oxygen-bearing valence ends. -/
  no_peroxide : ∀ e : ValenceEnds n, ¬ (e.1.valenceAtom = .oxygen ∧
      (partner e).1.valenceAtom = .oxygen)
  /-- No intra-instance bond and no two bonds between the same pair of
  fragment instances (either would create a molecular ring). -/
  no_parallel_bonds : ∀ e₁ e₂ : ValenceEnds n,
      e₁.instanceOf = e₂.instanceOf →
      (partner e₁).instanceOf = (partner e₂).instanceOf → e₁ = e₂
  /-- The fragment-instance bonding graph has no cycles. -/
  acyclic : (instanceGraph partner partner_involutive).IsAcyclic
  /-- The assembled fragments form one connected molecule. -/
  connected : (instanceGraph partner partner_involutive).Connected

/-! ## The handshake and the parity conclusion -/

/-- **Handshake lemma** (trusted_general_law: every covalent bond formed
during assembly consumes exactly two free valences, and a completely
assembled molecule has no dangling wavy ends): in a complete assembly the
total number of free valences is even — twice the number of assembled bonds.

Proof: `asm.partner` with `asm.partner_involutive` and `asm.partner_ne_self`
is a fixed-point-free involution of the finite type `ValenceEnds n`; its
orbits are exactly the 2-element bond pairs `{e, partner e}`.  Summing the
constant `1 : ZMod 2` over all ends, the two ends of each bond cancel
(`Finset.sum_involution`), so `(Fintype.card (ValenceEnds n) : ZMod 2) = 0`,
i.e. the cardinality is even; conclude with `card_valenceEnds`. -/
theorem assembly_even_totalFreeValences {n : ℕ} (asm : Assembly n) :
    Even (totalFreeValences n) := by
  rw [← card_valenceEnds n]
  have hsum : ∑ e : ValenceEnds n, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (s := Finset.univ) (f := fun _ => (1 : ZMod 2))
      (fun e _ => asm.partner e) (fun e _ => by decide)
      (fun e _ _ => asm.partner_ne_self e) (fun e _ => Finset.mem_univ (asm.partner e))
      (fun e _ => asm.partner_involutive e)
  have hcast : (Fintype.card (ValenceEnds n) : ZMod 2) = 0 := by
    rw [← hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

/-- **Main parity theorem** (T5 question 5.1): every fragment count `n`
admitting a complete assembly of PL1 is odd.  The valence inventory is
`n + 17` (`totalFreeValences_eq`) and must be even
(`assembly_even_totalFreeValences`), hence `n` is odd. -/
theorem assembly_parity_odd {n : ℕ} (h : Nonempty (Assembly n)) : Odd n := by
  obtain ⟨asm⟩ := h
  obtain ⟨m, hm⟩ := assembly_even_totalFreeValences asm
  rw [totalFreeValences_eq] at hm
  exact ⟨m - 9, by omega⟩

/-- Kind index of a fragment type, used for the numerical key below. -/
def FragmentKind.kindIdx : FragmentKind → ℕ
  | .a => 0
  | .b => 1
  | .c => 2
  | .d => 3

/-- A numerical key for the 18 valence ends at `n = 1` — `100·k + 10·i + j`
with `k` the kind index, `i` the copy index, `j` the valence slot — used so
that the kernel can evaluate `witnessPartner` via fast `ℕ`-literal
comparisons (Nat literals are kernel-accelerated, unlike dependent
`Fin`-`Sigma` equality tests). -/
def ValenceEnds.key (e : ValenceEnds 1) : ℕ :=
  e.1.kindIdx * 100 + e.2.1.val * 10 + e.2.2.val

/-- The explicit bond-partner map for the cardiolipin skeleton at `n = 1`
(the nine bonds listed in the docstring of `assembly_one_exists`): with b₁, b₂
the two phosphate fragments, c₁, c₂, c₃ the three glyceryl fragments,
d₁,…,d₄ the four acyl fragments and a₁ the single hydrogen cap, the bonds are
b₁–c₁, b₁–c₂, b₂–c₂, b₂–c₃ (two phosphodiester bridges),
c₁–d₁, c₁–d₂, c₃–d₃, c₃–d₄ (four fatty-acid esters),
c₂–a₁ (the free 2-hydroxyl of the central glycerol).
The map sends each free valence end to its bond partner; the 18 ends are
`⟨k, ⟨i, j⟩⟩` with `i` the copy index and `j` the valence slot. -/
def witnessPartner (e : ValenceEnds 1) : ValenceEnds 1 :=
  if e.key = 0 then ⟨.c, ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩⟩
  else if e.key = 100 then ⟨.c, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 101 then ⟨.c, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 110 then ⟨.c, ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩⟩
  else if e.key = 111 then ⟨.c, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 200 then ⟨.b, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 201 then ⟨.d, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 202 then ⟨.d, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 210 then ⟨.b, ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩⟩
  else if e.key = 211 then ⟨.b, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 212 then ⟨.a, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 220 then ⟨.b, ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩⟩
  else if e.key = 221 then ⟨.d, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 222 then ⟨.d, ⟨⟨3, by decide⟩, ⟨0, by decide⟩⟩⟩
  else if e.key = 300 then ⟨.c, ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩⟩
  else if e.key = 310 then ⟨.c, ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩⟩
  else if e.key = 320 then ⟨.c, ⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩⟩
  else ⟨.c, ⟨⟨2, by decide⟩, ⟨2, by decide⟩⟩⟩

/-- Source-stated feasibility (problem_text, T5 shared context: "it is
possible to assemble the non-ionised form of PL1"): a complete assembly
exists at `n = 1` — the cardiolipin (1,3-bisphosphatidylglycerol) skeleton.

Proof: the explicit bond witness `witnessPartner` (nine bonds, consuming all
1 + 4 + 9 + 4 = 18 valence ends) is a fixed-point-free involution joining no
two oxygen ends and no two ends of one instance to the same instance, all by
finite `decide` checks; the bonding graph on the 10 fragment instances is a
tree — it is connected (explicit walks from every instance to the central
glycerol c₁) and has 9 = 10 − 1 edges (degree-sum formula by `decide`), so it
is acyclic by `SimpleGraph.isTree_iff_connected_and_card`. -/
theorem assembly_one_exists : Nonempty (Assembly 1) := by
  have hpinv : ∀ e : ValenceEnds 1, witnessPartner (witnessPartner e) = e := by
    decide
  have hpself : ∀ e : ValenceEnds 1, witnessPartner e ≠ e := by decide
  have hpox : ∀ e : ValenceEnds 1,
      ¬ (e.1.valenceAtom = .oxygen ∧ (witnessPartner e).1.valenceAtom = .oxygen) := by
    decide
  have hpar : ∀ e₁ e₂ : ValenceEnds 1, e₁.instanceOf = e₂.instanceOf →
      (witnessPartner e₁).instanceOf = (witnessPartner e₂).instanceOf → e₁ = e₂ := by
    decide
  letI : DecidableRel (instanceGraph witnessPartner hpinv).Adj := fun v w =>
    inferInstanceAs (Decidable (v ≠ w ∧ ∃ e : ValenceEnds 1,
      e.instanceOf = v ∧ (witnessPartner e).instanceOf = w))
  letI : DecidablePred (fun (x, y) ↦ (instanceGraph witnessPartner hpinv).Adj x y) :=
    fun p => inferInstanceAs (Decidable ((instanceGraph witnessPartner hpinv).Adj p.1 p.2))
  -- the nine assembly bonds, one adjacency proof per bond
  have e_b0_c0 : (instanceGraph witnessPartner hpinv).Adj ⟨.b, ⟨0, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    ⟨by decide, ⟨.b, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_d0_c0 : (instanceGraph witnessPartner hpinv).Adj ⟨.d, ⟨0, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    ⟨by decide, ⟨.d, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_d1_c0 : (instanceGraph witnessPartner hpinv).Adj ⟨.d, ⟨1, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    ⟨by decide, ⟨.d, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_c1_b0 : (instanceGraph witnessPartner hpinv).Adj ⟨.c, ⟨1, by decide⟩⟩ ⟨.b, ⟨0, by decide⟩⟩ :=
    ⟨by decide, ⟨.c, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_b1_c1 : (instanceGraph witnessPartner hpinv).Adj ⟨.b, ⟨1, by decide⟩⟩ ⟨.c, ⟨1, by decide⟩⟩ :=
    ⟨by decide, ⟨.b, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_a0_c1 : (instanceGraph witnessPartner hpinv).Adj ⟨.a, ⟨0, by decide⟩⟩ ⟨.c, ⟨1, by decide⟩⟩ :=
    ⟨by decide, ⟨.a, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_c2_b1 : (instanceGraph witnessPartner hpinv).Adj ⟨.c, ⟨2, by decide⟩⟩ ⟨.b, ⟨1, by decide⟩⟩ :=
    ⟨by decide, ⟨.c, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_d2_c2 : (instanceGraph witnessPartner hpinv).Adj ⟨.d, ⟨2, by decide⟩⟩ ⟨.c, ⟨2, by decide⟩⟩ :=
    ⟨by decide, ⟨.d, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  have e_d3_c2 : (instanceGraph witnessPartner hpinv).Adj ⟨.d, ⟨3, by decide⟩⟩ ⟨.c, ⟨2, by decide⟩⟩ :=
    ⟨by decide, ⟨.d, ⟨⟨3, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩
  -- walks from every fragment instance to the central glycerol c₁ = ⟨.c, 0⟩
  have w_b0 : (instanceGraph witnessPartner hpinv).Walk ⟨.b, ⟨0, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    e_b0_c0.toWalk
  have w_d0 : (instanceGraph witnessPartner hpinv).Walk ⟨.d, ⟨0, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    e_d0_c0.toWalk
  have w_d1 : (instanceGraph witnessPartner hpinv).Walk ⟨.d, ⟨1, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    e_d1_c0.toWalk
  have w_c1 : (instanceGraph witnessPartner hpinv).Walk ⟨.c, ⟨1, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    SimpleGraph.Walk.cons e_c1_b0 w_b0
  have w_b1 : (instanceGraph witnessPartner hpinv).Walk ⟨.b, ⟨1, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    SimpleGraph.Walk.cons e_b1_c1 w_c1
  have w_a0 : (instanceGraph witnessPartner hpinv).Walk ⟨.a, ⟨0, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    SimpleGraph.Walk.cons e_a0_c1 w_c1
  have w_c2 : (instanceGraph witnessPartner hpinv).Walk ⟨.c, ⟨2, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    SimpleGraph.Walk.cons e_c2_b1 w_b1
  have w_d2 : (instanceGraph witnessPartner hpinv).Walk ⟨.d, ⟨2, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    SimpleGraph.Walk.cons e_d2_c2 w_c2
  have w_d3 : (instanceGraph witnessPartner hpinv).Walk ⟨.d, ⟨3, by decide⟩⟩ ⟨.c, ⟨0, by decide⟩⟩ :=
    SimpleGraph.Walk.cons e_d3_c2 w_c2
  have hreach : ∀ v : FragmentInstance 1,
      (instanceGraph witnessPartner hpinv).Reachable v ⟨.c, ⟨0, by decide⟩⟩ := by
    intro v
    fin_cases v
    · exact ⟨w_a0⟩
    · exact ⟨w_b0⟩
    · exact ⟨w_b1⟩
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨w_c1⟩
    · exact ⟨w_c2⟩
    · exact ⟨w_d0⟩
    · exact ⟨w_d1⟩
    · exact ⟨w_d2⟩
    · exact ⟨w_d3⟩
  have hconn : (instanceGraph witnessPartner hpinv).Connected :=
    (instanceGraph witnessPartner hpinv).connected_iff_exists_forall_reachable.mpr
      ⟨⟨.c, ⟨0, by decide⟩⟩, fun w => (hreach w).symm⟩
  have hcardE : (instanceGraph witnessPartner hpinv).edgeFinset.card = 9 := by
    have h2 := (instanceGraph witnessPartner hpinv).two_mul_card_edgeFinset
    have hfilt : (Finset.univ.filter fun p : FragmentInstance 1 × FragmentInstance 1 ↦
        (p.1 ≠ p.2 ∧ ∃ e : ValenceEnds 1,
          e.instanceOf = p.1 ∧ (witnessPartner e).instanceOf = p.2)).card = 18 := by
      decide
    have h3 : 2 * (instanceGraph witnessPartner hpinv).edgeFinset.card = 18 :=
      h2.trans hfilt
    omega
  have hcardV10 : Nat.card (FragmentInstance 1) = 10 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    decide
  have htree : (instanceGraph witnessPartner hpinv).IsTree := by
    refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcardE, hcardV10]
  exact ⟨Assembly.mk witnessPartner hpinv hpself hpox hpar htree.isAcyclic htree.connected⟩

/-- The source stipulates that PL1 can be assembled from the stated
inventory, so some fragment count admits a complete assembly. -/
theorem assembly_feasible : ∃ n : ℕ, Nonempty (Assembly n) :=
  ⟨1, assembly_one_exists⟩

/-- No even fragment count admits a complete assembly: options (a) and (c) of
question 5.1 are refuted. -/
theorem no_even_assembly : ¬ ∃ n : ℕ, Nonempty (Assembly n) ∧ Even n := by
  rintro ⟨n, h, heven⟩
  obtain ⟨k, hk⟩ := assembly_parity_odd h
  obtain ⟨l, hl⟩ := heven
  omega

/-! ## Raw and reported result specifications -/

/-- Raw derivation spec for question 5.1 (before any reporting step):

1. the free-valence inventory of the stated fragments is `n + 17`
   (`totalFreeValences_eq`; problem_image);
2. every complete assembly pairs all wavy ends into bonds, two ends per bond,
   so the total valence count is even (`assembly_even_totalFreeValences`;
   handshake, problem_text + trusted_general_law);
3. consequently every assembly-admitting `n` is odd (`assembly_parity_odd`);
4. the source stipulates that assembling PL1 is possible
   (`assembly_feasible`). -/
def RawResultSpec : Prop :=
  (∀ n : ℕ, totalFreeValences n = n + 17)
    ∧ (∀ n : ℕ, Nonempty (Assembly n) → Even (totalFreeValences n))
    ∧ (∀ n : ℕ, Nonempty (Assembly n) → Odd n)
    ∧ (∃ n : ℕ, Nonempty (Assembly n))

/-- Reported (final) classification spec for question 5.1: the correct
statement is **(b) n is an odd number** — an assembly exists and every
assembly-admitting `n` is odd (so (b) holds); no assembly-admitting `n` is
even (so (a) fails, and (c) "n can be either odd or even" fails).  The
output is an exact symbolic classification; no rounding applies
(reporting policy of the requested output: `exact_symbolic`). -/
def ReportedResultSpec : Prop :=
  (∃ n : ℕ, Nonempty (Assembly n))
    ∧ (∀ n : ℕ, Nonempty (Assembly n) → Odd n)
    ∧ ¬ (∃ n : ℕ, Nonempty (Assembly n) ∧ Even n)

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("590785ae339025c105058f5f666551e9dea92b58c88d1de7e860f3750db2236d" : String)
      = "590785ae339025c105058f5f666551e9dea92b58c88d1de7e860f3750db2236d"
      ∧ RawResultSpec := by
  refine ⟨rfl, totalFreeValences_eq, ?_, fun _ h => assembly_parity_odd h,
    assembly_feasible⟩
  rintro n ⟨asm⟩
  exact assembly_even_totalFreeValences asm

/-- Reported result certificate: binds the answer-blind reported-role payload
digest to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("c6636c7cd54c60cd7a414f6df5f9f6239932a717d3c9cfb478d223246385b275" : String)
      = "c6636c7cd54c60cd7a414f6df5f9f6239932a717d3c9cfb478d223246385b275"
      ∧ ReportedResultSpec :=
  ⟨rfl, assembly_feasible, fun _ h => assembly_parity_odd h, no_even_assembly⟩

end IChO2026Problems.Icho2026T5A1
