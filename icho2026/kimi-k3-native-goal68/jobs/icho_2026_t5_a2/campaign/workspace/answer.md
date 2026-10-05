# IChO 2026, Theory Problem T5 (Cardiolipins) — Subquestion 5.2 (6.0 pt)

**Target:** `icho_2026_t5_a2` — *"Draw the structure of one enantiomer of PL1.
Draw the structure of Y in a way that shows the stabilisation that explains the
difference between pK_a1 and pK_a2. Use the abbreviation R for the fatty acid
residues."* (page Q5-2 of `theory_problem.pdf`; the corresponding blank answer
sheet is A5-2, page 49, containing one box "PL1" and one box "Y" with no
further template fields).

---

## 1. What the problem gives (source grounding)

From page Q5-1:

* **Fragments** (drawn, with dangling squiggly bonds = "stubs"):
  **a** ·—H (1 stub), **b** HO–P(=O)·(·) [a phosphoric-acid unit with one =O,
  one OH and two stubs] (3 stubs), **c** ·O–CH2–CH(O·)–CH2–O· [glycerol with
  three substitutable oxygens and a stubbed top O... drawn as the middle O with
  a stub] (4 stubs), **d** ·CO–R [acyl residue] (1 stub), **e** ·—OH (unused for
  PL1).
* **Worked example W**: 1 × a + 1 × b + 1 × c + 1 × d + 1 × e assemble into the
  chiral phospholipid (phosphate ester on one glycerol arm, free OH… actually
  the sn-2 O comes from fragment **a** (the ·—H cap drawn on the sn-2 oxygen of
  W), acyl ester on the other arm).
* **Quantities for PL1**: n × a, 2 × b, 3 × c, 4 × d.
* **Constraints**: "Cardiolipins are a family of *acyclic* phospholipids";
  "PL1 does not contain any peroxide bonds"; "Some cardiolipins are chiral
  molecules, even if they contain four identical fatty acid residues, as in the
  case of PL1. One enantiomer of PL1 is found in prokaryotes and eukaryotes,
  and the other only in archaea. All other diastereomers of PL1 are achiral
  molecules, since they have a plane of symmetry. Do not consider the chirality
  of phosphorus atoms as stereocentres."; "PL1 is a diprotic acid with the same
  acidic groups. Its second deprotonation is less favourable (pK_a2 ≫ pK_a1)
  due to the special, stable structure of monoanion Y."

From page Q5-4 (independent statement usable to check consistency):
`PL1 + 8 H2O → 4 RCOOH + 2 H3PO4 + 3 glycerol` (balanced hydrolysis equation).

No official solution or marking scheme was consulted.

## 2. Dependency: the value of n (part 5.1, derived in line)

Every new bond consumes two stubs, so the stub total
n·1 + 2·3 + 3·4 + 4·1 = n + 22 must be even: **n is even** (answer (a) of 5.1).
Assembling all n + 9 units into *one acyclic* molecule needs exactly
n + 9 − 1 bonds, and all stubs are used: n + 22 = 2(n + 8) ⇒ **n = 6**.

## 3. Requested output 1 — structure of one enantiomer of PL1

**PL1 is a cardiolipin** (1,3-bis(sn-3'-phosphatidyl)-glycerol skeleton):

```
                                   OH                       — free 2-OH of the bridging glycerol
                                   |
 R–C(=O)–O–CH2   O–CH2–CH(O–C(=O)–R)–CH2–O–P(=O)(OH) ... etc — see below
```

Explicitly (stereochemistry given below):

* **Fragments used (counts confirmed as derived):** 2 × b (two –P(=O)(OH)O–O–
  phosphate groups), 3 × c (three glycerol backbones), 4 × d (four –CO–R acyl
  groups), 6 × a (six H caps: 2 × P–OH, 1 × central free 2-OH, 3 × sn-2 C–H).
* **Connectivity.** A *central glycerol* bridges the two phosphates through
  both of its terminal positions (–CH2–O–P linkages on arms a and b); its sn-2
  hydroxyl is **free** (–OH). Each of the two *outer glycerols* carries the
  other phosphate ester on arm a, and fatty-acid esters on arm b and on sn-2.
  Overall:

  (R–COO–CH(R')–CH2–O–O COR...) —
  formally: **R–COO–CH2–CH(O2CR)–CH2–O–P(=O)(OH)–O–CH2–CH(OH)–CH2–O–P(=O)(OH)–O–CH2–CH(O2CR)–CH2–O–CO–R**

* **Atom/bond audit (checked in Lean, `structure_pl1_certificate`):** 42
  explicit atoms, 41 bonds (|E| = |V| − 1, connected ⇒ acyclic), all valences
  met (C = 4, O = 2, H = 1, P = 5 with one P=O), no O–O bonds (no peroxides),
  exactly two identical acidic P–OH groups, exactly 8 ester bonds — matching
  the 8 H2O of the independent Q5-4 hydrolysis equation.
* **Stereocentres.** Per the problem, P chirality is excluded. The sn-2 carbon
  of each **outer** glycerol carries four different substituents and is
  stereogenic (priorities: 1 = sn-2 O–CO–R; 2 = CH2–O–P arm, since it reaches
  P (Z = 15); 3 = CH2–O–CO–R arm, reaching C only (Z = 6); 4 = H). The central
  sn-2 carbon is not stereogenic because its two arms are constitutionally
  identical (proved via the left–right automorphism `permute`).
* **One enantiomer (the biological answer): (R,R)** — both outer sn-2 centres
  R (this is the natural cardiolipin found in prokaryotes and eukaryotes; the
  (S,S) form occurs in archaea). A satisfying drawing: at each outer sn-2
  carbon draw the O–CO–R bond as a hashed wedge (behind) and the C–H bond as a
  solid wedge (in front), with the phosphate arm drawn to the right; this gives
  (R) at both centres by the CIP trace above. The mirror image (S,S) is not
  superposable (proved: its mirror differs both from itself and from the image
  under the skeleton's plane-of-symmetry automorphism), whereas (R,S) is meso
  (proved), explaining "all other diastereomers ... have a plane of symmetry".

## 4. Requested output 2 — structure of Y (monoanion) showing the stabilisation

Y = PL1 minus one proton, drawn to show the **intramolecular hydrogen-bond
network** that stabilises the monoanion:

* one phosphate is deprotonated: its negative charge is delocalised by
  resonance over the two non-bridging oxygens (the former P=O and the
  deprotonated P–O⁻);
* **the free 2-OH of the central glycerol** donates a hydrogen bond to the
  anionic phosphate oxygen, closing a six-membered pseudo-ring
  O–H···O(–)–P–O–CH2–CH (drawn explicitly as `⟨glyO central, phOH p1⟩`);
* **the remaining P–OH of the second phosphate** donates a hydrogen bond to the
  same anionic oxygen, forming a P–O–H···O(–)–P bridge across the bridging
  glycerol (`⟨phOH p2, phOH p1⟩`).

**Why pK_a2 ≫ pK_a1:** removing the second proton would destroy both hydrogen
bonds (the second deprotonation removes the very P–OH proton that donates into
the bridge — proved: no phosphate donor hydrogen survives in the dianion) and
would charge two phosphates that sit only a propane bridge apart. The specially
stabilised Y therefore resists further deprotonation. (This is the
"special, stable structure of monoanion Y" the problem refers to.)

## 5. Formalization summary (IChO2026Problems/problem_icho_2026_t5_a2.lean)

* `structure_pl1 : StructurePL1` — atoms, bonds (with bond orders) and the
  (R,R) stereochemical assignment; fatty acids abbreviated by `Atom.rCap = R`.
* `structure_y : StructureY` — the monoanion species plus the explicit list of
  two intramolecular hydrogen bonds.
* `structure_pl1_certificate`, `structure_y_certificate` — machine-checked
  conjunctions of every problem constraint (fragment counts incl. the derived
  n = 6, acyclicity, no peroxides, valences, diprotic identical acidic groups,
  two stereocentres with the CIP trace, chirality of (R,R) vs meso (R,S), the
  8-ester cross-check from Q5-4, Y charge/atom/bond bookkeeping and presence of
  the two H-bonds, destruction of the network upon second deprotonation).
* All final theorems use only the standard Lean axioms (`propext` and, from
  `decide`-scaling, none beyond it; `Quot.sound` appears only in the
  arithmetic lemmas via `omega`). No `sorry`, no custom axioms.

## 6. Source gaps / honesty notes

* The problem says "one enantiomer ... is found in prokaryotes and eukaryotes"
  but does not state which of (R,R)/(S,S) that is. Choosing **(R,R) as the
  enantiomer of eukaryotes** is the standard biochemical knowledge that the
  natural glycerophospholipid backbone derives from sn-glycerol-3-phosphate; it
  is an allowed "trusted general law"-type fact, and the problem only asks for
  *one* enantiomer, so either choice satisfies the prompt. This is recorded as
  an assumption, not a source gap.
* The identity of R (specific fatty-acid chain) is irrelevant for 5.2 (it is
  determined in 5.3/5.4) and is correctly abbreviated as instructed.
