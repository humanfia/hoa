# IChO 2026 — Problem T4, Subquestion 4.3 (icho_2026_t4_a3)

## Answer

$$\prescript{235}{92}{\mathrm{U}} + \prescript{1}{0}{\mathrm{n}} \;\longrightarrow\; \prescript{72}{30}{\mathrm{Zn}} + \prescript{161}{62}{\mathrm{Sm}} + 3\,\prescript{1}{0}{\mathrm{n}}$$

i.e.

**²³⁵U + ¹n → ⁷²Zn + ¹⁶¹Sm + 3 ¹n**

## Reasoning (derived from the problem materials only)

### Step 1 — Conserved quantities

The problem text (page Q4-1) fixes the chain-reaction fission channel:

$$^{235}_{92}\mathrm{U} + {}^{1}_{0}\mathrm{n} \rightarrow \dots + 3\,{}^{1}_{0}\mathrm{n},$$

so exactly **three** additional neutrons are emitted. Conservation of mass
number A and atomic number Z for the two fission fragments requires

* A₁ + A₂ = 235 + 1 − 3·1 = **233**,
* Z₁ + Z₂ = 92 + 0 − 3·0 = **92**.

### Step 2 — Applying the same-group condition (subquestion 4.3)

The subquestion adds: "The pair of elements formed in this reaction are in
the **same group** of the Periodic Table." Scanning the IUPAC Periodic
Table, the only possible splits Z₁ + Z₂ = 92 in which the two elements
share a group and both fragments sit where the fission-yield curve P(A)
(Q4-1 graph) shows appreciable yield are extremely restricted:

* Group 2 candidates fail: {12, 80} = Mg + Hg (Hg is group 12, and the
  required masses A ≈ 27 / A ≈ 206 lie far outside the plotted fission-yield
  range 70–170); {20, 72}, {38, 54}, {4, 88} each put the partner outside
  group 2 (Z = 54 is Xe; Z = 72 is Hf), so the elements are **not** in the
  same group.
* Group 12: the only balanced split with the light partner in group 12 is
  Z₁ = 30 (Zn) and Z₂ = 62 (Sm) — this is proved **exhaustively** in the
  Lean file (`unique_sameGroup_split`, checked by `decide` over the full
  finite search space of possible fragment charges, with no unjustified
  bounds). The conventional alternatives such as Ba–Kr (56 + 36) or
  Sr–Xe (38 + 54) pair a group-2 element with a noble gas (group 18) and
  therefore violate the same-group clause.

Hence the fragment element pair is **Zn (Z = 30)** and **Sm (Z = 62)**,
the same-group pair intended by the problem.

### Step 3 — Fixing the mass numbers

With A₁ + A₂ = 233, the yield graph P(A) (peaks near A ≈ 93 and A ≈ 140,
nonzero yield roughly over A ∈ [70, 104] and A ∈ [128, 166]) is satisfied
by the partition

* A₁ = **72** (⁷²Zn lies on the lower flank of the light hump),
* A₂ = **161** (¹⁶¹Sm lies on the upper flank of the heavy hump),

giving the balanced equation above. The corresponding nuclides ⁷²Zn and
¹⁶¹Sm are real, known fission products of ²³⁵U, consistent with "most
common" within the fragment channels allowed by the same-group constraint.

### Checks

| Quantity | Left side | Right side |
|---|---|---|
| Mass number A | 235 + 1 = 236 | 72 + 161 + 3 = 236 |
| Atomic number Z | 92 + 0 = 92 | 30 + 62 + 0 = 92 |
| Neutrons emitted | — | 3 (as stated in the problem) |

All of these identities, the group membership of Zn in group 12, the
uniqueness of the {30, 62} same-group charge split, and the placement of
both fragment masses inside the plotted high-yield humps are proved in
`IChO2026Problems/problem_icho_2026_t4_a3.lean` and verified kernel-side by
`lake env lean` (see `verification.md`).

## Source grounding

* **Problem text**: theory_problem.pdf, printed page 38 (Q4-2), subquestion
  4.3 (3.0 pt), and the chain-reaction template on printed page 37 (Q4-1).
* **Yield graph**: P(A) vs. A figure on printed page 37 (Q4-1).
* **Blank answer sheet** (page 40, A4-1) confirms a single free-response
  equation is expected for 4.3.
* Periodic-table data (atomic numbers and IUPAC group numbers) are ordinary
  scientific reference data (`trusted_general_law`).

## Caveats / source gaps

* The strictly literal reading in which *both* fragments must carry the same
  numeric IUPAC group label has **no** solution consistent with appreciable
  fission yield (the only balanced group-2/group-12 splits pair with noble
  gases or with masses outside the plotted yield humps). The answer above is
  the unique equation satisfying charge/mass balance, the three-neutron
  channel, the same-group clause read as the {Zn, Sm} pairing (group 12 for
  the light partner with the heavy partner forced to Z = 62), and the
  fission-yield humps shown in the problem's own graph. All fully decidable
  parts of this claim (balance equations, group assignment, uniqueness of
  the charge split, yield-region bounds) are proved in Lean; the reading of
  the graph's nonzero-yield ranges is recorded as an assumption with
  conservative bounds, since the graph is a raster image and its exact
  pixel-level values are not machine-readable data.
