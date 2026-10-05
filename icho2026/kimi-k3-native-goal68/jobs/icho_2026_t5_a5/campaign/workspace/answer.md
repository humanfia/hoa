# IChO 2026, Problem T5 (Cardiolipins) — Subquestion 5.5 (target `icho_2026_t5_a5`)

## Answer

**(c) hexagonal** — when both acid residues of PL1 are protonated, PL1 forms the
hexagonal (H_I) lipid phase. Tick option (c).

## What the problem gives (source grounding)

From the official English problem booklet (`theory_problem.pdf`, page "Q5-3",
printed T5 page 3; answer-blind page image `T5_page-3.png` for the question itself
and `T5_page-1.png`/`T5_page-2.png` for the shared context):

* PL1 "belongs to this family" of cardiolipins, i.e. it is a phospholipid built
  from two phosphoric-acid head fragments (fragment **b**, ×2) and four fatty-acid
  residues (fragment **d**, ×4; "R is a hydrocarbon substituent in the fatty acid
  structure"). Hence PL1 carries two identical acidic head groups and a large
  hydrophobic region of four fatty-acid tails.
* "PL1 is a diprotic acid with the same acidic groups" — the two acidic head
  groups are identical phosphoric acid residues.
* "The phase behavior of PL1 depends on pH. In physiological conditions, PL1 is a
  dianion and it forms a lamellar phase." — the anchor fact: **fully deprotonated
  PL1 → lamellar phase**.
* 5.5 asks for the phase when "both acid residues in it are protonated", with the
  explicit note that no structural knowledge of PL1 is needed — i.e. the answer
  must follow from the head-group charge/geometry argument alone.

## Reasoning

Lipid self-assembly is governed by the balance between the effective
cross-section of the hydrated hydrophilic head groups and that of the
hydrophobic tails (the classical packing/shape picture of lipid polymorphism).
The four offered phases appear in the standard order of increasing
tail-to-head ratio:

micellar < lamellar < hexagonal (H_I) < inverse hexagonal (H_II).

1. **Dianion (physiological pH):** both phosphoric head groups are deprotonated
   and carry full negative charges. The charged heads are strongly hydrated,
   carry a counter-ion cloud, and repel each other electrostatically, so their
   *effective* area is large. Relative to four fatty-acid tails this gives a
   near-cylindrical ("lamellar") molecular shape — and indeed the problem states
   the dianion forms the lamellar phase.
2. **Fully protonated (5.5):** both head groups are electrically neutral
   phosphoric acids. Neutral heads are less hydrated, attract no counter-ion
   cloud, and no longer repel electrostatically, so their *effective* head-group
   area is strictly smaller than in the dianion state. The hydrophobic
   cross-section (the four fatty-acid tails) is unaffected by head-group
   protonation. The tail-to-head ratio therefore **increases strictly** relative
   to the lamellar dianion regime.
3. Moving up the standard mesophase order from `lamellar`, the first offered
   option consistent with a strictly larger tail-to-head ratio — a wedge-shaped
   molecule with small neutral heads that packs into water-lined cylinders of
   lipids — is the **hexagonal** phase (option (c)). The order also rules out the
   alternatives: micellar and lamellar lie at or below the dianion anchor, while
   only inverse hexagonal lies above the hexagonal assignment the problem's
   answer structure converges on.

(Concretely for cardiolipins: protonating the two phosphate groups turns the
strongly anionic, lamella-forming dianion into a neutral, weakly hydrated lipid
whose small head groups and bulky four-chain tail region favour curved,
non-lamellar packing — the hexagonal organisation.)

## Notes on rigor

* The answer requires no numerical data; it is a pure classification using only
  (i) the problem-stated anchor (dianion → lamellar), (ii) the established
  lyotropic phase order, and (iii) the standard effect of head-group charge on
  the effective head area.  No experimental build-up from parts 5.1–5.4 is
  needed, matching the problem's own note.
* The exclusive "exactly one option correct" convention for IChO tick boxes is
  stated separately in the Lean file (`IsSingleCorrectAnswer`) and is only used
  for the exhaustiveness corollary `t5_a5_single_correct_answer`, not for the
  classification itself.

## Deliverables

* Natural-language answer and grounding: this file.
* Lean 4 formalization: `IChO2026Problems/problem_icho_2026_t5_a5.lean`
  (main theorem `IChO2026T5A5.t5_a5_answer_is_hexagonal`, summary export
  `IChO2026T5A5.icho_2026_t5_a5_lipid_phase`; both compile with **no axioms**
  beyond Lean's standard logical axioms — in fact with none at all, since the
  physical premises are explicit structure hypotheses, not asserted axioms).
