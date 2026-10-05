# IChO 2026 — T7 (Nitrogen Fixation), Subquestion 7.1 (T7-A1)

**Question (from TASK.json / T7 page 1):** *Tick the gases contained in **M1** and **M2**; and tick the correct relationship between 𝑥 and 𝑦.*

---

## Answers

### Gases in **M1** (effluent of reactor II, the autothermal partial-oxidation reactor)

$$\boxed{\text{N}_2,\ \text{CO},\ \text{H}_2}$$

### Gases in **M2** (effluent of the ammonia synthesis reactor, before the cooler CLR)

$$\boxed{\text{N}_2,\ \text{H}_2,\ \text{NH}_3}$$

### Correct relationship between 𝑥 and 𝑦

$$\boxed{x > y}$$

(See the "Source gaps" section below: the problem page does not print the
list of candidate relations, and the strict numerical identity sometimes
discussed, e.g. `2x = 3y`, is **not** derivable from the problem inputs; the
only order relation forced by the printed plant is `x > y`.)

---

## How each answer is obtained from the problem-only inputs

All information is taken from Fig. 1 on T7 page 1 (`T7_page-1.png`, printed
page 1, source page 63 of `theory_problem.pdf`) and the general sentence
*"assume that all reactions in Fig. 1, except NН₃ formation, are quantitative."*

### Reactions printed in Fig. 1

| Reactor | Printed reaction | Role |
|---------|------------------|------|
| I (steam reformer) | `CH₄ + H₂O → CO + 3H₂` | makes H₂ from CH₄ + steam `xCH₄ + yH₂O` |
| II (autothermal POX) | `2CH₄ + O₂ → 2CO + 4H₂` | burns surplus CH₄ with air `4N₂ + 1O₂` |
| III (water-gas shift) | `CO + H₂O → CO₂ + H₂` | converts CO after M1 |
| (ammonia loop) | `N₂ + 3H₂ ⇌ 2NH₃` | the only *non-quantitative* step |

### Why M1 = {N₂, CO, H₂}

* **N₂:** Enters reactor II in the air feed `4N₂ + 1O₂`. N₂ is inert in all
  printed reactions and no unit between the air inlet and M1 removes it.
* **CO:** Produced by both (I) and (II); the shift reactor III that could
  consume it is *downstream* of M1, so CO is still present.
* **H₂:** Produced by both (I) (3 H₂ / CH₄) and (II) (2 H₂ / CH₄); both
  reactions are stipulated quantitative, so H₂ leaves reactor II.
* *No H₂O:* steam enters reactor III only as a **separate side feed** (a
  different unit), not through M1. *No CO₂:* formed only downstream and
  scrubbed at Z. *No NH₃:* synthesis happens later. *No CH₄:* reactors I and
  II are quantitative, so any methane is consumed.

### Why M2 = {N₂, H₂, NH₃}

M2 leaves the ammonia reactor *before* the cooler CLR that draws off liquid
NH₃. Because the synthesis step is the one non-quantitative (equilibrium)
reaction, unreacted N₂ and H₂ are still present together with the NH₃ product
(which has not yet been liquefied/removed). Hence {N₂, H₂, NH₃}.

### Why x > y

Let

* `a` = mol CH₄ reformed in reactor I (= mol steam, since (I) is 1 : 1 and quantitative),
* `b` = mol CH₄ oxidized in reactor II,
* `c` = mol N₂ in the air feed (so `c/4` mol O₂).

Element balances (C, H, O) through the three quantitative reactors and the
shift give the synthesis-gas inventory:

* H₂ produced before the shift: `3a + 2b`;
* CO produced (one per CH₄ from either reactor): `a + b`;
* after the quantitative shift `CO + H₂O → CO₂ + H₂`, total H₂
  `3a + 2b + (a + b) = 4a + 3b`.

The scrubber output is exactly `N₂, H₂` and feeds `N₂ + 3H₂ ⇌ 2NH₃`, so

```
4a + 3b = 3c            (H₂ stoichiometry)
b = c/2                 (reactor II oxygen demand from 4N₂ + 1O₂)
```

⟹ `a : b : c = 3 : 4 : 8`.  The single printed feed line `xCH₄ + yH₂O`
into reactor I reads `x = a + b` (total methane) and `y = a` (steam for the
reformed part), giving `x : y = 7 : 3`, hence **x > y**: methane must be fed
in excess of the reforming steam so that reactor II has methane to burn —
exactly the surplus shown by the printed `CH₄, CO, H₂` stream between the two
reactors.

---

## Source grounding

* **Problem image:** `icho_2026_source/image/T7_page-1.png` (sha256
  `ee7fe1ad…` per `isolation_manifest.json`), printed page 1, PDF source page
  63 of `theory_problem.pdf`.
* **Text:** shared official problem context in `TASK.json` ("Fig. 1. M1 –
  Mixture 1, M2 – Mixture 2, Z – CO₂ scrubber, CLR – cooler" and the
  quantitative-reaction stipulation).
* **General law used:** conservation of chemical elements (a trusted general
  law under the task's candidate-domain policy).

No external or official-solution material was consulted.

## Source gaps / underdetermined points

* The problem page itself does **not** print the list of candidate x–y
  relations to tick and there is **no separate T7 answer-sheet page** in the
  provided `theory_problem.pdf` (it ends at Q9; no Q7 answer boxes are
  included). The strict identity `2x = 3y` (sometimes guessed from the 7.2
  numbers, which use the *separately printed* 4N₂ + 1O₂ composite feed
  ratio) is **not derivable** from the T7-A1 problem inputs alone. What the
  printed figure *does* force is the order relation `x > y` (methane in
  excess over the 1 : 1 reforming steam), which is what I report.
* The compositions of M1 and M2 are fully determined by the figure and are
  not a source gap.
