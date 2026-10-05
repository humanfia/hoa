# IChO 2026, T9-A1 (Question 9.1): molar mass of β-cyclodextrin

## Answer (requested output)

- **Raw value:** M(β-CD) = **1135.008 g mol⁻¹**
- **Displayed (3 significant figures, per the reporting policy in TASK.json):** **1135 g mol⁻¹** (≈ 1.14 × 10³ g mol⁻¹)

## How it is derived

1. **Number of glucose units.** The shared problem context on Q9-1 states that α-, β-, γ-cyclodextrins contain 6, 7, and 8 α-D-glucopyranoside units respectively, and the figure on the same page is labelled "n = 7 β-CD". So β-CD has 7 glucose units.

2. **Water eliminated on ring closure.** The context states the glucose subunits are "joined by α-1,4-glycosidic bonds". Each glycosidic bond is an acetal linkage formed by condensation of the anomeric hydroxy of one unit with the 4-hydroxy of the next, which eliminates one H₂O. A cyclic chain of 7 units has 7 such bonds, so 1 mol of β-CD corresponds to 7 mol of glucose minus 7 mol of water: the β-CD residue formula is (C₆H₁₂O₆)₇ − 7 H₂O = C₄₂H₇₀O₃₅.

3. **Molar mass of water.** From the IChO 2026 data sheet printed on the inside front cover of `theory_problem.pdf`: A_r(H) = 1.008, A_r(O) = 16.00. Therefore M(H₂O) = 2 × 1.008 + 16.00 = 18.016 g mol⁻¹.

4. **Arithmetic (no intermediate rounding):**
   M(β-CD) = 7 × 180.16 − 7 × 18.016 = 1261.12 − 126.112 = **1135.008 g mol⁻¹**.

5. **Reporting.** The reporting policy requires the final value at three significant figures, quantum 1 g mol⁻¹ for a value in [1000, 10000), ties half-away-from-zero. The raw value 1135.008 rounds to **1135 g mol⁻¹**.

## Source grounding

- Q9-1 problem statement and figure (`T9_page-1.png`, PDF page 84) supply: β-CD = 7 units, the glycosidic-bond structure of the ring, and the printed datum M𝑤(glucose) = 180.16 g mol⁻¹.
- The answer sheet (PDF page 89, A9-1) confirms the single requested output is `M𝑤 : β-CD`.
- The only external data used are H and O atomic masses from the IChO 2026 data sheet, which is part of the problem materials. No official solution, marking scheme, or prior answer was consulted.
