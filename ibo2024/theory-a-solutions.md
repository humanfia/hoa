# IBO 2024 Theory Part A — Worked Solutions

Source: the International Biology Olympiad (IBO) official English 2024 Theoretical Exam, Parts A and B, including the embedded official solutions.

The source material and this derived solution collection are shared under CC BY-NC-SA 4.0: attribution is required, use is noncommercial, and adaptations must be shared under the same license.

These are natural-language worked solutions. The official T/F verdict is retained even where a solution includes a clearly labeled source discrepancy note.

## Contents

1. [Task 1 — Tulip morphology and maximum-parsimony phylogeny](#part-a-task-1)
2. [Task 2 — Owl phylogeny, classification, and biogeography](#part-a-task-2)
3. [Task 3 — Maximum-parsimony gene trees and phylogenetic congruence](#part-a-task-3)
4. [Task 4 — Tumor metabolism, oxygen consumption, and extracellular acidity](#part-a-task-4)
5. [Task 5 — Binding-site mutagenesis and cardiac glycoside recognition](#part-a-task-5)
6. [Task 6 — Ramachandran angles and peptide-backbone conformations](#part-a-task-6)
7. [Task 7 — Flux and carbon rearrangement in the pentose phosphate pathway](#part-a-task-7)
8. [Task 8 — Epigenetic control and CTCF–cohesin looping at the IGF2–H19 locus](#part-a-task-8)
9. [Task 9 — Cryo-EM interpretation and ATAD1 membrane-protein extraction](#part-a-task-9)
10. [Task 10 — Magnetotactic bacteria navigating an oxic–anoxic transition zone](#part-a-task-10)
11. [Task 11 — Growth-coupled directed evolution of an NADH-dependent enzyme in engineered E. coli](#part-a-task-11)
12. [Task 12 — DMSO oxidation products, membrane penetration, and routes of elimination](#part-a-task-12)
13. [Task 13 — Nutrient enrichment and legume performance in nitrogen-limited steppe grassland](#part-a-task-13)
14. [Task 14 — Latitudinal diversity gradients: carrying capacity, diversification rate, and diversification time](#part-a-task-14)
15. [Task 15 — Walker circulation, ENSO, and ecological responses](#part-a-task-15)
16. [Task 16 — Fractal geometry, resource scaling, and an organism's spatial perspective](#part-a-task-16)
17. [Task 17 — Renewable freshwater, water scarcity, and virtual water](#part-a-task-17)
18. [Task 18 — Wildlife responses to traffic and the road-barrier effect](#part-a-task-18)
19. [Task 19 — Cumulative cultural evolution and route learning in rock pigeons](#part-a-task-19)
20. [Task 20 — Allele frequencies in alternating haploid and diploid generations](#part-a-task-20)
21. [Task 21 — Out-of-Africa expansion, heterozygosity, and effective population size](#part-a-task-21)
22. [Task 22 — Agriculture, ethanol metabolism, and selection on ADH1B](#part-a-task-22)
23. [Task 23 — Drosophila allele-frequency dynamics and heterozygote advantage](#part-a-task-23)
24. [Task 24 — Codon usage bias and translational efficiency](#part-a-task-24)
25. [Task 25 — Mitochondrial RNase P mutations, targeting, and inheritance](#part-a-task-25)
26. [Task 26 — Carbon-cycle perturbations, extinction thresholds, and the biological pump](#part-a-task-26)
27. [Task 27 — Epistasis and accessible evolutionary trajectories in beta-lactamase](#part-a-task-27)
28. [Task 28 — Distribution of fitness effects, effective neutrality, and mutation accumulation](#part-a-task-28)
29. [Task 29 — Endogenous retroviruses, solo-LTRs, and evolutionary change](#part-a-task-29)
30. [Task 30 — Long-distance and intracellular transport of gibberellin in roots](#part-a-task-30)
31. [Task 31 — Photorespiration, glycine decarboxylase, and C4 photosynthesis](#part-a-task-31)
32. [Task 32 — Electrical and osmotic coordination of grass stomata](#part-a-task-32)
33. [Task 33 — Xanthophyll-cycle photoprotection and light acclimation](#part-a-task-33)
34. [Task 34 — Diurnal carbohydrate allocation in maize leaves and developing kernels](#part-a-task-34)
35. [Task 35 — Hydraulic strategies and tree height in California redwoods](#part-a-task-35)
36. [Task 36 — Dissolved inorganic-carbon uptake by aquatic plants](#part-a-task-36)
37. [Task 37 — Water uptake, aerenchyma formation, and osmosis in a eudicot root](#part-a-task-37)
38. [Task 38 — ECG leads, cardiac action potentials, and atrioventricular block](#part-a-task-38)
39. [Task 39 — Oxygen affinity and allosteric regulation of snow-leopard hemoglobin](#part-a-task-39)
40. [Task 40 — Feeding time, circadian alignment, activity, and body temperature in mice](#part-a-task-40)
41. [Task 41 — Circadian and homeostatic control of active sleep bouts in Octopus laqueus](#part-a-task-41)
42. [Task 42 — Mechanical detection and active electrolocation in electric-eel hunting](#part-a-task-42)
43. [Task 43 — Saiga nasal anatomy, airflow, and movement on snow](#part-a-task-43)
44. [Task 44 — TLR7/8 activation and swim-up separation of X- and Y-bearing sperm](#part-a-task-44)
45. [Task 45 — Endothelial cells, FGF-2, and perfusion of engineered cardiac tissue](#part-a-task-45)
46. [Task 46 — Optogenetic control of hippocampal neurons with channelrhodopsin-2](#part-a-task-46)
47. [Task 47 — Cost of transport and the energetics of animal locomotion](#part-a-task-47)
48. [Task 48 — Helium-dilution measurement of residual lung volume](#part-a-task-48)
49. [Task 49 — Esophageal Doppler monitoring, blood-flow velocity, and cardiac output](#part-a-task-49)
50. [Task 50 — Renal countercurrent multiplication and vasa recta exchange](#part-a-task-50)

<a id="part-a-task-1"></a>
## Task 1 — Tulip morphology and maximum-parsimony phylogeny

**Official answer: A — False; B — False; C — True; D — True**

### Reasoning

**A — False.** Taking the states of *T. borszczowii* as ancestral, the derived states are nested. Yellow stamen filaments unite the other four species; loss of the dense bulb hairs then unites *T. lemmersii*, *T. salsola*, and *T. bifloriformis*; and stamen hairs together with two leaves unite *T. salsola* and *T. bifloriformis*. Thus a most-parsimonious rooted topology is `(T. borszczowii, (T. altaica, (T. lemmersii, (T. salsola, T. bifloriformis))))`. The three species named in the statement contain their most recent common ancestor and all of its descendants, so they form a monophyletic, not polyphyletic, group.

**B — False.** Each of the five variable characters can be placed on that tree as a single change: black to yellow filaments at the base of the four-species group, loss of dense bulb hairs at the base of the three-species group, gain of stamen hairs and reduction from at least three leaves to two on the branch shared by *T. salsola* and *T. bifloriformis*, and the change from one flower to two or more on the terminal branch of *T. bifloriformis*. This gives five steps, the minimum possible for five characters that each have both states represented. No state has to evolve twice or return to its ancestral state, so the parsimonious reconstruction requires no reversal.

**C — True.** *Tulipa* belongs to the monocotyledons. Monocot leaves characteristically have their main veins running alongside one another; depending on leaf shape, these veins may remain nearly straight (parallel) or curve together in arcs (arcuate). Tulip leaves therefore satisfy the stated parallel-or-arcuate venation condition.

**D — True.** Two or more flowers occur only in *T. bifloriformis*. Its sister species, *T. salsola*, already shares the other derived states that diagnose their common branch but still has one flower. The shift to two or more flowers is therefore placed after those species diverged, on the terminal *T. bifloriformis* branch, whereas all other derived characters occur on deeper branches. It is consequently the most recently evolved character in this reconstruction.

<a id="part-a-task-2"></a>
## Task 2 — Owl phylogeny, classification, and biogeography

**Official answer: A — True; B — False; C — False; D — True**

### Reasoning

**A — True.** Matching the partial geographic ranges and the stated divergence times to the complete tree gives the genus assignments 1 = *Asio*, 2 = *Athene*, 3 = *Glaucidium*, 4 = *Otus*, and 5 = *Surnia ulula*. In particular, the 5-million-year common ancestor identifies 3 and 5 as the *Glaucidium*–*Surnia* pair, after which their ranges distinguish the two. The other age and range constraints determine the remaining genera. The numbers on the tree show that these genera contain 9, 6, 22, 51, and 1 species, respectively. Thus bird 5, *Surnia ulula*, is the sole species in its genus, so one of the five birds is indeed the only representative of its genus.

**B — False.** Species 3 and 5 are the closest pair because their most recent common ancestor lived only 5 million years ago. The next branching event among the five joins species 2 to the 3–5 clade at about 20 million years ago; consequently, species 2 has the next-closest relationship to both 3 and 5. Species 1 and 4 meet at an older node, so they are not the second most closely related pair.

**C — False.** The inferred assignments place the birds in five different genera: *Asio*, *Athene*, *Glaucidium*, *Otus*, and *Surnia*. Therefore, no two of the five given species belong to the same genus.

**D — True.** Most of the lineages in the *Strix*-containing clade from *Pulsatrix* through *Megascops* are American, whereas *Strix* also occurs in Eurasia and Africa. If their common ancestor lived in America, the observed ranges can be explained by a single dispersal of the *Strix* lineage from America into the Old World. An African/Eurasian ancestor would instead require two separate dispersals into America and losses of the ancestral Old World range in two descendant lineages. Because the America-to-Old-World reconstruction requires fewer events, it is the more parsimonious direction of dispersal.

<a id="part-a-task-3"></a>
## Task 3 — Maximum-parsimony gene trees and phylogenetic congruence

**Official answer: A — True; B — False; C — False; D — False**

### Reasoning

**A. True.** In alignment I, sites 2 and 4 group B with C: their states are C/C versus G/G at site 2 and T/T versus C/C at site 4. This is the split shown by tree X, in which B and C are sister strains. Counting the minimum substitutions on tree X gives two changes at site 1, one each at sites 2 and 4, none at the constant site 3, and one on the C branch at site 5, for a total of (2+1+0+1+1=5) changes. The other two possible ingroup arrangements require six or seven changes, so alignment I reconstructs tree X by maximum parsimony.

**B. False.** Only three of the five sites in alignment I help choose among topologies. Site 3 is constant (A in every strain), so it requires no change on any tree. Site 5 differs only in C (A in C and T in A, B, and D); this singleton difference always costs one change on the C branch, irrespective of topology. Thus sites 1, 2, and 4 are topology-informative, not four sites.

**C. False.** Tree X conflicts with the reference ribosomal-protein tree Z, whereas tree Y has the same topology as Z. The gene for RNA polymerase subunit β is a conserved bacterial housekeeping gene and is therefore expected to retain the organismal, vertically inherited relationship represented by the reference tree. A transposase belongs to a mobile genetic element and is more liable to horizontal transfer, so its gene tree may disagree with the strain tree. Therefore Y is the more plausible RNA-polymerase-β tree, while X is the transposase tree.

**D. False.** Fixing D as the outgroup still leaves three possible rooted binary relationships among A, B, and C, corresponding to each possible sister pair: A–B, A–C, or B–C. Equivalently, the topologies are (D,(C,(A,B))), (D,(B,(A,C))), and (D,(A,(B,C))). Hence there are three possibilities, not two.

<a id="part-a-task-4"></a>
## Task 4 — Tumor metabolism, oxygen consumption, and extracellular acidity

**Official answer: A — False; B — True; C — False; D — False**

### Reasoning

**A — False.** In Figure 1A, the cancer cells have a significantly higher oxygen consumption rate than the corresponding normal cells for all three patients. Greater oxygen consumption is evidence of increased, rather than decreased, oxygen-dependent metabolic activity and is consistent with the high energy and biosynthetic demands of proliferating tumor cells.

**B — True.** Cancer cells commonly shift a larger fraction of glucose metabolism toward glycolysis and fermentation relative to oxidative phosphorylation, even when oxygen is available. The resulting lactate and associated proton export acidify the extracellular environment, so this altered balance can account for the lower pH of the tumor tissues in Figure 1B.

**C — False.** Elevated oxygen consumption removes oxygen from the local environment; it does not make that environment hyperoxic. When high tumor-cell demand is combined with limited oxygen delivery through an inadequate or disorganized blood supply, the tumor microenvironment tends to become hypoxic.

**D — False.** Heterogeneity in single-cell oxygen consumption is reflected by the spread of the measurements. The cancer-cell data for patient 2 have the largest spread and error bar in Figure 1A, whereas those for patient 3 are less variable. Thus, patient 2, not patient 3, has the most heterogeneous cancer-cell oxygen consumption among the three patients.

<a id="part-a-task-5"></a>
## Task 5 — Binding-site mutagenesis and cardiac glycoside recognition

**Official answer: A — True; B — False; C — True; D — True**

### Reasoning

**A — True.** At Tyr-33, replacing tyrosine with the aromatic residues tryptophan or phenylalanine gives the strongest ELISA signals among the substitutions, with Tyr-33-Trp particularly prominent. Because absorbance was normalized to the wild-type value of 1, these larger ratios indicate stronger glycoside binding under the assay conditions. Retaining a bulky aromatic side chain at this position therefore appears favorable for binding.

**B — False.** Asn-35 is a counterexample to the claim about every position. The wild-type Asn column has a normalized value of 1, whereas every tested replacement at Asn-35 gives a lower signal for each of the four glycosides. Thus, although beneficial substitutions occur at Tyr-33 and Trp-100, no substitution shown improves binding at Asn-35.

**C — True.** Tyr-33-Trp and Trp-100-Arg are among the strongest single substitutions in their respective heatmaps, producing high signals for the cardiac glycosides. Combining them is therefore a reasonable candidate for an antibody used to detect this class of compounds. The double mutant itself was not tested in the figure, however, so this is a prediction: interactions between the two mutations could make their combined effect non-additive.

**D — True.** Digoxigenin (P) and digoxin (R) have the same listed substituents except at R1: digoxin carries a sugar there, while digoxigenin does not. Their different binding patterns across the antibody mutants can therefore be attributed to that sugar moiety, showing that the sugars contribute to antibody recognition and affinity.

<a id="part-a-task-6"></a>
## Task 6 — Ramachandran angles and peptide-backbone conformations

**Official answer: A — False; B — False; C — True; D — True**

### Reasoning

**A — False.** Using the reference orientations in Figure 1C, structure (a) requires rotations of approximately \(\phi=-100^\circ\) about the N–Cα bond and \(\psi=+120^\circ\) about the Cα–C bond. A Ramachandran plot places \(\phi\) on the horizontal axis and \(\psi\) on the vertical axis, so this pair falls in the upper-left cluster, labelled Region 1. It does not fall in Region 2, which is the lower-left cluster.

**B — False.** The corresponding rotations for structure (b) are about \(\phi=-60^\circ\) and \(\psi=-60^\circ\). Both coordinates are negative, placing the structure in the lower-left allowed cluster, Region 2. Region 3 instead lies at positive \(\phi\) and positive \(\psi\), so structure (b) is not located there.

**C — True.** Structure (c) corresponds approximately to \(\phi=+90^\circ\) and \(\psi=-90^\circ\). This point lies in the lower-right quadrant of the plot, outside the densely populated allowed regions; the plotted residues show essentially no occupancy there. Thus this backbone conformation is uncommon among the non-glycine residues of rabbit pyruvate kinase.

**D — True.** The point \((\phi,\psi)=(0^\circ,0^\circ)\) is at the origin of the plot, where no non-glycine residue from the enzyme is shown. At this conformation, backbone atoms and the side chain approach one another too closely, producing severe steric clashes. Glycine is excluded from the plotted data because its side chain is only hydrogen and therefore gives it unusually broad conformational freedom, but for the residues covered by the statement the origin is unoccupied.

<a id="part-a-task-7"></a>
## Task 7 — Flux and carbon rearrangement in the pentose phosphate pathway

**Official answer: A — True; B — False; C — True; D — False**

### Reasoning

**A — True.** Rapidly dividing cells require ribose 5-phosphate (R5P) to synthesize nucleotides. In the diagram, this demand removes some R5P from the pathway at the branch leading to nucleotides, before R5P can enter the first transketolase (TKT) reaction. Consequently, the upstream reactions that supply the pentose-phosphate pool carry a greater flux than the later non-oxidative reactions: only the pentose not diverted to nucleotide synthesis continues past the first TKT step.

**B — False.** Carbon counting shows that TKT transfers a two-carbon unit. In the first TKT reaction, two five-carbon substrates are rearranged into a seven-carbon product and a three-carbon product. One substrate therefore loses two carbons, changing from C5 to C3, while the other gains those two carbons, changing from C5 to C7. This is a two-carbon, not a one-carbon, transfer.

**C — True.** G6PDH catalyzes the first oxidative PPP reaction and reduces NADP⁺ to NADPH. Red blood cells lack mitochondria and depend strongly on the PPP for NADPH, which is needed to maintain antioxidant defenses and reduce reactive oxygen species such as hydrogen peroxide. G6PDH deficiency therefore lowers NADPH production, while antioxidant reactions continue to consume the available NADPH, leaving a smaller usable pool.

**D — False.** The two F6P molecules shown are not produced from one G6P. Three G6P molecules provide three C5 pentose phosphates after the oxidative phase, because each C6 substrate loses one carbon as CO₂. The non-oxidative phase conserves the remaining 15 carbons and rearranges them as

\[
3\,\mathrm{C5P} \longrightarrow 2\,\mathrm{F6P} + 1\,\mathrm{GA3P},
\]

since \(3\times5=2\times6+3=15\). Thus three G6P yield two F6P (plus one GA3P), corresponding to \(2/3\) of an F6P per G6P rather than two F6P per G6P.

<a id="part-a-task-8"></a>
## Task 8 — Epigenetic control and CTCF–cohesin looping at the IGF2–H19 locus

**Official answer: A — False; B — False; C — True; D — True**

### Reasoning

**A — False.** Each DNA loop needs two anchoring contacts. If each of the four CTCF-binding sites could be used only once, they could form at most \(4/2=2\) separate loops. The folded chromosomes in Figures 1A and 1B instead form a multi-loop hub: the loop bases meet at the same CTCF–cohesin contact region, and three looped DNA domains are visible in the maternal configuration. Adjacent loops must therefore share at least one CTCF-binding site. A site is not restricted to participating in only one loop.

**B — False.** The paternal and maternal structures differ because methylation of the ICR prevents CTCF from binding there. The methylated paternal chromosome in Figure 1A consequently has one fewer loop-base contact than the unmethylated maternal chromosome in Figure 1B. Mapping that methylation-sensitive contact back onto the linear locus in Figure 1D identifies CTCF-binding site 3, which lies at the H19 region, as the ICR. The ICR therefore does not overlap site 2.

**C — True.** An enhancer stimulates IGF2 most strongly when chromatin folding brings the two elements into physical proximity. IGF2 is active in the paternal conformation in Figure 1A but has only basal expression in the maternal conformation in Figure 1B, so comparison of the two folds locates the relevant enhancer on the distal side of H19, before CTCF-binding site 4. Figure 1D places H19 at CTCF-binding site 3; therefore the interval between H19 and site 4 is also the interval between sites 3 and 4.

**D — True.** Figure 1D places the methylation-sensitive ICR at the H19 promoter region. When this region is methylated on the paternal chromosome, transcription factors and the transcriptional machinery cannot gain normal access to the H19 promoter, so H19 is inactive. On the maternal chromosome the region is unmethylated, and the question explicitly states that CTCF binding itself does not disrupt promoter function. This is a direct promoter-accessibility effect of ICR methylation and does not require any change in enhancer action.

<a id="part-a-task-9"></a>
## Task 9 — Cryo-EM interpretation and ATAD1 membrane-protein extraction

**Official answer: A — True; B — False; C — False; D — False**

### Reasoning

**A — True (official key).** A single-particle cryo-EM map is an average over many particles. Features that repeatedly occupy nearly the same position reinforce one another and become well resolved, whereas a mobile region or a region occurring in several conformations is blurred by averaging. In Figure 1A, M1–M5 have clear density while M6 is the one poorly resolved subunit position. The official interpretation is therefore that one subunit at a time occupies this flexible, conformationally heterogeneous M6 position.

There is a wording caveat: an averaged density map demonstrates that the *M6 position* is uniquely heterogeneous in this reconstruction, but it cannot by itself prove the stronger instantaneous claim that “at any moment” exactly one subunit is flexible. Other subunits could undergo smaller motions that remain resolved, for example. Thus the official **True** answer is preserved, but the temporal wording is somewhat stronger than the evidence shown.

**B — False.** The C-terminal helices lie at contacts between ATAD1 subunits. Such an interfacial helix can place hydrophobic side chains toward a buried protein–protein contact while presenting polar or charged side chains toward water or other polar parts of the protein. It is therefore amphipathic rather than being composed entirely of hydrophobic amino acids.

**C — False.** Replacing glutamate with glutamine removes a negative charge at residue 193, but Figure 1C shows that the substrate in the central pore is contacted by the aromatic pore residues Trp-166 and Tyr-167. Residue 193 lies outside that substrate-contacting pore. E193Q may consequently alter ATAD1 activity indirectly, but the displayed structure does not support a direct physical interaction between residue 193 and the substrate.

**D — False.** The structural pore and the fluorescence assay support ATAD1 acting on a mislocalized membrane protein such as Gos28: the aromatic pore residues can grip its polypeptide chain while ATAD1 pulls it out of the mitochondrial membrane. This is membrane-protein extraction, not translocation of a protein into the mitochondrial matrix.

<a id="part-a-task-10"></a>
## Task 10 — Magnetotactic bacteria navigating an oxic–anoxic transition zone

**Official answer: A — False; B — False; C — True; D — False.**

### Reasoning

**A — False.** Magnetosomes passively align a bacterium with Earth's magnetic field, reducing a three-dimensional search for the proper oxygen concentration to movement mainly along the field axis. In Figure 1B that axis is inclined, however, whereas the geometrically shortest route from a given depth to the horizontal OATZ would be vertical. Magnetosomes therefore make navigation more directed and energetically economical, but they do not guarantee the shortest path.

**B — False.** Figure 1B shows that a northern-hemisphere polar bacterium above the OATZ uses counterclockwise flagellar rotation to move toward it. In the Southern Hemisphere, both the relevant direction of Earth's field and the magnetosome polarity are reversed. These two reversals compensate, so the rotation response associated with being above the OATZ remains counterclockwise rather than becoming clockwise.

**C — True.** Oxygen can enter the tube through both openings, producing an oxygen gradient on each side of the central anoxic starting region and hence two suitable transition zones. Axial magnetotactic bacteria can adopt either orientation along the magnetic-field axis, so one group can travel left and another right. They will consequently accumulate at the two transition zones as two distinct bands.

**D — False.** The bacteria begin in the red anoxic region, which corresponds to having less oxygen than at the OATZ—that is, the situation represented below the OATZ in Figure 1B. The indicated response to that condition is clockwise flagellar rotation. As in B, the reversed magnetic polarity of southern-hemisphere polar bacteria preserves the appropriate rotation response, so they do not begin with counterclockwise rotation.

<a id="part-a-task-11"></a>
## Task 11 — Growth-coupled directed evolution of an NADH-dependent enzyme in engineered E. coli

**Official answer: A — False; B — False; C — True; D — True.**

### Reasoning

**A — False.** Directed evolution requires heritable variation on which selection can act. In the described experiment, randomizing Enzyme D before selection creates a library whose variants already have different activities. Selective pressure then changes the frequencies of those variants; it does not direct Enzyme D to acquire the desired mutation. Although occasional spontaneous mutations could arise during growth, waiting for them would not replace the deliberately diverse library used in this scheme.

**B — False.** Enzyme D is most strongly coupled to growth under **anaerobic**, not aerobic, conditions. Carbon metabolism reduces NAD⁺ to NADH, so continued metabolism requires NADH to be oxidized back to NAD⁺. The native fermentative NAD⁺-regenerating routes shown with red crosses have been deleted from strain AL. In the absence of oxygen, the respiratory electron-transport chain also cannot provide an alternative route for NADH oxidation, leaving the reaction catalysed by Enzyme D as the engineered route for restoring NAD⁺. Under aerobic conditions, respiration can regenerate NAD⁺ and therefore weakens the selective dependence on Enzyme D.

**C — True.** The exogenous substrate and non-toxic product are otherwise disconnected from the bacterium's native metabolic network; the useful connection is the shared NADH/NAD⁺ pool. As Enzyme D converts substrate to product, it consumes NADH and regenerates NAD⁺. A high-activity variant therefore supports a larger NAD⁺-regeneration flux, allowing carbon metabolism and growth to continue faster than in cells carrying a low-activity variant. Growth and enrichment of the cells consequently provide a readout that distinguishes variants by their effective cellular activity and permits selection of the highest-activity variants.

**D — True.** The large intestine has very little oxygen, and the figure specifies that Enzyme D's exogenous substrate is present there. Strain AL therefore cannot rely effectively on aerobic respiration, while its deleted fermentative pathways cannot adequately reoxidize NADH. A more active Enzyme D regenerates NAD⁺ more rapidly, maintains redox balance, and lets carbon catabolism continue. Cells carrying such a variant consequently have a survival and growth advantage in the large-intestinal environment.

<a id="part-a-task-12"></a>
## Task 12 — DMSO oxidation products, membrane penetration, and routes of elimination

**Official answer: A True; B True; C False; D False.**

### Reasoning

**A — True.** DMSO is extremely water-soluble (≥150 g L⁻¹ in the table), whereas DMSO₂ is a stable, solid oxidation product with a slightly lower listed solubility of 150 g L⁻¹. DMSO₄ is less soluble (28 g L⁻¹), but the question states that it rapidly hydrolyses in water, so it would not persist in aqueous blood long enough to be the likely crystalline material. Of these three compounds, accumulated DMSO₂ is therefore the most plausible source of the white crystals.

**B — True.** DMSO is a penetration enhancer: it can enter biological barriers such as skin, disturb the ordered packing and interactions of membrane lipids and proteins, and thereby increase the passage of other dissolved compounds. There is a wording issue in the official rationale, which treats DMSO as simply strongly hydrophobic. Its polar sulfoxide group and the table's very high water solubility show that this description is misleading; DMSO's amphiphilic solvent properties better explain its ability to interact with both aqueous solutes and membrane components. This issue does not alter the truth value of the statement.

**C — False.** Taking the standard enthalpy of formation of O₂ as zero, the tabulated values make the two oxidation steps exothermic. For DMSO + ½O₂ → DMSO₂, ΔH ≈ −373 − (−150) = −223 kJ mol⁻¹; for DMSO₂ + O₂ → DMSO₄, ΔH ≈ −687 − (−373) = −314 kJ mol⁻¹. These calculations describe reaction enthalpy, not reaction speed. Whether oxidation occurs rapidly at room temperature depends on the activation barrier and the presence of a suitable reaction pathway or catalyst; thermodynamic favourability would in any case be assessed from Gibbs free energy, not enthalpy alone. The rapid hydrolysis of DMSO₄ after it forms is a separate reaction and does not show that its formation by oxidation is rapid.

**D — False.** Obstruction of the ureters could restrict renal elimination because urine must pass from the kidneys to the bladder through them, but urinary excretion is not the only possible route. The garlic-like material was detected in air coming from the patient's mouth, evidence that volatile sulfur-containing material was also leaving through the lungs. Thus ureteric metastases may reduce one route of elimination without blocking all elimination of DMSO and its derivatives.

<a id="part-a-task-13"></a>
## Task 13 — Nutrient enrichment and legume performance in nitrogen-limited steppe grassland

**Official answer: A — False; B — False; C — True; D — True.**

### Reasoning

**A — False.** “Potassium coupled with nitrogen” is the NK⁺ treatment. In the legume-cover panels (Figure 1A), the NK⁺ result carries a black dot after both three years and six years. The caption defines a black dot as a statistically significant difference from the control, so the effect is significant at both sampling times, not non-significant. The negative normalized changes also show that adding N and K⁺ reduced legume cover relative to the control.

**B — False.** The biomass panels (Figure 1C) show broadly the same directional pattern after three and six years. Treatments containing nitrogen—especially N alone and NP—generally give negative normalized changes, whereas P, K⁺, and PK⁺ without nitrogen generally give positive changes. The sizes of the responses change with time, but their signs are mostly preserved; therefore the six-year response is not the opposite of the three-year response.

**C — True.** Nitrogen fixation gives legumes an advantage over plants that must obtain all of their nitrogen from the soil when available soil nitrogen is scarce. Across the three measured properties—cover, species richness, and biomass—the nitrogen-containing treatments tend to reduce legume performance, while enrichment with P and/or K⁺ without nitrogen does not show that general negative pattern. Adding nitrogen therefore appears to release non-fixing competitors from nitrogen limitation and removes much of the legumes’ special advantage. This supports the conclusion that the steppe community is generally nitrogen-limited, even though the legumes themselves respond negatively because of increased competition.

**D — True (official key).** Under the nitrogen-limitation interpretation in C, non-nitrogen-fixing plants should benefit directly when usable soil nitrogen is supplied. In an analogous comparison with the untreated control, their aggregate cover or biomass is therefore expected to increase, giving a positive normalized change under nitrogen enrichment.

There is a scope caveat to the official **True** answer: Figure 1 contains data only for legumes, and nitrogen addition does not guarantee a positive response for every non-fixing species or for every possible response variable (species richness can fall through competitive exclusion). The answer is justified if “non-nitrogen fixing plants” means their overall performance in the simplified nitrogen-limited system intended by the question, rather than a universal claim about every species and metric.

<a id="part-a-task-14"></a>
## Task 14 — Latitudinal diversity gradients: carrying capacity, diversification rate, and diversification time

**Official answer: A — True; B — True; C — False; D — True.**

### Reasoning

**A — True.** In hypothesis C, the two regions have the same diversification dynamics but begin diversifying at different times. Tropical diversification starts earlier, so tropical species can span a wider range of ages, including lineages older than any produced after the later temperate start. The temperate age distribution is truncated at that older end and should therefore have a smaller age variance in this simplified model. A larger tropical variance is consequently evidence consistent with hypothesis C, although age variance by itself would not prove the hypothesis because extinction and turnover can also alter species-age distributions.

**B — True.** Hypothesis C attributes the gradient to a historical head start: the tropics have simply had longer in which to accumulate species. If a global catastrophe effectively reset both regional biotas at the same time, that head start would be removed. Re-establishment of the same tropical-to-temperate richness gradient after such a reset would show that persistent regional differences can recreate the pattern, favouring a difference in carrying capacity or diversification rate over the original-start-time explanation. This argument assumes that the catastrophe erased the previous histories of the two regions to a similar extent; an incomplete or geographically unequal reset would be a weaker test.

**C — False.** Seasonal environmental variation is generally greater in temperate regions than in the tropics. If greater seasonality increased diversification, it would predict a higher diversification rate in the temperate zone. Hypothesis B shows the opposite relationship: with the starting point and carrying capacity held equal, the tropical curve rises faster because tropical diversification is higher. The proposed effect of seasonality would therefore oppose, not support, hypothesis B as drawn.

**D — True (official key).** The official rationale interprets this nested distribution as tropical ancestry followed by later colonization and diversification in temperate regions: the temperate taxa are largely drawn from an older tropical pool, while many additional tropical taxa never occur in the temperate zone.

There is a likely mismatch between the statement and the official explanation. That explanation supports **hypothesis C**, in which tropical diversification begins first, whereas the statement names **hypothesis A**, which changes only carrying capacity. A higher tropical carrying capacity could be compatible with the tropics containing the smaller temperate pool plus extra species, but a carrying-capacity difference alone does not predict this taxonomic nestedness. Thus the observation is not specific evidence for A; the item may have intended to say “supports hypothesis C.” The official **True** value is retained here as required.

<a id="part-a-task-15"></a>
## Task 15 — Walker circulation, ENSO, and ecological responses

**Official answer: A — True; B — False; C — False; D — False.**

### Reasoning

**A — True.** In neutral Walker circulation, warm surface water in the western Pacific supplies moist air that rises. As the rising air expands and cools, water vapour condenses and falls as precipitation. The eastern Pacific is under the descending branch of the circulation, where dry air suppresses rainfall. Greater water availability in the west generally permits more plant growth, leaf area, and photosynthesis, so the intended terrestrial gross primary productivity is higher in the western Pacific region than in the drier eastern Pacific region.

**B — False.** Figure 2B shows the red-kangaroo population increasing from 1987 to 1988. Australia lies on the western-Pacific side of the circulation. La Niña strengthens the normal Walker circulation, favouring stronger convection and greater rainfall over Australia; the rain can increase plant production and therefore food supply, survival, and reproduction in kangaroos. El Niño weakens or reverses that circulation and is instead commonly associated with reduced Australian rainfall. Thus the increase is consistent with La Niña, not the proposed El Niño explanation. The population graph alone does not establish causation or label the ENSO phase, so this conclusion relies on the regional ENSO relationship intended by the question.

**C — False.** The C2 map has a strong band of high algal productivity near the equator, whereas C1 is predominantly low-productivity blue. During El Niño, weaker surface winds reduce the wind-driven upwelling of cold, nutrient-rich deep water, and the boundary between warm surface water and cold deep water becomes deeper. Fewer nutrients then reach the sunlit surface layer, so phytoplankton productivity should decrease rather than produce the C2 bloom. C2 is therefore more consistent with strengthened or recovering upwelling, while the low-productivity C1 pattern is the one more compatible with El Niño; the proposed sequence “pre-El Niño C1, El Niño C2” has the response in the wrong direction.

**D — False.** Year Y is the only displayed state with a large corixid abundance, and its native-grazer community differs sharply from those in X and Z. Because the corixids are described as invasive freshwater predators, their establishment in the saline Great Salt Lake is explained by extra precipitation and freshwater inflow lowering the lake's salinity. Their predation can then alter the abundance and composition of the native grazers. The official interpretation associates the precipitation responsible for this dilution in North America with El Niño, so the changes in Y are not attributed to La Niña. As with B, the bars themselves show the ecological change but do not independently identify its ENSO phase; that attribution depends on the climate mechanism supplied by the task.

<a id="part-a-task-16"></a>
## Task 16 — Fractal geometry, resource scaling, and an organism's spatial perspective

**Official answer: A — False; B — False; C — False; D — True.**

### Reasoning

**A — False.** Region 2 has the more irregular outline, with more fine-scale bays, projections, and islands than region 1. It therefore has the greater coastline complexity. Under the relationship intended in the question, increasing the measurement scale removes proportionally more of this fine detail, so coastline length changes more sharply with scale for region 2. Its log–log line, not that of region 1, should consequently have the steeper downward slope in magnitude.

There is a notation problem in Figure 1B. Taking the printed equation \(Q=kL^d\) literally gives \(\log Q=\log k+d\log L\), so the plotted slope is \(d\). The figure nevertheless shows a negative slope while describing larger \(d\) as greater complexity; a numerically larger exponent would not by itself produce the claimed steeper downward line. A minus sign or a different exponent convention appears to be missing. The official **False** answer is consistent with the intended comparison of the two coastlines, but the displayed equation and caption are not fully self-consistent.

**B — False.** Point b represents a much larger operating scale than point a, and the descending line gives \(Q_b<Q_a\). In the intended ecological interpretation, an individual operating at the larger scale uses resources or territory over a larger spatial unit, so a fixed ecosystem supports fewer such individual units, not more. The greater value of \(Q\) at the finer scale a also points in the same direction. Using logarithmic axes changes the spacing of values but does not reverse their ordering.

Strictly, the graph defines \(Q\) as available resources or biomass, not directly as number of individuals. Converting biomass into abundance would require per-individual biomass, while converting operating scale into abundance would require an assumption about area or territory per individual. Thus the official **False** answer relies on the intended assumption that larger operating scale means a larger resource/territory requirement per individual; it is not established by the log scale alone.

**C — False.** The spatial scale at which an animal operates is set by such factors as how dispersed its food is and how much territory it must search or defend. It is not a measure of the animal's body size. A predator may therefore need a broad operating range and occur at low density without being physically larger than its prey. The scaling argument cannot support the universal claim that every predator must be larger-bodied than its prey.

**D — True.** An animal in a herd does not obtain and use spatial information entirely independently: it follows group movement and can respond to resources or threats detected by other members. The area collectively surveyed or used by the herd can therefore determine the effective perspective scale of each member. Herd formation can consequently alter an individual's operating scale.

<a id="part-a-task-17"></a>
## Task 17 — Renewable freshwater, water scarcity, and virtual water

**Official answer: A — True; B — False; C — True; D — True.**

### Reasoning

**A — True.** The mean residence time of water in a reservoir is approximately the amount of water stored there divided by the rate at which water leaves it. Human withdrawals remove water from rivers, lakes, aquifers, or managed reservoirs and send it through use, treatment, discharge, and evaporation before it enters other parts of the water cycle. Greater withdrawal and transfer therefore increase the effective flux between reservoirs; for a comparable stored amount, that larger flux gives water molecules a shorter mean residence time. This is the sense in which the official answer interprets “higher human activity.”

**B — False.** From $R_{ws}=(W-S)/Q$, a low value means that withdrawal from renewable freshwater, after subtracting desalinated-water use, is small relative to the renewable freshwater resource $Q$. That does not show that people can actually obtain enough usable water. For example, a region may have a large $Q$ but very low $W$ because it lacks pipes, treatment plants, pumps, storage, or the economic capacity needed to use that water. Such a region can have a low $R_{ws}$ while still suffering the second kind of water crisis described in the question: inability to utilize available RFWR.

**C — True.** Since $A_w=Q/C$, its reciprocal is $1/A_w=C/Q$. The two indicators are related by

\[
R_{ws}=\frac{W-S}{Q}=\frac{W-S}{C}\,\frac{C}{Q}
=\frac{W-S}{C}\,\frac{1}{A_w}.
\]

Thus $R_{ws}$ would track $1/A_w$ closely if non-desalinated withdrawal per person, $(W-S)/C$, were fairly similar among regions. Poor infrastructure constrains actual withdrawal and can make this per-person factor both low and highly variable: a crowded region with little water per person may still withdraw little of its available RFWR. This decouples $R_{ws}$ from water crowding and weakens their correlation.

The equation alone does not guarantee that the correlation must be weaker: that result depends on the intended assumption that poor infrastructure makes per-capita withdrawal more variable or less responsive to need. The official explanation also invokes population patterns without explicitly stating this assumption, so its justification is incomplete, although the official **True** classification follows the intended interpretation.

**D — True.** Agriculture and industrial production require far more water than people need for direct drinking and household consumption. Importing food therefore imports “virtual water”: the dry region receives the product while the large amount of water used to grow it is supplied in the exporting region. This avoids both local agricultural water demand and the cost and energy required to transport an equivalent bulk volume of water over long distances. Physical water supplies are still needed for domestic uses, but food import is the better long-term strategy for reducing the dominant water burden identified here.

<a id="part-a-task-18"></a>
## Task 18 — Wildlife responses to traffic and the road-barrier effect

**Official answer: A — True; B — False; C — True; D — False.**

### Reasoning

**A — True.** The western barn owl has the nonresponder profile: its avoidance probability remains essentially zero as traffic increases, so the total barrier effect closely follows its rising collision mortality. The prompt notes that reactions to vehicles can resemble reactions to natural threats. Top predators are normally the hunters and face less predation pressure themselves, so they may be less inclined to interrupt movement in response to an unfamiliar danger cue such as an approaching vehicle. Nonresponding behaviour is therefore plausibly more common among top predators, although this is a tendency rather than a claim that every top predator is a nonresponder.

**B — False.** In the mule-deer graph, mortality rises at very low traffic volume and then stays fairly steady over an intermediate range, but avoidance is still low during most of that interval. The mortality plateau therefore cannot be attributed to road avoidance. It is instead consistent with the speeder strategy: deer continue to cross rapidly and can use gaps between vehicles while traffic is still relatively light. Only at higher traffic volume, when the avoidance curve rises strongly, does mortality eventually decline.

**C — True.** Armadillos show the pauser profile. At lower traffic volume, pausing on the road prolongs exposure to vehicles, so mortality is high while avoidance is low. Near point Z, increasing traffic causes a sharp transition: the mortality curve falls and the avoidance curve rises past it. This indicates that an armadillo is becoming more likely to stop at the road edge before attempting to cross, which contributes to avoidance, than to pause after entering the road surface, which contributes to collision mortality.

**D — False.** The Indiana-bat graph is dominated by avoidance: avoidance rises even at low traffic volume, whereas mortality has only a small early peak and then approaches zero. That is the expected profile of an avoider, whose movement is restricted by even slight traffic. A speeder would keep crossing through traffic gaps and consequently retain a more substantial collision-mortality component, as in the mule-deer graph.

<a id="part-a-task-19"></a>
## Task 19 — Cumulative cultural evolution and route learning in rock pigeons

**Official answer: A — True; B — True; C — True; D — True.**

### Reasoning

**A — True.** The experimental treatment forms a transmission chain. After every 12 flights, an experienced member remains while its partner is replaced by a pigeon with no experience of that route. Route efficiency does not return to its initial low value with each replacement; instead, route performance is retained and eventually improves across rounds. The newcomer must therefore acquire route information from its experienced partner, and can later transmit that information when paired with the next newcomer. This is evidence of social learning and of cumulative cultural transmission.

**B — True.** A new experimental bird needs several flights to learn and help refine the inherited route. Accordingly, the experimental curve often falls early in a round and then recovers by its final flights. A mean over all 12 flights would mix this temporary adjustment cost with the pair's established end-of-round performance. Comparing such whole-round means could therefore conceal improvement across successive rounds or make the experimental treatment appear worse simply because it repeatedly receives naive birds. This is why the informative comparison shown in the task uses performance near the end of each round.

**C — True.** Successive experimental pairs do more than preserve the efficiency reached by the previous pair: their final route efficiency rises over rounds and ultimately exceeds that of the controls. Purely passive following or exact copying by each newcomer could transmit an existing route, but would not by itself explain this cumulative improvement. The intended inference is that newcomers contribute variation to the pair's joint route choice; beneficial route changes can then be retained by the experienced partner and passed to the next bird. Thus the new pigeon participates actively in route development.

**D — True according to the official key, but the item is internally inconsistent.** Collective choice by a pair is part of the mechanism that allows an experienced bird and a newcomer to combine inherited route information with new route variants. Under a broad reading in which this intergenerational joint refinement is itself called collective decision-making, it helps generate the experimental group's cumulative improvement.

However, the statement as printed says that collective decision-making is the *main reason for the difference* between the experimental and control groups. The experimental treatment and the pair control both always contain two pigeons, so both permit pairwise collective decision-making. What distinguishes them is the repeated replacement of one bird, which creates a succession of learners and permits cumulative cultural evolution. Indeed, the official explanation itself points out the equal group sizes and their different performances—an observation that argues against collective decision-making alone being the main cause and would normally make D **False**. The **True** label above is retained solely because it is the official answer.

<a id="part-a-task-20"></a>
## Task 20 — Allele frequencies in alternating haploid and diploid generations

**Official answer: A — False; B — True; C — False; D — False.**

### Reasoning

**A — False.** Let the frequencies of alleles $A_1$, $A_2$, and $A_3$ be $p$, $q$, and $r$, respectively. Because $A_3$ is the most recessive allele, only $A_3A_3$ diploids have the $A_3$ phenotype. Genetic equilibrium therefore gives $r^2=0.01$, so $r=0.10$. The $A_2$ phenotype occurs in $A_2A_2$ and $A_2A_3$ diploids, hence

\[
q^2+2qr=0.08.
\]

Substituting $r=0.10$ gives $q^2+0.20q-0.08=0$, whose biologically meaningful root is $q=0.20$. Thus $p=1-q-r=0.70$. In a haploid, the single allele directly determines the phenotype, so the $A_1$ phenotype has frequency $p=70\%$, not more than $75\%$. As a check, the predicted diploid $A_1$-phenotype frequency is $p^2+2pq+2pr=0.49+0.28+0.14=0.91$, matching the information given.

**B — True.** With the dominance order $A_1>A_2>A_3$, a diploid shows the $A_2$ phenotype only when it has no $A_1$ allele and has at least one $A_2$ allele. The two possible genotypes are therefore $A_2A_2$ and $A_2A_3$. An $A_1A_2$ individual instead has the $A_1$ phenotype, while $A_3A_3$ has the $A_3$ phenotype.

**C — False.** A diploid individual is formed by fusion of two haploid individuals and later produces haploid descendants by meiosis. Although those two earlier haploids are the descendant's two genetic sources (the statement's “grandfather” and “grandmother”), meiosis does not guarantee that any particular haploid product receives exactly half of its genome from each one. Homologous chromosomes assort randomly, and crossing-over makes transmitted chromatids mosaics of the two ancestral chromosome sets. The expected contribution from each source is $50\%$ over many meiotic products, but an individual haploid's realized proportions need not be exactly $50\%:50\%$.

**D — False.** Recessiveness can conceal a lethal allele in a diploid heterozygote because the normal dominant allele can supply the required function. That protection disappears in the haploid generation: a haploid carrying the mutant allele has no second allele to mask it. Because the mutation blocks mitosis, such a haploid cannot proliferate normally and is eliminated before it can maintain and transmit the allele through repeated life cycles. The allele might be temporarily masked in a diploid heterozygote, but obligatory passage through the haploid stage prevents the usual long-term persistence of a recessive lethal allele.

The official explanation contains two editorial slips. Its rearranged quadratic is printed once with $+0.08=0$, but the correct rearrangement is $q^2+2qr-0.08=0$, as also shown by its reported value $q=0.20$. It also labels the explanations corresponding to C and D as “B”; read in statement order, the official pattern is unambiguously **False, True, False, False**.

<a id="part-a-task-21"></a>
## Task 21 — Out-of-Africa expansion, heterozygosity, and effective population size

**Official answer: A — False; B — True; C — True; D — False.**

### Reasoning

**A — False.** Figure 1 shows the opposite pattern: mean heterozygosity decreases strongly as distance from East Africa increases (the reported correlation is $r=-0.91$). Neutral genetic diversity is ordinarily greater in populations with a larger long-term effective population size because genetic drift removes alleles more slowly. For example, at mutation–drift equilibrium for a diploid population, expected heterozygosity increases with $4N_e\mu$. The lower heterozygosity of populations farther along the migration route therefore indicates smaller, not larger, long-term average effective population sizes, consistent with repeated population bottlenecks.

**B — True.** The African populations in the graph have higher heterozygosity than the Native American populations, implying a larger effective population size. In a larger population, random genetic drift is weaker relative to selection, so purifying selection can remove a slightly deleterious allele more efficiently. In a smaller population, such as one produced by serial founder events in the peopling of the Americas, drift can overwhelm weak negative selection and occasionally carry a slightly deleterious allele to fixation. Thus, all else being equal, fixation is less likely in the African population.

**C — True.** During range expansion out of Africa, each newly colonized region was founded by only a subset of the preceding population. Such founders carry only a sample of the source population's alleles, and rare alleles are especially likely to be omitted. Repetition of this sampling process through a series of migrations progressively reduces heterozygosity and effective population size. This serial founder-effect model therefore explains why genetic diversity falls with increasing distance from East Africa.

**D — False.** The plotted mean heterozygosities are high and are intended to summarize many neutral, highly variable markers, such as microsatellites, that reveal population history. The functional sequences of DNA-polymerase genes are essential and strongly conserved; damaging variants are removed by purifying selection, so these genes are not expected to show heterozygosity on the scale represented in the graph. They would therefore be poor markers for producing this particular pattern and range of values.

A wording qualification is that neutral intronic or synonymous sites located within a DNA-polymerase locus can still carry a demographic signal. Thus, the word *could* makes D broader than the official explanation. The official **False** answer relies on the intended comparison between conserved functional DNA-polymerase sequence and the highly variable markers used to estimate the heterozygosity shown here.

<a id="part-a-task-22"></a>
## Task 22 — Agriculture, ethanol metabolism, and selection on ADH1B

**Official answer: A — False; B — True; C — False; D — True.**

### Reasoning

**A — False.** Alcohol dehydrogenase existed before agriculture and intentional large-scale fermentation. In the historical framework of the question, regular exposure to large amounts of exogenous ethanol arose as a consequence of agricultural production, whereas the ancestral enzyme would have handled much smaller amounts of endogenous ethanol or ethanol encountered incidentally in food. It is therefore unjustified to say that the ancestral allele evolved specifically to metabolize high exogenous alcohol loads.

**B — True.** ADH1B\*2 converts ethanol to acetaldehyde more rapidly than ADH1B\*1. Because acetaldehyde is toxic, rapid production can cause an unpleasant acetaldehyde build-up when alcohol is consumed, discouraging continued heavy drinking and thereby reducing the likelihood of sustained ethanol abuse. The protection is thus mainly an aversive behavioural effect; rapid completion of this first reaction does not mean that alcohol has been harmlessly detoxified.

**C — False.** Figure 1A identifies Area 3 as an early centre of agriculture, but it gives no evidence that agriculture there was strongly linked to fermenting crops into ethanol. Moreover, Figure 1B does not show a high ADH1B\*2 frequency around Area 3 comparable with the high-frequency regions associated with Areas 1 and 2. Agriculture alone is therefore insufficient to infer strong ethanol production in Area 3, and the allele-frequency pattern does not support that claim.

**D — True.** The two separated regions of high ADH1B\*2 frequency broadly coincide with agricultural Areas 1 and 2, where agriculture could have supplied the proposed selective pressure through fermented products. A simple interpretation is that the rapid-metabolism allele rose locally under positive selection in each region. This spatial correspondence is more plausible from the supplied data than assuming that the allele was formerly common and was driven down by negative selection throughout most of the rest of the world. The maps establish only relative plausibility: by themselves they do not prove selection, identify the selective agent, or exclude demographic explanations such as migration and population history.

<a id="part-a-task-23"></a>
## Task 23 — Drosophila allele-frequency dynamics and heterozygote advantage

**Official answer: A — False; B — False; C — True; D — False**

### Reasoning

**A — False.** In Experiment #1, the A1 frequency falls from about 0.60 but then approaches an internal equilibrium near 0.30 rather than continuing toward loss of A1. Directional selection would consistently favor one end of the phenotypic distribution and drive the corresponding allele toward fixation. Here, both alleles persist at a stable frequency. Because the homozygous phenotypes occupy the phenotypic extremes, favoring the intermediate heterozygote is phenotypic stabilizing selection; at the locus, its effect is balancing selection through heterozygote advantage.

**B — False.** The replicate trajectories fluctuate much more widely around the same theoretical equilibrium in Experiment #2 than in Experiment #1. Sampling error in allele transmission, and hence genetic drift, becomes stronger as population size decreases; for a diploid population its one-generation sampling variance is approximately \(pq/(2N)\). The greater stochastic variation therefore indicates that Aizhan reduced, rather than increased, the population size in Experiment #2.

**C — True.** A stable internal equilibrium under frequency-independent selection is the expected outcome of overdominance: A1A2 must be fitter than both A1A1 and A2A2. If the heterozygote were the least fit, the internal equilibrium would be unstable and replicate populations would tend to move toward alternative allele fixations. Genotype abundance should not be confused with fitness: at \(p(A1)\approx 0.30\), Hardy–Weinberg frequencies are about \(p^2=0.09\) A1A1, \(2p(1-p)=0.42\) A1A2, and \((1-p)^2=0.49\) A2A2, so A2A2 can be more common than A1A2 even though A1A2 has the greatest fitness.

**D — False.** Let the relative fitnesses be \(w_{12}=1\), \(w_{11}=1-s\), and \(w_{22}=1-t\), where heterozygote advantage means \(s,t>0\). The stable A1 equilibrium is \(p^*=t/(s+t)\). Since the graph gives \(p^*\approx 0.30<0.50\), it follows that \(t<s\), so \(w_{22}=1-t>w_{11}=1-s\). Thus A2A2 has higher fitness than A1A1, and the complete fitness order is A1A2 > A2A2 > A1A1.

<a id="part-a-task-24"></a>
## Task 24 — Codon usage bias and translational efficiency

**Official answer: A — True; B — True; C — False; D — False.**

### Reasoning

**A — True.** Genes encoding ribosomal proteins and other heavily used components of ribosome production are expressed at high levels because cells continually need ribosomes for translation. A synonymous codon that is efficiently recognized by an abundant tRNA saves a small amount of time and reduces decoding errors during each translation event; in a very highly expressed gene, those small benefits are repeated many times. Selection therefore tends to enrich ribosome-related coding sequences for preferred codons, producing strong codon usage bias.

**B — True.** A donor organism and a transgene recipient can differ in which synonymous codons they use most often and, correspondingly, in the relative abundance of the matching tRNAs. If the unmodified transgene contains many codons that are rare in the recipient, ribosomes may wait longer for the relevant charged tRNAs, slowing elongation and lowering protein output. Synonymously recoding the gene toward the recipient's preferred codons leaves the amino-acid sequence unchanged while generally increasing translational efficiency relative to the uncorrected construct.

**C — False.** Viruses can and do show codon usage bias. Most viruses depend on a host's ribosomes and tRNA pool, so selection can favor viral codons that the host translates efficiently; mutation patterns and nucleotide composition can also shape the viral bias. Some bacteriophages even encode their own tRNAs, which can help translate codons that are common in the viral genome. Thus, the absence of an autonomous viral translation system does not imply an absence of biased codon use.

**D — False.** In the standard genetic code, methionine is specified only by AUG. Codon usage bias compares the frequencies of alternative synonymous codons for the same amino acid, so there are no methionine codons among which usage can be biased. The initiator methionine at the start of a newly translated polypeptide may increase demand for methionine decoding, but it cannot create a synonymous-codon preference; moreover, that initiator residue can later be removed from the mature protein.

A qualification to B is that codon optimization is a general expectation rather than a universal guarantee: synonymous recoding can also change mRNA structure, stability, or the translation pace needed for protein folding. The official **True** answer follows the simplified tRNA-pool model explicitly emphasized in the question, so this qualification does not change the official pattern.

<a id="part-a-task-25"></a>
## Task 25 — Mitochondrial RNase P mutations, targeting, and inheritance

**Official answer: A — False; B — False; C — False; D — True.**

### Reasoning

**A — False.** Position Z is more strongly conserved than position X in the alignment. Z is alanine in all six organisms shown and is surrounded by several other highly conserved residues, whereas X is tyrosine in the vertebrates but phenylalanine in *Drosophila*, and its neighboring sequence is more variable. Residues at or near an enzyme's active site are usually subject to strong purifying selection because changes there readily impair catalysis or substrate binding. Thus, under the conservation-based inference requested here, Z—not X—is the better candidate for being closer to the active site. An alignment cannot establish three-dimensional distance by itself, but it does not support the statement's proposed ordering.

**B — False.** Threonine is encoded by ACN codons, whereas alanine is encoded by GCN codons, where N can be any nucleotide. A single-nucleotide Thr-to-Ala substitution therefore changes the first codon position from A to G. Adenine and guanine are both purines, so this is a transition, not a purine-to-pyrimidine transversion.

**C — False.** Figure 1B gives both TRMT10C and PRORP their own N-terminal mitochondrial targeting sequences. Such signals direct precursor proteins to the mitochondrial import machinery, supporting import of the subunits followed by assembly of the RNase P complex inside the mitochondrion. The diagram therefore contradicts the claim that all three subunits first form a complete complex in the cytoplasm and are then transported together.

**D — True.** The affected child in family A2, born to two unaffected parents, indicates autosomal-recessive inheritance and makes both parents obligate carriers. For their unaffected son II-2, the possible Mendelian genotypes have conditional proportions $1/3$ non-carrier and $2/3$ carrier, so $P(\text{II-2 carries Y})=2/3$. Individual II-3 from family A1 is specified to carry mutation X. If II-2 also carries Y, each parent transmits the pathogenic allele with probability $1/2$, giving a $1/2 \times 1/2=1/4$ chance that their child inherits both disease alleles and is affected. Hence the total probability is

\[
\frac{2}{3}\times\frac{1}{4}=\frac{1}{6}.
\]

<a id="part-a-task-26"></a>
## Task 26 — Carbon-cycle perturbations, extinction thresholds, and the biological pump

**Official answer: A — True; B — False; C — True; D — True**

### Reasoning

**A — True.** In Graph B, the red point labelled FF (the Frasnian–Famennian extinction) differs from the other mass-extinction points: despite representing a relatively long event, it lies below the fitted threshold region rather than above it. Graph A likewise shows FF as a long-lasting event with only a modest isotopic shift. Its separation from the pattern followed by the other red points makes it reasonable to infer that this extinction probably involved a different dominant mechanism. The plots support that inference, although they do not by themselves identify the mechanism.

**B — False.** Loss of old, small signals from the geological record could create a sampling bias by removing minor ancient events from Graph C. That bias can explain why few low-mass events are recorded far in the past, but it cannot explain the absence of high-mass events near the present, where the record should be more complete. Thus incomplete information about early minor events may contribute to the pattern, but it cannot *alone* account for the overall decrease in recorded mass change toward the present.

**C — True.** Graph B compares the mass change with event duration. For a given duration, a point above the line has a larger mass change and therefore a higher average rate of carbon addition; equivalently, for a given mass change, the perturbation occurred more rapidly. Almost all red mass-extinction events lie above this line, whereas most blue non-extinction events lie below it. The line, with its gray uncertainty band, can therefore be interpreted as an empirical critical boundary above which a carbon-cycle perturbation is much more likely to coincide with catastrophic extinction, not as proof that every event above it must cause one.

**D — True.** A stronger biological pump transfers carbon from the surface ocean into deep-ocean reservoirs more effectively, so an added-carbon anomaly is buffered and redistributed more rapidly. This limits the mass change that accumulates and shortens the time for which the perturbation persists. The temporal plots match this expectation: as the biological pump strengthened over the last approximately 220 million years, Graph C shows generally smaller mass changes toward the present, and Graph D shows shorter durations for the non-mass-extinction events included there.

<a id="part-a-task-27"></a>
## Task 27 — Epistasis and accessible evolutionary trajectories in beta-lactamase

**Official answer: A — True; B — False; C — False; D — False.**

### Reasoning

**A — True.** The effect of a mutation depends on the genetic background, an interaction called epistasis. In Figure 1A, Mut1 alone raises the efficiency only from 0.09 to 0.13, about a 1.4-fold change. Once Mut2 is also present, however, the two-mutation enzyme has an efficiency of 362: adding Mut1 to the Mut2 background raises the value from 1.41 to 362, about 257-fold. Thus, a mutation that has little effect by itself can have a large effect after another mutation has occurred.

**B — False.** A cumulative probability curve rises by the probability assigned to each newly included trajectory. The first few trajectories in Figure 1B produce large vertical increases, whereas later trajectories add progressively smaller increases as the curve approaches 1. For example, the first trajectory already accounts for roughly one quarter of the total probability, while each of the last several contributes only a small increment. The trajectories are therefore ordered approximately from greatest to least probability, not in increasing order; trajectory 1 is the most probable.

**C — False.** A mutation's fitness effect does not determine whether that DNA change arises. Its de novo occurrence is governed by the mutation process and mutation rate, and mutations do not arise because they would be advantageous. Fitness affects what happens afterward: a beneficial mutation is more likely to survive drift, spread, and become fixed, so it is more likely to appear as a successful step in an evolutionary trajectory. The statement incorrectly identifies this differential fixation as a difference in the probability of mutation occurrence.

**D — False.** Every ordering of the five mutations ends with the same five-mutation genotype, BL*, shown with an efficiency of 4100. Consequently, all 5! = 120 orders have the same final fitness, yet only 18 are accessible; final fitness therefore cannot explain the difference. Accessibility depends mainly on the fitnesses of the intermediate genotypes and on epistasis. If a particular order requires a fitness-decreasing intermediate step or reaches a local fitness maximum, selection will not favor continuing along that route merely because the eventual endpoint would be highly fit.

<a id="part-a-task-28"></a>
## Task 28 — Distribution of fitness effects, effective neutrality, and mutation accumulation

**Official answer: A — True; B — True; C — True; D — False.**

### Reasoning

**A — True.** The condition \(N_e|s|<1\) means that selection on the mutation is too weak to act efficiently in a population of effective size \(N_e\). Random sampling of alleles from one generation to the next therefore dominates the mutation's fate, so an effectively neutral allele reaches fixation, if it does so at all, through genetic drift rather than a consistent selective advantage. Strictly, a nonzero \(s\) can still alter the fixation probability slightly; thus the word *only* is an approximation built into the term “effectively neutral,” not a claim that selection is mathematically exactly zero. Under the convention intended by the question, the statement is true.

**B — True.** Increasing \(N_e\) lowers the largest value of \(|s|\) that satisfies \(N_e|s|<1\). Consequently, mutations with small beneficial effects that would behave almost neutrally in a small population can be acted on by positive selection in a large population. Large populations also usually generate more new mutant copies per generation, increasing the supply from which adaptive variants can spread. In this population-genetic sense, a larger \(N_e\) gives a species greater capacity for adaptation. The wording is broader than the underlying model—actual adaptability also depends on mutation rate, recombination, environment, and other constraints—but the official True answer follows from the stated effective-neutrality framework.

**C — True.** In a mutation-accumulation experiment, replicate lines are repeatedly propagated through very small bottlenecks so that drift permits many mildly deleterious mutations to persist; their fitness is later compared with that of the preserved ancestor. However, a lethal mutation leaves no surviving carrier to found the next generation, and mutations causing sterility or extremely poor survival are also likely to remove their line before measurement. These missing outcomes belong to the deleterious part of the true distribution of new mutational effects. The effects recovered from surviving lines therefore underrepresent deleterious mutations, especially the most severe class. Here, *always* reflects this unavoidable survivor bias when the complete DFE includes lethal mutations.

**D — False.** The \(d_N/d_S\) statistic compares the rates of nonsynonymous and synonymous substitutions that have become established between lineages; it does not directly count all mutations that originally arose. Deleterious nonsynonymous mutations are preferentially removed by purifying selection and hence usually never appear as substitutions. Thus a low \(d_N/d_S\) can indicate strong purifying selection, but the value is not proportional to the fraction of new mutations that are deleterious. Among observed nonsynonymous substitutions, neutral or effectively neutral changes usually contribute most under purifying selection, while values above one can indicate positive selection.

<a id="part-a-task-29"></a>
## Task 29 — Endogenous retroviruses, solo-LTRs, and evolutionary change

**Official answer: A — True; B — False; C — False; D — True.**

### Reasoning

**A — True.** A retrovirus becomes a provirus when its DNA copy integrates into an infected cell's chromosome. For that insertion to become an endogenous retrovirus and be inherited by later generations, it must occur in a germ-line cell, a gamete precursor, or another cell that contributes to an offspring's germ line. An insertion confined to a somatic cell may persist and replicate within that individual, but it is lost when the individual dies. Thus whether an integrated provirus can become a heritable ERV does depend on the type of host cell infected.

**B — False.** An autonomous, infectious retrovirus requires every essential part of its replication cycle, so disabling even one indispensable gene can be sufficient to make an ERV incapable of producing infectious progeny. For example, loss or inactivation of `env` removes the envelope protein needed for efficient entry into new cells. An element retaining `gag`, `pro`, `pol`, and its LTRs may still copy or mobilize within a genome like an LTR retrotransposon, but it is no longer a complete autonomous virus. There is therefore no requirement that at least two genes must be lost.

**C — False.** The two LTRs flanking a newly integrated ERV have very similar sequences. Homologous recombination between them can delete the entire internal proviral region, leaving one recombinant LTR at the insertion site. Because this deletion can occur repeatedly over long evolutionary periods, solo-LTRs are very common ERV remnants rather than the least common derivative. There is a minor schematic discrepancy in the question: Figure 1B is captioned as a “solo-LTR” but labels two separate boxes, 5′-LTR and 3′-LTR. Biologically, the usual recombination product called a solo-LTR contains one remaining LTR; the intended recombination argument and the official False answer are nevertheless clear.

**D — True.** An ERV-derived restriction factor that blocks entry of a harmful, species-specific exogenous retrovirus benefits hosts while that virus is prevalent. Positive selection can therefore drive the protective ERV rapidly to a high population frequency, as line X initially shows. If the exogenous virus later becomes rare or extinct, the protection no longer provides an advantage. Over millions of years, deletion or inactivation variants can then spread if continued ERV expression has a cost, and neutral loss can also occur by drift, producing the later decline shown by X. Loss of the viral threat alone does not make decline inevitable, but the statement asks whether this history *can* occur, so line X is a plausible trajectory.

<a id="part-a-task-30"></a>
## Task 30 — Long-distance and intracellular transport of gibberellin in roots

**Official answer: A — False; B — True; C — True; D — False.**

### Reasoning

**A — False.** In Figure 1A, the graft labels are ordered as root/shoot. A wild-type graft, Col-0/Col-0, has a root endodermal Nile-red fluorescence of about 10 arbitrary units. A gibberellin-deficient `ga1-3` root attached to a wild-type shoot, `ga1-3`/Col-0, has approximately the same value (about 10.5, with no significant difference from the wild type), whereas `ga1-3`/`ga1-3` falls to about 7 and is significantly different. Thus, gibberellin made in the wild-type shoot can reach and rescue the root. The experiment supports shoot-to-root transport, opposite to the root-to-shoot direction stated here. It does not establish that gibberellin can never move root-to-shoot in any setting, but that is not the direction demonstrated by these grafts.

**B — True.** In wild type, Figure 1B shows a large gibberellin pool in the vacuoles of the inner root cells, including the pericycle: the orange-red colour is near the upper end of the vacuolar scale, roughly 3–4 arbitrary units. In the `npf2.14` mutant, this vacuolar signal is essentially zero, while cytoplasmic gibberellin rises markedly, reaching about 2.4 units in an inner cell layer and about 1 unit even in more external tissues. Sequestration in pericycle vacuoles can therefore act as a reservoir and buffer: NPF2.14-mediated uptake prevents cytoplasmic gibberellin from immediately exceeding a response threshold and helps control how much hormone is subsequently available to neighbouring tissues. The official explanation calls this image “Figure 2,” but on the question page it is panel B of Figure 1.

**C — True.** NPF3.1 transports gibberellin into the root endodermis, where gibberellin promotes suberin deposition. Loss of NPF3.1 therefore lowers the endodermal gibberellin signal and weakens this hydrophobic diffusion barrier. The endodermis normally regulates radial movement of water and mineral ions into the stele and helps exclude harmful solutes; a less suberized endodermis consequently makes the mutant more prone to water or mineral imbalance and toxin entry than wild type. The official explanation describes this as defective formation of the Casparian strip. More precisely, the Casparian strip is primarily lignified, whereas suberin lamellae form a distinct endodermal barrier. Reduced suberization still supports the intended conclusion and the official True answer, but the two structures should not be equated.

**D — False.** NPF2.14 is a counterexample to the word *all*: it is located on the tonoplast, the membrane surrounding the vacuole, rather than on the plasma membrane. The `npf2.14` pattern in Figure 1B is consistent with this localization—removing the transporter abolishes vacuolar gibberellin accumulation and leaves more hormone in the cytoplasm. Therefore, even if the other listed transporters act at the plasma membrane, the universal statement is false.

<a id="part-a-task-31"></a>
## Task 31 — Photorespiration, glycine decarboxylase, and C4 photosynthesis

**Official answer: A — True; B — False; C — False; D — True.**

### Reasoning

**A — True.** In the interpretation intended by the official key, inhibiting glycine decarboxylase (GDC) removes the mitochondrial decarboxylation step that releases \(\mathrm{CO_2}\), \(\mathrm{NH_3}\), and produces NADH, but it does not eliminate every possible source of serine in the cell. Serine made by another route can enter gluconeogenic reactions and form carbon intermediates such as 3-phosphoglycerate (3-PGA). Once 3-PGA enters the Calvin-cycle reaction network, its carbon can contribute to regeneration of RuBP. Thus the alternative route shown from serine to gluconeogenesis provides the basis for the official True answer.

There is a biological ambiguity in this statement. In the canonical photorespiratory cycle, GDC works with serine hydroxymethyltransferase to convert glycine derived from 2-phosphoglycolate into serine; strong GDC inhibition therefore blocks ordinary recycling of that photorespiratory carbon and causes glycine to accumulate. The official answer is defensible only if “could still recover” permits serine supplied by other metabolism and the alternative gluconeogenic route, rather than requiring the normal photorespiratory pathway itself to continue.

**B — False.** RuBisCo's carboxylase and oxygenase reactions compete for the same active site. Raising the atmospheric \(\mathrm{CO_2}\) concentration by itself increases the availability of \(\mathrm{CO_2}\) relative to \(\mathrm{O_2}\), so RuBisCo performs proportionally more carboxylation and less oxygenation. Less oxygenation means less 2-phosphoglycolate is produced and therefore less photorespiratory salvage is needed, not more.

**C — False.** The figure states that overexpression of an orange-star enzyme has no effect on reaction rate, whereas overexpression of a magenta-circle enzyme slows the reaction. The displayed peroxisomal steps contain orange and magenta enzymes, including magenta enzymes on both the outward and return portions of the pathway. Overexpressing all of them therefore cannot make every peroxisomal step faster: the orange enzymes provide no gain and the magenta enzymes introduce slower steps. The complete photorespiratory cycle would consequently not take less time than in the wild type.

**D — True.** C4 plants first fix inorganic carbon with PEP carboxylase in mesophyll cells, transport it as four-carbon compounds, and then release \(\mathrm{CO_2}\) in bundle-sheath cells. This carbon-concentrating mechanism creates a high \(\mathrm{CO_2}\) concentration around bundle-sheath RuBisCo, favoring its carboxylase activity over its oxygenase activity. C4 plants therefore form less 2-phosphoglycolate and rely less on photorespiration than C3 plants, whose RuBisCo is exposed more directly to the ambient \(\mathrm{CO_2}/\mathrm{O_2}\) balance.

<a id="part-a-task-32"></a>
## Task 32 — Electrical and osmotic coordination of grass stomata

**Official answer: A — True; B — False; C — False; D — True.**

### Reasoning

**A — True.** The diagram shows that opening and closing use opposite electrical states. In the light, the guard-cell membrane is hyperpolarized while the subsidiary-cell membrane is depolarized; this promotes transfer of K⁺ and then water toward the guard cells, increasing their turgor and opening the pore. In darkness, the membrane states and net K⁺/water movement are reversed, so guard cells lose turgor and the pore closes. An electrode of the appropriate polarity can impose either hyperpolarization or depolarization, bypassing the environmental signal and initiating either sequence. Electrical stimulation can therefore drive both opening and closing, depending on the pulse applied.

**B — False.** Rapid grass-stomatal movement depends not only on synchronized solute exchange but also on the subsidiary cells being able to lose turgor and deform inward as the guard cells expand. Lignin would reinforce and stiffen their walls. That extra rigidity would resist the required change in cell shape; it would not accelerate ion transport or osmosis and would tend to restrict or slow pore opening. Thus lignifying the subsidiary-cell walls would undermine the mechanical advantage described in the question.

**C — False.** K⁺ is a principal osmotically active solute in this mechanism. During opening, K⁺ accumulates in guard cells, lowering their water potential so that water enters through aquaporins and raises guard-cell turgor. Continuous potassium deficiency would limit the available K⁺ gradient and hence the amount of water and turgor the guard cells can gain. Their maximum expansion—and therefore the maximum pore area—would be smaller rather than larger.

**D — True.** Aquaporins are passive water channels: they increase membrane hydraulic conductivity but do not create the osmotic gradient or determine its direction. Those functions are supplied here by electrically controlled ion transport, especially redistribution of K⁺. With the same ion concentrations and cell-wall mechanics, adding aquaporins lets water approach the same osmotic equilibrium more quickly, changing how rapidly the stoma opens or closes without changing its final equilibrium aperture. This official conclusion applies to the simplified mechanism in the question; in an intact plant, altered aquaporin expression could also have broader effects on tissue water relations.

<a id="part-a-task-33"></a>
## Task 33 — Xanthophyll-cycle photoprotection and light acclimation

**Official answer: A — True; B — True; C — False; D — True.**

### Reasoning

**A — True.** Excess light drives proton accumulation in the thylakoid lumen. The resulting low pH activates de-epoxidase, which uses reduced ascorbate to convert precursor xanthophylls (Pre-Z) into zeaxanthin (Z). Protonated zeaxanthin then promotes a photosystem-II conformation that releases excess excitation energy as heat rather than allowing it to generate damaging reactive oxygen species. Deleting the de-epoxidase gene blocks this inducible conversion and weakens photoprotection, so a formerly sun-tolerant plant would suffer more photo-oxidative stress in strong light and perform relatively better in shade. Here, “shade preference” means a shift in the light conditions under which the plant performs best, not active movement toward shade.

**B — True.** A shrub in open steppe receives intense, direct light much more consistently than a conspecific shrub beneath a forest canopy. A larger total leaf pool of xanthophylls gives the steppe plant more substrate that can be shifted toward zeaxanthin when lumen pH falls, increasing its capacity for thermal dissipation. The shaded understory plant faces less excess excitation and therefore has less need to maintain that costly photoprotective pool. Thus high-light acclimation or local adaptation supports higher xanthophyll content in the steppe population.

**C — False.** The statement concerns the *total* xanthophyll concentration, not merely the fraction present as zeaxanthin. Sunlight-induced lumen acidification controls the reversible Pre-Z→Z conversion within an existing pool, so it does not by itself show that a hotter climate must enlarge that pool. Moreover, in a cold but sunny climate, low temperature can restrict carbon-fixation and other downstream reactions while light absorption continues; the resulting excess excitation can create an especially strong need for xanthophyll-based photoprotection. It is therefore not valid to infer that the hot, sunny climate would have the higher total concentration.

The official explanation additionally argues that releasing more energy as heat is disadvantageous in an already hot leaf and that long-term adaptation could therefore reduce the total pool. That specific mechanism is not demonstrated by the figure, and climate alone is insufficient to predict pool size: species, water status, light intensity, and acclimation also matter. This is an ambiguity in the official rationale, but it does not require changing the official **False** answer because the claimed necessary increase is unsupported.

**D — True.** Reduced ascorbate is both the de-epoxidase cofactor shown in the diagram and an antioxidant. Leaves at the top of a canopy receive more irradiance, undergo stronger xanthophyll-cycle activity, and face greater oxidative stress than shaded lower leaves, so high-light acclimation is expected to maintain a larger reduced-ascorbate pool there. Within the hypothetical comparison in the question, top-canopy leaves should therefore supply more vitamin C. This is not a general dietary recommendation, because actual vitamin C content also depends on species, leaf age, and growth conditions.

<a id="part-a-task-34"></a>
## Task 34 — Diurnal carbohydrate allocation in maize leaves and developing kernels

**Official answer: A — False; B — True; C — True; D — False.**

### Reasoning

**A — False.** The first two measurements are at 06:00 and 09:00. In both vegetative stages (panels A and B), leaf starch and total soluble carbohydrate (TSC) generally increase over this interval, and TSC also increases before 09:00 in the reproductive stage (panel C). Carbohydrate accumulation has therefore already occurred by 09:00, so the graphs do not support the claim that photosynthesis starts only after that time. Moreover, measurements at three-hour intervals could not establish its exact starting time. The official explanation overstates the pattern by saying that both pools increase in all three stages: in panel C, starch does not rise consistently from 06:00 to 09:00 across the cultivars. This does not alter the False answer, because the pre-09:00 increases elsewhere are already enough to refute the statement.

**B — True.** The reproductive-stage TSC curves in panel C peak at about 120–125 concentration units around 12:00. This is higher than the peaks of roughly 85–100 in panel A and 60–70 in panel B, the two vegetative stages. Developing kernels are strong carbohydrate sinks. Their demand can stimulate source-leaf carbon production and the conversion of assimilated carbon into soluble, phloem-mobile sugars—especially sucrose—for export to the kernels. A larger transient leaf TSC pool during reproduction is therefore consistent with kernel growth. The graph shows an association rather than proving this causal mechanism, but kernel demand can biologically explain the observed difference as the statement says.

**C — True.** The 24:00 measurement connects to 06:00 on the next daily cycle. During the intervening dark period, photosynthetic carbon input stops or becomes negligible, whereas cellular respiration continues. Soluble sugars in the TSC pool, or sugars obtained after their conversion to respiratory intermediates, are oxidized to supply ATP; this can contribute to the difference between the midnight and early-morning concentrations. Respiration need not be the only cause, because phloem export, growth, and interconversion between soluble sugars and starch also change TSC. That is why the statement appropriately says the difference comes *partially* from respiration.

**D — False.** A low starch concentration in a source leaf is not necessarily detrimental to seed size. It can indicate that less fixed carbon is being retained as temporary starch in the leaf and that more is being mobilized into soluble sugars and exported through the phloem to the developing kernels. Efficient source-to-sink allocation can thus favor, rather than hinder, the production of larger seeds. Low leaf starch alone could also result from poor carbon assimilation, so it is not automatically beneficial; the error is treating it as intrinsically detrimental. The official explanation is mechanistically imprecise in describing starch as moving to the endosperm: leaf starch is degraded, carbon is transported mainly as sucrose, and starch is then synthesized anew in the kernel endosperm.

<a id="part-a-task-35"></a>
## Task 35 — Hydraulic strategies and tree height in California redwoods

**Official answer: A — True; B — False; C — True; D — False.**

### Reasoning

**A — True.** In the plot, the open symbols for *Sequoiadendron giganteum* are generally farther left than the filled symbols for *Sequoia sempervirens*, so *S. giganteum* has the lower average PC3 score. The caption states that PC3 is inversely related to wood density: a lower PC3 therefore corresponds to denser wood. Thus the interspecific shift in the plotted points supports a higher mean wood density in *S. giganteum*.

**B — False.** Symbol size represents tree height, whereas increasing PC2 represents a shift from efficient stomatal control toward more efficient xylem water use. Among the filled *S. sempervirens* symbols, the largest symbols occur mainly at relatively high PC2, while many of the smallest symbols occur at low PC2. The intended inference is therefore that the stronger xylem-based hydraulic adaptations occur in taller, not shorter, trees. This is also reasonable because increasing height lengthens the transport path and increases the tension required to lift water, making protection of xylem function increasingly important. Strictly, the caption identifies PC2 with xylem water-use efficiency rather than directly measuring embolism or blockage resistance, so the wording of the statement and official explanation involves that intended proxy; it does not alter the **False** answer.

**C — True.** *S. giganteum* comes from comparatively dry mountain slopes and mostly occupies the low-PC2 part of the graph, consistent with relying on stomatal restriction to conserve water. The question states that structural xylem adaptations require a larger initial carbon and water investment but permit greater transpiration. If irrigation removes the long-term water constraint, that costly hydraulic capacity can become more advantageous than tightly restricting water loss through the stomata. Across several generations, selection could therefore shift the population toward greater xylem investment and higher PC2. The statement says this *might* happen, not that irrigation guarantees it.

**D — False.** Because wood density decreases as PC3 increases, a strong negative relationship between density and height would appear as a strong *positive* relationship between PC3 and symbol size: the largest filled symbols should consistently lie farthest to the right. They do not. The largest *S. sempervirens* symbols are concentrated mostly at intermediate PC3, whereas several of the smallest symbols lie at high PC3, with the middle-height symbols scattered between them. Hence the graph does not support the claimed strong negative density–height correlation; if anything, its weak visual tendency is in the opposite direction, toward taller trees having lower PC3 and thus denser wood.

The official explanation likewise marks D false, although its added claim that denser wood is necessarily more flexible is not established by this figure and is not generally implied by density alone. The plotted PC3 and symbol-size pattern is sufficient for the answer, so this issue does not create a discrepancy in the official truth pattern.

<a id="part-a-task-36"></a>
## Task 36 — Dissolved inorganic-carbon uptake by aquatic plants

**Official answer: A — False; B — True; C — True; D — True.**

### Reasoning

**A — False.** The cuticle chiefly limits water loss and uncontrolled exchange with the surroundings, but a fully submerged plant is not threatened by evaporative water loss. Instead, it must obtain dissolved inorganic carbon across its surface in a medium where diffusion is already much slower than in air. A thicker hydrophobic cuticle would add another barrier to that exchange. Submerged leaves therefore tend to have a thin or reduced cuticle, allowing epidermal cells to take up dissolved carbon more readily.

**B — True.** At the oceanic pH of about 8, the graph places almost all dissolved inorganic carbon in the bicarbonate, \(\mathrm{HCO_3^-}\), region; free \(\mathrm{CO_2/H_2CO_3}\) forms only a small fraction. The question also states that plants can take up bicarbonate faster than carbon dioxide. Uptake of this abundant bicarbonate, followed by its conversion to \(\mathrm{CO_2}\), therefore gives aquatic plants access to a much larger carbon pool than reliance on dissolved \(\mathrm{CO_2}\) alone. Because Rubisco itself accepts only \(\mathrm{CO_2}\), bicarbonate is an indirect \(\mathrm{CO_2}\) source rather than Rubisco's substrate.

**C — True.** Releasing \(\mathrm{H^+}\) acidifies the thin layer of stationary water next to the epidermis. Lower pH shifts the carbonate equilibrium toward carbon dioxide:

\[
\mathrm{HCO_3^- + H^+ \rightleftharpoons CO_2 + H_2O}.
\]

This raises the local proportion of the carbon form that can cross into the plant and ultimately be fixed by Rubisco. The effect is especially plausible in stationary water because the acidified boundary layer and the newly formed \(\mathrm{CO_2}\) are not immediately swept away by flow.

**D — True (official key).** The intended argument treats Rubisco as the intracellular sink that gives the reversible carbonic-anhydrase reaction a useful net direction. After bicarbonate enters a cell, carbonic anhydrase rapidly equilibrates it with \(\mathrm{CO_2}\). Rapid fixation by Rubisco removes that \(\mathrm{CO_2}\), keeping its concentration below equilibrium and pulling further \(\mathrm{HCO_3^- + H^+}\) conversion toward \(\mathrm{CO_2}\). On the official interpretation, efficient Rubisco is therefore coupled to the carbonic-anhydrase strategy, while cytoplasmic buffering prevents the associated proton chemistry from causing a large pH shift.

There is a logical discrepancy in this item. Carbonic anhydrase requires a continuing \(\mathrm{CO_2}\) sink for sustained net flux, but neither the reaction nor the speciation graph shows that the Rubisco enzyme in these plants must have *intrinsically higher fixation efficiency* than Rubisco in plants that absorb \(\mathrm{CO_2}\) directly. Indeed, carbonic-anhydrase-assisted bicarbonate use can increase the local supply of \(\mathrm{CO_2}\) around Rubisco without changing Rubisco's own kinetics. Thus the official **True** answer rests on an additional comparative adaptation assumption that is not established by the information given; read literally, D is not compelled by the data.

<a id="part-a-task-37"></a>
## Task 37 — Water uptake, aerenchyma formation, and osmosis in a eudicot root

**Official answer: A — False; B — False; C — True; D — True.**

### Reasoning

**A — False.** Water entering the root cortex (zone B) does not all have to cross a plasma membrane at the soil–root boundary. Some can move by the apoplastic route through porous cell walls and extracellular spaces, while other water follows symplastic or transmembrane routes. The Casparian strip in the endodermis, at the boundary between the cortex (B) and vascular cylinder (C), blocks continued apoplastic movement and forces water and dissolved ions across an endodermal plasma membrane before they enter the stele. Thus membrane crossing is obligatory at the endodermal barrier, not for every water molecule as it first enters B from A.

**B — False.** The arrows show net water entry from the soil (A) into the root cortex (B). Under the intended optimal conditions, this requires the water potential in B to be lower than that in A. Accumulated solutes lower water potential by reducing the mole fraction and chemical activity of water, so zone B has a lower, not greater, concentration of free water molecules than zone A. Water consequently moves into B down its water-potential gradient.

**C — True.** Flooding fills soil air spaces with water and greatly slows oxygen delivery to roots. In some flood-tolerant plants, programmed death and lysis of cortical cells in zone B create interconnected gas-filled cavities called lysigenous aerenchyma. These voids provide a low-resistance internal route for oxygen diffusion to submerged root tissues, helping the root tolerate hypoxia.

**D — True.** Under the usual ideal-dissociation approximation, each mole of NaCl produces about one mole of Na⁺ and one mole of Cl⁻. The external osmolarity is therefore approximately

\[
0.2\ \mathrm{mol\,L^{-1}} \times 2 = 0.4\ \mathrm{Osm\,L^{-1}}.
\]

This exceeds the stated intracellular osmolarity of zone B, \(0.3\ \mathrm{Osm\,L^{-1}}\). The NaCl solution is thus initially hyperosmotic to the cortical cells and has the more negative osmotic potential, so water moves out of those cells by osmosis.

<a id="part-a-task-38"></a>
## Task 38 — ECG leads, cardiac action potentials, and atrioventricular block

**Official answer: A — False; B — False; C — False; D — True.**

### Reasoning

**A — False.** Sinoatrial-node cells are autorhythmic: after repolarization, their membrane potential does not remain at a stable resting value but slowly depolarizes again until the next action potential begins. That spontaneous pacemaker potential is shown by trace 3. Trace 2 instead rests near \(-90\ \mathrm{mV}\), has a rapid upstroke, and repolarizes quickly without the long plateau of trace 1. It therefore represents a contractile atrial cardiomyocyte; the long-plateau trace 1 represents a ventricular cardiomyocyte.

**B — False.** Complete atrioventricular block prevents sinoatrial impulses from being conducted from the atria to the ventricles, but it does not mean that only atrial depolarization is electrically detectable. A subsidiary pacemaker below the block will usually drive a slower ventricular escape rhythm, producing QRS complexes and T waves that are independent of the P waves. Even in the simplified case where ventricular depolarization were absent, atrial repolarization would still occur. Its small signal (the atrial T or Ta wave) is normally hidden by the much larger QRS complex but could become visible without that overlap. Thus an ECG would not necessarily contain only P waves.

**C — False.** The entire QRS complex, including the S wave, represents ventricular **depolarization**. The S wave is negative because the mean vector during the late part of ventricular depolarization points away from the positive electrode of the illustrated lead. A downward deflection therefore identifies the direction of the measured vector, not repolarization. Ventricular repolarization is represented mainly by the T wave, while atrial repolarization is normally obscured by the QRS complex.

**D — True.** A lead records the component, or projection, of the heart's mean electrical vector along that lead's positive axis: for a vector of fixed magnitude, the measured component varies as \(\cos\theta\), where \(\theta\) is the angle between the vector and the lead axis. In Figure 1A, the P vector is directed much more nearly along lead II than along lead III. Its projection, and hence the P-wave amplitude, is therefore larger in lead II.

The official explanation describes the P vector as both aligned with lead II and perpendicular to lead III. That wording is only schematic: in an ideal Einthoven triangle, the positive axes of leads II and III differ by \(60^\circ\), so a vector exactly parallel to lead II cannot also be exactly perpendicular to lead III. The pictured vector nevertheless has a clearly larger projection on lead II, so this geometric imprecision does not alter the official **True** answer for D.

<a id="part-a-task-39"></a>
## Task 39 — Oxygen affinity and allosteric regulation of snow-leopard hemoglobin

**Official answer: A — False; B — True; C — False; D — False.**

### Reasoning

**A — False.** An allosteric effect of DPG is visible as a displacement between the oxygen-equilibrium curve measured without DPG (circles) and the curve measured after DPG is added (triangles). In Figure 1B, the corresponding filled symbols for each snow-leopard hemoglobin isoform lie close together, so DPG produces little change in its oxygenation curve. By contrast, the white human-Hb symbols are clearly separated: adding DPG shifts human Hb toward lower fractional saturation at a given oxygen partial pressure, or equivalently toward a higher \(P_{50}\). Thus human Hb is substantially more sensitive to DPG than snow-leopard Hb, the reverse of the statement.

**B — True.** At high altitude, the low inspired oxygen pressure promotes hyperventilation. Excess ventilation removes carbon dioxide from the blood, lowering arterial \(P_{\mathrm{CO_2}}\). Because carbon dioxide participates in the equilibrium

\[
\mathrm{CO_2 + H_2O \rightleftharpoons H_2CO_3 \rightleftharpoons H^+ + HCO_3^-},
\]

the fall in \(P_{\mathrm{CO_2}}\) initially lowers \(\mathrm{H^+}\) concentration and causes respiratory alkalosis. During longer-term renal compensation, the kidneys reabsorb less filtered bicarbonate and therefore excrete more \(\mathrm{HCO_3^-}\). Lowering blood bicarbonate brings the bicarbonate-to-dissolved-CO2 ratio, and hence pH, back toward normal. Snow leopards chronically hyperventilating at high altitude should consequently excrete more bicarbonate than comparable lowland animals.

**C — False.** The measurements were standardized for pH and anion concentrations, so the curves can be used to compare the intrinsic oxygenation properties of the hemoglobins. The snow-leopard curves in Figure 1B do not show a distinctive left shift relative to those of the lowland African lion in Figure 1A, especially in the low-oxygen range. A left shift, corresponding to a lower \(P_{50}\) and higher affinity, would improve pulmonary oxygen loading when ambient \(P_{\mathrm{O_2}}\) is low. Instead, snow-leopard Hb retains the generally low oxygen affinity of felid Hb. The figure therefore gives no evidence for a snow-leopard-specific biochemical adaptation of hemoglobin to altitude; physiological responses such as hyperventilation provide the relevant compensation.

**D — False.** Figure 1C reports \(\Delta\log P_{50}\) relative to cofactor-free Hb. The black KCl bars are positive for both lion HbA and snow-leopard HbB, so KCl raises \(P_{50}\). A larger \(P_{50}\) means that more oxygen pressure is required to reach 50% saturation and therefore that oxygen affinity has **decreased**, not increased. The black bar is slightly larger for African-lion HbA (about 0.20) than for snow-leopard HbB (about 0.18), indicating a slightly stronger KCl-induced *decrease* in affinity in lion HbA. The statement assigns the effect the wrong direction.

<a id="part-a-task-40"></a>
## Task 40 — Feeding time, circadian alignment, activity, and body temperature in mice

**Official answer: A — True; B — False; C — False; D — False.**

### Reasoning

**A — True.** The triangle curves in Figure 1 show caloric intake: at most measurements, light-fed mice (LC) consumed slightly more energy than dark-fed mice (DC). Meanwhile, after the initial measurement, locomotor activity of the light-fed group (LA, dotted square curve) was below that of the dark-fed group (DA, solid square curve), and the difference generally grew with time. Greater energy intake together with less energy spent on movement tends to produce a more positive energy balance, so it is reasonable to expect the light-fed mice to gain more mass and have a higher body weight. The figure does not directly measure body mass or every component of energy expenditure, so this is the qualitative expectation requested by the statement rather than a calculation of the size of the weight difference.

**B — False.** Mice are nocturnal: their normal active and feeding phase is the dark phase. Restricting food to night therefore aligns feeding with their usual behavioral phase rather than misaligning the two. Figure 2B is consistent with this interpretation because dark-phase feeding largely preserves the regular daily body-temperature oscillation. Feeding during the light, inactive phase is the circadian–behavioral misalignment; it is also the treatment associated with the conspicuous disruption of temperature rhythms in Figure 2A.

**C — False.** Figure 2 shows the opposite pattern. In panel A, the light-fed mice initially oscillate over a range of roughly 36–38 °C, but during restricted light-phase feeding they develop much deeper temperature troughs, reaching approximately 33–34 °C, while the upper values remain near 38–39 °C. Their temperature range therefore widens appreciably. In panel B, dark-phase feeding leaves the approximate daily range and regular oscillation much closer to the pre-restriction pattern. Thus **light-time**, not night-time, feeding alters the circadian temperature range more strongly.

**D — False.** The proposed cause is contradicted by Figure 1. From about the middle of week 2 through the middle of week 6, caloric intake by the light-fed group stays approximately level, near 95–100 kcal, whereas its locomotor-activity curve continues to fall markedly. Light-fed caloric intake is also generally similar to or slightly greater than dark-fed intake, not reduced. Consequently, reduced calorie intake cannot explain the observed decline in locomotor activity, and the plotted association would in any case be insufficient by itself to establish that causal mechanism.

<a id="part-a-task-41"></a>
## Task 41 — Circadian and homeostatic control of active sleep bouts in Octopus laqueus

**Official answer: A — True; B — False; C — False; D — True.**

### Reasoning

**A — True.** In Figure 1C, the number of active bouts per hour continues to rise and fall with an approximately daily rhythm while the octopuses are kept in prolonged constant darkness. Because the light–dark transitions have been removed but the oscillation persists, the immediate environmental light signal cannot by itself be producing each peak and trough. The result instead supports an endogenous circadian oscillator, although environmental light can normally entrain that oscillator. The embedded official explanation mentions constant light as well as constant darkness, but the figure and its caption show only the constant-darkness treatment; that treatment alone is sufficient for the conclusion.

**B — False.** The gray regions in Figure 1A are the nights. Under the normal, pre-deprivation condition (Q), the active-bout rate is low through most of those gray intervals and becomes high mainly during the intervening light period. This fits a nocturnal animal that is mostly awake at night and undergoes quiet and active sleep chiefly in the daytime. Integrating the elevated daytime rate (roughly 0.6–0.8 bouts per hour over much of a 12-hour light phase) can give a total of about eight bouts, but that is a rough **daytime** total, not eight bouts per night.

**C — False.** None of the panels measures how long an individual active bout lasts. Figure 1A gives the number of bouts per hour, Figure 1B gives the waiting time until the next bout, and Figure 1C again gives bouts per hour. A rise in bout frequency after sleep deprivation therefore cannot be interpreted as an increase in mean bout duration; duration data would be needed to test that claim.

**D — True.** Both manipulations show compensatory rebound. In Figure 1A, the post-deprivation curve (R) generally lies above the normal curve (Q), especially during times when normal active-bout frequency is low, so bouts lost during deprivation are followed by extra bouts. In Figure 1B, after a bout is interrupted (T), the distribution of the interval to the next bout shifts strongly toward shorter times, with a peak near 30–35 minutes rather than the roughly 55–60-minute peak after a completed normal bout (S). Thus an omitted or incomplete active bout increases the tendency for another bout to occur soon, supporting homeostatic replenishment.

<a id="part-a-task-42"></a>
## Task 42 — Mechanical detection and active electrolocation in electric-eel hunting

**Official answer: A — False; B — False; C — False; D — False.**

### Reasoning

**A — False.** The two types of discharge have different roles in the sequence shown. A low-voltage impulse stimulates the electrically connected fish corpse, whose ATP supply allows its muscles to contract. This twitch provides evidence that prey is nearby. Exact targeting then involves the high-voltage volley: a conductive object changes the electric field produced by the eel, and the eel senses that disturbance with its electroreceptors. The conductive rod produced such an electrical target, so the eel localized and attacked the rod as though it were the prey. Low-voltage impulses alone are therefore not sufficient for the complete electrolocation process described here.

**B — False.** Figure 1 and the text explicitly describe the transparent divider as perforated. It separated the eel from the experimental objects but did not make a watertight barrier, so water movement could pass between the compartments. This is functionally important: contraction of the stimulated corpse produced a mechanical disturbance that could reach the eel and be detected by its mechanoreceptors. The divider blocked direct access, not movement of water.

**C — False.** In Figure 2A, the isolated low-voltage impulse occurs before the high-voltage volley. The timing guide links the first frame in Figure 2B to the beginning of that volley, so the earlier low-voltage stimulus had already been delivered. Since that stimulus induces the ATP-supplied corpse to twitch, the intended sequence is that contraction had already begun before the first frame was taken. Thus the first frame is not evidence of a pre-contraction state.

**D — False.** The eel uses the two sensory channels for different spatial tasks. Mechanoreceptors detect the water disturbance caused by the corpse's electrically induced twitch, revealing that prey is present nearby, but that mechanical cue does not identify the exact target in this setup. During the subsequent high-voltage volley, electroreceptors detect how a conductive body alters the eel's electric field. The eel's attack on the conductive rod rather than on the corpse shows that this electrical information guides precise localization. The claim reverses those roles.

<a id="part-a-task-43"></a>
## Task 43 — Saiga nasal anatomy, airflow, and movement on snow

**Official answer: A — False; B — False; C — False; D — False.**

### Reasoning

**A — False.** The transverse diagrams do not use the darkest shade as the sole marker of bone. Bony parts of the skull, including parts around the orbital region in the posterior sections, are also represented in lighter gray. Thus identifying every bone simply by selecting only the darkest regions would omit bony structures.

**B — False.** The two nostril openings in section A have a smaller total cross-sectional area than the enlarged nasal passages in section C. For approximately steady airflow through successive parts of the same respiratory passage, conservation of volume gives \(Q=Av\). Therefore, when the available area \(A\) increases in the nasal cavity, the mean linear speed \(v\) decreases: air should move faster through the narrow nostrils and more slowly through the wider cavity. The claimed inequality is reversed.

The official explanation invokes Poiseuille's law here. The conclusion agrees with the key, but the most direct justification for comparing mean speeds at two serial cross-sections is the continuity relation \(Q=Av\); Poiseuille's law instead relates pressure drop, resistance, and flow in an idealized tube.

**C — False.** The leader lines marked “wy” in sections D and E point to the tongue in the oral cavity, not to a dust-filtering component of the nasal airway. The tongue's principal roles include manipulating food, taste, and assisting swallowing. Airborne particles are trapped mainly by nasal hairs and mucus and are then moved by cilia, so dust removal is not the main function of the indicated structure.

There is a label discrepancy in the official material: the question and figure call the structure “wy,” whereas the embedded official explanation calls it “l” and identifies it as the tongue (*lingua*). The location indicated by the leader lines is consistent with a tongue, and the official **False** answer is preserved.

**D — False.** On firm, open ground a saiga's stated maximum speed of 75–80 km/h greatly exceeds a wolf's 40–45 km/h, favoring escape. Snow changes that comparison because the saiga places \(500/160=3.125\) times as much weight on each unit area of support as the wolf. It therefore tends to sink farther into snow and be slowed more severely, while the wolf's lower load per unit area lets it travel over snow more effectively. Wolves should consequently have greater hunting success in snowy winter than in summer, opposite to the statement.

<a id="part-a-task-44"></a>
## Task 44 — TLR7/8 activation and swim-up separation of X- and Y-bearing sperm

**Official answer: A — False; B — True; C — True; D — True.**

### Reasoning

**A — False.** R848 activates TLR7/8 in the receptor-expressing, X-bearing sperm. In Figure 2A, adding R848 lowers their straight-line velocity rather than raising it: at both 2 mM and 10 mM glucose, the R848 group has a significantly lower VSL than its untreated control. Activation therefore reduces progressive motility under the conditions in which a significant effect is detected.

**B — True.** The upper layer of a swim-up assay contains the sperm that moved upward most effectively, so it is the high-mobility fraction. After R848 treatment, Figure 2B shows that this fraction is about 90% Y-bearing sperm, and Figure 2C shows that IVF with the upper-layer sperm produces about 90% XY embryos. Because an egg supplies an X chromosome, an XY embryo must have been fertilized by a Y-bearing sperm. The plotted proportion is therefore clearly greater than 80%.

**C — True.** TLR7/8 is associated with the X chromosome, so R848 selectively slows the X-bearing sperm. The relatively unaffected Y-bearing sperm preferentially reach the upper layer, whereas more X-bearing sperm remain in the lower layer. This is supported both by the direct sperm counts in Figure 2B and by the embryo sexes in Figure 2C: the upper fraction yields mostly XY embryos, while the lower fraction yields mostly XX embryos. Thus receptor activation combined with swim-up can enrich the two fractions for different sex-chromosome-bearing sperm, although the separation is not perfect.

**D — True.** At 0 mM glucose in Figure 2A, R848-treated sperm have a somewhat lower mean VSL than controls, but there is no asterisk, so that difference is not statistically significant. At 2 mM and 10 mM glucose, the R848 bars are marked with asterisks and are significantly below their corresponding controls. In these data, a statistically significant effect of TLR7/8 activation is therefore seen only when glucose is present. The embedded official explanation states this point only tersely, but the significance markings in the graph support the official answer.

<a id="part-a-task-45"></a>
## Task 45 — Endothelial cells, FGF-2, and perfusion of engineered cardiac tissue

**Official answer: A — True; B — False; C — True; D — False.**

### Reasoning

**A — True.** In Figure 1B, the EC-negative sheets contain little or no endothelial staining within the cardiac cell sheet, whereas the EC-positive sheets contain endothelial cells extending through the sheet and forming vessel-like, lumen-containing structures. Co-cultured endothelial cells can therefore organize into a microvascular network and connect with the underlying vascular bed, increasing vascular development in the engineered tissue.

**B — False.** FGF-2 is pro-angiogenic: it promotes endothelial-cell migration and proliferation rather than inhibiting them. This is consistent with the comparison between the two EC-positive samples in Figure 1B. With FGF-2, endothelial staining is more extensive and organized throughout the cell sheet than it is without FGF-2, indicating enhanced vascular growth and connection to the vascular bed.

**C — True.** At late times in Figure 1C, the EC(−) FGF(+) curve reaches a plateau of roughly \(1.6\text{–}1.7\times10^8\) photons s\(^{-1}\), above the roughly \(1.3\times10^8\) photons s\(^{-1}\) plateau of EC(+) FGF(−). Once luciferin delivery has equilibrated, the plateau signal is interpreted as reflecting the number of surviving luciferase-expressing cardiac cells. Given the statement's assumption of equal proliferation rates (and equal starting cell numbers), the higher plateau implies better survival in EC(−) FGF(+) tissue. This is the official interpretation, although strictly the inference also requires comparable luciferase expression and non-limiting luciferin at the plateau; those controls are not stated explicitly in the task.

**D — False.** Direct diffusion alone cannot explain the especially rapid, high signal in EC(+) FGF(+) tissue. If diffusion through the stacked tissue layers were the main route, the EC-negative tissues should show a similarly prompt response, but their curves begin rising much later. The dense endothelial network in the EC(+) FGF(+) sheet instead provides a perfusable route from the vascular bed, rapidly carrying luciferin into the tissue. Direct diffusion may still contribute, but transport through the newly connected vessels is the main explanation for the fast increase.

<a id="part-a-task-46"></a>
## Task 46 — Optogenetic control of hippocampal neurons with channelrhodopsin-2

**Official answer: A — False; B — False; C — True; D — True.**

### Reasoning

**A — False.** During each one-second illumination in Figure 1A, the neuron first depolarizes strongly but then fires only intermittent, variably timed groups of spikes while the light remains on. A maximum firing frequency would impose a minimum interval between spikes; it does not by itself explain these long, irregular pauses. Figure 1C also shows that closely spaced, separate light pulses can evoke successive action potentials reliably. The pattern under continuous illumination is therefore not evidence that the neuron has simply reached its firing-rate ceiling. Sustained ChR2 activation can instead produce a declining photocurrent and neuronal accommodation or depolarization block, in which persistent depolarization promotes sodium-channel inactivation and potassium-current activation. The experiment does not separate those possible mechanisms, but it does not support the claimed firing-frequency explanation.

**B — False.** In the upper trace of Figure 1C, four 10-ms light pulses are delivered at the same spacing. The first three initiate action potentials, whereas the fourth produces a depolarization that remains below threshold. In the lower trace, increasing the pulse duration to 15 ms allows all four pulses, including the fourth, to initiate action potentials. The longer pulse keeps ChR2 open longer, admits more net inward positive charge, and lets the membrane reach threshold. The pulse onsets are separated by tens of milliseconds, much longer than the brief absolute refractory period following a neuronal action potential, and a fourth spike is possible at the same spacing in the 15-ms series. Thus the fourth failure in the 10-ms series reflects insufficient excitation under the neuron's current state, not absolute refractoriness. Strictly, the embedded official explanation's observation that the fourth pulse depolarizes the membrane is not by itself enough to exclude an absolute refractory period, because an imposed current can still change voltage while sodium channels are unavailable; the timing and the 15-ms comparison are the stronger evidence for the official **False** answer.

**C — True.** If ChR2 passed only sodium, opening it at a neuron's negative resting potential would drive sodium inward because the membrane potential is far below the sodium equilibrium potential, causing depolarization. If it passed both sodium and potassium, potassium would tend to leave the cell, but its outward driving force at rest is much smaller than sodium's inward driving force. A nonselective Na⁺/K⁺ channel consequently has a reversal potential near 0 mV, well above the resting potential. Opening such a channel therefore still produces a net inward cation current and moves the membrane potential upward. Selectivity affects the size and reversal potential of the photocurrent, but both proposed selectivities yield light-induced depolarization.

**D — True.** An action potential is an all-or-none response: once a light pulse supplies enough ChR2 current to cross threshold, a range of still longer pulse durations can also initiate a spike. Producing a subthreshold depolarization requires the pulse to stay on the non-spiking side of that threshold, while still being long enough to give a detectable and reproducible response. Figure 1C illustrates how narrow this boundary can be: 10-ms pulses can leave the fourth response subthreshold, whereas 15-ms pulses make every response suprathreshold. Consistently obtaining subthreshold responses therefore requires finer control of pulse length than merely ensuring that an action potential is triggered.

<a id="part-a-task-47"></a>
## Task 47 — Cost of transport and the energetics of animal locomotion

**Official answer: A — False; B — False; C — False; D — True.**

### Reasoning

**A — False.** A bird beginning flight and remaining airborne at its lowest viable forward speed must still generate enough lift to support its body, using powerful and metabolically expensive flight-muscle contractions. A similarly sized cod is supported by buoyancy and, at a low swimming speed, has a lower locomotor demand. The bird therefore would not be expected to have the lower oxygen consumption proposed in the statement. This is a qualitative comparison—the supplied graph contains cod data only—but it is the biological comparison used by the official key.

**B — False.** For the fitted cod relationship

\[
\mathrm{COT}(V)=0.17-0.22V+0.14V^2,
\]

the minimum occurs where its derivative is zero:

\[
\frac{d(\mathrm{COT})}{dV}=-0.22+2(0.14)V=0,
\qquad
V=\frac{0.22}{0.28}\approx 0.786\ \mathrm{km\,h^{-1}}.
\]

Because the coefficient of \(V^2\) is positive, this stationary point is a minimum. Thus the minimizing speed is about \(0.79\ \mathrm{km\,h^{-1}}\), not \(0.6\ \mathrm{km\,h^{-1}}\). The velocity units in the fitted equation are km/h, even though the figure's horizontal axis is labelled m/s.

**C — False.** A horse uses distinct gaits such as walking, trotting, and galloping. Each gait has its own cost-of-transport curve and an energetically favourable speed near that curve's minimum. Horses should therefore spend disproportionate amounts of time near several preferred speeds and change gait rather than use every intermediate speed equally. Sampling many horses over a week would consequently give a broad, multimodal speed distribution, with gait-associated peaks, rather than placing all observations in one narrow range.

**D — True.** A swimming cod must overcome water drag, which rises strongly with speed; the mechanical power and oxygen consumption needed to swim therefore rise increasingly steeply, as the upward-curving plot shows. For a terrestrial runner at ordinary speeds, air resistance is comparatively small, and the energy used per unit distance is approximately constant within a gait. Oxygen use per unit time is then roughly proportional to speed, so its oxygen-consumption-versus-velocity relationship is more nearly linear than the cod's.

<a id="part-a-task-48"></a>
## Task 48 — Helium-dilution measurement of residual lung volume

**Official answer: A — True; B — False; C — True; D — True.**

### Reasoning

**A — True.** The patient is connected just after an ordinary expiration, when the lungs contain the functional residual capacity, \(\mathrm{FRC}=\mathrm{ERV}+\mathrm{RV}\), and the spirometer contains \(V_s\). At the end, a maximal forced expiration leaves only RV in the lungs. The additional volume transferred from the lungs to the spirometer is therefore ERV, so

\[
V_{sf}=V_s+\mathrm{ERV}.
\]

The intervening tidal breaths mix the helium but do not create a net volume transfer once the patient returns to the same end-expiratory level.

**B — False.** Helium is neither absorbed into the blood nor lost from the closed lung–spirometer system, so its initial and final amounts are equal. Writing concentrations as volume fractions gives

\[
C_1V_s=C_2(V_{sf}+\mathrm{RV}),
\qquad
\mathrm{RV}=\frac{C_1V_s}{C_2}-V_{sf}.
\]

For Patient 2,

\[
\mathrm{RV}
=\frac{(0.10)(5.0\ \mathrm L)}{0.080}-5.6\ \mathrm L
=6.25\ \mathrm L-5.6\ \mathrm L
=0.65\ \mathrm L=650\ \mathrm{mL}.
\]

Thus 750 mL is not the measured RV. (The embedded official explanation accidentally labels this Patient 2 calculation as “RV1,” but its numerical result is 650 mL.)

**C — True.** Applying the same helium balance to the healthy control and Patient 1 gives

\[
\mathrm{RV}_{\text{control}}
=\frac{0.50}{0.068}-6.1
\approx1.253\ \mathrm L,
\qquad
\mathrm{RV}_{1}
=\frac{0.50}{0.065}-5.6
\approx2.092\ \mathrm L.
\]

From statement A, their expiratory reserve volumes are \(6.1-5.0=1.1\ \mathrm L\) and \(5.6-5.0=0.6\ \mathrm L\), respectively. Hence

\[
\mathrm{FRC}_{\text{control}}\approx1.253+1.1=2.353\ \mathrm L,
\qquad
\mathrm{FRC}_{1}\approx2.092+0.6=2.692\ \mathrm L.
\]

Because total lung capacity satisfies \(\mathrm{TLC}=\mathrm{FRC}+\mathrm{IC}\), an inspiratory capacity unchanged from the control makes Patient 1's TLC about \(2.692-2.353=0.339\ \mathrm L\) larger. Patient 1's increased RV is therefore consistent with an increased total lung volume, even after accounting for the simultaneous 0.5 L decrease in ERV. The official answer interprets “inspiratory capacity is constant” as unchanged relative to the control.

**D — True.** Patient 2 has \(\mathrm{ERV}=5.6-5.0=0.6\ \mathrm L\) and, from B, \(\mathrm{RV}=0.65\ \mathrm L\), so its measured FRC is only \(1.25\ \mathrm L\). The control values are \(\mathrm{ERV}=1.1\ \mathrm L\), \(\mathrm{RV}\approx1.253\ \mathrm L\), and \(\mathrm{FRC}\approx2.353\ \mathrm L\). Thus Patient 2 has both a smaller forced-expiratory contribution to the spirometer and a much smaller helium-accessible residual volume; correspondingly, the helium is diluted less and its final concentration is higher (8.0% rather than 6.8%). Partial collapse of one lung in a pneumothorax reduces ventilated lung volume and can also leave regions that do not communicate with the helium mixture, producing this same qualitative pattern.

The official explanation says such a patient would have only one functioning lung, which is stronger than the question's “incomplete lung collapse” warrants. A partially collapsed lung may retain some ventilation, and helium dilution measures only communicating gas. These qualifications do not change the expected direction of the measurements or the official True answer.

<a id="part-a-task-49"></a>
## Task 49 — Esophageal Doppler monitoring, blood-flow velocity, and cardiac output

**Official answer: A — True; B — False; C — True; D — True.**

### Reasoning

**A — True.** Each systolic velocity waveform represents ejection during one heartbeat. Tachycardia means more heartbeats per minute, so the cardiac-cycle period, \(T=60/\mathrm{HR}\), becomes shorter. The onset-to-onset or peak-to-peak interval between successive Doppler waveforms therefore decreases (as does the intervening time available for diastole).

**B — False.** Greater arterial resistance increases the load opposing ventricular ejection. If the heart does not compensate by generating a larger pressure difference or changing its contractility, the relation \(Q=\Delta P/R\) predicts a lower flow rate. Because mean flow velocity satisfies \(v=Q/A\), an unchanged aortic cross-sectional area then also gives a lower, not higher, peak velocity. The embedded official explanation describes the increased load in terms of high arterial pressure even though the statement specifies high arterial resistance; these quantities are not identical, but the explicit absence of cardiac compensation supports the same **False** conclusion.

**C — True.** Rearranging the supplied Doppler equation gives

\[
v=\frac{\Delta f\,c_s}{2f_0\cos\theta}.
\]

Using \(\Delta f=4.4\ \mathrm{kHz}=4.4\times10^3\ \mathrm{s^{-1}}\), \(c_s=1540\ \mathrm{m\,s^{-1}}\), \(f_0=4.0\times10^6\ \mathrm{s^{-1}}\), and \(\cos\theta=\sqrt{2}/2\),

\[
v=
\frac{(4.4\times10^3)(1540)}
{2(4.0\times10^6)(\sqrt2/2)}
\approx 1.20\ \mathrm{m\,s^{-1}}
=120\ \mathrm{cm\,s^{-1}}.
\]

Thus a maximum frequency shift of \(4.4\ \mathrm{kHz}\) corresponds to a peak blood velocity of about \(120\ \mathrm{cm\,s^{-1}}\).

**D — True.** One triangular systolic waveform extends from \(1/3\) s to \(2/3\) s, so its base is \(1/3\) s and its height is \(100\ \mathrm{cm\,s^{-1}}\). Its velocity–time integral, which is the distance advanced by the blood during one beat, is

\[
\mathrm{VTI}=\frac12\left(\frac13\ \mathrm{s}\right)
\left(100\ \mathrm{cm\,s^{-1}}\right)
=16.67\ \mathrm{cm}.
\]

Figure 1A gives an aortic diameter of \(2.5\ \mathrm{cm}\), hence a radius of \(1.25\ \mathrm{cm}\) and cross-sectional area

\[
A=\pi r^2=\pi(1.25\ \mathrm{cm})^2\approx4.91\ \mathrm{cm^2}.
\]

The stroke volume represented by one waveform is therefore

\[
\mathrm{SV}=A\times\mathrm{VTI}
\approx(4.91)(16.67)
=81.8\ \mathrm{cm^3}=81.8\ \mathrm{mL}.
\]

Successive waveforms are one second apart (for example, their onsets are at \(1/3\) s and \(4/3\) s), giving a heart rate of \(60\ \mathrm{min^{-1}}\). Hence

\[
\mathrm{cardiac\ output}
=(81.8\ \mathrm{mL\,beat^{-1}})(60\ \mathrm{beats\,min^{-1}})
\approx4908\ \mathrm{mL\,min^{-1}}
=4.9\ \mathrm{L\,min^{-1}}.
\]

This result uses the figure's intended idealizations: \(2.5\ \mathrm{cm}\) is treated as the aortic diameter, the cross-section as circular and constant, and the plotted velocity as representative across that cross-section.

<a id="part-a-task-50"></a>
## Task 50 — Renal countercurrent multiplication and vasa recta exchange

**Official answer: A — False; B — True; C — False; D — True.**

### Reasoning

**A — False.** In Figure 1A, the imposed pressure $P$ produces bulk water flow across the semipermeable membrane, so the immediate driving force is a hydrostatic-pressure difference. Water leaves the water-permeable descending limb of the loop of Henle by osmosis, down a water-potential gradient created by the hyperosmotic medullary interstitium. That gradient is generated chiefly by NaCl reabsorption from the water-impermeable ascending limb, together with urea recycling; the ascending limb itself does not allow appreciable water movement. The two examples therefore do not have the same primary driving force. The embedded official explanation describes renal water movement as secondary active transport following sodium, but that wording is physiologically inaccurate: sodium transport helps establish the gradient, whereas water crosses passively by osmosis.

**B — True.** The figure shows that fluid in the descending limb (1) and collecting duct (3) can have different osmolarities at the same medullary depth. The labelled values are 1100 versus 560 mOsmol kg⁻¹ at the middle level, a difference of $1100-560=540$ mOsmol kg⁻¹, and 2000 versus 1600 mOsmol kg⁻¹ near the bend, a difference of $2000-1600=400$ mOsmol kg⁻¹. NaCl has been reabsorbed from the tubular fluid, especially in the ascending limb and then in distal nephron segments, before and during its passage through the collecting duct. Consequently, collecting-duct fluid need not match descending-limb fluid at the same depth. The official answer attributes the difference specifically to sodium reabsorption in the collecting duct; that is a simplified account, because collecting-duct osmolarity also depends strongly on ADH-controlled water permeability and urea handling, and much of the relevant NaCl removal occurs earlier in the nephron.

**C — False.** At region Q, Figure 1B labels the descending-limb and collecting-duct fluids as 290 mOsmol kg⁻¹, while the dilute ascending-limb fluid is 100 mOsmol kg⁻¹. For the interstitium to draw water out of a tubule containing fluid at 290 mOsmol kg⁻¹, its effective osmolarity must be slightly greater than 290 mOsmol kg⁻¹, not strictly between 100 and 290. If it were below 290, the osmotic gradient would instead favour water entry into that tubule. This is the dynamic interpretation used by the official key; the diagram does not directly label the interstitial value, and exactly 290 would give no net osmotic water flow.

**D — True.** The red descending vasa recta receives near-isosmotic arterial blood at about 290 mOsmol kg⁻¹, whereas the returning blue limb is labelled 250 mOsmol kg⁻¹ near Q. Thus, on the values and flow directions intended by the diagram, blood entering the vasa recta at Q has the higher concentration: $290-250=40$ mOsmol kg⁻¹. As blood descends, it loses water and gains medullary solute; on ascending, it gains reabsorbed water and loses solute, so countercurrent exchange limits washout of the medullary gradient. The official explanation's suggestion that this concentration difference by itself implies indefinite sodium accumulation is not a valid steady-state mass-balance argument: osmolarity is a concentration, and solute transport also depends on blood volume and flow. The numerical comparison in the supplied figure nevertheless supports the official **True** answer.
