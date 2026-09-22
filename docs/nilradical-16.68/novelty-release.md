# Literature and contribution scope

This is a publication summary of the recorded 21 September 2026 audits and a bounded primary-source refresh on 22 September. It separates the proved results from historical priority.

A suitable contribution statement is: **an elementary proof of the complex case and an explicit counterexample for the real case of Kourovka 16.68, with complete Lean verification; the compact SO₃(ℝ) negative answer is due to Andreas Thom.** No absolute priority claim is made. The recorded human approval concerns the Lean statements; it supplies no separate novelty or contribution decision.

## Established ingredients

- Schneider–Thom, [Lemma 1](https://arxiv.org/html/1802.09289v1), provides the established elementary-matrix trace specialization and its nonzero leading coefficient.
- Mushkarov–Nikolov, [Example 1(iii), p. 38](https://ems.press/content/serial-article-files/52191), gives the elementary polynomial observation underlying the two exceptional trace values. The formalized polynomial-matrix curve argument is proved in the project itself.
- Gordeev–Kunyavskii–Plotkin, [Proposition 2.6](https://arxiv.org/html/1808.02303v1), guarantees split semisimple values over the reals. Its stronger semisimple conclusion assumes an involution is already attained. The real counterexample concerns precisely an omitted involution.
- Thom's [Corollary 1.2](https://arxiv.org/html/1003.4093v3) gives arbitrarily small nontrivial word images in unitary groups. Its restriction to SO₃(ℝ) yields the known compact negative answer, which is not claimed as new or included in these Lean endpoints.

## Recorded 21 September searches

The complex audit screened the 177 records reported by its broad arXiv query, inspected the closest statements and proofs, checked official Notebook material and public code, and examined supplementary DOI metadata. It found no earlier complete all-word PSL₂(ℂ) theorem in the sources inspected. This is not a claim that every screened item was read in full, nor that all relevant work was retrieved.

The final real-word audit examined the concrete 44-letter word and its universal real trace bound, current official sources, good-word and trace-polynomial literature, recent papers and public code. It found no earlier real projective counterexample or earlier proof of this word's asserted trace restriction in the inspected sources. The finite comparisons with published trace-polynomial tables did not exhaust substitutions, trace-equivalent words or automorphism orbits.

The Mycielski originals, the final Marshall–Martin chapter and the full 2026 Gordeev–Plotkin author manuscript had access gaps. Private, unindexed or inaccessible work remains outside the recorded search. These boundaries prevent turning a failure to locate earlier work into an absolute novelty certificate.

## Bounded publication refresh: 22 September 2026

The editors' [current Notebook PDF](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/21tkt.pdf), p. 102, was reopened. It still gives Mycielski's three branches without a solution annotation. [arXiv:1401.0300](https://arxiv.org/abs/1401.0300) still identifies v46, dated 1 September 2026. Annotation history alone is not global open-status evidence.

The established ingredients above were reread in their primary sources. The relevant newer work remained outside the exact claims here: Alekseev–Schneider's [Theorem 19 and Corollary 21](https://arxiv.org/html/2609.09058v1) concern image dimensions of words with constants; Bandman–Kunyavskii–Skorobogatov's [Theorem 3.2](https://arxiv.org/html/2504.15461v2) concerns conic bundles for noncentral semisimple targets; and [Jezernik–Sánchez](https://arxiv.org/abs/2101.12534) treats a restricted double-commutator family. The current arXiv metadata dates the Bandman–Kunyavskii–Skorobogatov v2 to 12 June 2026.

The public [JUrban/kour1 note](https://github.com/JUrban/kour1/blob/dce7931e980c7db83100a07fbe084fc1dd655fdb/research/16.68-16.69-prior-results.md) remained at its checked 19 September commit and left the projective cases unresolved in that project. The full [Gordeev–Plotkin author PDF](https://u.math.biu.ac.il/~plotkin/papers/RELATION_Final111_Zh.pdf) remained inaccessible; only the indexed introduction could be checked. Exact-target web searches were noisy and provide weak negative evidence.

No new competing full-scope result surfaced in this bounded refresh. The mathematical correctness claims rest on the proof and verification records; this literature assessment does not replace them.
