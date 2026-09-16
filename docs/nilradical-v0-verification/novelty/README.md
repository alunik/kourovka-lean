# Nilradical v0: bounded novelty and competing-solution audit

Checked on 16 September 2026. This is a primary-source and public-chronology review of the seven proposed v0 records. It does not certify absolute priority, mathematical correctness of every cited paper, or completion of the separate Lean verification gate.

**Disposition: retain six records after the bounded literature check; exclude 21.99 from the first-solution catalogue because a complete competing solution exists and priority remains unresolved.** No earlier complete solution was established for the other six in the bounded searches below. Problem 21.29 remains outside this audit and outside Nilradical credit; its Thomas–Rizzoli record must remain unchanged.

| Problem | Catalogue disposition | Evidence-based qualification |
| --- | --- | --- |
| 21.3, first question | Retain, bounded literature check passed | No competing solution located. The official repository links this same project’s solution; the original paper states the assertion as Conjecture 2. |
| 21.38 | Retain, credit prior generation theorem prominently | The conclusion is a short corollary of substantial published generation theory plus a fixed-point argument. No earlier explicit spread-one solution located. |
| 21.40 | Retain, bounded literature check passed | Earlier structural results assume solubility, virtual nilpotence, finite rank, residual finiteness, or finite generation. They do not settle the full statement. |
| 21.44 | Retain, bounded literature check passed | Brieussel's cited intermediate-growth construction requires local degrees at least 29. Woryna's degree-five-compatible construction has exponential growth. |
| 21.68 | Retain, bounded literature check passed | Kida supplies the order-96 complement/subgroup pair; his order-192 example disproves the converse. The official repository links this same project’s solution. |
| 21.99 | Exclude from first-solution catalogue | Muliarchyk gives a complete independent negative solution. Available dates do not establish which public solution came first. Preserve the separate local formalization. |
| 21.106 | Retain, bounded literature check passed | The original and subsequent papers give positive partial results and still formulate the question; no earlier full counterexample located. |

## 21.99: the confirmed competing solution and unresolved priority

The [official Notebook repository](https://kourovkanotebookorg.wordpress.com/repository/) links to Kyrylo Muliarchyk, [*A counterexample to Problem 21.99 of the Kourovka Notebook*](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_21.99_solution.pdf). **Theorem 1** supplies a faithful transitive soluble action of degree **23,437,500**, with two distinct points whose entire transporter consists of elements fixing exactly one point. This is the complete negation of the local `NotebookStatement`, not a special-case positive result or a different problem. Sections 2–4 construct the action and cover every transporter through the fixed-block calculation. I read the four-page paper, including that calculation. It is a different, smaller construction than the local degree-36,621,093,750 witness; smaller degree itself says nothing about priority.

The relevant chronology is:

| UTC time | Evidence | What it establishes |
| --- | --- | --- |
| 9 Sep 2026, 20:22:21 | [GitHub commit b6b1b690](https://github.com/alunik/kourovka-lean/commit/b6b1b69015bdf15c35e3def25b8ac236c7beef40) | The local solution's recorded commit time, while the repository was private. |
| 9 Sep 2026, 20:22:35–21:08:54 | [GitHub Actions run 34400649810](https://github.com/alunik/kourovka-lean/actions/runs/34400649810) | A recorded CI run, also while private. |
| 10 Sep 2026, 07:54:33.775 | Original saved tool output | `gh repo view` reported `PRIVATE`. |
| 10 Sep 2026, 07:54:42.218 | Original saved command and successful tool output | Visibility was changed to `PUBLIC` and immediately verified. This is the verified public-release event. |
| 10 Sep 2026, 08:45:52 | Live HTTP `Last-Modified` for Muliarchyk's PDF | The timestamp of the currently served file version, about 51 minutes after the verified public-release event. It is not a first-publication certificate. |
| 11 Sep 2026 | Existing local posting-status audit | Muliarchyk's paper was already linked from the official repository by that check. |

The Muliarchyk PDF has no internal date or version history. A replaced file, earlier draft, earlier public posting, or private communication is not resolved by its present server header. Conversely, private Git history must not be described as an earlier public solution. **Neither “Muliarchyk solved it first” nor “our public solution was first” is established by this audit.**

The catalogue applies a first-solution admission policy. Its exclusion wording is: **“Excluded: a complete independent solution by Kyrylo Muliarchyk is available in the official Notebook repository; priority is unresolved.”** This does not withdraw the correctness or independent construction of the local Lean proof.

Exact sanitized timestamp evidence is in [publication_chronology.json](publication_chronology.json); the original research archive preserves the fetched sources and metadata. A recorded repository-visibility operation establishes the public-release time.

## 21.3: retain the first question only

Anagnostopoulou-Merkouri–Burness, [*On the regularity number of a finite group and other base-related invariants*](https://arxiv.org/abs/2405.15300), was submitted **24 May 2024**, revised **27 October 2024**, and has no later arXiv version listed. [Conjecture 2 in v2](https://arxiv.org/html/2405.15300v2#S1.Thmconjecture2) is the eventual assertion for arbitrary pairs of soluble subgroups. Their theorem for soluble **maximal** subgroups at degree at least 17 does not cover arbitrary soluble subgroups. The subsequent threshold-21 speculation is stronger than the local endpoint.

The current official [21.3(a) solution](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_21_3a.pdf) is this project’s *The soluble-intersection limit in Sn*, dated **11 September 2026**. Theorem 1.1 and the alternating corollary match the catalogue's eventual scope. This is not an independent competing solution. Focused problem-number and soluble-intersection searches located no other full solution. The source's narrower maximal-subgroup theorem and older counting inputs must not be presented as new contributions.

## 21.38: retain the corollary with explicit prior credit

Gili Golan-Polak's [*Thompson's group F is almost 3/2-generated*](https://arxiv.org/abs/2210.03564) has **v1, 7 October 2022**, and a 2023 journal publication. I read [Theorem 2 and Proposition 16(1)](https://arxiv.org/html/2210.03564v1). For nonidentity `f`, prescribed endpoint exponents `(c,d)` with both nonzero give a companion generating the full inverse image of the lattice generated by the two endpoint vectors. Taking `(c,d)=(1,1)` directly supplies spread at least one for the diagonal subgroup, including inputs in `F'`.

Her [2024 spread paper](https://arxiv.org/abs/2402.19444), **v1, 29 February 2024**, still expressly treats existence of an infinite group of spread exactly one as unknown. Its [Lemma 2 and Remark 11](https://arxiv.org/html/2402.19444v1) contain the relevant fixed-point obstruction and the observation that endpoint exponents with nonnegative product force an interior fixed point. Those ingredients give the local upper-bound argument after specializing to the diagonal subgroup and two disjointly supported elements.

The first paper does not explicitly conclude ordinary spread exactly one for that subgroup, and the second does not record that corollary. The potentially new contribution is identifying and proving the **ordinary-spread-one conclusion**, not the generation theorem or fixed-point principle. No explicit earlier full solution was found in the current official repository, the two current arXiv records, or targeted searches. This is a bounded “no prior conclusion located” finding, not a claim that the result is conceptually independent of those papers.

## 21.40: retain the unrestricted rational-linear theorem

The literal statement has no finite-generation, finite-rank, or solubility hypothesis. The following theorem statements were checked at source:

- Bastos–Dantas–de Melo, [2019 preprint / 2020 journal paper](https://arxiv.org/pdf/1908.01375v1), **Theorem A, p. 2**: assumes solubility and finite rank.
- The same authors, [2020 preprint / 2021 journal paper](https://arxiv.org/pdf/2008.10800v1), **Theorem 1.2, p. 2**, and **Corollary 1.3, p. 3**: assume virtual nilpotence, or virtual solubility and finite rank.
- Dantas–de Melo–Kato, [online 14 November 2025 / 2026 issue](https://doi.org/10.1080/00927872.2025.2578695), **Theorems 1.1–1.3, p. 2342**: assume mixed order, solubility or metabelianity, finite rank, and four or five orbits. The user-supplied publisher PDF's introduction and all three statements were read afresh; the existing full-article review was also checked.
- Dantas–de Sousa, [3 May 2026, v1](https://arxiv.org/html/2605.02090v1), **Theorems A–C**: concern residually finite groups, finitely generated locally graded groups, and specified rational nilpotent completions.
- De Melo–Kato, [10 October 2025, v1](https://arxiv.org/html/2510.09353v1): concerns full unitriangular groups and motivates broader classification; it does not assert the arbitrary rational-linear implication.

These assumptions cannot be silently added to `G ≤ GL_n(Q)`. For example, `(Q,+)` is rational linear with two automorphism orbits and is not residually finite. The later finite-generation theorem therefore leaves precisely an essential part of the local scope untouched. The current official repository and focused rational-linear/automorphism-orbit searches produced no competing full solution. The longer local [context audit](../../21.40-context.md) records additional earlier literature checks, whose search scope is broader than this fresh recheck.

## 21.44: retain the exact degree-five result

Brieussel's [doctoral thesis](https://imag.umontpellier.fr/~brieussel/these_brieussel.pdf), defended **29 September 2008**, contains the primary author version of the method published in [Math. Z. 263 (2009), 265–293](https://doi.org/10.1007/s00209-008-0417-3). I read the hypotheses surrounding **Propositions 3.6.1, 3.6.3 and 3.6.6** and **Remark 3.6.7**, printed pp. 76–80. The group is defined using eligible generator pairs in alternating groups with **every local degree at least 29**. Its intermediate-growth theorem does not specialize to the natural degree-five action.

[Woryna's 2015 paper](https://link.springer.com/article/10.1007/s10801-015-0584-3), **Corollary 2**, does apply to the natural `A5` action but expressly constructs an amenable subgroup of **exponential** growth. Amenability and contraction do not supply the required subexponential-growth conclusion.

Eberhard–Maini–Sabatini–Tracey, [arXiv:2604.15303](https://arxiv.org/abs/2604.15303), **v1 16 April 2026; v2 17 April 2026**, repeats the exact degree-five question at the end of **§9**, including in [current v2](https://arxiv.org/html/2604.15303v2). Its lower growth restriction leaves subexponential growth near exponential possible. Thus the checked predecessors supply methods and related constructions, not an earlier full solution to 21.44. No competing exact-degree-five solution was located by the bounded current search.

## 21.68: retain; distinguish the direction of Kida's examples

Kida, [*On semiabelian groups*](https://doi.org/10.1515/jgth-2024-0010), was published online **9 November 2024**, in the 2025 volume. I read **Conjecture 1.3**, **Theorem 1.4**, and the discussion on **p. 710** in the [open article](https://d-nb.info/1364524341/34). The conjecture is semiabelian implies monomial. The order-192 example is monomial but not semiabelian, so disproves the **converse**. The order-96 semiabelian group containing `SL2(3)` is prior input to the local construction, not itself the required nonmonomial semiabelian example.

The official [21.68 solution](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_21_68.pdf) is this project’s order-2592 theorem, dated **11 September 2026**; its own text credits Kida's complement/subgroup pair. No other full counterexample was found in the current repository or focused semiabelian/monomial searches. Neither minimal order nor originality of the general character-transfer mechanism is established by this audit.

## 21.106: retain the formula counterexample

Conte–Petschick, [*Conciseness of first-order formulae*](https://arxiv.org/abs/2505.01411), **v1 2 May 2025**, asks the residually finite question as **Question 1**. The [journal version](https://link.springer.com/article/10.1007/s00605-025-02127-5), published online **15 October 2025**, retains that question. I read the question, parameter-free convention and existential-formula theorem in both versions. That theorem is **1.2 in the preprint**, **1.1 in the journal**, and does not cover the local existential–universal–existential formula.

Ciobanu–Conte, [*Concise formulae in groups of non-positive curvature*](https://arxiv.org/html/2605.06023v1), **v1 7 May 2026**, still describes positive partial progress on the general question; its results about acylindrically hyperbolic groups and existential formulas do not settle the Heisenberg construction. Neither paper records the displayed two-value counterexample. Current official-repository and targeted conciseness/Heisenberg/problem-number searches found no earlier full solution. This statement concerns first-order formulas; the separate word-conciseness problem remains outside the catalogue record.

## Evidence and limitations

All seven local `Statement.lean` files and problem READMEs were read. The prior audit notes were used to identify candidate predecessors, then the major primary theorem statements above were reopened. The research archive retains the fetched primary sources; this public record links their original publishers. The machine-readable decision record is [novelty.json](novelty.json).

Searches included exact problem numbers and source titles, author names, and the relevant mathematical statements. Literal searches sometimes produced irrelevant results; those failures provide weak negative evidence. Search-engine dates and aggregator “open/solved” labels were not treated as priority evidence. The official repository has selective coverage, so absence of a link cannot certify novelty. The WordPress media-list endpoints were unavailable without authorization; they were not bypassed. No authors or editors were contacted. 

Retained records should say **“No earlier complete solution located in the sources checked, as of 16 September 2026”**, rather than claiming established worldwide priority. Their admission also remains subject to the separate correctness and reproducibility gates.
