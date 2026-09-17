> Publication note, 17 September 2026: this report is preserved at its review-time scope. Later technical and human gates passed; see [the current record](README.md). Machine-local path prefixes are removed in this public copy.

# Final independent mathematics review: Kourovka 21.53

**Verdict: PASS.** The assembled constructive matrix argument supplies a counterexample to the exact question in Problem 21.53. I found no unresolved substantive mathematical defect. This accepts the mathematics of the delivered argument; it is not a novelty verdict, protected Lean integrity receipt, human acceptance, or publication authorization.

Reviewer: fresh Codex agent context `/root/constructive_math_review`, 16 September 2026. I did not author either proof or any reviewed Lean module. I authored this report and the separate arithmetic replay only. Coordinator requested GPT-6 Astra, max effort, fresh context; underlying execution setting was not independently verified by this reviewer. I followed the mathematical-review brief in `LOCAL_HOME/.codex/skills/math-research-agent/references/reviews.md`. The separate final semantic and novelty reviews have different owners.

## Snapshot and scope

The governing contract is `verification/contract.json`, SHA256 `e02b24ffc6e1c9c8adb3aa507a9c59de2df762492495f27dd8d788133de257ff`. At 19:50:28 UTC I independently recomputed all **719** source hashes named in that contract: **zero mismatches**. `mathematics-constructive-snapshot.json` records the 168 current Problem2153 Lean source hashes and the following mathematical artifacts. Its SHA256 is `d93843bb5789b3e14cb2702d046f6b8e41aac7bc9701093a7b5161763c02aa3a`.

| File relative to the campaign | SHA256 |
| --- | --- |
| `problem.md` | `6febe3fc5bc84e193c328f81e5eb096b549e34a390441fa308728c3fdf2e9b1c` |
| `proof/constructive-matrix-route.md` | `91c22246b5dd928512c61aef115b8aa86e3ca0e734953894ddccc3a3e9994933` |
| `proof/ree-counterexample.md` | `406511b8c977bb4ca5eb9fd3f01943026c30992cbe42e27693e7fc975fc40e71` |
| `lean/structural/sources/Wilson-ReeF4alg.pdf` | `300c3a4d5be9372c393ba2c7da51dd0c3a3bface442e1a532fc6d685b51b0234` |

I read both ordinary proofs and checked the constructive route against the actual group definitions, structural interfaces, finite-data soundness bridges and final instantiation. This is an assembled-argument review, not merely a check that cited source theorems exist. The manifest pins generated modules without implying that every generated multiplication line was manually read. The arithmetic replay independently checks the critical finite families listed below.

The principal manually inspected Lean interfaces are `Core`, `Field8`, `WilsonModel`, `WilsonModel.Sparse`, `RootSystem`, `TorusAction`, `RootRelations`, `RootRelations.Data`, `RootCollection`, `UnipotentFactorization`, `Borel`, `BorelQuotient`, `Triangular`, `Weyl`, `RankOne.CellIdentities`, `RankOne.Orientation`, `RankOne.Radicals`, `RankOne.Nondegenerate`, `Structure.RankOneBruhat`, `BNPair.Construction`, `BNPair`, `External.TitsSystem.Basic`, `External.TitsSystem.Bruhat`, `External.TitsSystem.Coverage`, `AmbientFacts`, `AmbientFacts.Frame`, `AmbientFacts.Frame.Linear`, `Simplicity.Scalar`, `Parabolic`, `ParabolicMaximal`, `NormalGeneration`, `NormalGeneration.Basic`, `NormalGeneration.Identities`, `NormalGeneration.RootSubgroup`, `NormalGeneration.Witnesses`, `Simplicity`, `Simplicity.Concrete`, `Simple`, `BruhatReduction`, `WilsonModel.ClassTests.Base`, `WilsonModel.ClassTests.Centralizers`, `WilsonModel.ClassTests.ProductBase`, `WilsonModel.ClassTests.ProductReduction`, `WilsonModel.ClassTests.Products`, `Endpoint`, and `Final`.

## Exact question

I checked Problems 21.52–21.53 in [the primary Notebook, arXiv:1401.0300v46](https://arxiv.org/pdf/1401.0300v46), printed page 175. The ambient group is finite, nonabelian and simple; the vertices form an entire involution class; labels are the exact integer product orders; and the second retained label is the least odd prime divisor of the ambient order. The question does not require either retained relation to be nonempty. Consequently an empty order-three relation is legitimate here.

`Core.Statement` has those universal quantifiers, standard group orders, a full `IsConj` subtype and permutations of that entire subtype. The ordered-pair implementation agrees with the unordered edges because `ab` and `ba` have the same order. A small-universe concrete witness suffices to refute the mathematical universal claim. The use of a named-group isomorphism, an exact group-order formula, or a classification theorem is unnecessary for this negative resolution.

## Mathematical audit

### Concrete group and finite identities

The field has eight distinct constructors and ordinary proved field operations, agreeing with binary polynomial arithmetic modulo `X³+X+1`. The actual carrier is a subgroup closure inside `GL(26,8)`, not an abstract object supplied with desired properties. The generators and all witnesses are genuine units, with their word membership and inverse identities proved. Finiteness follows from the finite matrix carrier.

The sparse checker is mathematically sound: `rowEval` sums every listed contribution, including repeated indices; `rowEval_dot` proves that its dot product is the ordinary finite sum; and the matrix checker yields standard matrix multiplication. Injectivity of subgroup/units coercions transfers those identities to the same actual group. The Python producers are not hypotheses. My independent replay also aligned all 96 root matrices with the defining torus-conjugate words.

The order-two and order-three elements suffice to show that 2 and 3 divide the group order, and there is no integer prime strictly between them. The certified order-five product of involutions proves noncommutativity. Determinants of the four nondiagonal generators are one because their orders divide 2 or 4 while a nonzero field scalar has order dividing 7; all 49 torus determinants are checked. This justifies the later scalar-kernel argument without assuming special-linearity.

### Collection, rank one and coverage

The proof correctly avoids treating every root curve as a subgroup. The same-curve product and inverse corrections are included. The coordinate selectors are justified by universally quantified finite equalities for every nonzero parameter; the default values of `Option.getD` do not create an unchecked branch. Zero parameters are handled separately by root identity and empty-coordinate cases. Torus covariance carries every representative equality and its support condition to the required parameters.

For the two rank-one subgroups, `RootCollection` explicitly proves the one- and two-parameter covers using product, inverse and commutation laws. All 63 nonzero parameter pairs and seven nonzero scalar parameters occur in the rank-one cell metadata. The proof only needs the implication “nonidentity element has a nonzero parameter tuple,” which follows from the identity tuple; it does not silently require coordinate uniqueness.

The radical normality argument is valid. The distinct-root commutators have zero coordinates 0, 1 and 3, so they belong to both relevant radical subgroups. Reversing the two entries in the commutator gives its inverse, covering either root order. A one-sided conjugation inclusion extends to inverse conjugation because the conjugator has finite order. Thus each rank-one subgroup normalizes its radical and the joins have the claimed product decompositions. This closes the previously potentially dangerous global factorization step.

The orientation argument checks all 16 Weyl representatives for both reflections, using proved root paths, and extends from root generators to their subgroup closures. Its left-versus-right conjugation convention is consistent. In the two-cell proof, the positive orientation absorbs the root factor into `B`; in the negative orientation, a trivial root factor remains in the adjacent cell, and a nontrivial one uses the rank-one identity to enter the original cell. Inversion converts this to the left convention of the Tits-system axiom.

I inspected the concrete construction's generation, intersection normality, quotient generation, involution, two-cell and nondegeneracy fields. The intersection computation uses actual lower triangularity and the finite Weyl list. No field asserts the desired coverage in advance. The vendored abstract Bruhat proof closes the union of `BnB` cells under products and inverses and uses generation to obtain the whole group. Finally, `B=UH=HU`, `N=HW` and torus normalization yield the exact `g=u h w v` form. Full ordered twelve-coordinate coverage and uniqueness are not required by the final dependency path.

### Simplicity

The subgroup `P` is proper because it stabilizes the base line while `s` does not. Equality with the entire line stabilizer is not required. The frame certificate gives actual orbit words for 26 basis vectors and a 27th vector with every coordinate nonzero in that basis. If an element is in the core of `P`, its conjugates lie in `P`, so it fixes every orbit line. The basis lines make it diagonal; the last line equates all diagonal scalars. Its determinant then gives `λ²⁶=1`; field arithmetic gives `λ⁷=1`; coprimality makes it the identity. This proves the core is trivial in the original matrix group, not only in a projective quotient.

Bruhat coverage genuinely proves maximality. A larger subgroup contains a Weyl representative outside `P`, hence outside `{1,r}`. Each of the remaining fourteen Weyl representatives, together with `r`, supplies the longest word. The certified relation `t t^(w₀) t=s` then supplies the missing generator. The argument needs only those two excluded representatives, and does not assume a prior classification of parabolic overgroups.

The normal-generation words start from the last root involution, transport back to `x²`, recover `r`, a torus generator and `x`, and then recover `t`, `s` and the second torus generator. Every use of conjugation occurs inside a normal subgroup. The explicit last-root commutator puts a normally generating element in the derived subgroup, proving perfectness without circular use of simplicity.

The Iwasawa conclusion is complete. For normal `K≤P`, the trivial core forces `K=1`. Otherwise maximality gives `KP=G`. Since `P` normalizes the abelian subgroup `Z`, `KZ` is normal in `G`; normal generation forces `KZ=G`, so `G/K` is abelian. Perfectness forces `K=G`. All premises are discharged for the same concrete group by `ambient_isSimpleGroup_of_coverage` and the proved BN-pair coverage.

### Whole conjugacy class and the changed edge

The witness definitions give `X,Y,A` in one actual ambient conjugacy class, with exact orders `|AX|=5` and `|AY|=7`. Primality plus the nonidentity products establishes exactness, and also puts `A` outside the swapped pair.

The 784 centralizer tests compare actual group commutation against every torus-Weyl representative after correctly removing the second torus parameter using the last root's character `(1,0)`. The 112 last-root/Weyl products are all covered by the 56 representatives: left multiplication of the Weyl word by `r` fixes the conjugated root. Exponents in `{1,2,4,5,7,13}` exclude divisibility by three, which is stronger than the required exclusion of exact order three. The Lean result needs only exponent bounds, not the exploratory exact-order distribution.

The passage from these tables to the whole group is sound. For `g=u h w v`, both unipotent factors centralize `X` and `Y`, giving `Commute(X,g) ↔ Commute(X,hw)` and the analogous statement for `Y`. For the product test, the initial unipotent factor fixes the conjugated root, while the terminal factor conjugates the entire product and hence preserves its order. Simultaneous conjugation reduces the first member of any class pair to `X`, so the order-three relation is empty on the **whole class**, not just the listed representatives.

The transposition exhausts all edge cases: disjoint edges are fixed; the swapped pair is preserved as an unordered pair; and edges containing exactly one swapped vertex preserve commutation because the ambient centralizers agree. For distinct involutions, commutation is equivalent to product order two. The order-three relation is vacuous. The edge `(A,X)` moves to `(A,Y)` and changes label from 5 to 7. `Final.not_statement` applies the proved coverage to the complete endpoint; no unresolved mathematical criterion remains.

## Independent arithmetic and source checks

I wrote and ran `python3 reviews/mathematics-constructive-replay.py` from the campaign, using a fresh polynomial-reduction field implementation and literal final Lean data. No campaign search/generator module is imported. The final run at **19:49:34 UTC** returned `PASS_BOUNDED_REPLAY` in 1.165 seconds. The corresponding JSON receipt records input SHA256 values.

| Family independently replayed | Coverage |
| --- | ---: |
| Root-word/table alignments | 96 |
| Full torus covariance | 4,704 |
| Torus determinants | 49 |
| Reduced inverse/product/commutator/simple-Weyl identities, with support | 207 |
| Rank-one two-cell identities | 70 |
| Centralizer Boolean patterns | 784 |
| Last-root/Weyl product orders | 112 |
| Normal-generation/perfectness identities | 7 |
| Actual projective-frame orbit words | 27, each of length 48 |

The replay also checks the generator orders, nondegeneracy entries, 16 Weyl word matrices and their closure under the two generators, witness product orders, both frame inverse products and the nonzero bridge coordinates. It reproduces the finite product distribution `1:2, 2:68, 4:28, 5:2, 7:6, 13:6`. This is a diagnostic on the delivered tables, not an enumeration of the ambient group or a replacement for the proved whole-group reduction.

I additionally ran `lake env lean Kourovka/Problem2153/Final.lean` in `LOCAL_HOME/notebook/kourovka-lean`. It exited **0** and reported exactly `[propext, Classical.choice, Quot.sound]` for both `whole_class_counterexample` and `not_statement`. This was a direct endpoint source check using the existing imported `.olean` files, not a clean rebuild or protected kernel replay. The command and exact stdout are recorded in `mathematics-constructive-lean-check.json`.

Primary sources inspected live were the Notebook page above; [Wilson's author draft](https://webspace.maths.qmul.ac.uk/r.a.wilson/pubs_files/ReeF4alg.pdf), including the matrix conventions and Theorem 2's Iwasawa route; [Aschbacher–Guralnick–Segev](https://ems.press/content/serial-article-files/29479), Hypothesis 10.1 and Lemma 10.2; and [Revin–Zavarnitsine](https://arxiv.org/pdf/2212.13785), Section 3 and Lemmas 4 and 8. Wilson already proves the underlying Ree simplicity result, and his introduction credits Coolsaet's earlier geometry and generator construction. The added attribution paragraph is consistent with the inspected source.

The original structural proof has the correct elementary assembly: the centralizer formula is independent of the nonidentity root parameter, and a product of two involutions is inverted by either factor. Those published inputs explain its empty order-three relation and equal-centralizer swap. They remain substantial source inputs to that historical route; I have not recursively re-proved the literature on which they depend. The accepted constructive route replaces them with concrete matrix, subgroup and coverage arguments, so their formal availability is not an assumption of the final theorem.

## Limits and disposition

No substantive correction is required for the reviewed constructive proof. The concise writeup necessarily refers to finite data rather than printing every matrix product; the pinned Lean tables and separate replay make those finite assertions inspectable and reproducible.

This review does not establish an exact ambient group order, an isomorphism with a named Ree group, minimality of the counterexample, or a theorem for every field size. None is needed for 21.53. I have not enumerated the full group or full involution class, independently rerun the entire Lean build, or executed the protected Comparator/nanoda integrity procedure. Those are separate receipts and responsibilities. I did not contact authors, publish material, or edit the frozen proof/Lean source. Novelty, attribution approval and final human statement verification remain separate gates.
