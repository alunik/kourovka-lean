# Kourovka 21.53 — whole-class counterexample

The complete Lean theorem is in [Final.lean](Final.lean):

```lean
theorem Kourovka.Problem2153.not_statement : ¬ Statement.{0}
```

It refutes the universal equality asked in Problem 21.53. For one explicitly
constructed finite nonabelian simple matrix group, a permutation of a whole
conjugacy class of involutions preserves product-order colours 2 and 3 while
changing an edge from colour 5 to colour 7. No recognition theorem identifying
the matrix group with a named Ree group is assumed.

The endpoint has compiled with transitive axioms `propext`, `Classical.choice`,
and `Quot.sound` only. Independent mathematical and semantic reviews and the protected
Comparator/Lean/Nanoda integrity gate have passed on the frozen source. The final
novelty search is clear within its recorded scope. Human statement verification
and separate acceptance of the bounded novelty wording were explicitly recorded
on 17 September 2026 against the unchanged source snapshot. This is an accepted
Nilradical v1.0.0 result. Its publication was authorized on 17 September 2026. See the [acceptance and verification
record](../../docs/nilradical-21.53/README.md) and the subsequent
[proof walkthrough](../../docs/walkthroughs/21.53.md).

## Source and interpretation

The question is due to I. B. Gorshkov, in the 21st edition of
[The Kourovka Notebook](https://arxiv.org/abs/1401.0300v46), printed page 175,
with the notation inherited from 21.52. [Core.lean](Core.lean) defines the whole
ambient conjugacy class, exact colour preservation, the two smallest prime
divisors, and the universal assertion. [Endpoint.lean](Endpoint.lean) constructs
the concrete class permutation. [Final.lean](Final.lean) discharges every premise.

## Proof organization

- [Field8.lean](Field8.lean) and [WilsonModel.lean](WilsonModel.lean): the field,
  actual invertible matrices, ambient subgroup, and distinguished witnesses.
- [RootRelations.lean](RootRelations.lean), [RootCollection.lean](RootCollection.lean),
  and [UnipotentFactorization.lean](UnipotentFactorization.lean): checked relations
  and the two factorizations needed for the simple reflections.
- [Weyl.lean](Weyl.lean), [RankOne.lean](RankOne.lean), and [BNPair.lean](BNPair.lean):
  the concrete Tits system and coverage of every ambient group element.
- [AmbientFacts/Frame.lean](AmbientFacts/Frame.lean),
  [NormalGeneration.lean](NormalGeneration.lean), and [Simple.lean](Simple.lean):
  core-freeness, normal generation, perfectness, and actual simplicity.
- [WilsonModel/ClassTests.lean](WilsonModel/ClassTests.lean),
  [BruhatReduction.lean](BruhatReduction.lean), and [Endpoint.lean](Endpoint.lean):
  finite tests promoted to the entire conjugacy class and the colour-changing swap.

## Reproduction

Use the repository pins: Lean `4.34.0-rc2` and mathlib
`87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`. The target is:

```sh
lake build Kourovka.Problem2153.Final
lake env lean Kourovka/Problem2153/Final.lean
```

The finite matrix certificates can consume substantial memory when many modules
build simultaneously. The recorded Auckland replay uses sequential module builds
with `lean -M6144 -j1 -D Elab.async=false`, a 30-minute timeout per module, and the
same library pins. Raw certificates are checked by Lean's kernel; no native
evaluation oracle or external computation is an assumed mathematical premise.

## References and credits

The matrices come from R. A. Wilson,
[A simple construction of the Ree groups of type ²F₄](https://webspace.maths.qmul.ac.uk/r.a.wilson/pubs_files/ReeF4alg.pdf),
J. Algebra 323 (2010), 1468–1481. Wilson credits K. Coolsaet’s earlier
[Ree–Tits octagon construction](https://doi.org/10.2140/iig.2005.1.67),
Innovations in Incidence Geometry 1 (2005), 67–131, including explicit root
elements and parabolic generators. These group constructions and simplicity
results are prior mathematics. The abstract Tits-system and Bruhat proofs reuse
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/tree/ede1468fb951c5117f1462008216ceb13214e29f/TauCeti/GroupTheory/TitsSystem)
at the pinned commit, with its Apache-2.0 license and provenance retained in
[External/TitsSystem](External/TitsSystem/PROVENANCE.json).

The construction, formalization, computational checks, and review artifacts are
part of the Nilradical v1.0.0 campaign. Mathematical validity,
bounded novelty assessment, human acceptance, and publication are separate records.
