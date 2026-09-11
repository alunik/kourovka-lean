# TauCeti induction theory

These files are a minimal dependency closure from
[TauCeti](https://github.com/TauCetiProject/TauCeti), commit
`285435d0b4cb5b86819ade410ce78abc77580bf6`, used for the induction theory in
Kourovka problem 21.68. Copyright and authorship remain with the Tau Ceti
contributors. The upstream [Apache 2.0 license](LICENSE) is retained.

[provenance.json](provenance.json) records every upstream module and its original
SHA-256 digest. Upstream used Lean 4.34.0-rc2 and mathlib
`03616a12cdf1e3f499349f69e80eee82b28745bc`; this repository keeps its existing
mathlib pin `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.

Local modifications: import paths now start with `Kourovka.External.TauCeti`,
and a modification notice was added to each file. Mathematical namespaces
remain unchanged. The compatibility adaptations are described below.

Compatibility changes in `GroupTheory/GroupAction/Stabilizer.lean`,
`GroupTheory/DoubleCoset/Orbits.lean`, and
`RepresentationTheory/Induction/Mackey/Subgroup.lean` make the ambient group
action explicit with `change` before rewriting coset stabilizers. One nested
stabilizer membership is proved explicitly. These accommodate the older
mathlib subgroup-action instances without changing any theorem statement.
All three entry modules compile at this repository's pin.

The entry modules are `RepresentationTheory/Induction/Mackey/Irreducible.lean`,
`RepresentationTheory/Induction/FrobeniusReciprocity.lean`, and
`RepresentationTheory/Induction/LinearCharacter.lean`.
