# Problem 21.68

## Problem

M. Kida conjectures that every finite semiabelian group is monomial. A group
is semiabelian if it admits a subgroup chain from the identity to the whole
group, each next group being a quotient of an abelian semidirect product with
the preceding group. Monomial means that every irreducible complex
representation is induced from a linear character of a subgroup.

Source: [The Kourovka Notebook, version 46](https://arxiv.org/abs/1401.0300v46),
problem 21.68; see also Kida's Conjecture 1.3 and Definition 2.1 below.

## Result and scope

The answer is negative. The construction is a semiabelian group
of order **2592** with an irreducible complex representation of degree **8**
that is not monomial. The complete disproof is formalized in Lean.
No claim of minimal counterexample order is made.

Let `H = Q₈ ⋊ C₃`, with the order-three element cycling the three quaternion
units. Embed `H` in the order-96 group `W = C₂³ ⋊ (C₂² ⋊ C₃)` of even signed
permutations of the four quaternion basis elements. Let `X = W/H` and let
`A` be the augmentation submodule of `𝔽₃ˣ`, of order 27. The counterexample
is `G = A ⋊ W`.

## Formal statement

[Statement.lean](Statement.lean) defines `IsSemiabelian` by the source's actual
subgroup chain and `IsMonomial` by induction of one-dimensional complex
representations. [Solution.lean](Solution.lean) proves
`Kourovka.P21_68.not_notebookStatement : ¬ NotebookStatement`.
It does not assume a classification result, a character-table calculation,
or a finite-search conclusion.

## Proof outline

A [self-contained mathematical proof](../../../docs/21.68.md) gives the
matrices, the subgroup chain and the induction argument in detail.

The coordinate character `λ` at the identity coset has inertia subgroup
`I = A ⋊ H`, because the four coordinate characters remain distinct on the
augmentation submodule. Extend `λ` to `I` and multiply it by the inflation of
the explicit irreducible degree-two quaternion representation. Induction to
`G` is irreducible of degree eight: all nonidentity Mackey terms vanish
because they intertwine different scalar characters of the normal subgroup.

If this representation were induced from a linear character of `L`, then
`[G:L] = 8`. The normal subgroup `A` has order 27, so `A ≤ L`. Frobenius
reciprocity and the scalar character weights put `L` inside a conjugate of
`I`. Projecting to the corresponding copy of `H` gives a subgroup of index
two. Such a subgroup cannot exist: the order-three conjugation cyclically
permutes `i,j,k`, while `ij=k`, forcing every homomorphism `H → C₂` to vanish.

Semiabelianity follows from an actual chain of embedded successive abelian
split extensions. The normal 3-subgroup `A` need not be a Sylow subgroup.

## File guide

- [Statement.lean](Statement.lean): the original conjecture.
- [Solution.lean](Solution.lean): the unconditional disproof and its degree-eight witness.
- [Audit.lean](Audit.lean): the public statement, witness and guarded axiom checks.
- [Proof/README.md](Proof/README.md): the supporting modules in reading order.
- [External induction theory](../../External/TauCeti/README.md): upstream
  attribution, exact pins, retained license and local compatibility changes.

## Verification

The targeted solution build and independent endpoint axiom audits passed.
The [verification receipt](../../../docs/21.68-verification.md) records these
checks and their scope.
Finite group and Gaussian-integer identities use kernel
reduction; no external group computation is trusted by the proof.

```sh
lake build Kourovka.Problems.P21_68.Solution
lake env lean Kourovka/Problems/P21_68/Audit.lean
```

## References and credits

- M. Kida, *On semiabelian groups*, Journal of Group Theory **28** (2025),
  697–712. [DOI](https://doi.org/10.1515/jgth-2024-0010),
  [open text](https://d-nb.info/1364524341/34).
  Page 710 already records a semiabelian group `C₂³ ⋊ A₄` containing `SL₂(3)`.
  The complement/subgroup pair is prior mathematical input. The signed
  permutation embedding is checked explicitly here, without identifying a
  SmallGroups catalogue entry.
- J.-P. Serre, *Linear Representations of Finite Groups*, Section 7.3, for
  Mackey theory.
- [TauCeti](https://github.com/TauCetiProject/TauCeti), the Apache-licensed
  source of the vendored induction theorems. Its authorship is preserved.

The construction, independent mathematical audits and Lean development were
carried out in Aluna Rizzoli's research project with substantial Codex
assistance. The literature checks do not establish publication priority for
the counterexample or its general transfer argument.
