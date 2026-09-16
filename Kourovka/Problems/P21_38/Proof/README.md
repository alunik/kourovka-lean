# Proof roadmap for Problem 21.38

[Problem overview](../README.md) · [Public statement](../Statement.lean) · [Public theorem](../Solution.lean)

Donoven and Harper's Question 2 in [*Infinite 3/2-generated groups*
(2020)](https://doi.org/10.1112/blms.12356), subsequently Kourovka Notebook
21.38, is answered by the subgroup of Thompson's group $F$ with equal
endpoint slopes. Start with [Solution.lean](../Solution.lean) for the
public endpoints. Supporting declarations are in `Kourovka.P21_38`;
imported foundations retain their upstream namespaces.

## Mathematical reading order

The generation proof and fixed-point obstruction meet only at the final
spread theorem. The following twelve stages give a reading order through
the main arguments; auxiliary modules are grouped under their mathematical
role rather than listed individually.

| Stage | Main module | Role |
| --- | --- | --- |
| 1. Ordinary spread | [Spread.lean](Spread.lean) | Defines generation by a pair and the common-companion condition for finite tuples. The bounds establish its monotonicity and the exact-one interpretation. |
| 2. Concrete witness | [EndpointSlopes.lean](EndpointSlopes.lean) | Defines the rational dyadic PL interval group `F`, proves the endpoint exponents form a character, and defines `diagonalSubgroup`. |
| 3. The compact core | [CorePerfect.lean](CorePerfect.lean) | Uses the proved standard-generator calculation to identify the endpoint kernel with the derived subgroup and establish its perfectness. |
| 4. Finite branch realization | [TreePairRealization.lean](TreePairRealization.lean) | Turns ordered finite partitions into actual PL permutations, using binary interval partitions and proved affine gluing. |
| 5. A nonidentity input | [FirstMovingBranches.lean](FirstMovingBranches.lean) | Finds three successive interior branches of a nontrivial map or its inverse, including maps with zero endpoint exponents. |
| 6. The companion | [CompanionConstruction.lean](CompanionConstruction.lean) | Builds Golan-Polak's finite companion for the case $c=d=1$, proves both endpoint exponents are one, and obtains uniform communication among deep interior branches. |
| 7. Generation data | [GenerationData.lean](GenerationData.lean) | Collects the constructed branch relations, dyadic transitivity, a nontrivial core element, and the one-sided slope witness. Every field is proved for the actual two-generated subgroup. |
| 8. Interval motion | [FixerMotion.lean](FixerMotion.lean) | Proves that the relevant pointwise fixers preserve no interior real cut; the orbit and compression lemmas then move compact intervals into the required region. |
| 9. Finite interpolation | [LocalInterpolation.lean](LocalInterpolation.lean) | Uses conjugates of integer powers of the slope witness to correct successive branches, preserve earlier agreement, and cancel endpoint characters. Refined core partitions supply the finite induction data. |
| 10. Recover the group | [DiagonalGeneration.lean](DiagonalGeneration.lean) | Local agreement recovers core commutators; perfectness yields the entire core. A companion of character $(1,1)$ then fills the diagonal quotient. |
| 11. Every input has a mate | [PrescribedGeneration.lean](PrescribedGeneration.lean) | Discharges all interpolation hypotheses from the constructed companion and proves `exists_generating_companion` and `diagonal_hasSpreadAtLeast_one`. |
| 12. Obstruction and infinitude | [UpperBound.lean](UpperBound.lean) | Proves an interior rational fixed point for every diagonal element, exhibits two nonidentity elements whose fixed sets cover the interval, excludes a common companion, and proves the witness infinite. |

## What is proved from the generation papers

The required specialization of [Golan-Polak's Proposition
16(1)](https://doi.org/10.1112/blms.12841) is implemented through finite
binary branches. The construction supplies a companion $g$ of endpoint
exponents $(1,1)$ for every nonidentity input $f$, with no restriction on
the endpoint exponents of $f$.

Branch equivalence alone gives local agreement on individual pieces. The
formalization proves the additional steps needed to obtain elements of the
ordinary subgroup $H=\langle f,g\rangle$: interval compression, a finite
induction of branch corrections, and cancellation of both endpoint
characters. The local-interpolation mechanism follows [Lemmas 7.9–7.15 and
Theorem 7.16 of the earlier generation
paper](https://arxiv.org/abs/1608.02572v2).

[CommutatorExtraction.lean](CommutatorExtraction.lean) provides the final
algebraic step. If $h$ agrees with $f$ on a set supporting $g$, and $k$
agrees with $g$ on a set supporting $h$, then $[h,k]=[f,g]$. Applying this
to compact-core elements gives the core's commutator subgroup inside $H$.
Perfectness gives the full core. Finally, for a diagonal element $z$ with
character $(n,n)$, the element $zg^{-n}$ lies in that core. Thus $H$ is
the whole diagonal subgroup.

## Rational points and real cuts

The group acts concretely on rational points. For the upper bound,
[RationalPLFixedPoint.lean](RationalPLFixedPoint.lean) finds a sign crossing
on a finite affine grid and solves the affine equation over $\mathbb Q$.
This supplies the rational fixed point used by the action obstruction.

The separate interval-motion proof uses real cuts of rational orbits.
An orbit bounded above can have an irrational supremum, so absence of
common rational fixed points alone would be insufficient. The fixer
argument excludes every interior invariant real cut; the supremum argument
then justifies the required motion. No extension of the entire action to
real homeomorphisms is assumed.

## Foundations and verification

The imported concrete PL and Thompson-group foundations come from
[SauersML/group-approximation](https://github.com/SauersML/group-approximation/tree/a39c9b72861bd04c71fc8e18876d13307851d777),
commit `a39c9b72861bd04c71fc8e18876d13307851d777`, under Apache-2.0.
[THIRD_PARTY.md](THIRD_PARTY.md) records the exact source closure, licensing,
and integration changes. The new endpoint-kernel calculation, prescribed
companion argument, and spread obstruction are proved in the local modules.

These are symbolic Lean proofs, including the finite tree and partition
constructions. There are no generated certificate shards or external
computation assumptions. The final existence assertions are closed, and
their guarded axiom checks permit only `propext`, `Classical.choice`, and
`Quot.sound`; `sorry`, custom mathematical axioms, and `native_decide` are
excluded. See [verification](../README.md#verification) for the solution
build and repository audit.

Mathematical sources and the Nilradical v0 contribution are
acknowledged in the [problem references](../README.md#references-and-credits)
and [repository credits](../../../../AUTHORS.md).
