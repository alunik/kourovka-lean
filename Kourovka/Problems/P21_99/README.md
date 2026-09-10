# Problem 21.99

[All problems](../../../README.md) · [Contributing](../../../CONTRIBUTING.md)

## Problem

Peter Müller asks whether, in every finite transitive permutation group,
each ordered pair of distinct points can be joined by a group element
whose number of fixed points is different from one.
See [*The Kourovka Notebook*, 21st edition, Problem 21.99, p. 182](https://arxiv.org/pdf/1401.0300v46#page=182).
The question also appears in [Müller's paper, Remark (f)](https://arxiv.org/pdf/2304.08459v4#page=5).

## Result and scope

**Negative**, witnessed by a finite transitive action of degree
$6\cdot5^{14}=36\,621\,093\,750$. Every element carrying one specified point
to another fixes exactly one point. The transporter theorem is universal
over those elements and their translations; there is no sampling premise.

## Formal statement

[`Kourovka.P21_99.NotebookStatement`](Statement.lean) quantifies over subgroups
of the full symmetric group on an arbitrary finite type with a transitive
action (`MulAction.IsPretransitive`). For every ordered pair of distinct
points it asks for a transporter whose fixed-point condition is the negation
of unique existence.

The public theorem is
[`Kourovka.P21_99.not_notebookStatement`](Solution.lean). Its concrete input is
[`transporter_unique`](Proof/Instance.lean), which proves unique existence of
a fixed point for every element in the chosen transporter.

## Proof outline

### Counterexample

Let $V=\mathbb F_5^{18}$. An explicitly generated group acts linearly on $V$
and permutes six blocks. In block $i$, the points are coordinates for a
14-dimensional quotient of $V$. The point set is therefore

$$\Omega=\{0,\ldots,5\}\times\mathbb F_5^{14},
\qquad |\Omega|=6\cdot5^{14}=36\,621\,093\,750.$$

Translations by $V$ and the linear group act together on these six fibres.
For the source point $(0,0)$ and the target point $(2,P_2b)$, use

$$b=(3,4,0,0,1,3,2,2,0,0,3,0,0,2,0,0,0,4),$$

where $P_2$ is the explicit projection for block 2. The points are distinct,
the action is transitive, and **every element carrying the source to the
target fixes exactly one point**. Taking the image of the action in
$\operatorname{Sym}(\Omega)$ supplies the permutation group required by the
notebook formulation.

### Argument

The proof does not enumerate the points of $\Omega$.

1. A table of 384 explicit linear/block transformations contains the
   identity and is closed under right multiplication by eight generators.
   A [general finite-set argument](Proof/Generated.lean) proves that the table
   covers the generated subgroup. Explicit generator words reach all six blocks.
2. Sparse matrix identities verify the six quotient projections and their
   compatibility with the group action. Translations make each fibre
   transitive, completing the transitivity proof.
3. The table indices carrying block 0 to block 2 are covered by 64 explicit
   cases. Each fixes two blocks. In one, an explicit inverse for $I-T$
   proves that every choice of translation gives exactly one fixed point.
   In the other, a linear
   functional proves that the fixed-point equation has no solution for
   any translation satisfying the transporter condition. The remaining
   blocks contain no fixed points because they are moved.
4. [`Transfer.lean`](Proof/Transfer.lean) passes the obstruction to the
   image permutation group and contradicts the notebook assertion.

The formal argument needs the table to cover the generated subgroup. It
does not assume that its entries are distinct or identify the subgroup
with a named group from an external catalogue.

## File guide

| File | Purpose |
| --- | --- |
| [`README.md`](README.md) | Problem, scope, and proof overview. |
| [`Statement.lean`](Statement.lean) | The notebook question, independent of the proof. |
| [`Solution.lean`](Solution.lean) | The public answer theorem. |
| [`Proof/README.md`](Proof/README.md) | Roadmap through the supporting Lean modules. |
| [`Proof/Certificates/README.md`](Proof/Certificates/README.md) | Sparse certificates and the finite acceptance checks. |
| [`Proof/generation_receipt.json`](Proof/generation_receipt.json) | Source-data and generated-file hashes for reproduction. |

## Verification

From the repository root, after the [initial setup](../../../README.md#check-the-proofs):

```sh
lake build Kourovka.Problems.P21_99.Solution
```

Use the [full build and axiom audit](../../../README.md#check-the-proofs) to
check all public solutions. The [verification record](../../../docs/verification.md)
documents the recorded build. The toolchain and dependencies are pinned;
the endpoint uses only `propext`, `Classical.choice`, and `Quot.sound`.

The committed finite certificates use `decide +kernel`. The build requires
neither a C++/GAP installation nor execution of the Python generator. The
[generator](../../../scripts/generate_21_99.py) and its
[exact input data and reproduction instructions](../../../scripts/data/21_99/README.md)
are included so that the sparse certificates can be regenerated.
The generator is not part of the trusted proof: Lean checks the identities
in its output.

## References and credits

- Peter Müller,
  [*The Kourovka Notebook*, 21st edition, Problem 21.99, p. 182](https://arxiv.org/pdf/1401.0300v46#page=182).
- [Müller's paper, Remark (f)](https://arxiv.org/pdf/2304.08459v4#page=5).

The counterexample and Lean development came from Aluna Rizzoli's
computational search project, with substantial Codex assistance. See
[repository credits](../../../AUTHORS.md).

Custom C++ searches found the example on Auckland, and independent GAP
computations checked the original transporter. Those computations explain
the discovery and provide additional checks; the Lean theorem has no
external computational assumptions.
