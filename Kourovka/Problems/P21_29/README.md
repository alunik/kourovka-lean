# Problem 21.29

[All problems](../../../README.md) · [Contributing](../../../CONTRIBUTING.md)

## Problem

Let $G\leq\operatorname{Sym}(\Omega)$ be a finite primitive permutation group
with a regular suborbit (that is, $G$ has a trivial $2$-point stabiliser).
Then is it true that for all $\alpha,\beta\in\Omega$, there exists
$\gamma\in\Omega$ such that the $2$-point stabilisers $G_{\alpha,\gamma}$
and $G_{\beta,\gamma}$ are both trivial?

Posed by T. C. Burness and M. Giudici in
[*The Kourovka Notebook*, 21st edition, Problem 21.29](https://arxiv.org/abs/1401.0300v46).

## Result and scope

**Negative**, witnessed by a single primitive permutation group of degree
$3^9=19\,683$ with a regular suborbit.

The solution is due to **Aluna Rizzoli and Adam R. Thomas**,
[*Common neighbour conjectures for Saxl graphs fail at every base size*](https://arxiv.org/abs/2609.01367).
This development formalizes one counterexample from their work.

## Formal statement

[`Kourovka.P21_29.NotebookStatement`](Statement.lean) quantifies over finite
subgroups of the symmetric group with a primitive action
(`MulAction.IsPreprimitive`). `TrivialPairStabilizer` expresses that the
intersection of two point stabilisers is the identity subgroup. The
assertion assumes one pair with trivial stabiliser and asks for a common
partner for every pair of points.

[`Kourovka.P21_29.not_notebookStatement`](Solution.lean) proves its negation.
The same file exposes `has_regular_suborbit`, the primitivity instance,
and `no_simultaneous_trivial_stabilizers` for the concrete example.

## Proof outline

### Counterexample

Index the coordinates of $V=\mathbb F_3^9$ by $\mathbb Z/9\mathbb Z$.
Let $D$ consist of the diagonal sign changes whose product on each of
$\{0,3,6\}$, $\{1,4,7\}$, and $\{2,5,8\}$ is $1$. Thus $D\cong C_2^6$.
Rotations and reflections of the nine coordinates give a dihedral group
of order $18$, normalizing $D$. Let $H=D\rtimes D_{18}$ and let
$G=V\rtimes H$ act affinely on $V$.

The pair $0,r$, with $r=(0,1,2,1,1,1,1,1,1)$, has trivial stabiliser.
However, for

$$\alpha=0,\qquad\beta=(0,1,1,0,1,1,0,1,1),$$

no $\gamma\in V$ makes both required stabilisers trivial.

### Argument

1. Construct the sign subgroup, its dihedral action, and their semidirect
   product. Prove that the linear action is irreducible: two diagonal
   differences isolate a coordinate, and rotations supply every basis vector.
   A general affine-action lemma then proves primitivity.
2. Enumerate all $1\,152$ elements of $H$ and all $19\,683$ vectors of $V$,
   with proofs that the enumerations cover their types. Kernel-checked
   finite calculations show that only the identity fixes $r$.
3. For each vector $\gamma$, provide one nonidentity element of $H$ fixing
   either $\gamma$ or $\gamma-\beta$. Lean checks every witness. The affine
   stabiliser identity transfers this obstruction to the two pairs in the
   notebook question.

## File guide

| File | Purpose |
| --- | --- |
| [`README.md`](README.md) | Problem, scope, and proof overview. |
| [`Statement.lean`](Statement.lean) | The notebook question, independent of the proof. |
| [`Solution.lean`](Solution.lean) | The public answer theorem and transfer to a permutation group. |
| [`Proof/README.md`](Proof/README.md) | Roadmap through the supporting Lean modules. |
| [`Proof/Certificates/README.md`](Proof/Certificates/README.md) | Finite checks and their coverage. |

## Verification

From the repository root, after the [initial setup](../../../README.md#check-the-proofs):

```sh
lake build Kourovka.Problems.P21_29.Solution
```

Use the [full build and axiom audit](../../../README.md#check-the-proofs) to
check all public solutions. The [verification record](../../../docs/verification.md)
documents the recorded build. The committed certificates use `decide +kernel`,
without native evaluation; the endpoint uses only `propext`, `Classical.choice`,
and `Quot.sound`.

The [certificate generator](../../../scripts/generate_21_29.cpp) is a
reproducibility aid; it is not trusted by the proof and is not run during a
normal build. See [certificate reproduction](../../../scripts/README.md).

## References and credits

- T. C. Burness and M. Giudici,
  [*The Kourovka Notebook*, 21st edition, Problem 21.29](https://arxiv.org/abs/1401.0300v46).
- Aluna Rizzoli and Adam R. Thomas,
  [*Common neighbour conjectures for Saxl graphs fail at every base size*](https://arxiv.org/abs/2609.01367).
- Codex assisted with the Lean formalization and certificate generator.
  The encoding and general affine-primitivity argument were adapted from
  Aluna Rizzoli's existing Burness–Giudici development. See
  [repository credits](../../../AUTHORS.md).
