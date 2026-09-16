# Problem 21.3 — first question

[All problems](../../../README.md) · [Contributing](../../../CONTRIBUTING.md)

## Problem

Let $G=A_n$ or $S_n$ and let $H,K$ be soluble subgroups of $G$. For all
sufficiently large $n$, can we always find an element $x\in G$ such that
$H\cap K^x=1$? Does this hold for all $n\geq 21$?

Note that the conclusion is false when $G=S_{20}$ and
$H=K=(S_4\wr S_4)\times S_4$.

Posed by M. Anagnostopoulou-Merkouri and T. C. Burness in
[*The Kourovka Notebook*, 21st edition, Problem 21.3, p. 167](https://arxiv.org/abs/1401.0300v46).

## Result and scope

**Affirmative**, for the first question in both groups. The theorem supplies
one cutoff valid for every pair of soluble subgroups. The question about the
specific threshold $21$ is not covered.

## Formal statement

[`Kourovka.P21_03.FirstQuestion`](Statement.lean) places the cutoff before
the subgroup quantifiers: there is one $N$ such that, for every $n\geq N$,
both conclusions hold for all soluble $H,K\leq S_n$. Subgroups of $A_n$ are
represented inside $S_n$ with explicit containment hypotheses, and the
alternating conclusion requires an even conjugator.

`Disjoint H (MulAut.conj x⁻¹ • K)` expresses $H\cap x^{-1}Kx=1$.
The public theorem is [`Kourovka.P21_03.firstQuestion`](Solution.lean).

## Proof outline

Read [How the proof works](../../../docs/walkthroughs/21.3.md),
an informal account by **Nilradical v0**, generated after human statement
acceptance and labelled **Agent-generated exposition; not refereed**.

1. Embed soluble permutation groups into suitable iterated wreath-product
   and direct-product envelopes. Separate the transposition core from the
   remaining elements and bound the latter's contribution uniformly.
2. Prove that the infimum, over soluble $H,K\leq S_n$, of the proportion of
   conjugators with trivial intersection tends to $e^{-9/2}>0$.
   Core counting gives the lower bound; four-point-block constructions
   give the matching upper bound. Positivity supplies the symmetric result.
3. Use a separate parity argument to obtain even conjugators for subgroups
   of $A_n$, then combine both eventual statements into a single cutoff.

## File guide

| File | Purpose |
| --- | --- |
| [`README.md`](README.md) | Problem, scope, and proof overview. |
| [`Statement.lean`](Statement.lean) | The notebook question, independent of the proof. |
| [`Solution.lean`](Solution.lean) | The public answer theorem. |
| [`Proof/README.md`](Proof/README.md) | Roadmap through the supporting Lean modules. |
| [`docs/21.3.md`](../../../docs/21.3.md) | Detailed explanation of the encoding and source map. |

## Verification

[Final human statement acceptance](../../../docs/nilradical-v0-acceptance/README.md)
was recorded on 16 September 2026 for source revision `5a6b2c18e326`.

The Nilradical v0 strict check passed on 16 September 2026 for 2
selected endpoints: fresh compilation, independently reviewed statement
comparison, the three-axiom policy, and Lean plus Nanoda proof replay.
See the [verification evidence](../../../docs/nilradical-v0-verification/README.md)
and [statement review](../../../docs/nilradical-v0-verification/statement-audits/21.3.md).

From the repository root, after the [initial setup](../../../README.md#check-the-proofs):

```sh
lake build Kourovka.Problems.P21_03.Solution
```

Use the [full build and axiom audit](../../../README.md#check-the-proofs) to
check all public solutions. The [verification record](../../../docs/verification.md)
documents the recorded build. All supporting arguments are proved in Lean;
the endpoint has no classification or finite-certificate premise and uses
only `propext`, `Classical.choice`, and `Quot.sound`.

## References and credits

- M. Anagnostopoulou-Merkouri and T. C. Burness,
  [*The Kourovka Notebook*, 21st edition, Problem 21.3, p. 167](https://arxiv.org/abs/1401.0300v46).
- The solution of the first question and its Lean proof are by
  **Nilradical v0**. See [repository credits](../../../AUTHORS.md).

Cite **Nilradical v0**, this problem number and the exact source commit.
Machine-readable citation: [CITATION.cff](CITATION.cff).
