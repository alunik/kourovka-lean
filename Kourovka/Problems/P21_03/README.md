# Problem 21.3 — first question

## Problem

Let $G=A_n$ or $S_n$ and let $H,K$ be soluble subgroups of $G$. For all
sufficiently large $n$, can we always find an element $x\in G$ such that
$H\cap K^x=1$? Does this hold for all $n\geq 21$?

Note that the conclusion is false when $G=S_{20}$ and
$H=K=(S_4\wr S_4)\times S_4$.

— M. Anagnostopoulou-Merkouri and T. C. Burness,
[*The Kourovka Notebook*, 21st edition, Problem 21.3, p. 167](https://arxiv.org/abs/1401.0300v46).

**Formalized result:** an affirmative answer to the first question, for both
groups. The theorem supplies one cutoff valid for every pair of soluble
subgroups. The question about the specific threshold $21$ is not covered.

## Lean strategy

1. Embed soluble permutation groups into suitable iterated wreath-product
   and direct-product envelopes. Separate the transposition core from the
   remaining elements and bound the latter's contribution uniformly.
2. Prove that the infimum, over soluble $H,K\leq S_n$, of the proportion of
   conjugators with trivial intersection tends to $e^{-9/2}>0$.
   Core counting gives the lower bound; four-point-block constructions
   give the matching upper bound. Positivity supplies the symmetric result.
3. Use a separate parity argument to obtain even conjugators for subgroups
   of $A_n$, then combine both eventual statements into a single cutoff.

The natural-language question is encoded in [`Statement.lean`](Statement.lean).
The final theorem is [`Kourovka.P21_03.firstQuestion`](Solution.lean).
All supporting arguments are proved in Lean in [`Proof/`](Proof/).
See the [detailed source map](../../../docs/21.3.md) and
[verification record](../../../docs/verification.md).
