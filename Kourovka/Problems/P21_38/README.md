# Problem 21.38

[All problems](../../../README.md#problems) · [Contributing](../../../CONTRIBUTING.md)

## Problem

Casey Donoven and Scott Harper asked whether an **infinite group of spread
exactly one** exists in Question 2 of [*Infinite 3/2-generated groups*
(2020)](https://doi.org/10.1112/blms.12356). The question subsequently appears
as Problem 21.38 in the [21st edition of the Kourovka
Notebook](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/21tkt.pdf),
where it asks whether any group of spread one exists.

The ordinary spread of a group $G$ is the greatest nonnegative integer $k$
such that every tuple of nonidentity elements $x_1,\ldots,x_k\in G$ has a
common companion $y\in G$ satisfying

$$
\langle x_1,y\rangle=\cdots=\langle x_k,y\rangle=G.
$$

The spread is infinite if these conditions hold for every $k$.

## Result and scope

**Yes.** Let $F$ be Thompson's group of increasing dyadic piecewise-linear
maps of the unit interval, and let

$$
\pi(f)=\bigl(\log_2 f'(0^+),\log_2 f'(1^-)\bigr).
$$

The explicit witness is

$$
G=\pi^{-1}\bigl(\mathbb Z(1,1)\bigr),
$$

the subgroup whose two endpoint slopes agree. The formalization proves
that $G$ is infinite and has ordinary spread exactly one. In particular,
every nonidentity element has a generating companion, while one fixed pair
of nonidentity elements has no common companion. It also proves the full
tuple profile: the spread condition holds exactly for $k\leq1$.

The substantial generation argument is due to Gili Golan-Polak:
[Proposition 16(1) of *Thompson's group F is almost 3/2-generated*
(2023)](https://doi.org/10.1112/blms.12841), specialized to $c=d=1$.
The required case is proved in Lean from its finite branch construction,
including the passage to actual subgroup generation. The fixed-point upper
bound is proved directly.

## Formal statement

[Statement.lean](Statement.lean) defines
`Kourovka.P21_38.OriginalQuestion` and
`Kourovka.P21_38.NotebookStatement`. It imports only the general spread
definitions in [Proof/Spread.lean](Proof/Spread.lean), so the formulation is
independent of the Thompson-group construction.

[Solution.lean](Solution.lean) proves:

- `Kourovka.P21_38.originalQuestion`: an infinite group of spread one exists;
- `Kourovka.P21_38.notebookStatement`: the Notebook existence statement;
- `Kourovka.P21_38.diagonal_hasSpreadExactlyOne`: the concrete witness has
  spread one;
- `Kourovka.P21_38.diagonal_spread_profile`: for every natural number $k$,
  `HasSpreadAtLeast diagonalSubgroup k ↔ k ≤ 1`.

`GeneratesPair a b` means `Subgroup.closure {a, b} = ⊤`, where closure is
ordinary subgroup generation. The witness uses increasing permutations of
$\mathbb Q$ with finite dyadic affine pieces, fixing the complement of
$(0,1)$. Endpoint exponents come from proved affine germ formulas.
This concrete rational model suffices for the abstract group-existence
statement. The fixed-point proof uses finite rational affine interpolation.

## Proof outline

Read [How the proof works](../../../docs/walkthroughs/21.38.md),
an informal account by **Nilradical v0**, generated after human statement
acceptance and labelled **Agent-generated exposition; not refereed**.

1. **Identify the endpoint kernel.** Construct $\pi$, calculate its values
   on standard generators, and prove that its kernel is the compact core
   $F'$, consisting of maps equal to the identity near both endpoints.
   Establish that this core is perfect.
2. **Construct a companion.** For every $1\ne f\in G$, build a finite
   tree-pair map $g$ with $\pi(g)=(1,1)$. Its branches connect sufficiently
   deep interior dyadic intervals and supply a map that is the identity
   immediately to the left of a local slope change.
3. **Prove ordinary generation.** Use interval motion and finite branch
   corrections to interpolate each core element on any compact interior
   interval by elements of $\langle f,g\rangle\cap F'$. Two such
   interpolations recover each core commutator. Perfectness then gives
   $F'\leq\langle f,g\rangle$. For $z\in G$ with $\pi(z)=(n,n)$,
   $zg^{-n}\in F'$, so $\langle f,g\rangle=G$. This includes inputs
   $f\in F'\setminus\{1\}$.
4. **Exclude spread two.** Every element of $G$ fixes an interior rational
   point: equal endpoint slopes make the endpoint displacements have
   opposite signs, or give an identity germ. Choose two nonidentity maps
   with disjoint interior supports. At any proposed companion's fixed
   point, one of these maps also fixes the point. Their generated subgroup
   lies in its proper stabilizer, so the pair has no common companion.
5. **Prove infinitude.** A nontrivial increasing core map has infinitely
   many distinct powers, giving infinitely many elements of $G$.

The [proof roadmap](Proof/README.md) groups the supporting modules by these
mathematical steps.

## File guide

| File | Purpose |
| --- | --- |
| [README.md](README.md) | Question, answer, and scope |
| [Statement.lean](Statement.lean) | Public formulations, independent of the witness |
| [Solution.lean](Solution.lean) | Public answers and exact spread profile |
| [Proof/README.md](Proof/README.md) | Supporting-module roadmap |
| [Proof/THIRD_PARTY.md](Proof/THIRD_PARTY.md) | Imported foundations, exact source revision, license, and local changes |

## Verification

[Final human statement acceptance](../../../docs/nilradical-v0-acceptance/README.md)
was recorded on 16 September 2026 for source revision `5a6b2c18e326`.

The Nilradical v0 strict check passed on 16 September 2026 for 7
selected endpoints: fresh compilation, independently reviewed statement
comparison, the three-axiom policy, and Lean plus Nanoda proof replay.
See the [verification evidence](../../../docs/nilradical-v0-verification/README.md)
and [statement review](../../../docs/nilradical-v0-verification/statement-audits/21.38.md).

From the repository root, build this solution:

```sh
lake build Kourovka.Problems.P21_38.Solution
```

Follow the [full build and audit
instructions](../../../README.md#check-the-proofs) and the
[verification guide](../../../docs/verification.md). The public endpoints
have closed-statement axiom guards. The permitted axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

Every mathematical dependency is supplied as a Lean proof. There are no
`sorry` declarations, custom mathematical axioms, or `native_decide`
proofs. The finite branch constructions are symbolic proofs; no external
computation or generated certificate is a proof assumption. The
[verification receipt](../../../docs/21.38-verification.md) records the
checked source snapshot and commands.
The [statement audit](../../../docs/21.38-statement-audit.md) checks the
quantifiers, the concrete rational PL witness, and the complete generation
argument, including inputs in the endpoint kernel.

## References and credits

1. Casey Donoven and Scott Harper, [*Infinite 3/2-generated
   groups*](https://doi.org/10.1112/blms.12356), Bulletin of the London
   Mathematical Society **52** (2020), 657–673, Question 2.
2. [*The Kourovka Notebook*, 21st
   edition](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/21tkt.pdf),
   September 2026 source edition, Problem 21.38, attributed there to
   S. Harper and C. Donoven.
3. Gili Golan-Polak, [*Thompson's group F is almost
   3/2-generated*](https://doi.org/10.1112/blms.12841), Bulletin of the London
   Mathematical Society **55** (2023), 2144–2157, Proposition 16(1) and
   Theorem 2; [preprint](https://arxiv.org/abs/2210.03564).
4. Gili Golan, [*The generation problem in Thompson group
   F*](https://arxiv.org/abs/1608.02572v2), especially Lemmas 7.9–7.10,
   7.13–7.15 and Theorem 7.16 in arXiv version 2. These supply the
   interval-motion and local-interpolation mechanism used here.
5. Gili Golan Polak, [*The “spread” of Thompson's group
   F*](https://arxiv.org/abs/2402.19444v1) (2024), Lemma 2 and Remark 11,
   for related fixed-point obstructions.
6. The concrete Thompson foundations are adapted from
   [SauersML/group-approximation](https://github.com/SauersML/group-approximation/tree/a39c9b72861bd04c71fc8e18876d13307851d777),
   commit `a39c9b72861bd04c71fc8e18876d13307851d777`, under Apache-2.0.
   See [third-party provenance](Proof/THIRD_PARTY.md).

The construction, mathematical proof and Lean formalization are by
**Nilradical v0**, using Codex and GPT Pro. See [repository credits](../../../AUTHORS.md).

Cite **Nilradical v0**, this problem number and the exact source commit.
Machine-readable citation: [CITATION.cff](CITATION.cff).
