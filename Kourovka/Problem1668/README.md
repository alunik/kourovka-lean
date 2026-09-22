# Kourovka 16.68 — word maps on projective linear groups

**Nilradical v0 · Complete Lean proofs for the complex and real cases**

[Mathematical note](../../docs/walkthroughs/16.68.md) · [Verification record](../../docs/nilradical-16.68/README.md)

## Problem

Let $w$ be a nonidentity element of the free group on two generators. Must the
word map $w:G\times G\to G$ be surjective when $G$ is
$\operatorname{PSL}_2(\mathbb R)$, $\operatorname{PSL}_2(\mathbb C)$, or
$\operatorname{SO}_3(\mathbb R)$?

The question is due to **Jan Mycielski**, Problem 16.68 in
[*The Kourovka Notebook*](https://arxiv.org/abs/1401.0300v46).

## Result and scope

**Affirmative over the complex numbers; negative over the real numbers.**
Both statements have complete Lean proofs in this entry.

The complex theorem proves more generally that every nonidentity two-variable
word induces a surjective word map on $\operatorname{PSL}_2(K)$ for every
algebraically closed field $K$ of characteristic zero. It makes no assertion
in positive characteristic or for the special linear group before taking its
central quotient.

For $\operatorname{PSL}_2(\mathbb R)$, use $[r,s]=rsr^{-1}s^{-1}$ and put

$$
d=bab^{-1},\qquad c=[a,d],\qquad
W=[aca^{-1},dc^{-1}d^{-1}].
$$

The formalization proves that this word is nonidentity and that its word map
omits the projective class of $\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$,
a nonidentity involution. Every evaluation on real determinant-one matrices
satisfies the strict bound $\operatorname{tr}W(A,B)>7/4$.

The negative answer for $\operatorname{SO}_3(\mathbb R)$ is prior work of
Andreas Thom. It is credited in the mathematical note and is not formalized
in this entry. These Lean projects cover the complex and real projective
linear cases only.

## Formal statement

Both developments use mathlib's `FreeGroup (Fin 2)`, `FreeGroup.lift`, and
`PSL(2, K)`, the quotient of the determinant-one matrix group by its center.
The original source modules and build configurations are preserved.

| Declaration | Statement |
| --- | --- |
| [`WordMaps.word_surjective`](Complex/WordMaps/Surjectivity.lean) | Surjectivity for every nonidentity word over any algebraically closed characteristic-zero field |
| [`WordMaps.complex_word_surjective`](Complex/WordMaps/Surjectivity.lean) | The full complex two-variable statement |
| [`RealWord.word_ne_one`](Real/RealWord/Counterexample.lean) | The explicit free-group word is nonidentity |
| [`RealWord.tr_value_gt_seven_fourths`](Real/RealWord/Counterexample.lean) | The strict trace bound for all real determinant-one input matrices |
| [`RealWord.word_omits_target`](Real/RealWord/Counterexample.lean) | Every projective evaluation omits the specified target |
| [`RealWord.exists_nontrivial_nonsurjective_word`](Real/RealWord/Counterexample.lean) | A nonidentity two-variable word with nonsurjective real projective word map |

The word itself is defined in [Definitions.lean](Real/RealWord/Definitions.lean).
The real endpoint also proves `word_not_surjective`, `project_target_ne_one`,
and `project_target_sq`. No unproved mathematical input is an endpoint hypothesis.

## Proof outline

For the complex case, reduce a nonidentity word up to conjugacy to either a
nonzero generator power or a product of alternating nonzero powers. Power maps
on the projective group are surjective. For the second case, elementary
polynomial matrices give a word-image curve with nonconstant trace. A polynomial
fiber argument makes one trace $\pm2$ fiber noncentral. Trace classification
then supplies every projective conjugacy class, including the unipotent class;
the identity is a word value by evaluation at the identity inputs.

For the real case, Fricke and skein identities give an exact factored expression
for the trace of $W$. The real character restriction and polynomial inequalities
prove the universal strict $7/4$ lower bound. An explicit evaluation proves
$W\ne1$. Every lift of the specified omitted projective class has trace zero,
so the trace bound excludes it from the word image.

The [proof reading map](Proof/README.md) connects each step to its Lean modules.

## File guide

| File or directory | Purpose |
| --- | --- |
| [Complex/WordMaps.lean](Complex/WordMaps.lean) | Public import of the complex proof |
| [Complex/WordMaps/Surjectivity.lean](Complex/WordMaps/Surjectivity.lean) | General and complex endpoints |
| [Real/RealWord.lean](Real/RealWord.lean) | Public import of the real proof |
| [Real/RealWord/Definitions.lean](Real/RealWord/Definitions.lean) | Exact free-group word and its evaluations |
| [Real/RealWord/Counterexample.lean](Real/RealWord/Counterexample.lean) | Trace bound, nonidentity witness and nonsurjectivity |
| [Complex/Audit.lean](Complex/Audit.lean) and [Real/Audit.lean](Real/Audit.lean) | Guarded publication axiom audits |
| [Frozen source manifest](../../docs/nilradical-16.68/source-manifest.json) | Hashes of the 23 preserved source and configuration files |
| [Verification record](../../docs/nilradical-16.68/README.md) | Original checks, acceptance scope and publication verification |

## Verification

The accepted source snapshots passed their recorded Lean, Comparator and
Nanoda checks. Their only permitted axioms are `propext`, `Classical.choice`,
and `Quot.sound`. The public source files are byte-identical to those snapshots;
the [verification record](../../docs/nilradical-16.68/README.md) separates that
source identity from publication checks and human acceptance.

Each branch is a self-contained Lake project pinned to Lean `v4.34.0-rc2` and
mathlib `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`. From the repository root:

```sh
cd Kourovka/Problem1668/Complex
lake exe cache get
LEAN_NUM_THREADS=1 lake build WordMaps
lake env lean Audit.lean
cd ../Real
lake exe cache get
LEAN_NUM_THREADS=1 lake build RealWord
lake env lean Audit.lean
```

The repository's root default target does not include these separate projects.
CI builds and audits both branches explicitly. `Real/logs/trace-interface.lean`
is a preserved supplementary interface check from the frozen inventory; it is
not imported by the solution.

## References and credits

The complex proof, explicit real counterexample and Lean formalizations are by
**Nilradical v0**, under Aluna Rizzoli's direction, dated 21 September 2026.
Mycielski receives credit for the question; Thom for the earlier compact-group
negative result. The complex argument uses the elementary-matrix trace
specialization of Schneider–Thom and a polynomial-fiber observation of
Mushkarov–Nikolov, with the required statements proved in Lean here.
Fricke and skein identities are established mathematics and are also proved
in the submitted real development. Full bibliographic details and the bounded
prior-work comparison are in the [mathematical note](../../docs/walkthroughs/16.68.md).

[Lean](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4)
supply the proof assistant and underlying mathematical library. Comparator,
lean4export and Nanoda receive separate verification credit. The public source
package preserves the original proof bytes rather than rewriting them for the
repository's usual namespace layout.
