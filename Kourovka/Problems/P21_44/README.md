# Problem 21.44

[All problems](../../../README.md#problems) · [Contributing](../../../CONTRIBUTING.md)

## Problem

Problem 21.44 of the [21st edition of the Kourovka
Notebook](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/21tkt.pdf),
attributed to S. Eberhard, asks:

For each $n$, form $W_n=A_5\wr\cdots\wr A_5$ using $n$ copies of
$A_5$, with its natural five-point action at each stage. Thus $W_n$ acts
on $5^n$ points. Equip $W=\varprojlim W_n$ with the inverse-limit topology.
Does this group have a dense, finitely generated subgroup whose ordinary
word growth is subexponential?

The source used here is the September 2026 edition, printed page 174.
The ambient group has its usual inverse-limit topology.

## Result and scope

**Yes.** In right-action notation on the alphabet $\{1,2,3,4,5\}$, define

$$
a=(1,1,1,a,1)(1\,2\,3),\qquad
b=(b,1,1,1,1)(3\,4\,5).
$$

These recursions define one fixed pair of compatible automorphisms of the
rooted tree. The formalization proves that their ordinary generated
subgroup $G=\langle a,b\rangle$ is dense in the full group $W$ and that

$$
\lim_{n\to\infty}\frac{\log |B_S(n)|}{n}=0,
\qquad S=\{1,a,a^{-1},b,b^{-1}\}.
$$

Here $B_S(n)=S^n$ is the ordinary word ball. Including the identity makes
products of exactly $n$ letters equal to products of at most $n$ letters.
The formal endpoint establishes this limit; it does not assert the
additional explicit upper bound proposed in the research consultation.

The argument uses finite wreath-product generation and a direct count of
words with few sign changes, followed by a uniform section-length estimate.
Brieussel's work supplies context for this counting method; the degree-five
construction and all its required bridge lemmas are proved in the local
Lean modules.

## Formal statement

[Statement.lean](Statement.lean) defines
`Kourovka.P21_44.NotebookStatement` as

```lean
∃ H : Subgroup AutTree,
  H.FG ∧ Dense (H : Set AutTree) ∧ HasSubexponentialGrowth H
```

`AutTree` is the compatible-sequence subgroup of the product of the finite
wreath groups. Each finite level is discrete, and `AutTree` carries the
induced product topology. `HasSubexponentialGrowth` uses a finite symmetric
generating set containing the identity and the limit of the logarithm of
its actual ball cardinalities divided by the radius.

[Solution.lean](Solution.lean) proves:

- `Kourovka.P21_44.notebookStatement`: the complete existence statement;
- `Kourovka.P21_44.subexponential_growth`: the logarithmic limit for the
  displayed pair;
- `Kourovka.P21_44.generatedSubgroup_fg`: finite generation by that pair.

The supporting theorem `dense_generated_pair` proves density by
surjectivity onto every finite level.

Lean numbers the branches by `Fin 5` and uses the section multiplication
rule $(gh)_i=g_i h_{\sigma_g^{-1}(i)}$. Accordingly, `rootA` and `rootB`
store the inverses of the cycles $(0\,1\,2)$ and $(2\,3\,4)$; the active
sections are at branches $3$ and $0$. This is the inverse-reindexing
convention corresponding to the displayed right-action recursions.

## Proof outline

1. **Construct the inverse limit.** Define the finite wreath groups and
   their projections, then the compatible generators $a,b$. Prove the
   faithful decomposition into a root permutation and five sections.
2. **Prove full generation at every level.** For a perfect group
   $P=\langle u,v\rangle$ with $u^3=v^3=1$, the two directed lifts generate
   $P^5\rtimes A_5$. Pairwise surjectivity and perfectness recover the full
   base group. Induction applies this result to every finite wreath level,
   yielding density of the same pair upstairs.
3. **Shorten sections.** Normalize words using $a^3=b^3=1$. Let $V(w)$
   count sign changes at distance two in an alternating word. Sixteen
   signed five-letter blocks each save a section letter. Greedily selecting
   disjoint blocks proves
   $\sum_i\ell(g_i)+V(w)/10\le |w|+1$.
4. **Count the exceptional words.** Length, three initial bits, and the
   sign-change positions determine an alternating word. Bernoulli weights
   bound the number with $V(w)\le\delta n$ by
   $8(n+1)\exp(nH(\delta))$, where $H$ is binary entropy.
5. **Force growth rate zero.** Count the remaining elements injectively
   by their root permutation and actual sections. The resulting recurrence
   improves every positive candidate for the least exponential growth
   rate. Since $H(\delta)\to0$, that least rate is zero. The ordinary
   logarithmic growth limit follows.

See the [proof roadmap](Proof/README.md) for the module-level reading order.

## File guide

| File | Purpose |
| --- | --- |
| [README.md](README.md) | Question, construction, and scope |
| [Statement.lean](Statement.lean) | Public formulation of the question |
| [Solution.lean](Solution.lean) | Concrete growth theorem and public answer |
| [Proof/README.md](Proof/README.md) | Supporting-module roadmap |
| [Proof/THIRD_PARTY.md](Proof/THIRD_PARTY.md) | Exact provenance of the imported word-geometry foundations |
| [Proof/Certificates/README.md](Proof/Certificates/README.md) | Reproduction of the finite root-generation certificate |

## Verification

The Nilradical v0 strict check passed on 16 September 2026 for 6
selected endpoints: fresh compilation, independently reviewed statement
comparison, the three-axiom policy, and Lean plus Nanoda proof replay.
See the [verification evidence](../../../docs/nilradical-v0-verification/README.md)
and [statement review](../../../docs/nilradical-v0-verification/statement-audits/21.44.md).

Verified on 15 September 2026 with Lean `v4.34.0-rc2` and mathlib revision
`87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`. The target build passed
3,205 jobs with zero warnings, and the full repository build passed
9,324 jobs. The closed public endpoint passed the guarded axiom audit with
exactly `propext`, `Classical.choice`, and `Quot.sound`.
The repository structure, finite certificate replay, and source hashes
were also checked.

From the repository root:

```sh
lake build Kourovka.Problems.P21_44.Solution
python3 scripts/check_repository.py
LEAN_NUM_THREADS=1 lake build
lake env lean Audit.lean
git diff --check
```

The finite permutation facts and sixteen shortening blocks use ordinary
kernel-checked proofs, including `decide`. No external computation is a
proof assumption. The [certificate guide](Proof/Certificates/README.md)
records reproduction of the finite root-generation certificate.

The [verification receipt](../../../docs/21.44-verification.md) records the
checked source snapshot. The [statement audit](../../../docs/21.44-statement-audit.md)
checks the ambient inverse limit, topology, finite generation, and ordinary
word-growth conclusion. Follow the [repository verification
guide](../../../docs/verification.md) for the complete acceptance checks.

## References and credits

1. [*The Kourovka Notebook*, 21st
   edition](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/21tkt.pdf),
   September 2026 source edition, Problem 21.44, S. Eberhard, printed
   page 174.
2. Jérémie Brieussel, [*Amenability and non-uniform growth of some directed
   automorphism groups of a rooted tree*](https://doi.org/10.1007/s00209-008-0417-3),
   Mathematische Zeitschrift **263** (2009), no. 2, 265–293. The related
   sign-change counting argument is also presented in Proposition 3.6.6 of
   [his doctoral thesis](https://imag.umontpellier.fr/~brieussel/these_brieussel.pdf).
3. Konstantin Slutsky and contributors,
   [*recurrent-sections-lean*](https://github.com/kslutsky/recurrent-sections-lean/tree/2b68f638c3af39a18a0630fa4977bb749d97a14a),
   commit `2b68f638c3af39a18a0630fa4977bb749d97a14a`, Apache-2.0.
   The two imported modules provide ordinary word geometry and general
   logarithmic-growth facts; see [third-party provenance](Proof/THIRD_PARTY.md).

The construction, mathematical proof and Lean formalization are by
**Nilradical v0**, using Codex and GPT Pro. See [repository credits](../../../AUTHORS.md).

Cite **Nilradical v0**, this problem number and the exact source commit.
Machine-readable citation: [CITATION.cff](CITATION.cff).
