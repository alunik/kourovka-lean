# Credits

The retained discovery catalogue and its formal proofs are credited to **Nilradical v0**.
Nilradical uses Codex and GPT Pro for mathematical exploration, independent
review, Lean development and verification. Original mathematical and code
sources are credited below.

Problem 21.3 was posed by M. Anagnostopoulou-Merkouri and T. C. Burness.
The solution of its first question and its Lean proof are by Nilradical v0.

Problem 21.29 was posed by T. C. Burness and M. Giudici. Its solution is due
to **Aluna Rizzoli and Adam R. Thomas**, in
[*Common neighbour conjectures for Saxl graphs fail at every base size*](https://arxiv.org/abs/2609.01367).
This repository formalizes one of their counterexamples. Codex assisted
with the Lean formalization and its certificate generator. The fixed-radix
encoding and the general affine-primitivity argument were adapted from
Aluna Rizzoli's existing Burness–Giudici Lean development; the concrete nine-dimensional group and
its certificates are formalized here directly.

The original spread-one question appears as Question 2 in C. Donoven and
S. Harper's [*Infinite 3/2-generated groups*](https://doi.org/10.1112/blms.12356)
(2020), before its inclusion as Notebook Problem 21.38. The affirmative
construction and formal proof are by Nilradical v0. The generation argument
specializes G. Golan-Polak's published prescribed-generation theorem; the
required specialization and its local interpolation dependencies are proved
in Lean here. The concrete Thompson-group foundations are adapted from the
[Apache-licensed group-approximation development](Kourovka/External/GroupApproximation/README.md),
with its exact source revision, original hashes, license, and adaptation
patch retained.

Problem 21.40 is attributed to A. Dantas and E. de Melo in the Notebook.
The exact question is present in the initial twenty-first-edition arXiv
version dated 8 January 2026; the [provenance review](docs/21.40-context.md)
distinguishes that verified source from any earlier original formulation.
The affirmative solution, quantitative structural theorem, and number-field
extension and their formal proofs are by Nilradical v0. The provenance
review identifies the verified formulation. Newton–Girard code is adapted
from the TNLean contributors' work in LionSR/QICLean, and the unitriangular
commutator filtration from the Tau Ceti contributors' work. Their
[exact source revisions and Apache license](Kourovka/Problems/P21_40/Proof/THIRD_PARTY.md)
are retained. Number-field heights and Northcott finiteness use existing mathlib.

Problem 21.44 was posed by Sean Eberhard. The explicit two-generator
construction and formal proof are by Nilradical v0. The proof
uses directed tree automorphisms and sign-change counting, with the related
work of J. Brieussel credited in the [problem references](Kourovka/Problems/P21_44/README.md#references-and-credits).
Ordinary word geometry and elementary exponential-growth lemmas are adapted
from Konstantin Slutsky and contributors' Apache-licensed
`recurrent-sections-lean` development. Its [exact provenance, retained notices,
and local changes](Kourovka/Problems/P21_44/Proof/THIRD_PARTY.md) are recorded.

Problem 21.68 was posed by M. Kida. The counterexample and formalization are
by Nilradical v0. Kida's *On semiabelian groups* already supplies the relevant
semiabelian complement containing the binary tetrahedral subgroup; the
embedding used here is proved explicitly. The induction infrastructure is
adapted from the Tau Ceti contributors' Apache-licensed work, with its
[exact provenance and license](Kourovka/External/TauCeti/README.md) retained.

Problem 21.99 was posed by Peter Müller. This counterexample and its Lean
development are by Nilradical v0. This result is excluded from the
discovery catalogue: Kyrylo Muliarchyk also gives a complete counterexample
in [his solution](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_21.99_solution.pdf),
and public priority is unresolved. The independent GAP
checks and Lean compilation were run on Auckland.

Problem 21.106 is attributed to M. Petschick in the Notebook. The original
question appears in Martina Conte and J. Moritz Petschick's
[*Conciseness of first-order formulae*](https://arxiv.org/abs/2505.01411v1)
(2025), before its inclusion in the 2026 Notebook. The Heisenberg
counterexample and its formalization are by Nilradical v0. The group and
formula are formalized directly here using mathlib; no third-party source
is vendored for this result.

The underlying library is [mathlib](https://github.com/leanprover-community/mathlib4),
maintained by the Lean mathematical community. It is an external pinned
dependency, not vendored source.

## Nilradical v1.0.0: Problem 21.53

Nilradical v1.0.0 supplies the complete counterexample and Lean formalization
for I. B. Gorshkov's Problem 21.53. The actual research run used the internal
`0.4.0-draft` workflow; this is its first public v1 release. Wilson's matrices,
Coolsaet's earlier construction, established group-theoretic arguments and
pinned Apache-2.0 TauCeti proofs retain their credit in the
[result README](Kourovka/Problem2153/README.md). Both human decisions and the
independent reviews are linked in the [verification record](docs/nilradical-21.53/README.md).

## Nilradical v1.0.0: Problem 21.35

The general word and extension arguments, their assembly and the conditional
Lean formalization are by Nilradical. The question, earlier lower-central and
soluble derived-word results, and centralization argument are due to Yerko
Contreras Rojas, Valentina Grazian and Carmine Monetta. Thompson's minimal-simple
classification and the coprime-commutator consequence of Liebeck–O'Brien–Shalev–Tiep
remain explicit mathematical inputs. All prior mathematics and reused code are
credited in the [mathematical note](docs/walkthroughs/21.35.md) and
[full credits](docs/walkthroughs/21.35-credits.md), including Yawara Ishida and the
OddOrder contributors, Qiuzhen-CFSG, Tau Ceti, mathlib and Lean. Original notices,
licenses and pinned provenance accompany the source.

**Final-stage approver: Aluna Rizzoli.** Both the statement and bounded contribution
assessment were accepted on 21 September 2026; see the
[source-bound acceptance and verification record](docs/nilradical-21.35/README.md).
