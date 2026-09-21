# Independent exact-statement challenge review — 2026-09-20

Reviewer: quasisimple-assumption worker. This review prepares the three
statement-only declarations in `Challenge.lean`; it is not a human acceptance
record, a Comparator pass, or a kernel-axiom audit. No builds or sync were run.
The challenge must be compiled in its separate trusted environment, never
imported into the submitted proof project. Only its three placeholder theorem
bodies use `sorry`; those bodies are not proof evidence.

## Source-to-statement judgment

I read the original intake `problem.md`, the cached September 2026 Notebook
entry 21.35 (`sources/notebook-sept2026.txt`, lines 8183–8189, printed page 172),
and the cached author preprint's introduction defining P(w,p), single values,
and the generated verbal subgroup. The intake identifies the primary PDF as
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/21tkt.pdf
and the author preprint as arXiv:2105.14474v1. This is a local cached-source
review, not a fresh web or priority-status check.

Judgment: the three challenge types faithfully express the full intended
conditional theorem. `problem2135_outerWord` is its explicit arbitrary-word
form, `problem2135` uses the existing exact `Problem2135` definition, and the
third combines that implication with the original converse. I checked the
full binder order, universes, finite/group instances, prime hypothesis, two
explicit approved assumptions, and conclusions against `ProblemComplete`.
No restriction on group solubility, prime, word shape, or order of the second
value has been added. Universe-zero external hypotheses suffice because all
finite groups can be transported to universe zero; the conclusion remains
polymorphic in `Type u`.

## Frozen-definition semantic review

- `OuterWord` has a leaf and arbitrary binary brackets. Its recursive input
  type is a product of the children's inputs, so even identical-looking
  subtrees use independent variables. It captures multilinear outer
  commutators in disjoint variables. The commutator convention is
  a^-1 b^-1 a b. The included leaf case adds the valid one-variable base case;
  it does not omit any commutator word requested by the Notebook.
- `OuterWord.values` is the range of one evaluation, not a generated subgroup
  or products of evaluations. `verbalSubgroup` is the actual subgroup closure
  of exactly that set.
- `ProductOrderCondition` quantifies x and y in the single-value set, with
  not-p-divides-order(x) and p-divides-order(y), then requires
  p-divides-order(x*y). For finite groups and prime p this is exactly the
  source's p'-order condition. The y quantifier includes all mixed-order
  p-divisible values. The preprint's additional word "non-trivial" is already
  implied by divisibility of order(y) by a prime.
- `HasNormalPComplement` asks for an actual normal subgroup with order
  coprime to p and index p^n. In the final conclusion that ambient group is
  the actual verbal subgroup. This is p-nilpotence, not a normal Sylow
  p-subgroup and not nilpotence.
- `MinimalSimpleClassification` quantifies actual finite nonabelian simple
  groups with every proper subgroup soluble. Its models are PSL(2,2^f) for
  prime f; PSL(2,3^f) for prime f unequal to 2; PSL(2,ell) for prime ell>3
  with 5 dividing ell^2+1; Suzuki(2^(2m+1)) for m>0 with prime 2m+1; and
  PSL(3,3). The definition uses actual concrete group models and multiplicative
  equivalences, not opaque family labels. No commutator, multiplier, lifting,
  or Frobenius assertion is packed into this classification premise.
- The other hypothesis is imported at its exact reviewed definition from
  `QuasisimpleCoprimeCommutators`. Because I authored that module, its
  independent semantic acceptance is supplied by the central-endpoint
  worker's `quasisimple-review.md`, which I read and pin below. That record
  verifies actual finite perfect groups, actual nonabelian simple central
  quotient, coprimality with the actual center cardinality, and a single
  ordinary commutator conclusion. This review does not pretend to be an
  independent review of my own hypothesis implementation.

## Challenge isolation and pins

The challenge imports only `Statement`, `MinimalSimpleModels`, and the
independently reviewed `QuasisimpleCoprimeCommutators`; it does not import
`ProblemComplete`, `CentralQuasisimpleComplete`, or the root project module.
The approved-definition modules contain earlier helper proofs, but none of
the three challenged declarations. Freeze the files below before configuring
Comparator; use the separately generated full source-closure manifest for
transitive dependency binding. The source SHA-256 values below bind this
review's exact direct inputs. They do not assert that Comparator has run.

Toolchain: `leanprover/lean4:v4.34.0-rc2`.
Mathlib revision: `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.
The pinned lake manifest binds the remaining package revisions.

```text
33c0f09e1b0161065727fc216041a0838e566a961bec8e891d7a034b441622e3  problem.md
2fcce9b98a4df10267fe120229217bfe556c70510704e311540da0cef438f911  sources/notebook-sept2026.pdf
a1fe8609f6f544d72f5d8bb4507cd208b70ef16f44ec2af6d320dc4494acc2d5  sources/notebook-sept2026.txt
12c0c1701c3a5d14a2705b703dae6ee11ee84944db655c37902eecd4104d2baa  sources/contreras-grazian-monetta-2105.14474v1.pdf
b9b7262579d3a14f2b4dad38f784e29f1a01d7cf2a20b43849bd83106a5c88cf  sources/contreras-grazian-monetta-2105.14474v1.txt
8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88  lean/lean-toolchain
8386b9b9ebd367dfdddb8652078510bb4623c1036165ae3075f9eaa17e08034a  lean/lakefile.toml
b300ba9a8449fd027357d73315a391147004b3bdeda15b3547776e8417e9a4ee  lean/lake-manifest.json
71558e1cef4230b9cc8e5abeb166ac837a10c63f8b4acbc11f20467c8bb6cb03  lean/Kourovka2135/OuterWord.lean
6b474d355e5396989e19ce08ce474770a2e344febd16535414cec22b59c6206f  lean/Kourovka2135/Complement.lean
2d0a58ca49ec8cd0a5694f8cc4faccb1250d73b4919de733ec7257d829170452  lean/Kourovka2135/Statement.lean
a18e09e9865b8e4c04f05edd2366874d523f373a520774441062018722078091  lean/Kourovka2135/MinimalSimpleModels.lean
003a82225bda28032477a4aa4f33cc45f793eaa8df444ac196d683402e9495db  lean/Kourovka2135/QuasisimpleCoprimeCommutators.lean
acc5fe6f682623243fec4f22d594fc8d8aee1fab090d7233bafc662496f5ee61  lean/Kourovka2135/ProblemComplete.lean
3d257142cad5d7f49035fa1412ecc17a43faaa2faf8c20cdf78f7590c201bca6  lean/verification/final-conditional-20260920/quasisimple-review.md
10197d78ade4a115a703062db62af37feda562fa2dce481a8e3297f64569ce94  lean/verification/final-conditional-20260920/Challenge.lean
```

## Final pre-freeze refresh

Re-read the current `ProblemComplete.lean` and
`CentralQuasisimpleComplete.lean`, and checked the root import of
`Kourovka2135.ProblemComplete`. The private least-counterexample proof uses
its obtained `groupH` and `finiteH` instances. The centralization interface
now spells the normalizer explicitly as `Subgroup.normalizer (P : Set G)`;
this is the intended set normalizer of the actual subgroup, with no changed
mathematical condition. All three full challenged theorem type texts still
match exactly, including universe and hypothesis binders. The direct-input
hash list above has been refreshed to the current bytes.

Additional final assembly source pins:

```text
8cfbff39406a20f26aca5c2e7105216bb0e483a2d3b9857ea7b99b4876235c74  lean/Kourovka2135/CentralQuasisimpleComplete.lean
fe355930922f33e390f56fa75c1b5720277f06bdc79a05db063ce396a244015c  lean/Kourovka2135.lean
```
No build, Comparator, Nanoda, runtime-canary, or human-acceptance pass is asserted by this refresh.
