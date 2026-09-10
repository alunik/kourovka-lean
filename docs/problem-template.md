# Problem template

[Repository](../README.md) · [Contribution guide](../CONTRIBUTING.md)

Use `P21_03` below as a placeholder for the new problem ID. Pad the problem
number to at least two digits. Keep these common entry points:

```text
Kourovka/Problems/P21_03/
├── README.md
├── Statement.lean
├── Solution.lean
└── Proof/
    ├── README.md
    └── …
```

The statement module defines the question in namespace `Kourovka.P21_03`;
the solution module imports the statement and supporting proof, then proves
the public answer in that namespace. Use the existing entries as Lean
examples. Do not add an unfinished theorem to the accepted catalogue.

## Problem README

Copy the following into the problem directory, replace every placeholder,
and preserve the seven section headings. Links below are relative to the
problem directory. The top heading may identify an answered subquestion.

````markdown
# Problem 21.3

[All problems](../../../README.md#problems) · [Contributing](../../../CONTRIBUTING.md)

## Problem

Give the notebook's natural-language question, including the hypotheses,
quantifiers, and relevant subquestions. Identify the problem authors and
link to the exact source edition; give a page only if verified.

## Result and scope

State the answer and exactly what is formalized. Record restrictions,
unsettled subquestions, or the scope of the particular counterexample.
Credit the mathematical solution here when it comes from a separate work.

## Formal statement

Link the named assertion in [Statement.lean](Statement.lean) and the named
public theorem in [Solution.lean](Solution.lean). Explain any encoding
choices needed to relate Lean's definitions to the original question.

## Proof outline

Give a short numbered account of the mathematical argument. Include a
counterexample or construction here when needed, with additional level-three
headings if useful. Link the [proof roadmap](Proof/README.md).

## File guide

| File | Purpose |
| --- | --- |
| [README.md](README.md) | Question, answer, and scope |
| [Statement.lean](Statement.lean) | Public formulation of the question |
| [Solution.lean](Solution.lean) | Public answer |
| [Proof/README.md](Proof/README.md) | Supporting-module roadmap |

Add links to any detailed notes or certificate documentation actually used.

## Verification

From the repository root, build this solution:

```sh
lake build Kourovka.Problems.P21_03.Solution
```

Follow the [full build and audit instructions](../../../README.md#check-the-proofs).
Link any applicable [verification evidence](../../../docs/verification.md).
If certificates are used, explain their kernel checks and link the generator
and reproduction guide; external computations are not proof assumptions.

## References and credits

List the source edition, problem authors, solution references, and relevant
formalization provenance. Link [repository credits](../../../AUTHORS.md)
for contributors and material AI assistance.
````

## Proof roadmap

In `Proof/README.md`, link back to the problem README, statement, and
solution. Give the main modules in mathematical reading order and explain
how they reach the public endpoint. Use linked module names, group related
lemmas, and distinguish hand-written arguments from generated certificate
sources when applicable. There is no need to list every certificate shard.

The existing [21.3](../Kourovka/Problems/P21_03/Proof/README.md),
[21.29](../Kourovka/Problems/P21_29/Proof/README.md), and
[21.99](../Kourovka/Problems/P21_99/Proof/README.md) roadmaps show how this
works for proofs of different sizes.

## Register and check

Update the root catalogue, `Kourovka.lean`, `Audit.lean`, and credits as
described in the [contribution guide](../CONTRIBUTING.md#add-a-problem).
Run `python3 scripts/check_repository.py` to check the common structure and
links, then run the Lean build and guarded audit.

## Related collections

This layout draws on the source references and file conventions in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md#file-structure-conventions),
the numbered mathematical entry points in
[FormalBook](https://github.com/mo271/FormalBook), and the maintained
problem catalogue in [Compfiles](https://github.com/dwrensha/compfiles#dashboard).
Here, each accepted entry presents a complete formal answer, with the same
reader-facing structure and room for its own supporting argument.
