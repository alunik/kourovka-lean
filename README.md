# Kourovka in Lean

[![Lean proofs](https://github.com/alunik/kourovka-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/alunik/kourovka-lean/actions/workflows/lean.yml)

Complete, kernel-checked Lean proofs answering selected problems from
[*The Kourovka Notebook*](https://arxiv.org/abs/1401.0300v46).
Each entry connects the original question to a precise formal statement,
its proof, and reproducible verification instructions.

## Problems

| Problem | Answer and scope | Statement | Final theorem |
| --- | --- | --- | --- |
| [21.3, first question](Kourovka/Problems/P21_03/README.md) | **Affirmative** for symmetric and alternating groups in all sufficiently large degrees; no explicit cutoff | [Lean statement](Kourovka/Problems/P21_03/Statement.lean) | [`Kourovka.P21_03.firstQuestion`](Kourovka/Problems/P21_03/Solution.lean) |
| [21.29](Kourovka/Problems/P21_29/README.md) | **Negative**, by a primitive affine counterexample of degree 19,683 | [Lean statement](Kourovka/Problems/P21_29/Statement.lean) | [`Kourovka.P21_29.not_notebookStatement`](Kourovka/Problems/P21_29/Solution.lean) |
| [21.68](Kourovka/Problems/P21_68/README.md) | **Negative**, by a semiabelian group of order 2592 with an irreducible nonmonomial complex representation of degree 8 | [Lean statement](Kourovka/Problems/P21_68/Statement.lean) | [`Kourovka.P21_68.not_notebookStatement`](Kourovka/Problems/P21_68/Solution.lean) |
| [21.99](Kourovka/Problems/P21_99/README.md) | **Negative**, by a finite transitive action in which every element carrying one specified point to another fixes exactly one point | [Lean statement](Kourovka/Problems/P21_99/Statement.lean) | [`Kourovka.P21_99.not_notebookStatement`](Kourovka/Problems/P21_99/Solution.lean) |

Every listed answer has a complete proof checked by Lean. The permitted
foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The [guarded audit](Audit.lean) checks the public endpoints. External
computations and unproved classification assumptions cannot stand in for proofs.

## Check the proofs

Install [elan](https://github.com/leanprover/elan), then clone the repository
and run the build:

```sh
git clone https://github.com/alunik/kourovka-lean.git
cd kourovka-lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The [Lean toolchain](lean-toolchain) and [dependencies](lake-manifest.json)
are pinned. On a machine with 8 GB of RAM, use
`LEAN_NUM_THREADS=1 lake build`; CI uses this setting for the larger finite
checks. Each problem's README also gives a command to build its solution alone.

The normal build uses the committed Lean certificates. To reproduce their
generation separately, see the [certificate guide](scripts/README.md).
The [verification record](docs/verification.md) documents the recorded build,
axiom audit, and source hashes.

## Read a solution

Start with the problem README for the question, answer, and scope. Then read
`Statement.lean` for the exact quantifiers and `Solution.lean` for the final
theorem. Each `Proof/README.md` maps the supporting argument to its Lean modules.

```text
Kourovka/Problems/P21_03/       # Same entry points for every problem
├── README.md                 # Question, scope, formal statement, proof guide
├── Statement.lean            # Public question, independent of its proof
├── Solution.lean             # Public answer
└── Proof/
    ├── README.md             # Roadmap to supporting modules
    └── …                     # Lemmas and any kernel-checked certificates
```

[`Kourovka.lean`](Kourovka.lean) imports all accepted solutions.
[`docs/`](docs/README.md) holds longer explanations and verification records;
[`scripts/`](scripts/README.md) holds repository checks and certificate generators.

## Contribute

Use the [contribution guide](CONTRIBUTING.md) and
[problem template](docs/problem-template.md) to add an entry with the same
structure. Check the catalogue, problem layout, audit coverage, and local
documentation links without installing Lean:

```sh
python3 scripts/check_repository.py
```

For mathematical provenance, human contributors, and material AI assistance,
see [credits](AUTHORS.md). Repository citation metadata is in
[`CITATION.cff`](CITATION.cff).
