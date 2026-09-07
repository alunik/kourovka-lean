# Kourovka in Lean

Complete Lean proofs answering selected problems from the Kourovka Notebook,
with an emphasis on recent, precisely stated questions.

| Problem | Result | Formal theorem |
| --- | --- | --- |
| [21.3, first question](Kourovka/Problems/P21_03/README.md) | Affirmative, for both symmetric and alternating groups in all sufficiently large degrees | [`Kourovka.P21_03.firstQuestion`](Kourovka/Problems/P21_03/Solution.lean) |
| [21.29](Kourovka/Problems/P21_29/README.md) | Negative, by a primitive affine counterexample of degree 19,683 | [`Kourovka.P21_29.not_notebookStatement`](Kourovka/Problems/P21_29/Solution.lean) |

Every listed answer has a complete proof checked by Lean. The admitted
foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
External computations and unproved classification assumptions cannot stand
in for proofs.

## Check the proofs

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The toolchain and all dependencies are pinned. `Audit.lean` displays the
public statements and verifies their axiom dependencies. CI runs the build and
audit. See [verification](docs/verification.md) for the recorded build.

## Organization

Each problem has a `README.md` giving the notebook's natural-language
formulation, the exact question answered, and a compact summary of the Lean
strategy. Beside it are `Statement.lean`, `Solution.lean`, and a `Proof/`
directory for supporting lemmas. Additional notes may live in `docs/`.
`Kourovka.lean` imports every accepted solution.

See [contribution rules](CONTRIBUTING.md) and [credits](AUTHORS.md).
