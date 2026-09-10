# Contributing a solution

Contributions must answer a precisely identified question or subquestion
from the Kourovka Notebook with a complete Lean proof. We prioritize recent
problems with clear formulations and mathematical interest.

## Add a problem

1. Identify the notebook edition, problem number, problem authors, and exact
   question answered. Explain the scope of the result, including any
   subquestions or thresholds it does not settle.
2. Create `Kourovka/Problems/P21_03/` using the
   [problem template](docs/problem-template.md), substituting the problem ID.
   Use at least two digits for the problem number: `P21_03`, `P21_29`,
   `P21_99`, `P21_100`.
3. State the question in `Statement.lean` using standard mathlib definitions
   wherever possible. Keep it independent of the proof. Put the public
   endpoint in `Solution.lean`, supporting modules in `Proof/`, and a reading
   map in `Proof/README.md`.
4. Add the solution import to [Kourovka.lean](Kourovka.lean), one row to the
   [problem catalogue](README.md#problems), and the statement, endpoint, and
   guarded endpoint axiom check to [Audit.lean](Audit.lean). Use the existing
   entries as examples.
5. Update [credits](AUTHORS.md), complete the checks below, and explain the
   result and validation in the pull request.

## Keep the documentation consistent

Every problem README uses these sections, in this order:

1. Problem
2. Result and scope
3. Formal statement
4. Proof outline
5. File guide
6. Verification
7. References and credits

Keep the README self-contained: include the natural-language question,
relevant qualifications, exact answer, and links to its public statement
and theorem. Place distinctive material, such as a counterexample, under
the appropriate section. The [template](docs/problem-template.md) gives
the content expected in each section.

Use `Proof/README.md` to explain the main modules in reading order. Internal
file names should describe the mathematics; different proofs need different
supporting modules. Add longer notes to `docs/` only when useful, and link
them from the problem README and [documentation index](docs/README.md).

If finite certificates are generated, commit the Lean sources needed for a
normal build. Document them in `Proof/Certificates/README.md`, include the
generator and its required inputs in `scripts/`, and add reproduction
instructions to the [certificate guide](scripts/README.md). Generate into a
fresh directory and compare against the committed files before replacing any
sources. Avoid committing binaries, build output, or temporary search files.

## Proof requirements

Retain normal mathematical hypotheses; do not assume an unresolved lemma,
classification, finite verification, or the desired conclusion. Review must
check that the formal statement faithfully answers the cited question,
including all quantifiers and subcases.

The contribution must build at the repository's pinned versions, and its
endpoint must depend only on `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project axioms, unsafe proof machinery, `native_decide`,
or `bv_decide` is accepted. Finite calculations must produce proofs checked
by the kernel; an external generator is not part of the trusted proof.

List human contributors and explain material AI assistance. Do not import
third-party source without retaining its attribution and license.

## Validate the contribution

Run from the repository root:

```sh
python3 scripts/check_repository.py
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Audit.lean
git diff --check
```

The Python check validates the documentation structure, catalogue/import/audit
coverage, and local Markdown links. It does not check mathematics; the Lean
build, guarded axiom audit, and statement review remain necessary. CI runs
the repository check before the Lean build and audit.

When certificate sources change, reproduce them and report the comparison
as well as the Lean build. Keep historical verification receipts intact;
record a new run separately when the verified source snapshot changes.
The [verification guide](docs/verification.md) explains the existing receipt.
