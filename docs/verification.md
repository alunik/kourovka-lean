# Verification

Verified on 9 September 2026 on Auckland (`mathcompprd27`, Linux).
The [machine-readable receipt](21.99-verification.json) records the build,
dependency revisions, source digest, and independent certificate replay.

## Environment

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- mathlib: `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.
- All remaining dependencies: `lake-manifest.json`.

Every dependency checkout was checked clean at its manifest commit. The
repository was built in a separate directory, using cached dependencies.
The new 21.99 proof modules were elaborated from source. The full standard
build also checked the existing 21.3 and 21.29 solutions.

## Checks

```text
lake build
Build completed successfully (9187 jobs).
Exit status: 0

lake env lean Audit.lean
Exit status: 0
```

The guarded axiom audit verifies exactly:

```text
'Kourovka.P21_03.firstQuestion' depends on axioms:
[propext, Classical.choice, Quot.sound]

'Kourovka.P21_29.not_notebookStatement' depends on axioms:
[propext, Classical.choice, Quot.sound]

'Kourovka.P21_99.not_notebookStatement' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The audit prints all three public statements and theorems. Their conclusions are
unconditional. For 21.3, the existential cutoff is uniform over the subgroups
and covers both symmetric and alternating groups. For 21.29, Lean constructs
one finite primitive permutation group with a regular suborbit and proves
that the required simultaneous trivial stabilisers do not always exist.
For 21.99, Lean constructs a finite transitive action and proves that every
element carrying one specified point to another fixes exactly one point.
Passing to the image permutation group gives the unconditional negation of
the notebook assertion.

All 21.29 finite certificates were checked with `decide +kernel`. Its C++17
witness generator was compiled with `-O2 -Wall -Wextra -Werror` and reproduced
all committed certificate sources in the 7 September verification.

All 80 finite-check batches for 21.99 passed with `decide +kernel`: inverse
partners, generator transitions, quotient compatibility, and fixed-point
obstructions. An independent generator replay on Auckland reproduced all
142 emitted Lean files and their generation receipt byte-for-byte. Its
inputs are included in [scripts/data/21_99](../scripts/data/21_99/README.md).
The generator and prior C++/GAP searches are not trusted by the Lean proof.

[source.sha256](source.sha256) records all 414 Lean source, configuration,
generator, and generator-input files. Their hashes were checked against the actual build
directory before the successful build and audit. To check the checkout:

```sh
LC_ALL=C LANG=C shasum -a 256 -c docs/source.sha256
```

A source scan found no placeholder proofs, project axioms, unsafe
declarations, native evaluation, custom elaborators, or local filesystem
imports. The public statements and solutions compile without warnings.
All new 21.99 supporting modules also compile without warnings.
The inherited 21.3 supporting development still emits style and deprecation
warnings; those have not been suppressed and do not change the axiom audit.

The Auckland full build used eight workers and took 517.7 seconds; the
guarded audit took 11.3 seconds. Some unchanged supporting modules were
already available from the preceding build in the same directory.
Individual 21.99 kernel-check batches were observed using approximately
6 GiB of resident memory, so CI uses one worker on the
[standard private-repository runner](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).

CI repeats `lake build` and the guarded public-theorem audit on pushes and
pull requests. This record describes the successful Auckland run, not an
unobserved CI result.
