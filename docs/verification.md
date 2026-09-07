# Verification

Verified on 7 September 2026 on Auckland (`mathcompprd27`, Linux).

## Environment

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- mathlib: `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.
- All remaining dependencies: `lake-manifest.json`.

The mathlib checkout was checked clean at the pinned commit. The repository
was built in a separate directory, using cached mathlib dependencies.
Both problems' proof modules were elaborated from source.

## Checks

```text
lake build
Build completed successfully (9036 jobs).
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
```

The audit prints both public statements and theorems. Both conclusions are
unconditional. For 21.3, the existential cutoff is uniform over the subgroups
and covers both symmetric and alternating groups. For 21.29, Lean constructs
one finite primitive permutation group with a regular suborbit and proves
that the required simultaneous trivial stabilisers do not always exist.

All 21.29 finite certificates were checked with `decide +kernel`. Its C++17
witness generator was compiled with `-O2 -Wall -Wextra -Werror`; a fresh run
reproduced all committed certificate sources exactly.

[source.sha256](source.sha256) records all 260 Lean source, configuration,
and generator files. Their hashes were checked against the actual build
directory before the successful build and audit. To check the checkout:

```sh
shasum -a 256 -c docs/source.sha256
```

A source scan found no placeholder proofs, project axioms, unsafe
declarations, native evaluation, custom elaborators, or local filesystem
imports. The public statements and solutions compile without warnings.
The inherited 21.3 supporting development still emits style and deprecation
warnings; those have not been suppressed and do not change the axiom audit.

CI repeats `lake build` and the guarded public-theorem audit on pushes and
pull requests. This record describes the successful Auckland run, not an
unobserved CI result.
