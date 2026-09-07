# Verification

Verified on 7 September 2026 on Auckland (`mathcompprd27`, Linux).

## Environment

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- mathlib: `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.
- All remaining dependencies: `lake-manifest.json`.

The mathlib checkout was checked clean at the pinned commit. The repository
was built in a separate directory, using cached mathlib dependencies.
The problem's relocated proof modules were elaborated from source.

## Checks

```text
lake build
Build completed successfully (8856 jobs).
Exit status: 0

lake env lean Audit.lean
Exit status: 0
```

The guarded axiom audit verifies exactly:

```text
'Kourovka.P21_03.firstQuestion' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The audit also prints the full definition of `FirstQuestion` and the public
theorem. The conclusion is unconditional; its existential cutoff is uniform
over the subgroups and covers both symmetric and alternating groups.

[source.sha256](source.sha256) records all 79 Lean source and configuration
files. Their hashes were checked against the actual build directory before
the successful audit. To check the checkout against that record:

```sh
shasum -a 256 -c docs/source.sha256
```

A source scan found no placeholder proofs, project axioms, unsafe
declarations, native evaluation, custom elaborators, or local filesystem
imports. The public statement and solution compile without warnings.
The inherited supporting development still emits style and deprecation
warnings; those have not been suppressed and do not change the axiom audit.

CI repeats `lake build` and the guarded public-theorem audit on pushes and
pull requests. This record describes the successful Auckland run, not an
unobserved CI result.
