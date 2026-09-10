# Repository checks and certificate reproduction

[Repository](../README.md) · [Contributing](../CONTRIBUTING.md)

## Repository check

Run `python3 scripts/check_repository.py` from the repository root. It needs
Python 3.9 or later and Git, with no Lean installation or third-party Python packages.
It checks the common problem layout and README sections, the catalogue,
solution imports, guarded audit coverage, and local Markdown links.
External URLs are not fetched. The Lean build and axiom audit remain the
proof checks; see [verification](../docs/verification.md).

## Certificate generators

The normal Lean build checks committed certificate sources and does not run
these generators. Their outputs are untrusted data: Lean checks the supplied
witnesses and identities using `decide +kernel`.

| Problem | Generator | Input | Documentation |
| --- | --- | --- | --- |
| [21.3](../Kourovka/Problems/P21_03/README.md) | None | None | [Proof roadmap](../Kourovka/Problems/P21_03/Proof/README.md) |
| [21.29](../Kourovka/Problems/P21_29/README.md) | [C++17](generate_21_29.cpp) | Construction encoded in the generator | [Reproduce below](#problem-2129) · [Certificates](../Kourovka/Problems/P21_29/Proof/Certificates/README.md) |
| [21.99](../Kourovka/Problems/P21_99/README.md) | [Python 3](generate_21_99.py) | [Sealed affine model and sparse certificate](data/21_99/README.md) | [Reproduction commands](data/21_99/README.md#reproduce-and-compare) · [Certificates](../Kourovka/Problems/P21_99/Proof/Certificates/README.md) |

## Problem 21.29

The C++17 generator searches for finite witnesses for the concrete group in
[LinearGroup.lean](../Kourovka/Problems/P21_29/Proof/LinearGroup.lean).
It writes the Lean certificate modules deterministically. With a C++17
compiler installed, run from the repository root:

```sh
repro_dir=$(mktemp -d)
c++ -O2 -std=c++17 -Wall -Wextra -Werror scripts/generate_21_29.cpp -o "$repro_dir/generate_21_29"
"$repro_dir/generate_21_29" "$repro_dir/Certificates"
diff -ru -x README.md -x '._*' Kourovka/Problems/P21_29/Proof/Certificates "$repro_dir/Certificates"
```

A successful `diff` exits with status 0 and produces no output. The comparison
excludes the hand-written certificate README and macOS metadata. The temporary
directory retains the regenerated sources for inspection.

The group index is `64 * p + d`. The six bits of `d` choose two signs on
each residue block; their product determines the third. Indices `p < 9`
encode rotations, and the other nine indices encode reflections. Vector
indices are little-endian ternary encodings. These conventions match
[FiniteModel.lean](../Kourovka/Problems/P21_29/Proof/FiniteModel.lean),
whose coverage theorems are proved in Lean.

There are 154 obstruction modules (128 vectors per module, 99 in the last)
and 18 regular-vector modules (64 group elements each).
[Checks.lean](../Kourovka/Problems/P21_29/Proof/Certificates/Checks.lean)
combines their results. Splitting the checks keeps kernel reductions bounded.
Every supplied witness is checked in Lean against the actual group action;
the generator's output alone establishes no theorem.

## Problem 21.99

The Python generator emits sparse matrix definitions, finite-check batches,
and a generation receipt. Its inputs and a command that regenerates into a
fresh directory and compares all emitted files are in the
[source-data guide](data/21_99/README.md#reproduce-and-compare).
The recorded independent replay ran on Auckland; its results are preserved
in the [verification record](../docs/verification.md).

See the [proof roadmap](../Kourovka/Problems/P21_99/Proof/README.md) for the
hand-written modules that turn those finite checks into the public theorem.
