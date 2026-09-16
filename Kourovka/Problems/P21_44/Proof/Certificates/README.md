# Finite certificates for Problem 21.44

[Proof roadmap](../README.md) · [Certificate guide](../../../../../scripts/README.md#problem-2144)

## Root-generation certificate

The generated certificate is the inline `rootWords` definition in
[WreathGeneration.lean](../WreathGeneration.lean). It contains 60 words in
two Boolean letters: `true` means `rootA`, and `false` means `rootB`.
Its longest word has length eight.

The standard-library-only [Python generator](../../../../../scripts/21_44_root_words.py)
uses these explicit permutations, written as zero-based image lists:

- `rootA = [2, 0, 1, 3, 4]`, the inverse of `(0 1 2)`;
- `rootB = [0, 1, 4, 2, 3]`, the inverse of `(2 3 4)`.

Multiplication is `(p * q)(i) = p(q(i))`, matching Lean's permutation
convention. Breadth-first search starts with the empty word and appends
`rootA` before `rootB` at every vertex. First-discovery order determines the
list order. The generator also checks independently that the discovered
permutations are exactly the 60 even permutations on five points.

The reproduced fragment starts at
`private def rootWords : List (List Bool) :=` and ends with the final newline
after its closing brackets. It excludes the preceding documentation and the
blank separator before `set_option maxRecDepth 100000 in`. The comparison
checks every byte within those definition boundaries.

## Reproduce and compare

Run from the repository root:

```sh
repro_dir=$(mktemp -d)
python3 scripts/21_44_root_words.py --output-dir "$repro_dir" --check
```

This writes `rootWords.lean.fragment` into the fresh directory and compares
it with the existing inline definition. Success reports `PASS` and exits
with status zero. The generator never replaces the Lean module. Use
`--output FILE` to choose a fragment filename, or `--check SOURCE` to compare
another copy of the module.

The normal Lean build consumes the inline list. The private theorem
`rootWords_cover` uses ordinary `decide` to prove that every element of
`A5` occurs among the evaluated words. `roots_generate` then proves subgroup
generation from this coverage. The Python computation is outside the trusted
proof; its output is checked by the Lean kernel.

## Other finite checks

[Shortening.lean](../Shortening.lean) checks all 16 five-letter shortening
patterns by four Boolean case splits followed by ordinary `decide`.
These cases come directly from the quantified theorem statement and need
no external certificate generator. The root permutation identities are
also checked directly in Lean.
