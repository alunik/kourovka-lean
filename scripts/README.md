# Reproducing the 21.29 certificates

The C++17 generator searches for finite witnesses for the concrete group in
`Kourovka/Problems/P21_29/Proof/LinearGroup.lean`. It writes the Lean certificate
modules deterministically. Run from the repository root:

```sh
c++ -O2 -std=c++17 -Wall -Wextra -Werror scripts/generate_21_29.cpp -o /tmp/generate_21_29
/tmp/generate_21_29 /tmp/kourovka-21-29-certificates
diff -ru Kourovka/Problems/P21_29/Proof/Certificates /tmp/kourovka-21-29-certificates
```

The group index is `64 * p + d`. The six bits of `d` choose two signs on
each residue block; their product determines the third. Indices `p < 9`
encode rotations, and the other nine indices encode reflections. Vector
indices are little-endian ternary encodings. These conventions match
`FiniteModel.lean`, whose coverage theorems are proved in Lean.

There are 154 obstruction modules (128 vectors per module, 99 in the last)
and 18 regular-vector modules (64 group elements each). `Checks.lean`
combines their results. Splitting the checks keeps kernel reductions bounded.
Every supplied witness is checked in Lean against the actual group action;
the generator's output alone establishes no theorem.
