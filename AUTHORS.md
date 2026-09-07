# Credits

Repository maintainer: Aluna Rizzoli.

Problem 21.3 was posed by M. Anagnostopoulou-Merkouri and T. C. Burness.
The proof development was extracted from Aluna Rizzoli's existing
Kourovka 21.3 project. Codex assisted with the Lean development and with
the extraction, public theorem interface, documentation, and verification.

Problem 21.29 was posed by T. C. Burness and M. Giudici. Its solution is due
to **Aluna Rizzoli and Adam R. Thomas**, in
[*Common neighbour conjectures for Saxl graphs fail at every base size*](https://arxiv.org/abs/2609.01367).
This repository formalizes one of their counterexamples. Codex assisted
with the Lean formalization and its certificate generator. The fixed-radix
encoding and the general affine-primitivity argument were adapted from
Aluna Rizzoli's existing Burness–Giudici Lean development; the concrete nine-dimensional group and
its certificates are formalized here directly.

The underlying library is [mathlib](https://github.com/leanprover-community/mathlib4),
maintained by the Lean mathematical community. It is an external pinned
dependency, not vendored source.
