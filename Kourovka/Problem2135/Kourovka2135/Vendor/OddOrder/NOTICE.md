# OddOrder Frobenius criterion dependency

Copyright (c) 2026 Yawara Ishida and the authors listed in individual source headers.
Released under Apache-2.0; see LICENSE.

Source: https://github.com/yawara/odd-order at 82e8b66fe80a2eb9f0c6568bf288186086af73af.
This is the recursive local import closure of OddOrder.Isaacs.Ch05_Transfer.Main.
Local import paths are rewritten; declaration namespaces and proofs are retained.
Original source hashes and files are recorded in FROBENIUS_PROVENANCE.json.

Compatibility patch for Lean 4.34: deprecated `if_pos` / `if_neg` aliases are replaced by `ite_eq_left` / `ite_eq_right`, which have the same hypothesis and conclusion.

Mathlib compatibility: three `Group.isNilpotent_of_finite_tfae.out` calls now use one-based indices, preserving nilpotence, normalizer condition, and Sylow-normality propositions.

Lean 4.34 compatibility: the deprecated `if_false` alias is replaced by `ite_false`.
