# Frobenius integration: author self-review

Date: 2026-09-20. Reviewer: coding agent responsible for this integration. This is a source-level self-review, not an independent mathematical review or a compiler/axiom certificate.

The public theorem `Kourovka2135.hasNormalPComplement_of_normalizer_centralization` assumes precisely that `G` is a finite group, `p` is prime, and every element of order prime to `p` in the normalizer of every `p`-subgroup centralizes that subgroup. There is no additional Frobenius assumption, classification assumption, odd-order restriction, solvability hypothesis, or restriction to nontrivial subgroups.

For distinct primes `q` and `p`, every element of a `q`-subgroup has order coprime to `p`. The public hypothesis consequently makes every `q`-subgroup normalizing a `p`-subgroup centralize it. The imported theorem `OddOrder.Isaacs.Ch05.hasNormalPComplement_of_prime_subgroups_centralize` turns this into a normal `p`-complement via Frobenius' criterion. Its intermediate quotient is the normalizer modulo the centralizer restricted to that normalizer, so the construction also covers nonabelian `p`-subgroups correctly.

The imported complement predicate provides one normal subgroup complementing every Sylow `p`-subgroup. The conversion selects any Sylow subgroup: the complement's order is prime to `p`, while its index equals the order of that Sylow subgroup and is therefore a power of `p`. This is exactly the existing project predicate `HasNormalPComplement`; it is not a normal Sylow-subgroup assertion.

The underlying Frobenius proof is attributed to Yawara Ishida's Apache-2.0 `yawara/odd-order` development at commit `82e8b66fe80a2eb9f0c6568bf288186086af73af`, Isaacs Ch.5, Theorem 5.26. The complete 42-module local import closure was retained. No source from unlicensed BurnsidePQ was copied. Original source hashes, adapted hashes, license, and compatibility edits are recorded beside this review. The two public adapter proofs in `FrobeniusCriterion.lean` are new project integration code.

The root agent reports all 42 vendor modules strictly compiled. Compilation of the project adapter and final transitive axiom checks remain the root agent's acceptance gate. Static lexical inspection after stripping nested comments and strings found no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` tokens in the imported closure. This lexical check does not replace the pending compiler and axiom audit.
