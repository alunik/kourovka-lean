# Thompson-group foundations

These 16 Lean modules are the dependency closure used in the complete proof
of [Kourovka 21.38](../../Problems/P21_38/README.md), adapted from
[group-approximation](https://github.com/SauersML/group-approximation) at commit
`a39c9b72861bd04c71fc8e18876d13307851d777`.
Original copyright and authorship remain with the upstream contributors.
The upstream [Apache 2.0 license](LICENSE) is retained.

[provenance.json](provenance.json) records original module names, original
SHA-256 hashes, local paths, and local SHA-256 hashes. The source used Lean
4.32.0; the destination keeps this repository's Lean 4.34.0-rc2 and mathlib
`87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.

## Adaptations

The complete [source patch](adaptations.patch) is included. Import paths now
start with `Kourovka.External.GroupApproximation`; mathematical namespaces are
unchanged, and each file includes a modification notice. Compatibility edits
rename the `FreeGroup.induction_on` identity case from `C1` to `one`, replace
deprecated `if_pos`/`if_neg`/`dif_pos`/`dif_neg` with their current names, and
replace two proposition-valued `haveI` declarations with `have`. No theorem
statement, mathematical definition, axiom allowlist, or guard was weakened.

The reused development provides actual dyadic PL rational permutations,
Brown's presentation, the interval model, local supported maps, and a
commutator comparison. Golan-Polak's prescribed-generation theorem is
proved by the new [21.38 modules](../../Problems/P21_38/Proof/README.md).
It is not an imported assumption.

The axiom guard's calibration deliberately refers to rejected compiler
axioms to verify their rejection. They are absent from the dependencies of
the mathematical endpoints.
