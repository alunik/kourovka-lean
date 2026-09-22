# Kourovka 16.68: complex and real word maps

The complex branch has an affirmative answer: every nonidentity word in two variables is surjective on PSL₂ over every algebraically closed field of characteristic zero. The real branch has a negative answer: an explicit nonidentity word has trace greater than 7/4 on every pair in SL₂(ℝ), so its projective word map misses the specified involution class.

Both statements were accepted by a human statement verifier on **21 September 2026**, after the protected checks had passed. Publication was authorized separately on **22 September 2026**. The compact SO₃(ℝ) negative answer is established work of Andreas Thom; it is not among these Lean endpoints. The research and formalization are credited to **Nilradical v1.0.0**, using the internal `0.4.0-draft` execution workflow. The [22 September version correction](version-correction.md) records the supporting evidence and preserves the original proof and verification records.

- [Problem and proof guide](../../Kourovka/Problem1668/README.md).
- [Human statement acceptance and publication scope](acceptance.json).
- [Exact source manifest](source-manifest.json) and [source comparison](source-identity-review.md).
- [Fresh publication build and axiom checks](publication-checks.json).
- [Verification summary](verification.json), sanitized [complex receipt](complex-verification.json) and [real receipt](real-verification.json).
- Exact original [complex checker log](complex-verification.log.txt) and [real checker log](real-verification.log.txt).
- Sanitized [complex contract](complex-contract.json) and [real contract](real-contract.json).
- [Statement correspondence](statement-review.md) and [bounded literature assessment](novelty-release.md).
- [Mathematical note](../walkthroughs/16.68.md).

The combined manifest preserves all **23 files** covered by the two original contracts, including the frozen auxiliary real interface. The ten complex Lean files and six real project Lean files contain the proved modules. The auxiliary interface is an archived specification, not a production proof. Publication audit files and documentation are outside that frozen inventory.

Comparator, Nanoda and Lean's default kernel accepted both frozen targets. The logs contain expected `sorry` warnings in the external independent challenges, whose statement placeholders are not submitted proofs and are not imported by the production modules. The permitted production axioms are `propext`, `Quot.sound` and `Classical.choice`.

The public contracts and receipts are explicitly sanitized derivatives: their original byte hashes are preserved, while machine-local paths are removed. Original identity-bearing approval records and operational records remain private. Later human statement approval does not retrospectively change historical receipt fields saying that approval was not yet recorded. No separate human novelty or contribution approval is claimed. The mathematical note is agent-generated, informal and not refereed.
