# Problem 16.68: workflow version correction

**22 September 2026.** The complex and real results are credited to
**Nilradical v1.0.0**. Their execution used the internal **`0.4.0-draft`**
workflow. The initial public attribution to Nilradical v0 inherited a stale
label from the local writeup.

The [v1.0.0 release](https://github.com/alunik/nilradical/releases/tag/v1.0.0),
published on 17 September 2026, explicitly distinguishes the public release
version from its internal execution version. Its pinned
[README](https://github.com/alunik/nilradical/blob/4d41912c80df71ef0d7ee565868600892578a21c/README.md#first-public-workflow-release)
and [publication adaptations](https://github.com/alunik/nilradical/blob/4d41912c80df71ef0d7ee565868600892578a21c/publication-adaptations.json)
map internal `0.4.0-draft` to public `1.0.0`; the older six results retain v0 credit.

The 21 September [complex](complex-verification.json) and
[real](real-verification.json) verification receipts record identical hashes for
`verify.py` and `sandbox.py`. Both match the internal workflow package and the
released [verifier](https://github.com/alunik/nilradical/blob/4d41912c80df71ef0d7ee565868600892578a21c/verification/verify.py)
and [sandbox](https://github.com/alunik/nilradical/blob/4d41912c80df71ef0d7ee565868600892578a21c/verification/sandbox.py).
The exact hashes and revision references are in the
[machine-readable correction](version-correction.json).

The initial publication at
[`77782846adb951ab7b231bfe272cc5e8fc7bc182`](https://github.com/alunik/kourovka-lean/commit/77782846adb951ab7b231bfe272cc5e8fc7bc182)
and the original proof source at
[`75b93ec1363f5ba4d138512a9dba13f749855f4e`](https://github.com/alunik/kourovka-lean/commit/75b93ec1363f5ba4d138512a9dba13f749855f4e)
remain preserved in repository history. This correction changes public version
credit and its explanatory provenance only. It does not alter the Lean proofs,
frozen source manifest, verification receipts, statement acceptance,
mathematical scope or prior-work credits.
