# Verification implementation evidence — 16 September 2026

**The supported macOS integrity gate is operational.** Eighteen real Lean controls, seven guardrail regressions and the complete public Kourovka 21.106 endpoint passed their required outcomes. This does not imply human statement approval, a completed novelty audit, or acceptance of the other repository results.

## Tested implementation and pins

- Runner SHA-256: `ebfd71d5e0392c1b55f35256c39a75d1fdb83ccd476edefcdf21fd362291648f`.
- Seatbelt adapter SHA-256: `76c455a4b6f3798f19e3c3ead9474ddfeac5e4e677c768b5c16dd047ee0f1348`.
- Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Comparator `2312244ac716564a61cc0bf4e107d9abf1757a61`.
- lean4export `cacf989bd75f608700820f6afc595f32e7a99a4d`.
- Nanoda `4c544ed4099c8227f07d5de77ad1e69fb0740a27` (built using isolated Rust 1.98.1).
- Checker binaries were built from clean pinned official repositories in this run; no dependency on the older TB3 build remains. Exact binary and runtime-library hashes are in each receipt. The initial compatibility experiment used that earlier build, but the final evidence uses newly built checkers.
- Actual macOS 15.2 Seatbelt enforcement was used. No development fake sandbox or Linux sandbox was used. The bounded CREATE availability probe did not establish a remote runtime; no cluster job was submitted.

## Real Lean controls

[Machine-readable summary](controls.json), with individual JSON receipts and raw logs under `controls/`:

| Control | Required and observed outcome |
| --- | --- |
| Honest theorem | Pass both kernels and all checks |
| Direct `sorry` | Reject reachable `sorryAx` |
| Hidden `sorry` in helper | Reject transitive `sorryAx` |
| Indirect custom axiom | Reject the custom axiom |
| Native evaluation | Reject computation-specific `verified._native.native_decide.ax_1_1` |
| Replaced theorem proposition | Reject statement mismatch |
| Added `False` hypothesis | Reject statement mismatch |
| Changed definition and conclusion | Reject mismatch |
| Changed definition with identical endpoint type text | Reject referenced-definition mismatch |
| Altered notation meaning | Reject elaborated mismatch |
| Altered typeclass interpretation | Reject dependent-instance mismatch |
| Missing named endpoint | Reject absent declaration |
| Forged success messages | Reject despite printed success text |
| Write to the frozen challenge | OS denies write; reject compilation |
| Write to checker configuration | OS denies write; reject compilation |
| Supplied stale/corrupt `.olean` | Ignore it, freshly rebuild honest source, pass |
| Source changed after freeze | Block before candidate execution |
| Contract bytes changed | Block before candidate execution |

Every execution also tests protected-file writes, inherited-child writes, writes through a dependency-style symlink, TCP sockets, Unix sockets and successful writes in the designated build directory. The first five are denied and the last is allowed.

[Seven guardrail regressions](guardrails.log) independently exercise source mutation during staging, source/cache directory symlinks, external package/source/configuration paths, and a nonpositive timeout. They all passed. Missing/changed binaries and an unsupported OS have explicit fail-closed code paths; they were not separately fault-injected in this pilot. A forced runtime timeout was not exercised; the process-group termination implementation remains a residual control to validate on the eventual dedicated deployment host.

## Real endpoint pilot

`Kourovka.P21_106.not_notebookStatement` passed the final runner in **145.391 seconds**, including byte inventories of project source, upstream compiled caches and Lean runtime libraries. The following checks all completed:

- Fresh compilation of the needed Kourovka project modules, including the first-order language, formula realization and Heisenberg counterexample.
- Exact challenge statement and dependent-definition comparison.
- Positive transitive axiom allowlist `{propext, Quot.sound, Classical.choice}`.
- Nanoda checking of the exported endpoint dependency closure.
- Lean kernel replay of that same closure.
- Unchanged frozen source/configuration/checker/cache hashes after verification.

The solution export is approximately 31 MB. The trusted upstream Mathlib cache was read-only and byte-bound; the run does not claim a fresh source build of Mathlib. No other Kourovka endpoint was run under this gate.

Evidence:

- [Exact contract](p21_106-contract.json).
- [Technical receipt](p21_106-verification.json).
- [Raw checker log](p21_106-verification.log).
- [Human review packet](p21_106-human-review.md), with statement and novelty approval deliberately pending.
- [Fully explicit declarations](p21_106-elaborated-statements.txt), printed by Nanoda from the exact accepted export while rechecking it with the same strict axiom policy.
- [Lean kernel-fix ancestry check](lean-fix-14576.json).

## Bounded independent review

A separate reviewer inspected the wrapper and the pinned Comparator source. This review identified two additional snapshot/configuration holes, both closed before these final controls and real-endpoint run:

1. Directory symlinks could hide source/cache subtrees from a recursive byte inventory. The supported profile now rejects them.
2. Nonstandard Lake package/configuration paths could resolve different dependencies from those inventoried. The supported profile now permits only the reviewed standard TOML/cache layout and exact Git requirements.

Root review additionally required staged-copy hashes to match the frozen contract immediately, challenge digest validation, before/after dependency-cache and runtime hashes, and denial through a writable-directory symlink. Those checks are in the tested runner. The reviewer confirmed Comparator serializes the challenge before building the solution, then applies its transitive axiom check, configured external Nanoda and built-in kernel replay. No further critical finding remained in that bounded review.

These reviews do not constitute a formal security audit. The sandbox restricts candidate Lean processes, not the same-user orchestrator's shell authority. The verifier/challenge hashes require independent trusted operator control; a hostile agent with unrestricted host access needs a separate verifier service/account/CI boundary. Human mathematical interpretation remains indispensable.

## Public evidence paths

Published evidence replaces the original host home path with `/HOST`.
[Publication transformations](publication-transforms.json) record both
original and public file hashes. Original contracts, receipts and logs are
preserved in the research archive. Hashes inside a historical receipt or
manifest identify those original bytes; proof-source hashes are unchanged.
These published copies are not edited inputs for replay: follow the checker
instructions to freeze a new local contract.

