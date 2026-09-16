# Nilradical v0: strict Lean verification

This bundle records fresh technical integrity checks of the retained Nilradical v0 Kourovka results on 16 September 2026. Each checked endpoint was compared against an independently reviewed frozen challenge and checked with the three-axiom policy by both Lean and Nanoda. Thomas–Rizzoli (21.29) is not a Nilradical result. Problem 21.99 is excluded from this discovery catalogue and was not rerun in this verification campaign.

A technical receipt is not a human mathematical approval. The receipts preserve their original `human_statement_approval: NOT_RECORDED` field; independent agent statement review and human acceptance are different records. The results table reports only completed technical passes.

| Problem | Named endpoints | Verification seconds | Evidence |
| --- | ---: | ---: | --- |
| 21.3 | 2 | 1111.077 | [Receipt](p21_03/receipt.json) · [Log](p21_03/receipt.log) · [Explicit declarations](p21_03/explicit-statements.txt) |
| 21.38 | 7 | 155.235 | [Receipt](p21_38/receipt.json) · [Log](p21_38/receipt.log) · [Explicit declarations](p21_38/explicit-statements.txt) |
| 21.40 | 6 | 218.381 | [Receipt](p21_40/receipt.json) · [Log](p21_40/receipt.log) · [Explicit declarations](p21_40/explicit-statements.txt) |
| 21.44 | 6 | 207.262 | [Receipt](p21_44/receipt.json) · [Log](p21_44/receipt.log) · [Explicit declarations](p21_44/explicit-statements.txt) |
| 21.68 | 7 | 369.446 | [Receipt](p21_68/receipt.json) · [Log](p21_68/receipt.log) · [Explicit declarations](p21_68/explicit-statements.txt) |
| 21.106 | 7 | 108.015 | [Receipt](p21_106/receipt.json) · [Log](p21_106/receipt.log) · [Explicit declarations](p21_106/explicit-statements.txt) |

See [summary.json](summary.json) for the exact endpoint lists and contract/receipt hashes, and the separate [semantic review and human decision packet](statement-audits/HUMAN_REVIEW_PACKET.md). Each problem directory contains the contract, receipt and checker log with host paths normalized for publication, frozen challenge bytes, and a fully explicit declaration view printed from the accepted solution export while Nanoda rechecked it. The declaration view omits proof bodies; the actual proof bodies are in the Lean source and checked export.

## What was checked

- The original Notebook meaning and important definitions were reviewed independently of the verification execution; the trusted challenge reconstructs the advertised endpoint types. Reviewed project definitions imported by that challenge are frozen by the source inventory. This is not an automatic informal-to-formal equivalence proof.
- Candidate project code was built afresh in a macOS Seatbelt sandbox. No existing project `.olean` was copied. The supported profile uses pinned, read-only upstream compiled caches, including Mathlib, and checks their bytes before and after. It does not claim a fresh source build of Mathlib.
- Comparator checked endpoint types, referenced definitions and their dependency closure against the frozen challenge, rejecting changes to the intended statement.
- Exactly `propext`, `Quot.sound` and `Classical.choice` were permitted. Reachable `sorryAx`, custom axioms and native compiler-oracle axioms were forbidden.
- The same solution dependency closure was checked by independently implemented Nanoda and replayed by Lean's kernel.
- Source, dependency-cache, toolchain and protected verifier/configuration hashes were unchanged after verification. OS canaries checked protected writes, inherited child writes, symlink writes and network denial.

The source inventory covers the complete project snapshot so its inclusion of other problem files does not mean their theorems were verified or credited to Nilradical. Only `theorem_names` in the per-result receipts are the selected public endpoints. Large raw exports and staged source/build snapshots are retained locally; [exports.json](p21_106/exports.json) exemplifies the public byte-length/SHA-256 records. No large generated export is committed here.

## Reproduction

The implementation and bootstrap sources are provided in `scripts/nilradical_verify/` at repository root. Copy that directory **outside this Lean checkout** before bootstrapping so checker source/build files do not become part of the mathematical project's source inventory. Use an unprivileged Apple Silicon macOS account with the pinned Lean toolchain installed. The tested profile is macOS Seatbelt; there is no unsandboxed or Linux fallback.

1. Verify the mathematical source snapshot from the repository root:

   ```sh
   shasum -a 256 -c docs/nilradical-v0-verification/source-files.sha256
   ```

Prepare the pinned dependencies and trusted upstream cache with the repository README's `lake exe cache get` command before freezing. The verifier requires clean dependencies at the committed revisions. An ordinary project build is not a substitute for this gate; candidate project modules are rebuilt in a fresh staged project.

2. Read the copied verifier's `README.md` and `pins.json`. With the matching Lean toolchain and Cargo installed, build the pinned official checkers and run their controls:

   ```sh
   python3 /absolute/path/checker/bootstrap.py --lean-prefix /absolute/path/lean-toolchain --cargo /absolute/path/cargo
   python3 /absolute/path/checker/selftest.py
   ```

   The bootstrap writes a new local `tools.local.json`; no published binary hash is silently substituted. The original local tool paths and hashes are retained in this evidence bundle for provenance.
3. Copy the selected `Challenge.lean.txt` to a reviewed `Challenge.lean` outside this checkout. It is a trusted challenge containing proof placeholders, not candidate proof code. Verify its bytes against the published contract's `challenge_sha256`, and independently assess its mathematical meaning.
4. Freeze a **new local contract**, using the project path, copied challenge, `solution_module`, and every `theorem_names` entry from the published contract:

   ```sh
   python3 /absolute/path/checker/verify.py freeze \
     --project /absolute/path/kourovka-lean \
     --challenge /absolute/path/review/Challenge.lean \
     --solution-module Kourovka.Problems.P21_106.Solution \
     --theorem Kourovka.P21_106.counterexample_values \
     --theorem Kourovka.P21_106.counterexample_not_concise \
     --theorem Kourovka.P21_106.not_notebookStatement \
     --theorem Kourovka.P21_106.realize_counterexampleFormula \
     --theorem Kourovka.P21_106.formulaCondition_iff \
     --theorem Kourovka.P21_106.formulaCondition_closure_infinite \
     --theorem Kourovka.P21_106.central_injective \
     --output /absolute/path/review/contract.json
   ```

5. Review the resulting contract and its printed SHA-256, then run:

   ```sh
   python3 /absolute/path/checker/verify.py run \
     --contract /absolute/path/review/contract.json \
     --contract-sha256 THE_NEW_REVIEWED_CONTRACT_SHA256 \
     --receipt /absolute/path/review/receipt.json \
     --timeout 3600
   ```

Paths, source/cache bytes and rebuilt tool binaries are part of a contract. Consequently a new machine or checkout requires a new contract; editing and reusing a published historical contract or receipt is not a replay. Missing or changed dependencies, failed checks and timeouts cannot produce acceptance. Preserve the new receipt, logs, exports and exact source snapshot.

The sandbox protects candidate elaboration from changing the verifier's files, but it does not restrict another same-user agent's unrestricted shell access. An adversarial service requires independently controlled accounts/CI. Human statement interpretation, novelty and attribution decisions remain separate acceptance records. The original technical receipts are retained in the research archive; no human decision is added to them.

## Publication record

Host home paths in the public evidence are replaced by `/HOST`. The
[transformation record](publication-transforms.json) gives original and public
SHA-256 hashes for each changed file. Statuses, selected statements, proof-source
hashes, checker hashes and recorded decisions are preserved. Contract/receipt
hashes inside the historical records identify the original bytes; public-copy
hashes are separate. The [public manifest](public-manifest.json) verifies the
published files, while `manifest.json` records the original evidence bundle.
Original byte-exact receipts, contracts and logs remain in the research archive.

The [novelty audit](novelty/README.md) explains the retained scopes and the
21.99 exclusion. No earlier complete solution was located for the six retained
scopes in the sources checked on 16 September 2026. Human statement acceptance
and acceptance of the novelty assessment remain separately recorded decisions.
Named human identity and decision evidence are kept privately; a future public
acceptance record identifies the role, date, source binding and decision digest.
