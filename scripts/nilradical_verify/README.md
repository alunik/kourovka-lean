# Nilradical Lean integrity gate

This is an executable, tested verification layer. It compares a submitted theorem and its defining vocabulary with a separately frozen challenge, enforces an axiom allowlist, then checks the same exported dependency closure with Lean's kernel and Nanoda's independently implemented Rust kernel. It rebuilds project code in an actual macOS Seatbelt sandbox. It never substitutes the development `fake-landrun` script.

**A technical pass is not a claim that the informal problem was solved, or a human approval.** Only an independent human can accept the mathematical meaning of the statements and definitions; novelty/attribution approval is a separate decision. Every technical receipt says that human approval has not been recorded.

## Supported profile

The initial profile is `macos-seatbelt-comparator-nanoda-v1`, tested on an unprivileged Apple Silicon macOS 15.2 account, Python 3.14 (Python 3.11+ required), Lean 4.34.0-rc2, and the exact upstream commits in [pins.json](pins.json). Kourovka currently uses this Lean release and Mathlib `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.

Project configuration must use standard-layout `lakefile.toml`, ordinary named `lean_lib` entries, exact Git dependency commits, `.lake/packages` and `.lake` paths. Executable project lakefiles, alternative source/build/package/configuration paths, and source/cache directory symlinks are rejected. This is a deliberate initial compatibility boundary; unsupported projects fail closed.

Comparator, lean4export and Nanoda were built from pinned upstream source. [bootstrap.py](bootstrap.py) reproduces those builds using an already installed matching Lean toolchain and Cargo. It writes a machine-local, hash-pinned `tools.local.json`. Rust for this pilot was installed only under `tools/cargo` and `tools/rustup`; no shell profile or global installation was changed. Generated `tools/`, `runs/` and `tools.local.json` are machine-local and must not be committed.

## Run a review

**Copy this checker directory outside the proof repository before setup or
execution.** Bootstrap creates upstream Lean sources and self-tests create
Lean projects. Keeping them outside the submission preserves the exact
project source inventory and the checker's independent location.

From the proof repository, with the pinned Lean toolchain and Cargo installed:

```sh
verification_dir="$(mktemp -d)"
cp -R scripts/nilradical_verify "$verification_dir/checker"
lake exe cache get
python3 "$verification_dir/checker/bootstrap.py" \
  --lean-prefix "$(lake env lean --print-prefix)" \
  --cargo "$(command -v cargo)"
python3 "$verification_dir/checker/selftest.py"
```

The following commands refer to `verify.py` in that external checker folder.
Keep challenge copies, contracts and generated receipts outside the proof
checkout too. Published `Challenge.lean.txt` files are frozen review inputs,
not imports or part of the submitted proof library.

1. The independent statement reviewer writes a **trusted** challenge module containing the intended declarations and exact theorem names. Proof placeholders are permitted only in this separate challenge. Include the significant definitions directly or import a reviewed, frozen source. An imported definition copied blindly from the solver is not an independently reviewed statement.
2. Freeze the challenge, named endpoint, all project Lean sources, reviewed Lake configuration, exact dependency revisions/source bytes/cache bytes, and checker manifest:

   ```sh
   python3 verify.py freeze \
     --project /absolute/path/to/project \
     --challenge /absolute/path/to/Challenge.lean \
     --solution-module Project.Solution \
     --theorem Project.finalTheorem \
     --output /absolute/path/to/contract.json
   ```

   Additional `--theorem` arguments cover each claimed endpoint and required correspondence theorem. The command prints the contract SHA-256. Store that hash in the independent review record. **Freezing is not approval.**
3. Run with the frozen hash explicitly:

   ```sh
   python3 verify.py run \
     --contract /absolute/path/to/contract.json \
     --contract-sha256 THE_REVIEWED_SHA256 \
     --receipt /absolute/path/to/verification.json \
     --timeout 3600
   ```

   The runner creates a fresh project directory. It copies no project `.olean` or other build output. Every staged source is checked against the frozen digest; the frozen challenge and verifier configuration remain outside the submission's writable area. Pinned upstream package caches are linked read-only and byte-checked before and after the run. They remain explicitly trusted compiled inputs, not fresh source rebuilds of Mathlib. The endpoint's actual proof dependency closure is exported and replayed by both kernels.
4. Review `INTEGRITY_PASSED`, `INTEGRITY_REJECTED`, or `INTEGRITY_BLOCKED` in the independently written JSON receipt. Preserve the raw log, both exports, contract, tools manifest and exact source snapshot. Exit status zero is possible only for a technical pass. Do not treat text printed by a submission as a receipt.
5. Prepare the final human packet: original problem, exact claim, fully explicit Lean types, definition/instance glossary, model/certificate correspondence, proof reviews, novelty evidence and technical receipt. The human records their own name/date, statement decision, separate novelty/attribution decision and exact contract/source/receipt hashes. Do not generate approval on their behalf. Changes require a new snapshot and renewed checks/acknowledgment.

The three permitted axioms are exactly `propext`, `Quot.sound`, and `Classical.choice`. Native compiler-oracle axioms are rejected, including computation-specific axioms produced by current `native_decide`. Ordinary proof-producing tactics are permitted. The runner uses Comparator's serialized export comparison and transitive closure, not text greps or solver-written reports.

## Isolation and trust boundaries

The custom Seatbelt profile denies operations by default. It permits reads, process execution/fork, read-only system queries, and writes only under the fresh project's `.lake` plus `/dev/null`. It permits no network, Mach lookup, process signaling, or privileged execution. Children inherit the restriction. Exports run without project write permission. Every run first checks protected-file denial, child-process denial, dependency-symlink denial, TCP/Unix-socket denial and permitted build writes. Unsupported sandbox startup or a failed canary blocks the run.

The outer `lake env` resolves **reviewed project TOML and pinned trusted upstream Lake configuration** before Comparator starts its sandboxes. Those configurations are part of the verifier's trust boundary and must not be supplied unchecked by a candidate. Actual candidate Lean elaboration and export always occur inside Seatbelt. Snapshot hashes also protect the configuration and runner before/after execution. A process-group timeout kills unfinished verification and records no acceptance.

The sandbox constrains the submitted Lean processes and their children. It does **not** restrict the orchestrator or other agents’ unrestricted shell access to this host. A trusted operator must control the challenge, checker installation and externally recorded hashes. To verify a hostile agent that can itself edit host files, run this verifier behind a separate service/account/CI authority; this shared local workspace is not that security boundary.

Filesystem read permission is broad, matching the upstream Comparator model. This profile protects verifier integrity; it is not a confidentiality boundary for third-party hostile uploads. Use a dedicated account/host without private material for such inputs. The current gate is for this controlled research workflow, not a publicly exposed submission service. Its operating-system policy received a bounded code review and adversarial canaries, not a formal security audit. No Linux profile is implemented; an unsupported platform blocks instead of falling back.

The toolchain pin is known to contain the fix for Lean issue 14576: GitHub's commit comparison places the inspected Lean commit 93 commits after the fix merge, with zero commits behind. That check is recorded in [evidence/lean-fix-14576.json](evidence/lean-fix-14576.json). This is not a claim that no checker bugs remain.

## Reproduce the controls

```sh
python3 selftest.py
```

The suite uses tiny real Lean projects and actual checker processes. It covers honest acceptance, direct and hidden `sorry`, indirect custom axioms, native evaluation, altered statements/hypotheses/definitions/notation/instances, missing endpoints, forged success output, forbidden challenge/configuration writes, stale compiled artifacts, and post-freeze source/contract changes. Each case retains its own receipt and log. See [evidence/RESULTS.md](evidence/RESULTS.md) for the tested snapshot and the real Kourovka 21.106 endpoint pilot.

Missing tools, hash changes, timeouts, inconsistent checks, unreadable snapshots and unsupported layouts cannot produce a pass. This version has no CLI option to remove Nanoda, widen the axiom list, disable the sandbox or accept a human signature invented by the agent.

## Primary tooling documentation

- [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
- [Comparator at the pinned commit](https://github.com/leanprover/comparator/tree/2312244ac716564a61cc0bf4e107d9abf1757a61)
- [Nanoda at the pinned commit](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27)
- [Lean kernel fix 14577](https://github.com/leanprover/lean4/pull/14577)
