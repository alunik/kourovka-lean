# Accepted-source comparison

Publication check: 22 September 2026.

The original human statement approval binds two frozen, non-Git proof projects through exact contract hashes and individual SHA-256 source hashes. Both original contracts and receipts match the hashes recorded by that approval. All 13 complex files and all 10 real files were hashed against the original source directories and their public copies; every hash matched.

The unchanged public source snapshot is commit `75b93ec1363f5ba4d138512a9dba13f749855f4e`. Every manifest entry was also checked against the bytes stored at that commit.

The publication layout adds only `Complex/` and `Real/` to the original relative filenames. No byte in a contract-covered file changed. The [combined manifest](source-manifest.json) is relative to `Kourovka/Problem1668` and records both original contract digests and the canonical hashes of their original source-file maps.

The frozen real inventory includes `logs/trace-interface.lean`, an auxiliary specification retained for identity with the original contract. It is outside the production module graph. The new `Audit.lean` files and README are publication additions; they are not represented as original accepted sources. The documentation and sanitized evidence are likewise later additions.

For each original source map, its recorded digest uses UTF-8 JSON with sorted keys, comma/colon separators and no trailing newline. Hashes of original private contracts and receipts identify the original bytes, not the sanitized public copies.

The normalized private website acceptance record preserves the original approval verbatim and explicitly records this path remapping. Its source revision identifies the commit containing the unchanged public copies. This is a publication binding of the recorded statement acceptance, not a new human decision or an approval of subsequent explanatory text.

From the repository root, `python3 scripts/check_repository.py` checks the full combined manifest as part of the publication source audit. The two standalone projects retain their own toolchain and dependency manifests so that the accepted proof targets can be replayed independently of the rest of the repository.
