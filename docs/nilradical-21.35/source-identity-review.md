# Public source identity review — 2026-09-21

Independent bounded publication-packaging review. Verdict: **PASS** for the frozen source copy and its Git commit. This review ran only file, archive, Git-blob, and import-graph checks. It ran no Lean build, elaboration, kernel checker, CI build, or proof development, and grants no human approval.

The reviewed source commit is `eb026951d20b1a362c7ec206ac116cd55547e96d` in `alunik/kourovka-lean`. Its `Kourovka/Problem2135/` subtree contains exactly the 762 files listed in the original source-package manifest: 745 Lean modules, three original project configuration files, and 14 vendor license, notice, provenance, and support records. Every working-copy file and every committed Git blob matches its manifest SHA-256. There are no extra files in that committed subtree. All 762 regular source-archive members also match the same manifest entries.

| Identity | SHA-256 |
|---|---|
| Finalized original source manifest | `3d156634b26f9c393f7f07a1392fd3654769959ea48233ec4dbe8a391c2212bc` |
| Original source archive, 1,807,545 bytes | `d58a903458a1f661223676c672da9c51ef49a0905c6a21150af38508ee3b77ed` |
| Frozen contract | `736152a70be7041fdf511bd874ca2cd5e451a2cf7749e89ef093de829408fb4d` |
| Endpoint source `Kourovka2135/ProblemComplete.lean` | `acc5fe6f682623243fec4f22d594fc8d8aee1fab090d7233bafc662496f5ee61` |
| `lakefile.toml` | `8386b9b9ebd367dfdddb8652078510bb4623c1036165ae3075f9eaa17e08034a` |
| `lake-manifest.json` | `b300ba9a8449fd027357d73315a391147004b3bdeda15b3547776e8417e9a4ee` |
| `lean-toolchain` | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |

The earlier source-identity review records a pre-finalization manifest digest, `b17402e6ae2657f0449c09a8ffbd0dcf76d8f47d83103f32666912732c9b2aa5`. The finalized manifest now contains integrity bookkeeping. Its source archive and all packaged source/configuration bytes retain the original identities above. The historical `AWAITING_HUMAN` and `NOT_ASSERTED` fields are receipt-era bookkeeping; this reviewer does not use them to infer or replace subsequent human decisions.

The copied directory is a standalone nested Lake project. Its original project root is `Kourovka/Problem2135/`, its library is `Kourovka2135`, and root-relative imports remain `Kourovka2135.*`. Traversal of `import` and `public import` from `Kourovka2135` reaches exactly all 745 packaged Lean modules, with no missing or surplus project module. The only external import root encountered is `Mathlib`. No alias, namespace rename, or parent-project integration is needed to preserve that layout. The configuration still pins Lean `v4.34.0-rc2` and mathlib `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.

The original three public endpoints remain unchanged:

- `Kourovka2135.problem2135_outerWord`
- `Kourovka2135.problem2135`
- `Kourovka2135.productOrderCondition_iff_hasNormalPComplement`

Each still has exactly the two explicit additional mathematical parameters `MinimalSimpleClassification.{0}` and `QuasisimpleCoprimeCommutators.{0}`. The source is a conditional formalization; neither parameter is proved by this packaging operation. The earlier source-identity review supplies the detailed statement audit; exact source identity preserves its audited statements.

Existing replay evidence is summarized in [verification.json](verification.json), with the recorded 14-line output in [replay.log.txt](replay.log.txt). The original continuation receipt SHA-256 is `d063624152c3fd8008a521058c4d1547462ad90c32063f544377584bc7990981`, and the replay-log SHA-256 is `d2bd005883928c0630f9eb9d87266d430173dd58812196bb42fdc17aafffe89d`; this reviewer independently rehashed the existing local receipt and log. The log records Nanoda and Lean default-kernel acceptance. The previously completed captured-evidence audit authenticates the larger evidence archive `1d5883abbadba9dce1bc252fabf44ba9bab3f17f935ac676286af36e5ec68867`, both captured exports, and the control suite. Those are existing completed-run results, not new build or replay results from this publication review. The public summary is not the raw receipt, which remains retained with the full evidence.

All 14 packaged vendor license/provenance/support records are preserved byte for byte. This confirms their preservation, not a new legal assessment or an independent mathematical novelty decision. Public documentation and website text were outside this review's scope.
