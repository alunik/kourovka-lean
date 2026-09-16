# Human statement acceptance — Nilradical v0

Final human verification of all six retained Lean statement scopes was
explicitly accepted on **16 September 2026 at 10:46:42 UTC**, following the
[independent statement review packet](../nilradical-v0-verification/statement-audits/HUMAN_REVIEW_PACKET.md)
and completed strict verification. Problem 21.3 covers its first question
only, with a uniform eventual cutoff and no claim of the specific bound 21.

The accepted mathematical source revision is
[`5a6b2c18e326b7b0281f00b64cade629acbfe1f5`](https://github.com/alunik/kourovka-lean/tree/5a6b2c18e326b7b0281f00b64cade629acbfe1f5).
The [source manifest](../nilradical-v0-verification/source-files.sha256)
binds all 551 mathematical source and configuration files. The six contracts
select 35 endpoints; the technical gate also rechecked 92 explicit declarations.

| Problem and proof account | Human statement decision | Checked endpoints |
| --- | --- | ---: |
| [21.3](../walkthroughs/21.3.md) | Accepted | 2 |
| [21.38](../walkthroughs/21.38.md) | Accepted | 7 |
| [21.40](../walkthroughs/21.40.md) | Accepted | 6 |
| [21.44](../walkthroughs/21.44.md) | Accepted | 6 |
| [21.68](../walkthroughs/21.68.md) | Accepted | 7 |
| [21.106](../walkthroughs/21.106.md) | Accepted | 7 |

[Machine-readable acceptance records](statements.json) give the acceptance
date, reviewer role, exact source revision and manifest hash, selected
declarations, contract hashes and decision-record digests. The named identity
and original human response are retained privately. Public discovery and
formalization credit remains **Nilradical v0**.

## Relationship to the earlier evidence

The [technical verification bundle](../nilradical-v0-verification/README.md)
was completed before this human decision. Its receipts and pending templates
remain unchanged as historical records, including their original
`human_statement_approval: NOT_RECORDED` fields. This separate acceptance
record supplies the later human statement decision; it does not rewrite the
verification history or change the accepted proofs.

Acceptance concerns the meaning and scope of the linked Lean statements.
It does not establish absolute publication priority. The bounded
[novelty assessment](../nilradical-v0-verification/novelty/README.md) and
its exclusions remain separate evidence.

## Proof walkthroughs

After acceptance, Nilradical v0 generated the linked accounts of how the
proofs work. They are **Agent-generated exposition; not refereed**. Human
acceptance of the mathematical snapshot does not imply review of this later
prose. Corrections to an account can be published independently of the proof;
mathematical changes require renewed verification of the affected source.
