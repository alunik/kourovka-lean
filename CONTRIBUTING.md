# Contributing a solution

Contributions must answer a precisely identified question or subquestion
from the Kourovka Notebook with a complete Lean proof. We prioritize recent
problems with clear formulations and mathematical interest.

For a problem numbered `21.k`, add:

- `Kourovka/Problems/P21_k/README.md`, with the notebook's natural-language
  formulation (including relevant subquestions and qualifications), its
  source and problem authors, the exact question answered, and a compact
  summary of the Lean strategy. Link to the statement and final theorem.
- `Kourovka/Problems/P21_k/Statement.lean`, stating the question using standard
  mathlib definitions wherever possible, independently of the proof.
- `Kourovka/Problems/P21_k/Solution.lean` and supporting modules in `Proof/`.
- Optional `docs/21.k.md` for a longer explanation of the formal encoding
  and a detailed source map. Keep the problem README self-contained.
- An import in `Kourovka.lean`, a catalogue entry, and an endpoint axiom audit
  in `Audit.lean`.

Use zero-padded problem numbers in module names, as in `P21_03`.
Every included problem must have its own README; a catalogue entry or an
external paper link is not a substitute.
Retain normal mathematical hypotheses; do not assume an unresolved lemma,
classification, finite verification, or the desired conclusion.

The contribution must build at the repository's pinned versions, and its
endpoint must depend only on `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project axioms, unsafe proof machinery, `native_decide`,
or `bv_decide` is accepted. Finite calculations must produce proofs checked
by the kernel. Review must check that the formal statement faithfully
answers the cited question, including all quantifiers and subcases.

List human contributors and explain material AI assistance. Do not import
third-party source without retaining its attribution and license.
