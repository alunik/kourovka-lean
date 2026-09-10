# Proof roadmap for Problem 21.99

[Problem overview](../README.md) · [Public statement](../Statement.lean) · [Public theorem](../Solution.lean)

Start with [`Instance.lean`](Instance.lean), where `transporter_unique`
proves that every element carrying `source` to `target` has exactly one
fixed point. [`Solution.lean`](../Solution.lean) applies the general
transfer theorem to negate the notebook assertion.

| Stage | Key modules | Role |
| --- | --- | --- |
| General affine action | [`Action.lean`](Action.lean) | Builds the action on quotient fibres and proves transitivity and fixed-point criteria. |
| Ambient group and coverage | [`FiniteGroup.lean`](FiniteGroup.lean), [`Generated.lean`](Generated.lean) | Defines linear/block transformations and proves finite coverage from generator transitions. |
| Sparse data interface | [`DataBasic.lean`](DataBasic.lean), [`DataPredicates.lean`](DataPredicates.lean) | Interprets sparse rows as linear maps and states the finite identities to check. |
| Finite certificates | [Certificate guide](Certificates/README.md), [`DataElementary.lean`](DataElementary.lean) | Checks inverses, generator transitions, quotient compatibility, transporter coverage, and fixed-point obstructions. |
| Concrete linear/block group | [`DataModel.lean`](DataModel.lean) | Builds the generated subgroup using the checked 384-entry table and words reaching all six blocks. |
| Concrete transporter | [`Instance.lean`](Instance.lean) | Assembles the six quotient fibres and proves unique fixed points for all allowed transporter translations. |
| Permutation-group conclusion | [`Transfer.lean`](Transfer.lean), [`Solution.lean`](../Solution.lean) | Passes to the image permutation group and proves `not_notebookStatement`. |

The proof uses 64 transporter table cases, without enumerating the
$6\cdot5^{14}$ points. It needs coverage of the generated subgroup by the
table; it does not require distinct table entries or an external group
identification. The [certificate guide](Certificates/README.md) describes
the checked identities, and the [source-data guide](../../../../scripts/data/21_99/README.md)
gives regeneration instructions and provenance.

For the solution build and repository audit, see
[verification](../README.md#verification).
