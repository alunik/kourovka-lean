# Proof roadmap for Problem 21.29

[Problem overview](../README.md) · [Public statement](../Statement.lean) · [Public theorem](../Solution.lean)

Start with [`Solution.lean`](../Solution.lean): it assembles primitivity,
the regular suborbit, and the obstruction, then realizes the affine action
as a subgroup of the symmetric group. All supporting declarations are in
`Kourovka.P21_29`.

| Stage | Key modules | Role |
| --- | --- | --- |
| General affine action | [`Affine.lean`](Affine.lean) | Constructs the affine group and proves primitivity from irreducibility over a prime field. |
| Concrete linear group | [`LinearGroup.lean`](LinearGroup.lean) | Defines the monomial group $C_2^6\rtimes D_{18}$ acting on $\mathbb F_3^9$. |
| Finite indexing and coverage | [`Encoding.lean`](Encoding.lean), [`FiniteModel.lean`](FiniteModel.lean) | Encodes all 1,152 linear elements and 19,683 vectors, defines the two distinguished vectors, and proves the obstruction checker sound. |
| Irreducibility | [`Irreducible.lean`](Irreducible.lean) | Uses diagonal differences to isolate a coordinate, then rotations to reach every basis vector. |
| Finite certificates | [`Certificates/Checks.lean`](Certificates/Checks.lean), [certificate guide](Certificates/README.md) | Combines the regular-vector and obstruction batches with the coverage proofs. |
| Permutation-group conclusion | [`Solution.lean`](../Solution.lean) | Relates pair stabilisers to stabilisers of vector differences and proves `not_notebookStatement`. |

The generator supplies explicit nonidentity witnesses, and Lean checks
them against the actual action with `decide +kernel`. Reproduction is
documented in the [certificate guide](Certificates/README.md); the generator
is not required for a normal build.

For the solution build and repository audit, see
[verification](../README.md#verification).
