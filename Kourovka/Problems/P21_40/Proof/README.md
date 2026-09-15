# Proof roadmap for 21.40

[Problem and scope](../README.md) · [Statement](../Statement.lean) · [Solution](../Solution.lean)

The proof has independent arithmetic and finite-dimensional algebra branches.
They meet at a finite-index normal kernel and a common rational unitriangular
basis. No search or generated certificate is part of the argument.

| Module | Role |
| --- | --- |
| [MatrixRoots.lean](MatrixRoots.lean) | Cyclotomic-polynomial argument proving injectivity of a sufficiently large prime power map |
| [Orbits.lean](Orbits.lean) | An injective equivariant map on finitely many orbits is surjective; coherent root chains |
| [DeepRoots.lean](DeepRoots.lean) | Northcott finiteness forces deep roots in a number field to have finite order |
| [Eigenvalues.lean](Eigenvalues.lean) | Stabilization of generated algebras, polynomial spectral mapping, and integral bounded traces |
| [TraceRadical.lean](TraceRadical.lean) | Newton–Girard identities and nilpotence from vanishing power traces |
| [TraceKernel.lean](TraceKernel.lean) | Rational group algebra, trace ideal, normal kernel, exact trace-vector fibers, and index bound |
| [FiniteOrbits.lean](FiniteOrbits.lean) | Combines large-prime roots and arithmetic to obtain the bounded traces and finite index |
| [RationalFlag.lean](RationalFlag.lean) | One rational basis simultaneously makes the nil ideal strictly upper triangular |
| [Unipotent.lean](Unipotent.lean) | Superdiagonal filtration, nilpotency class, and finite-order unipotent matrices |
| [ConjugateStructure.lean](ConjugateStructure.lean) | Transfers nilpotence, class, and torsion-freeness through rational conjugation |
| [NumberFields.lean](NumberFields.lean) | Faithful restriction of scalars and transport of abstract automorphism orbits |

`Solution.lean` applies the rational-flag result to the trace ideal, assembles
the explicit structural conclusion, and deduces virtual solubility. It also
discharges the rational-theorem parameter in `NumberFields.lean` to obtain
the unconditional torsion-free virtual-nilpotence result over every number field.

Two proof presentations differ from the mathematical write-up without
changing its result. The formal matrix-root proof chooses a coarser prime
threshold depending on the dimension of an endomorphism algebra; no prime
threshold occurs in the public statement. The arithmetic argument uses
coherent roots and stabilization of their generated algebras, followed by
the existing fixed-number-field Northcott theorem.

The generic supporting lemmas are not assumptions of the public theorem:
each is proved at the repository's pinned Lean and mathlib versions.
The [targeted audit](../Audit.lean) checks the final dependency closure.

See [THIRD_PARTY.md](THIRD_PARTY.md) for the exact QICLean and Tau Ceti source
revisions and adaptation details. These are ordinary proof sources compiled
by Lean; their original projects are not additional Lake dependencies.
