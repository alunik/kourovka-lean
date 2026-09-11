# Reading the proof of 21.68

The construction and the induction obstruction are separated so that the
finite calculations do not conceal the representation-theoretic argument.

1. [Groups.lean](Groups.lean) constructs `Q₈ ⋊ C₃`, proves that it has no
   subgroup of index two, and embeds it with index four in the order-96 group
   of even signed affine permutations.
2. [Semiabelian.lean](Semiabelian.lean) transports and extends actual subgroup
   chains. [AbelianKernel.lean](AbelianKernel.lean) constructs the ternary
   augmentation module, the order-2592 group, its semiabelian chain, and the
   coordinate character with the required inertia subgroup.
3. [QuaternionRep.lean](QuaternionRep.lean) gives the explicit irreducible
   degree-two complex representation. Its finite matrix identities reduce
   first to Gaussian-integer calculations checked by the kernel.
   [InertiaRep.lean](InertiaRep.lean) inflates it and twists by the extended
   coordinate character, preserving irreducibility through the invariant
   subspace lattice.
4. [ScalarInduction.lean](ScalarInduction.lean) proves the scalar-character
   form of Mackey irreducibility.
5. [Obstruction.lean](Obstruction.lean) proves normal-subgroup containment
   from a coprime index and the elementary weight and index obstructions.
   [LinearInduction.lean](Obstruction/LinearInduction.lean) extracts a
   linear-character eigenvector by Frobenius reciprocity.
6. [InducedCoordinates.lean](Obstruction/InducedCoordinates.lean) uses
   evaluation in the coinduced function model as jointly faithful coordinates
   of induction. [ConjugateInertia.lean](ConjugateInertia.lean) transports
   the inertia quotient across the resulting conjugate weights.
7. [NonmonomialInduction.lean](NonmonomialInduction.lean) assembles the general
   obstruction for degree-two induction from a scalar inertia subgroup.

[Solution.lean](../Solution.lean) combines these results into the unconditional
negation of the notebook conjecture.

The [external library provenance](../../../External/TauCeti/README.md) records
the reused Mackey and finite-dimensional induction infrastructure. It is
compiled at this repository's existing Lean and mathlib versions.
