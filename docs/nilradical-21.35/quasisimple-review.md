# Independent source review of the quasisimple hypothesis

Reviewer: central-endpoint worker, 2026-09-20. Reviewed
`Kourovka2135/QuasisimpleCoprimeCommutators.lean` and its word-value bridge in
`Kourovka2135/CentralWordValues.lean`. No source changes, builds, or sync were
performed for this review. Root reports the assumption module passed its first
strict compile; this note is a separate mathematical and specification review.

**Verdict: the explicit hypothesis matches the authorized uniform assertion.**
It quantifies over finite perfect groups whose quotient by their **actual
center** is nonabelian simple, then over each element whose order is coprime
to the cardinality of that **actual center**. Its conclusion is one ordinary
commutator `a⁻¹ * b⁻¹ * a * b = x`, not membership in the commutator subgroup,
a product of commutators, or an outer-word surjectivity assumption. The paper
commutator convention has the same value set as the alternate convention,
by replacing both inputs by their inverses. The explicit noncommutativity
condition is part of the usual quasisimple condition and introduces no
additional mathematical conjecture. This is a `Prop` parameter, not an axiom.

The ordinary Ore assertion for finite nonabelian simple groups is **derived**
from the same hypothesis: such a group is perfect and has trivial center;
its central quotient is isomorphic to itself; and every element order is
coprime to the center cardinality 1. No separate Ore assumption appears.

For a surjection `f : G →* Q` onto a nonabelian simple group with central
kernel, the proof correctly identifies `ker f = center G`: surjectivity sends
central elements into the center of Q, which is trivial, and the opposite
inclusion is the central-kernel premise. Thus the central quotient really is
Q and a p-group kernel really makes the full center a p-group. For a p′-element
x, coprimality of its order with the center cardinality follows from that
cardinality being a power of p, including exponent zero. The application of
the authorized assumption is therefore justified with the actual center.

The conversion from one ordinary commutator to one arbitrary outer-word value
uses the derived Ore assertion only on Q. Every outer word is surjective on Q;
its two required inputs can therefore be lifted to single values of the two
subwords in G. Their images match the ordinary-commutator inputs, so the lifts
differ by central elements and give exactly the same commutator. This retains
single values throughout and does not claim that all elements of G are
commutators or outer-word values. The leaf case is immediate.

The final public endpoint uses the universe-zero version of the uniform
hypothesis and transports arbitrary finite groups through `Shrink`; this
introduces no restriction on the abstract finite groups covered. The theorem
remains conditional: this review does not prove the uniform quasisimple
commutator assertion itself.
