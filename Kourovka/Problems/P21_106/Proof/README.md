# Proof roadmap for 21.106

[Problem](../README.md) · [Statement](../Statement.lean) · [Solution](../Solution.lean)

The proof has two independent foundations, followed by the algebraic
counterexample and its transfer to the public first-order statement.

1. [Formula.lean](Formula.lean) constructs the parameter-free group-language
   formula and proves that its realization is precisely `FormulaCondition`.
   Its language and the definition of conciseness come from
   [Statement.lean](../Statement.lean).
2. [Heisenberg.lean](Heisenberg.lean) constructs the group on triples,
   calculates commutators, and proves residual finiteness of the integral
   group by reduction to finite rings.
3. [Counterexample.lean](Counterexample.lean) proves that `FormulaCondition`
   holds exactly at the two central elements with coordinates `1` and `-1`.
   The determinant identity provides the obstruction; explicit witnesses
   provide the converse. An injective integer family in the generated
   subgroup proves it infinite.
4. [Solution.lean](../Solution.lean) identifies the syntax-level value set
   with the algebraic one and derives `not_notebookStatement`.

All modules contain ordinary Lean proofs. There are no generated finite
certificates, trusted external computations, or classification assumptions.
