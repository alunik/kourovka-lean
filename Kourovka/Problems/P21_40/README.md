# Problem 21.40

[All problems](../../../README.md#problems) · [Contributing](../../../CONTRIBUTING.md)

## Problem

Let `G` be a subgroup of `GL_n(ℚ)` with finitely many orbits under its full
abstract automorphism group. Must `G` be virtually soluble?

The question is attributed to **A. Dantas and E. de Melo** in the initial
arXiv version of the Notebook's 21st edition,
[version 39, dated 8 January 2026, page 167](https://arxiv.org/pdf/1401.0300v39#page=167).
It appears on page 173 in the later
[September revision, version 46](https://arxiv.org/pdf/1401.0300v46#page=173).
January is the earliest exact formulation verified in our search;
we do not claim to have established where it was first conceived or
published. It imposes no finite-generation hypothesis.
See the [origin and mathematical context](../../../docs/21.40-context.md)
for the earlier papers, nearby thesis questions, and the full journal-article check.

## Result and scope

The answer is **affirmative**. More precisely, `G` has a normal subgroup
`K` and one matrix `P ∈ GL_n(ℚ)` such that

```
[G : K] ≤ (2n+1)^(n²),
P⁻¹ K P ≤ UT_n(ℚ).
```

The index is finite. The subgroup `K` is torsion-free and nilpotent of
class at most `n−1`. Dimension zero is included using natural-number
subtraction: both the group and its nilpotency class are trivial.
The result holds for arbitrary subgroups, including infinitely generated
ones. No computational certificate or classification assumption is used.

Restriction of scalars also proves that every linear group over a number
field with finitely many automorphism orbits has a finite-index torsion-free
nilpotent subgroup.

Earlier work of Bastos, Dantas and de Melo established structural
decompositions under solubility and finite-rank hypotheses, or assuming
virtual nilpotence. This theorem obtains virtual nilpotence directly
from rational linearity and the finite-orbit condition. The classification
within nilpotent groups remains substantial: de Melo and Kato show that
`UT_6(ℚ)` has infinitely many automorphism orbits.

The solution, quantitative strengthening, number-field extension and Lean
formalization are by **Nilradical v0**. The Lean proof uses an efficient variant
of the written argument: a cyclotomic fixed-vector lemma gives uniqueness
of large prime roots; an ascending chain of finite-dimensional algebras
stabilizes, allowing the spectral root equations to be transferred to a
single number field, where mathlib's Northcott theorem applies. These
changes preserve the theorem and index bound.

## Formal statement

[Statement.lean](Statement.lean) defines `NotebookStatement` using
`HasFiniteAutomorphismOrbits` and `IsVirtuallySolvable`.
The orbit quotient is for the evaluation action of `MulAut G` on the
subtype group `G`; it is not restricted to automorphisms induced by the
ambient matrix group.

`StructuralConclusion` records the normal subgroup, explicit `FiniteIndex`,
numerical bound, nilpotence and class bound, absence of nonidentity finite-order
elements, and one rational conjugating matrix for all subgroup elements.
Explicit `FiniteIndex` avoids the convention that an infinite index has
natural-number value zero.

The public endpoints are `Kourovka.P21_40.structural_theorem` and
`Kourovka.P21_40.notebookStatement` in [Solution.lean](Solution.lean).
The unconditional extension to number fields is
`Kourovka.P21_40.numberField_structure`.

## Proof outline

1. For a sufficiently large prime `p`, the rational cyclotomic polynomial
   `Φ_p` has degree greater than the minimal-polynomial degree in the
   relevant finite-dimensional algebra. It follows that the `p`th-power
   map on rational invertible matrices is injective.
2. The power map is equivariant for every automorphism. Its induced map
   on the finite orbit set is injective and hence surjective, giving a
   coherent sequence `b_(k+1)^p = b_k` for every group element.
3. The algebras `ℚ[b_k]` form an increasing chain and stabilize. Polynomial
   spectral mapping transfers the root equations to a fixed number field.
   Northcott finiteness forces finite-order spectral values. Every group
   trace is therefore an integer between `−n` and `n`.
4. In `A = span_ℚ G`, let `I = {r ∈ A : tr(rb)=0 for every b ∈ A}`.
   This is a two-sided ideal. Newton–Girard and Cayley–Hamilton show that
   its elements are nilpotent; a finite-dimensional module argument
   produces a common rational flag that `I` lowers.
5. The normal subgroup `K = {g ∈ G : g−1 ∈ I}` is unitriangular in the
   resulting basis. A basis of `A` drawn from `G` supplies at most
   `(2n+1)^(dim A)` trace vectors whose fibers are exactly the cosets of `K`.
   The superdiagonal filtration gives the class bound, and a finite-order
   unipotent matrix in characteristic zero is the identity.

See the [proof roadmap](Proof/README.md) for the module structure.

## File guide

| File | Purpose |
| --- | --- |
| [Statement.lean](Statement.lean) | Original question and quantitative structural conclusion |
| [Solution.lean](Solution.lean) | Structural theorem and affirmative Notebook answer |
| [Audit.lean](Audit.lean) | Public statement inspection and guarded axiom checks |
| [Proof/README.md](Proof/README.md) | Supporting modules in mathematical order |
| [Proof/THIRD_PARTY.md](Proof/THIRD_PARTY.md) | Pinned source provenance, licenses, and adaptations |

## Verification

The Nilradical v0 strict check passed on 16 September 2026 for 6
selected endpoints: fresh compilation, independently reviewed statement
comparison, the three-axiom policy, and Lean plus Nanoda proof replay.
See the [verification evidence](../../../docs/nilradical-v0-verification/README.md)
and [statement review](../../../docs/nilradical-v0-verification/statement-audits/21.40.md).

From the repository root:

```sh
LEAN_NUM_THREADS=1 lake build Kourovka.Problems.P21_40.Solution
lake env lean Kourovka/Problems/P21_40/Audit.lean
python3 scripts/check_repository.py
git diff --check
```

The [verification receipt](../../../docs/21.40-verification.md) records the
actual source snapshot, targeted build, axiom audit, and semantic review.
The endpoint uses only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof holes, custom axioms, native decision procedures, or
external finite-check assumptions.

## References and credits

- E. I. Khukhro and V. D. Mazurov (eds.), *The Kourovka Notebook*, 21st
  edition, [arXiv:1401.0300v39](https://arxiv.org/abs/1401.0300v39),
  dated 8 January 2026, Problem 21.40, p. 167; question of A. Dantas and
  E. de Melo. Later [v46](https://arxiv.org/abs/1401.0300v46), p. 173.
- R. Bastos, A. C. Dantas and E. de Melo,
  [*Soluble groups with few orbits under automorphisms*](https://arxiv.org/abs/1908.01375),
  *Geometriae Dedicata* 209 (2020), 119–123, Theorem A; and
  [*Virtually nilpotent groups with finitely many orbits under automorphisms*](https://arxiv.org/abs/2008.10800),
  *Archiv der Mathematik* 116 (2021), 261–270, Theorem 1.2 and Corollary 1.3.
- E. de Melo and J. Kato,
  [*Automorphism Orbits of the Group of Unitriangular Matrices*](https://arxiv.org/abs/2510.09353v1),
  2025, introduction and Theorems 1.1–1.2.
- The finite-trace method is classical; see I. Kaplansky, *Fields and Rings*,
  second edition, 1972, Part II, §2, pp. 99–101, for the Burnside/Procesi
  argument and Kolchin's triangularization theorem.
- The arithmetic proof uses mathlib's number-field heights and Northcott
  finiteness development.
- Newton–Girard code is adapted from the TNLean contributors' work in
  LionSR/QICLean. The unitriangular commutator filtration is adapted from
  the Tau Ceti contributors' work. Their
  [exact provenance and Apache license](Proof/THIRD_PARTY.md) are retained.
- [Repository credits](../../../AUTHORS.md) record Nilradical v0 contributions in discovery, research, independent reviews, formalization,
  integration, and verification.

Cite **Nilradical v0**, this problem number and the exact source commit.
Machine-readable citation: [CITATION.cff](CITATION.cff).
