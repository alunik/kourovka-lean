# Third-party Lean proof sources for Problem 21.40

The two adaptations below are released under **Apache-2.0**. The full license
text is included in [LICENSE](LICENSE). Original copyright and author notices
are retained in the adapted source headers, together with notices identifying
the modifications. No additional external Lake dependency has been added.

## TraceRadical.lean

- Repository: [LionSR/QICLean](https://github.com/LionSR/QICLean).
- Exact commit: `cdaa636d1f41560f7caca7077c11068229cb9727`.
- Original path: `QICLean/Algebra/NewtonGirard.lean`.
- [Pinned original source](https://github.com/LionSR/QICLean/blob/cdaa636d1f41560f7caca7077c11068229cb9727/QICLean/Algebra/NewtonGirard.lean).
- Original source SHA-256: `ad31edfcc7fcfc65fcb9f8b4b0cdca6aa99a65dfed357183272573e8e674a33b`.
- Original notice: Copyright (c) 2025 TNLean contributors; authors TNLean contributors.
- Original license: Apache-2.0.

The algebraic Newton–Girard proof is retained: differentiating the determinant
and applying the adjugate identity gives a recursion for reverse characteristic
polynomial coefficients, hence equality of characteristic polynomials from
equality of traces of powers. The original file requires only mathlib imports.
The local additions compare a matrix with zero and use Cayley–Hamilton to prove
`A ^ Fintype.card n = 0`, and consequently `IsNilpotent A`, from vanishing traces
of all positive powers. The source header and license reference were adapted.

Discovery passed through [LionSR/TNLean](https://github.com/LionSR/TNLean) at
`4129cbabe68637a787bb35c8567c6ab96a9d8628`, whose manifest pins the above
QICLean commit. No TNLean-only theorem or dependency is imported.

## Unipotent.lean

- Repository: [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti).
- Exact commit: `355c248fa848acd70c2a4b412ca5f53d37b0402a`.
- Original path:
  `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/UpperUnitriangular/Nilpotent.lean`.
- [Pinned original source](https://github.com/TauCetiProject/TauCeti/blob/355c248fa848acd70c2a4b412ca5f53d37b0402a/TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/UpperUnitriangular/Nilpotent.lean).
- Original source SHA-256: `4d7854dac8598d89fdb1d5582b3fa927a0b3bc6a3d10aa2bd7c1aa81d90fffea`.
- Original notice: Copyright (c) 2026 The Tau Ceti contributors; authors The Tau Ceti contributors.
- Original license: Apache-2.0.

The superdiagonal filtration and commutator calculation are adapted to an
arbitrary subgroup of `GL (Fin n) R` with upper-unitriangular entries. This
avoids importing the TauCeti-specific group type and its dependency closure.
The local additions prove that the lower central series vanishes at `n - 1`,
record the corresponding nilpotency-class bound, and prove that each matrix
minus the identity is nilpotent. The separate rational torsion-free proof is
new local code using mathlib's squarefree-annihilator semisimplicity theorem
and the vanishing of a nilpotent semisimple endomorphism.

## Validation and scope

Both adapted modules were compiled independently against the project's
Lean `v4.34.0-rc2` and mathlib
`87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.
The seven new component endpoints depend only on `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx`, custom axiom, or native-decide axiom occurs.
These component checks do not by themselves certify the entire Problem 21.40
formalization.
