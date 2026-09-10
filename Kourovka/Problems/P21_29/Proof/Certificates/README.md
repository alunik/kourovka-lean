# Finite certificates for Problem 21.29

[Problem overview](../../README.md) · [Proof roadmap](../README.md)

The generated Lean modules certify two facts about the action of
$H=C_2^6\rtimes D_{18}$ on $V=\mathbb F_3^9$. Their enumerations and soundness
lemmas are defined in [`FiniteModel.lean`](../FiniteModel.lean).

| Certificate family | Checked fact |
| --- | --- |
| `Regular*.lean` | Among all 1,152 linear group elements, only the identity fixes `regularVector`. The 18 batches check 64 elements each. |
| `Obstruction*.lean` | For each of the 19,683 vectors, a supplied nonidentity element fixes that vector or its difference from `hole`. The 154 batches check 128 vectors each, except the final batch of 99. |
| [`Checks.lean`](Checks.lean) | Combines the batches and coverage proofs into `regularVector_regular` and `no_simultaneous_regular`. |

Each finite calculation uses `decide +kernel`. The fixed-radix coverage
proofs ensure that the results cover every group element and vector,
and `obstructionCheck_sound` interprets each successful Boolean check as
the required stabiliser witness. The affine stabiliser argument in
[`Solution.lean`](../../Solution.lean) transfers those facts to the notebook
formulation.

The [C++17 generator](../../../../../scripts/generate_21_29.cpp) is a
reproducibility aid and is not part of the trusted proof. It is not run
during a normal build. Follow the [reproduction instructions](../../../../../scripts/README.md)
to regenerate the Lean certificate files; this README is maintained separately.
Final proof acceptance requires the Lean build and the public theorem
[axiom audit](../../../../../README.md#check-the-proofs).
