# Proof roadmap for Problem 21.3

[Problem overview](../README.md) · [Public statement](../Statement.lean) · [Public theorem](../Solution.lean)

Start with [`AlternatingAsymptotic.lean`](AlternatingAsymptotic.lean), which
combines the symmetric and alternating eventual conclusions consumed by
`Kourovka.P21_03.firstQuestion`. Supporting declarations use the inherited
namespace `Kourovka213`.

| Stage | Key modules | Role |
| --- | --- | --- |
| Finite probability model | [`Basic.lean`](Basic.lean) | Defines the success proportion and the infimum over soluble subgroups. |
| Soluble group structure | [`PrimitiveSolvable.lean`](PrimitiveSolvable.lean), [`ForestContainer.lean`](ForestContainer.lean) | Embeds soluble actions into recursive direct-product and wreath-product envelopes. |
| Core and configuration model | [`TranspositionCore.lean`](TranspositionCore.lean), [`CorePartition.lean`](CorePartition.lean), [`CoreProbability.lean`](CoreProbability.lean) | Identifies core blocks of size at most four and separates core collisions from the remaining error. |
| Uniform core lower bound | [`ConfigurationPoisson/ConfigurationLimit.lean`](ConfigurationPoisson/ConfigurationLimit.lean), [`UniformBrunLower.lean`](UniformBrunLower.lean) | Uses finite collision moments and Bonferroni bounds to obtain the uniform asymptotic lower estimate. |
| Noncore error | [`ForestEnvelopeBounds.lean`](ForestEnvelopeBounds.lean), [`SupportError.lean`](SupportError.lean) | Converts support counts into a uniform error tending to zero. |
| Matching upper bound | [`FourBlockWitness.lean`](FourBlockWitness.lean), [`UpperWitness.lean`](UpperWitness.lean) | Constructs soluble four-point-block witnesses attaining the limiting value. |
| Final assembly and parity | [`Asymptotic.lean`](Asymptotic.lean), [`AlternatingReduction.lean`](AlternatingReduction.lean), [`AlternatingAsymptotic.lean`](AlternatingAsymptotic.lean) | Proves the symmetric limit $e^{-9/2}$ and obtains even conjugators for the alternating conclusion. |

The [detailed source map](../../../../docs/21.3.md) explains the formal
encoding and scope. The public result supplies an eventual cutoff and does
not establish the proposed threshold $n\geq21$. There are no external
certificates or classification premises in the endpoint.

For the solution build and repository audit, see
[verification](../README.md#verification).
