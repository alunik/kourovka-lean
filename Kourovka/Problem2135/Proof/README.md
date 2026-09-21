# Proof reading map

The original module names and every mathematical file are preserved. This guide is documentation, not a wrapper theorem or a new proof layer.

1. [OuterWord](../Kourovka2135/OuterWord.lean), [Statement](../Kourovka2135/Statement.lean) and [Complement](../Kourovka2135/Complement.lean) define independent-variable word trees, single values, the order condition and a normal p-complement.
2. [MinimalSimpleModels](../Kourovka2135/MinimalSimpleModels.lean) and [QuasisimpleCoprimeCommutators](../Kourovka2135/QuasisimpleCoprimeCommutators.lean) state the two retained published mathematical inputs.
3. [ProblemRemaining](../Kourovka2135/ProblemRemaining.lean) assembles the soluble, minimal-simple family and radical reductions. Its imports lead to the substantial binary extension and representation calculations.
4. [CentralQuasisimpleComplete](../Kourovka2135/CentralQuasisimpleComplete.lean) finishes the central-radical case using coprime commutators, word lifting and the proved Frobenius criterion.
5. [ProblemComplete](../Kourovka2135/ProblemComplete.lean) gives all three final endpoints, including the converse. [The public root](../Kourovka2135.lean) imports the complete development.

The [mathematical note](../../../docs/walkthroughs/21.35.md) explains the argument without requiring familiarity with Lean. The [source manifest](../../../docs/nilradical-21.35/source-manifest.json) records all 745 modules, the pinned build configuration and the retained third-party attribution files. Verification and reproduction details are in the [problem README](../README.md#verification).
