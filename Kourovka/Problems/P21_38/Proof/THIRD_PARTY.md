# Third-party sources

The formalization uses mathlib at the repository's existing pin and 16
Apache-licensed modules from
[group-approximation](https://github.com/SauersML/group-approximation), commit
`a39c9b72861bd04c71fc8e18876d13307851d777`.

The [upstream credit and adaptation record](../../../External/GroupApproximation/README.md),
[original license](../../../External/GroupApproximation/LICENSE),
[per-file provenance](../../../External/GroupApproximation/provenance.json), and
[complete patch](../../../External/GroupApproximation/adaptations.patch) are
retained. Only the dependency closure required by this solution is copied.
The concrete group definitions and their foundational theorems remain
kernel-checked at the pinned destination versions.

The new generation proof follows G. Golan-Polak,
[*Thompson's group F is almost 3/2-generated*](https://doi.org/10.1112/blms.12841),
Proposition 16(1), specialized to endpoint exponents `(1,1)`. Its required
local interpolation argument from
[*The generation problem in Thompson group F*](https://arxiv.org/abs/1608.02572v2)
is proved directly in Lean. Neither paper is treated as an axiom.

See the [proof roadmap](README.md) and [repository credits](../../../../AUTHORS.md).
