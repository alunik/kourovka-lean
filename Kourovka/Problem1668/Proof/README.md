# Proof reading map

The two independently verified projects retain their original module names and
source bytes. Start with the [problem README](../README.md) for the exact scope,
public endpoints and reproduction commands.

## Complex project

1. [Evaluation.lean](../Complex/WordMaps/Evaluation.lean) proves that word values
   commute with homomorphisms and are closed under conjugacy.
2. [WordReduction.lean](../Complex/WordMaps/WordReduction.lean) reduces every
   nonidentity two-generator word, up to conjugacy, to a nonzero generator power
   or alternating nonzero powers.
3. [WordMatrices.lean](../Complex/WordMaps/WordMatrices.lean) computes the leading
   trace coefficient for the elementary polynomial matrices.
   [WordSpecialization.lean](../Complex/WordMaps/WordSpecialization.lean) obtains
   the nonconstant word-image trace curve.
4. [Polynomial.lean](../Complex/WordMaps/Polynomial.lean) and
   [Curve.lean](../Complex/WordMaps/Curve.lean) find a noncentral trace $\pm2$
   point on that curve using a polynomial-fiber argument.
5. [Conjugacy.lean](../Complex/WordMaps/Conjugacy.lean) proves the matrix
   conjugacy and power-map facts. [Assembly.lean](../Complex/WordMaps/Assembly.lean)
   turns the curve into projective word-map surjectivity.
6. [Surjectivity.lean](../Complex/WordMaps/Surjectivity.lean) states the general
   characteristic-zero theorem and its complex specialization.

## Real project

1. [Definitions.lean](../Real/RealWord/Definitions.lean) defines the concrete
   free-group word, its evaluations and the trace polynomial.
2. [Trace.lean](../Real/RealWord/Trace.lean) proves the skein and Fricke
   identities and the exact factored trace formula for the word.
3. [RealDomain.lean](../Real/RealWord/RealDomain.lean) establishes the constraint
   on real characters, including the degenerate matrix-entry cases.
4. [Inequality.lean](../Real/RealWord/Inequality.lean) proves the strict $7/4$
   polynomial bound on that domain with exact Lean inequalities.
5. [Counterexample.lean](../Real/RealWord/Counterexample.lean) assembles the
   universal trace bound, exhibits a nonidentity evaluation, and proves that
   the projective word map omits the specified nonidentity involution.

The [mathematical note](../../../docs/walkthroughs/16.68.md) explains the arguments
without Lean. The [source manifest](../../../docs/nilradical-16.68/source-manifest.json)
binds the preserved files to the accepted verification snapshots. The added
publication audits do not alter either solution's import closure.
