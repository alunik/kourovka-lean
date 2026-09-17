> Publication note, 17 September 2026: this report is preserved at its review-time scope. Later technical and human gates passed; see [the current record](README.md). Machine-local path prefixes are removed in this public copy.

# Independent formalization and semantic review: Kourovka 21.53

**Verdict: PASS for statement correspondence and the reviewed final formal interfaces.**

**Protected integrity: pending separately. Human approval: not recorded.**

Date: 16 September 2026. Reviewer context: `/root/final_semantic_review`, independent of the authors of the mathematical construction and Lean proof. I authored only the trusted challenge, inspection input, and this review. I did not modify the submitted Lean proof. This report does not supply the separate fresh mathematical or novelty review required by the workflow.

## Accepted semantic scope and exact snapshot

The selected endpoint is `Kourovka.Problem2153.not_statement : ¬ Kourovka.Problem2153.Statement.{0}`, in `Kourovka.Problem2153.Final`.

The review is bound to `verification/contract.json`, whose bytes I independently hashed as:

`e02b24ffc6e1c9c8adb3aa507a9c59de2df762492495f27dd8d788133de257ff`.

I checked all 719 project source entries in the contract against the actual files; there were no missing files or hash mismatches. The contract contains 168 sources under `Kourovka/Problem2153/`. The complete relevant source list, hashes, source-question/write-up hashes, inspection-output hash, and the check time are recorded in `formalization-constructive-snapshot.json`. Hashing a file is not a claim to have read every certificate entry in it.

The pin is `leanprover/lean4:v4.34.0-rc2`, with Mathlib `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`. I inspected the actual `lean-toolchain` and ordinary `lakefile.toml`. Representative submission hashes are:

| File under `Kourovka/Problem2153/` | SHA-256 |
|---|---|
| `Core.lean` | `fa4bf589c954924f0197f3bd502bb88d1938ea41d73ebf26ab5e1bdec1553784` |
| `Endpoint.lean` | `47395a61e7921c4f3ba52a24bd4807f29a3f4d2e775fe7c221fbd9a82159aa51` |
| `BNPair.lean` | `7505bb7d68a79ef27718caf4371c5ec44e26df332da2ee8c2310f5ccdecf5b9e` |
| `Simple.lean` | `f5342338f40ca0d0e6f6409fce40449d381a7f429d6f990abbfa607839dbdc80` |
| `Final.lean` | `a9bcaa28d0e3c5317d37d1a241013931cb0c8df47e9203088e1ec684921691b3` |

## Source statement and definition audit

I read the primary Notebook text for both 21.52 and 21.53 in the preserved v46 extraction, `problem.md`, the original `proof/ree-counterexample.md`, and the final-route supplement `proof/constructive-matrix-route.md`. The source defines colour preservation as retaining each edge's product order, rather than permuting the colours. The restriction to finite nonabelian simple groups and a conjugacy class of involutions comes from 21.52.

The six definitions fixed by the challenge have the required meanings:

* `InvolutionClass d` is the subtype of **all** ambient elements `x` satisfying Mathlib's `IsConj d x`. The ambient group is unchanged inside this predicate. The public statement separately requires `orderOf d = 2`; conjugacy transfers that exact order to every vertex. No class-membership oracle or selected subset is present.
* `PreservesColour t τ` quantifies over every distinct pair of vertices and preserves the fixed natural-number label `t` in the direction used by the source. `τ` is a genuine `Equiv.Perm`, so bijectivity is included. Diagonal pairs are correctly excluded. Ordered pairs faithfully express the undirected relation because `orderOf (a*b) = orderOf (b*a)`.
* `PreservesAllColours τ` equates the actual two product orders for every distinct pair. No relabelling equivalence or divisibility surrogate replaces equality.
* `TwoSmallestPrimeDivisors n p` requires `2 ∣ n`, primality and oddness of `p`, `p ∣ n`, and minimality among odd prime divisors. The public statement does not hard-code `p = 3`. Primality of 2 is the usual numerical fact and need not be a separate field.
* `Nonabelian G` asserts an explicit noncommuting pair using the same group multiplication.
* `Statement` universally quantifies over the group type and its `Group`, `Finite`, and standard `IsSimpleGroup` instances, then nonabelianness, every order-two representative, and every prime satisfying the stated condition. Its conclusion is equality of the required two sets of permutations.

I checked Mathlib's actual definitions of `IsSimpleGroup` (nontriviality and only trivial/full normal subgroups), `IsConj`, and `orderOf`. The totalized value zero for infinite order does not weaken this statement: every group quantified in the statement is finite. The public counterexample is also a visibly finite matrix subgroup. The final theorem has no explicit or implicit hypotheses. Refuting the assertion already at universe zero is sufficient to answer the original question negatively; one concrete finite group suffices.

## Concrete construction and discharge of interfaces

The formal proof uses a substantive direct matrix argument, now explained by the constructive supplement. It need not prove that the matrix group is isomorphic to a separately defined named Ree group. The original question only needs a finite nonabelian simple group with the specified permutation. I did not treat the original write-up's published simplicity, centralizer, or no-three-inversion assertions as formal premises.

The actual carrier is `WilsonModel.ambient`, the ordinary subgroup closure of explicitly constructed units in `Matrix.GeneralLinearGroup (Fin 26) Field8.F8`. `RootSystem.G` is an abbreviation for that carrier, not a new abstract group. `F8` has an eight-constructor carrier and proved field laws; ordinary finite-type and subgroup instances give finiteness. No alternate multiplication, empty carrier, impossible premise, or group-identification assumption is used.

`WilsonModel.X`, `Y`, and `A` are elements of that same subgroup, with proved unit and membership certificates. `witness_orders` proves their order-two assertions and the exact product orders 5 and 7. `Y_eq_conj_X` and `A_eq_conj_X` use conjugators in the actual subgroup. `Endpoint.vertexX`, `vertexY`, and `vertexA` therefore lie in its whole ambient class. `classSwap` is `Equiv.swap` on that subtype. `changed_edge` and the generic `witness_ne` show that the fixed third vertex is distinct and that the changed edge goes from order 5 to order 7.

I traced the former conditional interfaces through their final concrete applications:

1. `U`, `H`, `W`, `B`, `N`, `P`, and `Z` are actual subgroup closures/joins in the same `G`. `Borel.lean` proves the factorization, intersection, and generation interfaces; `BorelQuotient.lean` proves the intersection's normality and generation of the genuine quotient by the two simple images.
2. `UnipotentFactorization.lean` proves `U_factor_r` and `U_factor_s`. It derives radical conjugation stability from the certified commutator supports, uses finite order to recover inverse stability, proves the subgroup joins equal `U`, and applies the normalizing-product lemma. These facts are not inputs at the public endpoint.
3. `BNPair/Construction.lean` supplies every field of the actual vendored `TauCeti.TitsSystem`. I inspected that structure's fields and the abstract Bruhat argument, including quotient generation and closure of the union of cells. There is no field assuming the desired whole-group coverage. `BNPair.concrete` and `uhwu_coverage` discharge both factorization parameters. The coverage conclusion quantifies over every `g : G`, with unipotent and torus factors carrying genuine subgroup membership.
4. `Simplicity/Concrete.lean` applies the Iwasawa subgroup theorem to the proved maximality, trivial normal core, normalization, abelianness, normal generation, and perfectness statements. I inspected the Iwasawa proof, normal-generation/perfectness assembly, root-subgroup interfaces, maximality assembly, and the projective-frame-to-trivial-core bridge. `Simple.lean` applies proved coverage and exports `IsSimpleGroup G` with no premise. `Endpoint.not_statement_of_coverage` independently supplies the same proved simplicity criterion once given coverage; `Final.lean` supplies that coverage.
5. The class tests are extended globally using the exact `U H W U` decomposition and the proved centrality of `X,Y` in `U`. I inspected `BruhatReduction.lean`, the class-test Boolean-to-group commutation bridge, the product-power-to-order exclusion bridge, and their final applications. The no-three relation is established on all pairs of the whole class by simultaneous conjugation. It is not inferred from testing a selected class subset.
6. `AmbientFacts.lean` proves nonabelianness from the order-five product and proves divisibility by 2 and 3 from actual elements of those orders. Thus `ambient_two_smallest_primes` applies to the cardinality of precisely the same group. No order formula is assumed.

The sparse certificate checker is connected to ordinary matrix multiplication by `rowEval_dot` and `mul_eq_of_check`; group equalities are transferred through an injective matrix homomorphism. Finite Python data are proposed certificates, not mathematical axioms. I inspected these encoding/soundness interfaces and representative data definitions; I did not independently multiply every recorded 26-by-26 matrix or replay all certificate generators by hand. The protected dependency replay is still necessary.

## Trusted challenge and checks actually performed

I independently prepared `verification/challenge/Challenge.lean`. It imports only Mathlib and defines the six audited custom notions directly. It imports no solver-controlled `Core`, witness model, or endpoint. Its one proof placeholder is confined to the trusted specification and cannot serve as the submitted proof. Its SHA-256 is:

`9f28dde89cf12a709007361f261ec4e050c674a03277686565f3129ef5f11381`.

The contract embeds exactly these challenge bytes and selects only `Kourovka.Problem2153.not_statement`. That endpoint is sufficient for the requested negative answer. No extra recognition or correspondence theorem is needed to interpret this existential refutation. Model-specific claims beyond this endpoint would require their own reviewed challenge vocabulary if separately selected for acceptance.

Commands I ran from `LOCAL_HOME/notebook/kourovka-lean`:

```sh
lake env lean campaign/verification/challenge/Challenge.lean
lake env lean campaign/verification/challenge/Inspect.lean
```

Both exited zero. The first emitted only the expected trusted-placeholder warning. The second successfully imported the compiled `Final` module, printed fully explicit definitions and endpoint types, and reported only `propext`, `Classical.choice`, and `Quot.sound` for `not_statement`. Its complete output is `verification/challenge/explicit-types.log`. This was an elaboration/import check using existing local build outputs, **not** my own clean rebuild of the complete dependency closure. I also inspected the coordinator-supplied `lean/implementation/bn-pair-01.log` and `simple-final-01.log`; their build and axiom results are supporting receipts, not independently rerun protected checks.

The source scan found no candidate proof admission, custom axiom declaration, native-evaluation proof dependency, or low-level environment manipulation in this subtree. This scan is only a diagnostic and cannot establish integrity. I independently verified the frozen contract hash, challenge text, and all frozen source hashes with Python.

## Open acceptance items and limits

No unresolved semantic defect was found in the frozen endpoint or the reviewed concrete instantiations. The earlier pending coverage and simplicity obligations are discharged in this snapshot. The constructive supplement supplies a readable account of the substantive formal route; its separate fresh mathematical acceptance and refreshed novelty assessment must be recorded by the appropriate independent contexts.

At this report's completion the coordinator had started the protected verification run, but I had not inspected a completed receipt. **This report does not claim `INTEGRITY_PASSED`.** The frozen-definition comparison, strict transitive axiom policy, protected clean build, fresh Lean replay, and Nanoda check must complete successfully on the same snapshot. A subsequent receipt may be attached without falsely attributing its inspection to this reviewer.

Final human statement verification and separate human novelty/contribution acceptance remain required. This report records neither, and authorizes no publication. Any change to the relevant source or statement invalidates the corresponding snapshot-bound review until the change is reviewed and the technical gate is rerun.
