# Third-party foundations for Problem 21.44

[Problem overview](../README.md) · [Proof roadmap](README.md)

## Exact source

Two modules are imported from Konstantin Slutsky and contributors'
[recurrent-sections-lean repository](https://github.com/kslutsky/recurrent-sections-lean/tree/2b68f638c3af39a18a0630fa4977bb749d97a14a),
commit `2b68f638c3af39a18a0630fa4977bb749d97a14a`, under Apache-2.0.
Their original copyright and assistance notices are retained.

| Upstream file | Integrated file | Role |
| --- | --- | --- |
| `RecurrentSections/WordGeometry.lean` | [RecurrentSections/WordGeometry.lean](RecurrentSections/WordGeometry.lean) | Finite symmetric generating sets containing the identity, finite word balls, ordinary word length, and basic volume bounds |
| `RecurrentSections/ExponentialGrowth.lean` | [RecurrentSections/ExponentialGrowth.lean](RecurrentSections/ExponentialGrowth.lean) | The normalized logarithmic definition of subexponential growth and general exponential-growth estimates |

These two files depend only on mathlib and each other. The degree-five
inverse limit, directed pair, finite-level generation, section shortening,
word encoding, and entropy recurrence are proved in this contribution's
own modules.

The following SHA-256 values identify the **original upstream bytes**:

```text
804d73088712ac84d1fa0d727cf74cf842bdd5b090ec25b262e411866129af48  RecurrentSections/WordGeometry.lean
bb70412d620c30a55e182a4fc4fcb27748dbe4371e517ac15250bf975f910720  RecurrentSections/ExponentialGrowth.lean
c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4  LICENSE
49e0b0a13c3b7c0345106e03698a88da329c7af82e67cb31d2f44c72c6426e25  AUTHORS.md
68b850201cebdfa46e0463ecd9e0b25d286c76143e75e9385b02566f46bbeef8  ACKNOWLEDGEMENTS.md
```

## License and retained attribution

The complete [Apache-2.0 license](RecurrentSections/LICENSE) is retained.
The original [authorship statement](RecurrentSections/AUTHORS.upstream.txt)
and [assistance acknowledgment](RecurrentSections/ACKNOWLEDGEMENTS.upstream.txt)
are preserved byte-for-byte as text files. They describe the broader
upstream project; only the two modules listed above are imported here.

The imported source headers refer to the upstream names `AUTHORS.md` and
`ACKNOWLEDGEMENTS.md`. Their preserved local copies use the `.upstream.txt`
names linked above so that links concerning the broader upstream project
are not treated as local repository documentation.

## Integration changes

The source revision used Lean `v4.33.0-rc2` and mathlib
`a6180e1994004a7c705114bcbebaf5fff4b8384d`. This contribution is checked
with the repository's Lean `v4.34.0-rc2` and mathlib
`87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`.

`WordGeometry.lean` is retained byte-for-byte. In
`ExponentialGrowth.lean`, the import of `RecurrentSections.WordGeometry`
is redirected to
`Kourovka.Problems.P21_44.Proof.RecurrentSections.WordGeometry` and a
prominent modification notice records this relocation. The upstream
`RecurrentSections` namespace, definitions, theorem statements, and proofs
are retained.

The [machine-readable provenance](RecurrentSections/provenance.json) records
original and integrated hashes, and the [adaptation patch](RecurrentSections/adaptation.patch)
records the exact change. The hashes above identify the upstream bytes. The
[verification receipt](../../../../docs/21.44-verification.md) identifies the
integrated source snapshot separately. The integrated solution target has
passed its build and public-endpoint axiom check; repository-wide checks
are recorded with the final contribution.
