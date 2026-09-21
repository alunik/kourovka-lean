# Additional selected TauCeti source: dual-number resolution

`Algebra/Homology/Ext/DualNumbers.lean` is selected from TauCetiProject/TauCeti, commit `7a4e28011b29a4e8c8365fe87f2144022cf1377f`, under the existing Apache-2.0 [LICENSE](LICENSE). The original copyright and author attribution remain unchanged in the source.

Its complete TauCeti import closure is three files (602 lines). The other two files, `Algebra/Homology/Ext/ProjectiveResolution.lean` and `Algebra/Homology/Opposite.lean`, were already present in the earlier six-file port and remain unchanged. This addition makes seven distinct locally selected TauCeti sources; it does not replace the earlier provenance record.

Only the internal import prefix is changed from `TauCeti` to `Kourovka2135.Vendor.TauCeti`. Mathematical namespaces, declarations, assumptions, and proofs are preserved. See `DUAL_NUMBERS_PROVENANCE.json` for exact source and validation records.

The new source constructs the periodic projective resolution of the residue module over `DualNumber k` and computes its self-Ext. It does not prove a group-algebra equivalence, an equivariant tensor-product resolution, or finite-group H1/H2 bounds.
