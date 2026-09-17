# Concrete rank-one certificates

All objects are elements or subgroups of `RootSystem.G`, the subgroup generated
by the explicitly certified 26-dimensional matrices over the actual field GF8.
The Python producer is untrusted; the Lean kernel checks every used identity.

`Words.lean` extends the existing sparse checker with diagonal torus atoms.
`Cells/` contains the 63 nonidentity cells for the 64-element rank-one family
and the seven nonidentity cells for the eight-element family. All 70 identities
passed Auckland replay in 13 six-case batches, plus the word checker, metadata,
and aggregate (16 modules total; 304.07 user CPU seconds; peak 2,549,248 KiB).
Logs are in `remote-logs/`.

`CellIdentities.lean` converts those checks to actual group equalities with
root-family factors and torus factors. `r_rankOne_of_coverage` and
`s_rankOne_of_coverage` explicitly take the small-family coverage proved in
`RootCollection`; they do not assume ambient Bruhat coverage.

`SimpleWeyl.lean` deduces the complete simple-reflection action on all positive
root curves from the 21 checked parameter-one relations and the proved torus
action. `Radicals.lean` proves preservation of the two radical subgroups by
their simple reflections and by the torus.

`Orientation.lean` proves both Bruhat orientations for every actual Weyl
representative. Its finite checks are 48 paths in the positive root-index
graph; the soundness theorem turns each step into a proved full-parameter
group identity. It does not enumerate the ambient group or the radical.

`Nondegenerate.lean` exhibits a nonzero upper-diagonal entry in each simple
reflection's conjugate of a positive root. Together with the proved lower
triangularity of B, these give both BN nondegeneracy witnesses.

Import `Kourovka.Problem2153.RankOne` for the full API, or an individual helper
to avoid later dependencies. `Audit.lean` prints the axiom dependencies.
