# Actual finite Weyl subgroup

`Weyl.lean` proves that the subgroup `W = <r,s>` of `RootSystem.G` has exactly
16 elements. The representatives are actual group words in the order

```
1, r, s, rs, sr, rsr, srs, rsrs, srsr, rsrsr, srsrs,
rsrsrs, srsrsr, rsrsrsr, srsrsrs, rsrsrsrs.
```

`Data.lean` supplies sparse matrices and 32 left-generator transitions, all
checked by the ordinary Lean kernel. Subgroup closure induction uses these
transitions and the two already proved involution identities. No ambient group
enumeration or asserted Weyl-group identification is used.

Main interfaces in namespace `RootSystem.Weyl`:

- `exists_rep_of_mem_W`, `rep_mem_W`, `rep_injective`, `card_W`;
- `rep_matrix`, `r_mul_rep`, `s_mul_rep`, `rep_mul`;
- `eq_one_of_mem_W_lowerTriangular`;
- `w0_eq : w0 = (r*s)^4`;
- `w0_mem_closure`, and `w0_mem_closure_of_not_mem` for parabolic maximality.

The 14 maximality words are checked through the same finite transition
system, rather than fresh dense matrix multiplication.

`Audit.lean` passed with only `propext`, `Classical.choice`, and `Quot.sound`.
`generate_data.py` is an untrusted producer; source evidence lives in the
campaign's `lean/structural` directory.
