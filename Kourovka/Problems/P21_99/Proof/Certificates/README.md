# Finite certificates for Problem 21.99

The generated Lean data encodes matrices over `ZMod 5` by lists of their nonzero
row entries. Every row of the 384 ambient 18-dimensional matrices has at most
two entries. `DataBasic.lean` interprets these lists as linear maps and proves
that checking coordinate basis images suffices for equality.

The acceptance checks are Lean theorems proved with `decide +kernel`:

- `InverseCheck*.lean`: inverse matrix and block-permutation partners for the
  384 explicit ambient elements.
- `StepCheck*.lean`: right multiplication by each of eight generators stays in
  the table, checking 3,072 transitions. The abstract generated-subgroup lemma
  supplies coverage; no arbitrary-pair multiplication table is needed.
- `CovarianceCheck*.lean`: compatibility with six surjective maps from 18 to 14
  coordinates. `DataElementary.lean` checks their explicit right inverses.
- `FixedCheck*.lean`: for each of the 64 table elements moving block 0 to block
  2, exactly two blocks are fixed. On one block, the difference between identity
  and the induced linear map has an explicit two-sided inverse. On the other,
  a covector is invariant and its translated value is nonzero for every allowed
  transporter translation.

`DataElementary.lean` also checks that the 64 transporter indices cover every
table element moving block 0 to block 2, and checks six generator words whose
block images cover all blocks. No points of the affine action are enumerated.

`scripts/generate_21_99.py` is an untrusted source-data generator. It takes the
sealed affine input and compact linear certificate and emits ordinary Lean
definitions plus the theorem statements above. Its Python assertions are only
generation diagnostics. The compiled Lean proof does not import JSON, invoke
Python or GAP, call `native_decide`, or assume the output of an external checker.
The exact source hashes and emitted-file hashes are recorded in
`../generation_receipt.json`; final proof acceptance requires a successful Lean
kernel build and the theorem axiom audit.
