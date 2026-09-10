# Source data for Problem 21.99

These files preserve the input to the untrusted Lean-data generator. The Lean
proof does not read them or trust their computational provenance.

- `input.af`: explicit characteristic-five affine model, exported from the
  Auckland search family
  `30T2763_p5_mixed_triple_irr1_irr3_irr6.af`.
  SHA-256: `b9c99c8ee4a094bb2f4c7f3ea3c1ff56e4feaa71e90e91082ae7b43f7c8debfe`.
- `compact_certificate.json`: extracted sparse linear data for the original
  transporter certificate, including its original translation vector.
  SHA-256: `1a5440c526959dd9f804fc8902da3f0d3dffa54017d53bc52c0baeaa4f315a37`.
  Its embedded source-certificate SHA-256 is
  `b6210092ba96fb5ecf4e469bd8b44124ff2c9cd2af63caf7562985f02fef2aea`.

The original search lead was recorded under
`30T2763_p5_mixed_triple_irr1_irr3_irr6_overlap_dense_1fca40d971`, candidate
`1000000002876`, target block 2. Independent GAP replay and the compact-data
extraction preceded the formalization. Those computations motivated the data;
they are not assumptions of the Lean theorem. In particular, metadata about
abstract group orders, group identifiers and search coverage is not asserted
by the formal theorem.

## Reproduce and compare

The recorded independent replay ran on Auckland. To repeat it there, run
from the repository root. Generate into a fresh directory:

```sh
repro_dir=$(mktemp -d)
python3 scripts/generate_21_99.py \
  --input scripts/data/21_99/input.af \
  --compact scripts/data/21_99/compact_certificate.json \
  --output "$repro_dir/Proof"
```

Compare the exact emitted inventory, all 142 generated Lean files, and the
generation receipt against the committed sources:

```sh
python3 - "$repro_dir/Proof" <<'PYTHON'
import hashlib
import json
from pathlib import Path
import sys

actual = Path(sys.argv[1])
expected = Path("Kourovka/Problems/P21_99/Proof")
receipt = json.loads((expected / "generation_receipt.json").read_text())
files = set(receipt["files"]) | {"generation_receipt.json"}
emitted = {
    str(p.relative_to(actual)) for p in actual.rglob("*")
    if p.is_file() and not p.name.startswith("._")
}
if emitted != files:
    raise SystemExit("FAIL: emitted file inventory differs")
for name in sorted(files):
    data = (actual / name).read_bytes()
    if data != (expected / name).read_bytes():
        raise SystemExit(f"FAIL: {name} differs")
    if name in receipt["files"]:
        if hashlib.sha256(data).hexdigest() != receipt["files"][name]:
            raise SystemExit(f"FAIL: {name} does not match the recorded hash")
print(f"PASS: {len(receipt['files'])} Lean files and the receipt match")
PYTHON
```

The comparison reads the committed sources without replacing them. The
temporary directory retains the regenerated files for inspection. To verify
the committed proofs, use the repository's
[full build and guarded audit](../../../README.md#check-the-proofs) at the
pinned versions. If intentionally updating the generated sources, rebuild
and audit the changed proof and record fresh verification evidence.

Generation assertions and the generation receipt are only diagnostics;
acceptance is the kernel-checked Lean proof and its axiom audit.
