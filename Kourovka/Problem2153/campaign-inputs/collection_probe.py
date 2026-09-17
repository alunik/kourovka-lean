#!/usr/bin/env python3
"""Extract finite local collection data for the explicit Wilson matrix model.

The output is arithmetic certificate data, not a formal proof of closure,
Bruhat coverage, simplicity, or the final counterexample.
"""
from __future__ import annotations

from collections import Counter
import json
import numpy as np
from wilson_probe import (OUT, I, MUL, mm, mpow, inv, conj, eq, commute, torus,
                         finite_closure, positive_matrix, rho, sigma, t, x)


def first_position(a):
    return min((int(i-j), int(i), int(j)) for i, j in zip(*np.nonzero(a ^ I)))


def root_data():
    W = finite_closure([("r", rho), ("s", sigma)], 16)
    H = [(a, b, torus(a, b)) for a in range(1, 8) for b in range(1, 8)]
    roots = {}
    for typ, a in [("t", t), ("x", x), ("z", mpow(x, 2))]:
        for word, w in W:
            b = conj(a, w)
            if positive_matrix(b):
                roots.setdefault((typ, b.tobytes()), (typ, word, b))
    families = []
    for typ, word, a in roots.values():
        root = {I.tobytes(): (0, 0, I.copy())}
        for ha, hb, h in H:
            b = conj(a, h)
            root.setdefault(b.tobytes(), (ha, hb, b))
        assert len(root) == 8, (typ, word, len(root))
        pos = first_position(a)
        parameterized = {int(b[pos[1], pos[2]]): (ha, hb, b) for ha, hb, b in root.values()}
        assert len(parameterized) == 8
        families.append({"type": typ, "word": word, "pivot": pos,
                         "family": [parameterized[i][2] for i in range(8)],
                         "torus_parameters": [[parameterized[i][0], parameterized[i][1]] for i in range(8)]})
    families.sort(key=lambda row: row["pivot"])
    assert len(families) == 12
    return families, W, H


ROOTS, W, H = root_data()
RF = [[a for a in row["family"]] for row in ROOTS]
RI = [[inv(a) for a in row] for row in RF]


def collect(a, roots=None):
    if roots is None:
        roots = list(range(12))
    out = []
    a = a.copy()
    for i in roots:
        _, r, c = ROOTS[i]["pivot"]
        v = int(a[r, c])
        out.append(v)
        a = mm(RI[i][v], a)
    assert eq(a, I), ("collection failed", out, roots)
    return out


def evaluate(coords):
    out = I.copy()
    for i, v in enumerate(coords):
        out = mm(out, RF[i][v])
    return out


def run():
    squares = []
    products = []
    swaps = []
    inverse = []
    for i in range(12):
        for s in range(8):
            coords = collect(RI[i][s])
            assert all(coords[j] == 0 for j in range(i))
            inverse.append([i, s, coords])
            for u in range(8):
                coords = collect(mm(RF[i][s], RF[i][u]))
                assert all(coords[j] == 0 for j in range(i))
                products.append([i, s, u, coords])
    for i in range(12):
        for j in range(i+1, 12):
            for s in range(8):
                for u in range(8):
                    # Convention [a,b]=a^-1 b^-1 a b.
                    c = mm(mm(mm(RI[i][s], RI[j][u]), RF[i][s]), RF[j][u])
                    coords = collect(c)
                    assert all(coords[k] == 0 for k in range(j+1)), (i,j,s,u,coords)
                    swaps.append([i,j,s,u,coords])
    wconj = []
    for i in range(12):
        for wn, w in [("r", rho), ("s", sigma)]:
            images = [conj(a,w) for a in RF[i]]
            if all(positive_matrix(a) for a in images):
                for val, a in enumerate(images):
                    coords = collect(a)
                    wconj.append([i,wn,val,coords])
    hconj = []
    for i in range(12):
        for a,b,h in H:
            for val, v in enumerate(RF[i]):
                coords=collect(conj(v,h))
                assert all(coords[j]==0 for j in range(12) if j!=i)
                hconj.append([i,a,b,val,coords[i]])
    cert = {
        "status": "PASS_LOCAL_COLLECTION_IDENTITIES_ONLY",
        "coverage_proved": False, "simplicity_proved": False,
        "root_order": [{"type": r["type"],"weyl": r["word"],"pivot":r["pivot"],
                         "torus_parameters":r["torus_parameters"]} for r in ROOTS],
        "counts": {"inverse":len(inverse),"same_root_product":len(products),
                   "commutator":len(swaps),"positive_weyl_conjugate":len(wconj),
                   "torus_conjugate":len(hconj)},
        "inverse":inverse,"same_root_product":products,"commutator":swaps,
        "positive_weyl_conjugate":wconj,"torus_conjugate":hconj
    }
    (OUT/"collection-certificate.json").write_text(json.dumps(cert,separators=(",",":"))+"\n")
    report = {k:v for k,v in cert.items() if k in ["status","coverage_proved","simplicity_proved","root_order","counts"]}
    (OUT/"collection-report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2),flush=True)


if __name__ == "__main__":
    run()
