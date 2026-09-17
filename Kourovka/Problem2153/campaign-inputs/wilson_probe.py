#!/usr/bin/env python3
"""Exact GF(8) probe of Wilson's 26-dimensional large-Ree generators.

Source: R. A. Wilson, A simple construction of the Ree groups of type 2F4,
author draft 05/06/09, sections 1, 3--5, pp. 3, 6--8.
https://webspace.maths.qmul.ac.uk/r.a.wilson/pubs_files/ReeF4alg.pdf

This file certifies only the explicitly reported matrix identities. It does
NOT certify that the generated group is simple or that Bruhat cells cover it.
Rows are images of basis vectors, so vectors act on the right.
GF(8) is GF(2)[omega]/(omega^3+omega+1), with omega encoded by 2.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import hashlib
import json
import numpy as np

OUT = Path(__file__).resolve().parent


def field_mul(a: int, b: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 11
    return out


MUL = np.array([[field_mul(a, b) for b in range(8)] for a in range(8)], dtype=np.uint8)


def fpow(a: int, n: int) -> int:
    if n < 0:
        assert a
        n %= 7
    out = 1
    while n:
        if n & 1:
            out = int(MUL[out, a])
        a = int(MUL[a, a])
        n >>= 1
    return out


# A-grade order. Eliminate w''_0 = w_0 + w'_0.
positive = [(1, 1), (0, 1), (2, -1), (0, 2), (2, 2), (0, 3),
            (1, 2), (2, 3), (1, 3), (1, 4), (2, 4), (0, 4)]
basis = [(p, -i) for p, i in reversed(positive)] + [(0, 0), (1, 0)] + positive
INDEX = {v: i for i, v in enumerate(basis)}
I = np.eye(26, dtype=np.uint8)


def vec(*terms: tuple[int, int]) -> np.ndarray:
    out = np.zeros(26, dtype=np.uint8)
    for term in terms:
        if term == (2, 0):
            out[INDEX[(0, 0)]] ^= 1
            out[INDEX[(1, 0)]] ^= 1
        else:
            out[INDEX[term]] ^= 1
    return out


def mapping(changes: dict[tuple[int, int], list[tuple[int, int]]]) -> np.ndarray:
    return np.array([vec(*changes.get(b, [b])) for b in basis], dtype=np.uint8)


def additions(changes: dict[tuple[int, int], list[tuple[int, int]]]) -> np.ndarray:
    return mapping({b: [b] + extra for b, extra in changes.items()})


def perm(swaps: list[tuple[tuple[int, int], tuple[int, int]]]) -> np.ndarray:
    changes = {}
    for a, b in swaps:
        changes[a] = [b]
        changes[b] = [a]
    return mapping(changes)


rho = perm([((0, -1), (0, 1)), ((0, -2), (0, 2)),
            ((1, -4), (1, -3)), ((1, -2), (1, -1)),
            ((1, 1), (1, 2)), ((1, 3), (1, 4)),
            ((2, -4), (2, -3)), ((2, -2), (2, 1)),
            ((2, -1), (2, 2)), ((2, 3), (2, 4))])
sigma = perm([((0, 0), (2, 0)), ((0, -4), (2, -4)),
              ((0, -1), (2, 1)), ((0, 1), (2, -1)),
              ((0, 4), (2, 4)), ((0, -3), (2, -2)),
              ((0, -2), (2, -3)), ((0, 3), (2, 2)),
              ((0, 2), (2, 3)), ((1, -3), (1, -2)),
              ((1, -1), (1, 1)), ((1, 2), (1, 3))])
t = additions({(2, -4): [(0, -4)], (0, 4): [(2, 4)],
               (0, -1): [(2, 1)], (2, -1): [(0, 1)],
               (1, -2): [(1, -3)], (1, 3): [(1, 2)],
               (0, 0): [(1, -1)], (1, 1): [(1, 0), (1, -1)],
               (0, -2): [(2, -2), (0, -3), (2, -3)],
               (2, -2): [(2, -3)], (0, -3): [(2, -3)],
               (2, 2): [(0, 2)], (0, 3): [(0, 2)],
               (2, 3): [(0, 3), (2, 2), (0, 2)]})
x = additions({(1, -4): [(2, -4)],
               (1, -3): [(1, -4), (2, -4)],
               (2, -3): [(1, -3), (2, -4)],
               (2, -2): [(1, -2)],
               (2, 1): [(2, -2), (1, -2)],
               (1, -1): [(2, 1), (1, -2)],
               (2, -1): [(1, 1)],
               (2, 2): [(2, -1), (1, 1)],
               (1, 2): [(2, 2), (1, 1)],
               (1, 3): [(2, 3)],
               (1, 4): [(1, 3), (2, 3)],
               (2, 4): [(1, 4), (2, 3)],
               (0, -1): [(0, -2)], (1, 0): [(0, -1)],
               (0, 1): [(0, 0), (0, -1), (0, -2)],
               (0, 2): [(0, 1), (0, 0), (0, -2)]})


def mm(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    # Only 26 XOR reductions; no floating-point arithmetic occurs.
    c = np.zeros((26, 26), dtype=np.uint8)
    for k in range(26):
        c ^= MUL[a[:, k, None], b[None, k, :]]
    return c


def mpow(a: np.ndarray, n: int) -> np.ndarray:
    out = I.copy()
    while n:
        if n & 1:
            out = mm(out, a)
        a = mm(a, a)
        n >>= 1
    return out


def eq(a: np.ndarray, b: np.ndarray) -> bool:
    return bool(np.array_equal(a, b))


def inv(a: np.ndarray) -> np.ndarray:
    a = a.copy()
    b = I.copy()
    for j in range(26):
        pivot = next(i for i in range(j, 26) if a[i, j])
        a[[j, pivot]] = a[[pivot, j]]
        b[[j, pivot]] = b[[pivot, j]]
        fac = fpow(int(a[j, j]), -1)
        a[j] = MUL[fac, a[j]]
        b[j] = MUL[fac, b[j]]
        for i in range(26):
            if i != j and a[i, j]:
                fac = int(a[i, j])
                a[i] ^= MUL[fac, a[j]]
                b[i] ^= MUL[fac, b[j]]
    assert eq(a, I)
    return b


def conj(a: np.ndarray, g: np.ndarray) -> np.ndarray:
    return mm(mm(inv(g), a), g)


def commute(a: np.ndarray, b: np.ndarray) -> bool:
    return eq(mm(a, b), mm(b, a))


def torus(alpha: int, beta: int) -> np.ndarray:
    # n=1 and 2^(n+1)=4. Exponents may be reduced mod7 for nonzero inputs.
    exponents = {
        (0, -4): (1, 0), (2, -4): (0, 1), (1, -4): (3, 3),
        (1, -3): (1, -3), (2, -3): (4, -1), (1, -2): (-3, 1),
        (0, -3): (3, 0), (2, -2): (0, 3), (0, -2): (-1, 4),
        (2, 1): (-2, -3), (0, -1): (-3, -2), (1, -1): (1, -1)
    }
    vals = {(0, 0): 1, (1, 0): 1}
    for (p, i), (a, b) in exponents.items():
        val = int(MUL[fpow(alpha, a), fpow(beta, b)])
        vals[p, i] = val
        vals[p, -i] = fpow(val, -1)
    return np.diag(np.array([vals[b] for b in basis], dtype=np.uint8))


def finite_closure(gens: list[tuple[str, np.ndarray]], cap: int) -> list[tuple[str, np.ndarray]]:
    found = {I.tobytes(): 0}
    out = [("", I.copy())]
    for word, a in out:
        for name, b in gens:
            c = mm(a, b)
            if c.tobytes() not in found:
                found[c.tobytes()] = len(out)
                out.append((word + name, c))
                assert len(out) <= cap
    return out


def matrix_order(a: np.ndarray, cap: int = 100) -> int:
    b = I.copy()
    for n in range(1, cap + 1):
        b = mm(b, a)
        if eq(b, I):
            return n
    raise ValueError("matrix order exceeds probe cap")


def positive_matrix(a: np.ndarray) -> bool:
    return bool(not np.any(np.triu(a ^ I, 1)))


def sparse(a: np.ndarray) -> list[list[int]]:
    return [[int(i), int(j), int(a[i, j])] for i, j in zip(*np.nonzero(a ^ I))]


def run() -> dict:
    assert len(basis) == len(INDEX) == 26
    assert all(MUL[a, b] == MUL[b, a] for a in range(8) for b in range(8))
    assert matrix_order(t) == 2 and matrix_order(x) == 4
    assert matrix_order(rho) == matrix_order(sigma) == 2
    assert matrix_order(mm(rho, sigma)) == 8
    W = finite_closure([("r", rho), ("s", sigma)], 16)
    H = [(a, b, torus(a, b)) for a in range(1, 8) for b in range(1, 8)]
    assert len(W) == 16 and len({h.tobytes() for a, b, h in H}) == 49
    hkeys = {h.tobytes() for a, b, h in H}
    assert all(conj(h, g).tobytes() in hkeys for a, b, h in H for g in [rho, sigma])
    roots = {}
    for typ, a in [("t", t), ("x", x)]:
        for word, w in W:
            b = conj(a, w)
            if positive_matrix(b):
                roots.setdefault((typ, b.tobytes()), (typ, word, b))
    positives = list(roots.values())
    assert Counter(typ for typ, word, a in positives) == {"t": 4, "x": 4}
    central_squares = [(word, mpow(a, 2)) for typ, word, a in positives if typ == "x"
                      and all(commute(mpow(a, 2), b) for typ2, word2, b in positives)]
    assert len(central_squares) == 1
    zword, z = central_squares[0]
    zparams = {}
    for a, b, h in H:
        zh = conj(z, h)
        zparams.setdefault(zh.tobytes(), (a, b, zh))
    assert len(zparams) == 7
    Z = [I.copy()] + [c for a, b, c in zparams.values()]
    zkeys = {c.tobytes() for c in Z}
    assert all(mm(a, b).tobytes() in zkeys for a in Z for b in Z)
    assert all(eq(mpow(a, 2), I) for a in Z)
    # H normalizes each positive relative root direction; test all H conjugates.
    positive_hconjs = [conj(b, h) for typ, word, b in positives for a, c, h in H]
    assert all(commute(zv, b) for zv in Z for b in positive_hconjs)
    # Actual finite double-cell representatives, not yet an ambient coverage claim.
    cases = []
    centralizer_patterns = []
    for zi, zv in enumerate(Z[1:], 1):
        centralizer_patterns.append([commute(zv, mm(h, w)) for a, b, h in H for word, w in W])
    assert all(pat == centralizer_patterns[0] for pat in centralizer_patterns)
    for a, b, zv in zparams.values():
        for word, w in W:
            prod = mm(z, conj(zv, w))
            n = matrix_order(prod)
            assert n != 3
            cases.append({"torus": [a, b], "weyl": word, "order": n})
    witnesses = {n: next(case for case in cases if case["order"] == n) for n in [5, 7]}
    report = {
        "status": "PASS_EXPLICIT_MATRIX_IDENTITIES_ONLY",
        "coverage_proved": False,
        "simplicity_proved": False,
        "field_modulus": "X^3+X+1",
        "source": "https://webspace.maths.qmul.ac.uk/r.a.wilson/pubs_files/ReeF4alg.pdf",
        "basis": basis,
        "weyl_size": len(W), "torus_size": len(H),
        "positive_roots": [{"type": typ, "weyl": word} for typ, word, a in positives],
        "central_involution": {"word": f"(x^2)^({zword or '1'})", "sparse_delta": sparse(z)},
        "root_subgroup_order": len(Z),
        "positive_root_centrality_checks": len(Z)*len(positive_hconjs),
        "centralizer_pattern_comparisons": len(centralizer_patterns),
        "centralizer_pattern_length": len(centralizer_patterns[0]),
        "centralizer_pattern_true_count": sum(centralizer_patterns[0]),
        "product_order_counts": dict(sorted(Counter(case["order"] for case in cases).items())),
        "pair_cases": cases,
        "order5_case": witnesses[5], "order7_case": witnesses[7],
        "source_sha256": hashlib.sha256((OUT / "sources/Wilson-ReeF4alg.pdf").read_bytes()).hexdigest(),
    }
    (OUT / "wilson-probe.json").write_text(json.dumps(report, indent=2) + "\n")
    raw = {"basis": basis, "t": t.tolist(), "x": x.tolist(),
           "rho": rho.tolist(), "sigma": sigma.tolist(), "z": z.tolist(),
           "torus": [{"a": a, "b": b, "diag": np.diag(h).tolist()} for a, b, h in H],
           "weyl_words": [word for word, w in W]}
    (OUT / "wilson-generators.json").write_text(json.dumps(raw, separators=(",", ":")) + "\n")
    return {k: v for k, v in report.items() if k not in ["basis", "pair_cases", "central_involution"]}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
