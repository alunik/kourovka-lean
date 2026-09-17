#!/usr/bin/env python3
"""Emit untrusted finite Weyl tables; every used fact is kernel checked in Lean."""
from pathlib import Path
import importlib.util
import json

HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
REPO=HERE.parents[2]
SOURCE = INPUTS / 'wilson_probe.py'
spec=importlib.util.spec_from_file_location('wilson_source',SOURCE)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
W=m.finite_closure([('r',m.rho),('s',m.sigma)],16)
indices={a.tobytes():i for i,(word,a) in enumerate(W)}
leftR=[indices[m.mm(m.rho,a).tobytes()] for word,a in W]
leftS=[indices[m.mm(m.sigma,a).tobytes()] for word,a in W]

def leanlist(xs):return '['+', '.join(str(x) for x in xs)+']'
def leanvec(xs):return '!'+leanlist(xs)
def boolword(s):return leanlist('false' if a=='r' else 'true' for a in s)
def rows(a):
    return leanvec(leanlist(f'({j}, e{int(row[j])})' for j in range(26) if row[j]) for row in a)

above=[]
for word,a in W:
    positions=[(i,j) for i in range(26) for j in range(i+1,26) if a[i,j]]
    above.append(positions[0] if positions else (0,0))
different=[]
for i,(_,a) in enumerate(W):
    row=[]
    for j,(_,b) in enumerate(W):
        positions=[(u,v) for u in range(26) for v in range(26) if a[u,v]!=b[u,v]]
        row.append(positions[0] if positions else (0,0))
    different.append(row)

certificate=json.loads(SOURCE.with_name('simplicity-certificate.json').read_text())
extraction={row['weyl']:row['w0_word'] for row in certificate['parabolic_maximality_weyl_words']}
extractwords=[leanlist('false' if a=='r' else 'true' for a in extraction.get(word,'')) for word,_ in W]

s='''import Kourovka.Problem2153.WilsonModel.SparseBenchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem.WeylData
open WilsonModel Field8 F8

'''
s+='def words : Fin 16 → List Bool :=\n  '+leanvec(boolword(word) for word,a in W)+'\n\n'
s+='def rows : Fin 16 → Sparse.Table (Fin 26) :=\n  '+leanvec(rows(a) for word,a in W)+'\n\n'
s+='def matrix (i : Fin 16) : WilsonModel.Mat := Sparse.eval (rows i)\n\n'
s+='def leftR : Fin 16 → Fin 16 := '+leanvec(leftR)+'\n'
s+='def leftS : Fin 16 → Fin 16 := '+leanvec(leftS)+'\n\n'
s+='def above : Fin 16 → Fin 26 × Fin 26 := '+leanvec(f'({i}, {j})' for i,j in above)+'\n\n'
s+='def distinguish : Fin 16 → Fin 16 → Fin 26 × Fin 26 :=\n  '+leanvec(leanvec(f'({i}, {j})' for i,j in row) for row in different)+'\n\n'
s+='def extractionWord : Fin 16 → List Bool :=\n  '+leanvec(extractwords)+'\n\n'
s+='''theorem matrix_zero : matrix 0 = 1 := by decide +kernel

theorem rho_left_check : ∀ i : Fin 16,
    Sparse.mulEval rhoSparse (matrix i) = matrix (leftR i) := by decide +kernel

theorem sigma_left_check : ∀ i : Fin 16,
    Sparse.mulEval sigmaSparse (matrix i) = matrix (leftS i) := by decide +kernel

theorem rho_left (i : Fin 16) : rho * matrix i = matrix (leftR i) :=
  Sparse.mul_eq_of_check_alignment rho rhoSparse _ _ rho_alignment (rho_left_check i)

theorem sigma_left (i : Fin 16) : sigma * matrix i = matrix (leftS i) :=
  Sparse.mul_eq_of_check_alignment sigma sigmaSparse _ _ sigma_alignment (sigma_left_check i)

theorem above_nonzero : ∀ i : Fin 16, i ≠ 0 →
    (above i).1 < (above i).2 ∧ matrix i (above i).1 (above i).2 ≠ 0 := by decide +kernel

theorem distinguish_ne : ∀ i j : Fin 16, i ≠ j →
    matrix i (distinguish i j).1 (distinguish i j).2 ≠
      matrix j (distinguish i j).1 (distinguish i j).2 := by decide +kernel

end Kourovka.Problem2153.RootSystem.WeylData
'''
(HERE/'Data.lean').write_text(s)
print('Generated16 sparse matrices and32 generator-transition checks.')
