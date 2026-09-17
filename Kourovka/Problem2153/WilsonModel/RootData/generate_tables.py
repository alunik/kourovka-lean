#!/usr/bin/env python3
"""Generate untrusted sparse root tables; subsequent Lean certificates establish alignment."""
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
STRUCT = INPUTS
sys.path.insert(0,str(STRUCT))
import collection_probe as c
s='''import Kourovka.Problem2153.WilsonModel
import Kourovka.Problem2153.WilsonModel.Sparse
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData
open Field8 F8

'''
for i,roots in enumerate(c.RF):
 s+=f'def rows{i} : Fin 8 → Sparse.Table (Fin 26) :=\n  !['
 mats=[]
 for mat in roots:
  rows=['['+', '.join(f'({j}, e{v})' for j,v in enumerate(row) if v)+']' for row in mat]
  mats.append('!['+',\n    '.join(rows)+']')
 s+=',\n  '.join(mats)+']\n\n'
s+='def rootRows (i : Fin 12) (a : Fin 8) : Sparse.Table (Fin 26) :=\n  (!['+', '.join(f'rows{i}' for i in range(12))+'] i) a\n\n'
s+='def rootMatrix (i : Fin 12) (a : Fin 8) : Mat := Sparse.eval (rootRows i a)\n\n'
s+='end Kourovka.Problem2153.WilsonModel.RootData\n'
(HERE/'Tables.lean').write_text(s)
