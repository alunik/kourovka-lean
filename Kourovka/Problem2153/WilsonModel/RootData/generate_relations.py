#!/usr/bin/env python3
"""Emit exact reduced word relations with individually checked sparse suffix products."""
from pathlib import Path
import sys,json
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
STRUCT = INPUTS
sys.path.insert(0,str(STRUCT))
import collection_probe as c
red=json.loads((STRUCT/'reduced-collection-certificate.json').read_text())
OUT=HERE/'Relations'; OUT.mkdir(exist_ok=True)
header='''import Kourovka.Problem2153.WilsonModel.RootData.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
'''
def root(i,a): return ('root',i,a)
def atom(a):
 return f'Atom.root {a[1]} {a[2]}' if a[0]=='root' else f'Atom.{a[0]}'
def atoms(w):return '['+', '.join(atom(a) for a in w)+']'
def mat(a):return c.RF[a[1]][a[2]] if a[0]=='root' else (c.rho if a[0]=='rho' else c.sigma)
def evaluate(w):
 result=c.I.copy()
 for a in w:result=c.mm(result,mat(a))
 return result
def coordword(v):return [root(i,a) for i,a in enumerate(v) if a]
rel={}
for kind,key in [('inverse','inverse_representatives'),('product','product_representatives'),('commutator','commutator_representatives'),('weyl','positive_weyl_representatives')]:
 rel[kind]=[]
 for row in red[key]:
  if kind=='inverse':
   i,a,v=row; lhs=[root(i,a)]+coordword(v); rhs=[]
  elif kind=='product':
   i,a,b,v=row; lhs=[root(i,a),root(i,b)];rhs=coordword(v)
  elif kind=='commutator':
   i,j,a,b,v=row;lhs=[root(i,a),root(j,b)];rhs=[root(j,b),root(i,a)]+coordword(v)
  else:
   i,w,a,v=row;g=('rho' if w=='r' else 'sigma',);lhs=[g,root(i,a),g];rhs=coordword(v)
  assert c.eq(evaluate(lhs),evaluate(rhs)), (kind,row)
  rel[kind].append((lhs,rhs))
s=header
for kind,pairs in rel.items():
 for side in ['lhs','rhs']:
  n=0 if side=='lhs' else 1
  s+=f'def {kind}_{side} : Fin {len(pairs)} → List Atom :=\n  !['+',\n    '.join(atoms(pair[n]) for pair in pairs)+']\n\n'
s+='end Kourovka.Problem2153.WilsonModel.RootData.Relations\n'
(OUT/'Metadata.lean').write_text(s)

def emit_table(name,m):
 if c.eq(m,c.I):return f'private def {name} : Mat := 1\n'
 rows=['['+', '.join(f'({j}, e{v})' for j,v in enumerate(row) if v)+']' for row in m]
 return f'private def {name} : Mat := Sparse.eval (!['+',\n    '.join(rows)+'])\n'

def emit_word(name,w,target):
 s=''
 if not w:
  return f'private theorem {name} : wordMatrix [] = {target} := by decide +kernel\n'
 last=atom(w[-1]); previous=f'{name}_s{len(w)-1}'
 s+=f'private theorem {previous} : wordMatrix {atoms(w[-1:])} = atomMatrix ({last}) := by simp\n'
 for j in reversed(range(len(w)-1)):
  this=f'{name}_s{j}'
  dest=target if j==0 else f'{name}_m{j}'
  if j>0:s+=emit_table(dest,evaluate(w[j:]))
  s+=f'''private theorem {this} : wordMatrix {atoms(w[j:])} = {dest} := by
  rw [wordMatrix_cons, {previous}]
  apply Sparse.mul_eq_of_check (atomRows ({atom(w[j])}))
  decide +kernel
'''
  previous=this
 if len(w)==1:
  s+=f'private theorem {name} : wordMatrix {atoms(w)} = {target} := by\n  rw [{previous}]\n  decide +kernel\n'
 else:s+=f'private theorem {name} : wordMatrix {atoms(w)} = {target} := {previous}\n'
 return s
batches={}
for kind,pairs in rel.items():
 paths=[]
 for start in range(0,len(pairs),6):
  bname=kind.capitalize()+f'{start//6:02}'
  paths.append(bname)
  s=header.replace('RootData.Words','RootData.Relations.Metadata')
  for k in range(start,min(start+6,len(pairs))):
   lhs,rhs=pairs[k];name=f'{kind}_{k}';target=name+'_target'
   s+=emit_table(target,evaluate(lhs))
   s+=emit_word(name+'_left',lhs,target)
   s+=emit_word(name+'_right',rhs,target)
   s+=f'''theorem {name} : wordGroup ({kind}_lhs {k}) = wordGroup ({kind}_rhs {k}) := by
  apply word_eq_of_matrix_eq
  exact {name}_left.trans {name}_right.symm

'''
  s+='end Kourovka.Problem2153.WilsonModel.RootData.Relations\n'
  (OUT/(bname+'.lean')).write_text(s)
 batches[kind]=paths
s=''
for paths in batches.values():
 for name in paths:s+=f'import Kourovka.Problem2153.WilsonModel.RootData.Relations.{name}\n'
s+='\nset_option autoImplicit false\nnamespace Kourovka.Problem2153.WilsonModel.RootData.Relations\n'
for kind,pairs in rel.items():
 s+=f'theorem {kind}_checked (k : Fin {len(pairs)}) : wordGroup ({kind}_lhs k) = wordGroup ({kind}_rhs k) := by\n  fin_cases k\n'
 for k in range(len(pairs)):s+=f'  · exact {kind}_{k}\n'
s+='end Kourovka.Problem2153.WilsonModel.RootData.Relations\n'
(HERE/'Relations.lean').write_text(s)
print({kind:len(v) for kind,v in rel.items()})
