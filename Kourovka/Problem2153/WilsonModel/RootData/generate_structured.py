#!/usr/bin/env python3
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
r=json.loads((INPUTS/'reduced-collection-certificate.json').read_text())
header='''import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations

'''
s=header+'''abbrev Coordinates := Fin 12 → Fin 8
structure InverseRow where
  i : Fin 12
  a : Fin 8
  coords : Coordinates
structure ProductRow extends InverseRow where
  b : Fin 8
structure CommutatorRow extends ProductRow where
  j : Fin 12
structure WeylRow extends InverseRow where
  sigma : Bool

'''
def vec(xs):return '!['+', '.join(map(str,xs))+']'
for kind,n,typ in [('inverse',12,'InverseRow'),('product',84,'ProductRow'),('commutator',90,'CommutatorRow'),('positive_weyl',21,'WeylRow')]:
 name='weyl' if kind=='positive_weyl' else kind
 key=kind+'_representatives'
 vals=[]
 for row in r[key]:
  if kind=='inverse':i,a,v=row; attrs=f'i := {i}, a := {a}'
  elif kind=='product':i,a,b,v=row;attrs=f'i := {i}, a := {a}, b := {b}'
  elif kind=='commutator':i,j,a,b,v=row;attrs=f'i := {i}, j := {j}, a := {a}, b := {b}'
  else:i,w,a,v=row;attrs=f'i := {i}, a := {a}, sigma := '+('true' if w=='s' else 'false')
  vals.append('{ '+attrs+', coords := '+vec(v)+' }')
 s+=f'def {name}Data : Fin {n} → {typ} :=\n  !['+',\n    '.join(vals)+']\n\n'
s+='''def coordinateWord (v : Coordinates) : List Atom :=
  ((List.ofFn fun i : Fin 12 => (i, v i)).filter fun p => p.2 != 0).map
    (fun p => Atom.root p.1 p.2)

def coordinateGroup (v : Coordinates) : RootSystem.G :=
  (List.ofFn fun i : Fin 12 => RootSystem.root i (v i)).prod

theorem wordGroup_append (a b : List Atom) :
    wordGroup (a ++ b) = wordGroup a * wordGroup b := by
  simp [wordGroup, List.map_append, List.prod_append]

private theorem filtered_wordGroup (l : List (Fin 12 × Fin 8)) :
    wordGroup ((l.filter fun p => p.2 != 0).map (fun p => Atom.root p.1 p.2)) =
      (l.map (fun p => RootSystem.root p.1 p.2)).prod := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨i,a⟩
    by_cases ha : a = 0
    · simp [ha, wordGroup, RootSystem.root_zero] at *
      exact ih
    · simp [ha, wordGroup, atomGroup] at *
      exact ih

theorem coordinateWord_group (v : Coordinates) :
    wordGroup (coordinateWord v) = coordinateGroup v := by
  rw [coordinateWord, filtered_wordGroup]
  simp [coordinateGroup]

def weylGenerator (b : Bool) : RootSystem.G := if b then RootSystem.s else RootSystem.r

theorem weylGenerator_inv (b : Bool) : (weylGenerator b)⁻¹ = weylGenerator b := by
  cases b <;> apply Subtype.ext <;> apply Units.ext <;> rfl

end Kourovka.Problem2153.WilsonModel.RootData.Relations
'''
(HERE/'Relations'/'Structured.lean').write_text(s)
s=header.replace('Relations.Metadata','Relations.Structured')
s+='abbrev Transport (n : ℕ) := Fin n × (Fin 7 × Fin 7)\n\n'
cm={}
for i,j,a,b,k,(x,y) in r['commutator_transport']:cm[i,j,a,b]=(k,x-1,y-1)
# The JSON fourth entry is a nonzero field ratio, not a representative index.
pm={(i,a,b):(7*i+k-1,x-1,y-1) for i,a,b,k,(x,y) in r['product_transport']}
for (i,a,b),(k,x,y) in pm.items():
 assert r['product_representatives'][k][0] == i
 assert r['product_representatives'][k][1:3] == [1,k % 7 + 1]
im={(i,a):(i,x-1,y-1) for i,a,(x,y) in r['inverse_transport']}
def opt(x):return 'none' if x is None else f'some ({x[0]}, ({x[1]}, {x[2]}))'
for i in range(12):
 for j in range(i+1,12):
  vals=['!['+', '.join(opt(cm.get((i,j,a,b))) for b in range(8))+']' for a in range(8)]
  s+=f'private def commPair_{i}_{j} : Fin 8 → Fin 8 → Option (Transport 90) :=\n  !['+',\n    '.join(vals)+']\n'
s+='def commutatorTransport (i j : Fin 12) (a b : Fin 8) : Option (Transport 90) :=\n  match i.val, j.val with\n'
for i in range(12):
 for j in range(i+1,12):s+=f'  | {i}, {j} => commPair_{i}_{j} a b\n'
s+='  | _, _ => none\n\n'
rows=[]
for i in range(12):rows.append('!['+',\n      '.join('!['+', '.join(opt(pm.get((i,a,b))) for b in range(8))+']' for a in range(8))+']')
s+='def productTransport : Fin 12 → Fin 8 → Fin 8 → Option (Transport 84) :=\n  !['+',\n    '.join(rows)+']\n\n'
s+='def inverseTransport : Fin 12 → Fin 8 → Option (Transport 12) :=\n  !['+',\n    '.join('!['+', '.join(opt(im.get((i,a))) for a in range(8))+']' for i in range(12))+']\n\n'
s+='end Kourovka.Problem2153.WilsonModel.RootData.Relations\n'
(HERE/'Relations'/'Transport.lean').write_text(s)
