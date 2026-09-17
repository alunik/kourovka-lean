"""Generate untrusted finite frame data. Lean checks every alignment and transition."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
SRC = INPUTS
g=json.loads((SRC/'wilson-generators.json').read_text())
f=json.loads((SRC/'simplicity-certificate.json').read_text())['faithful_projective_frame']
def mul(a,b):
    c=0
    while b:
        if b&1:c^=a
        b>>=1;a<<=1
        if a&8:a^=11
    return c
def rowmul(v,m):
    out=[]
    for j in range(26):
        a=0
        for i in range(26):a^=mul(v[i],m[i][j])
        out.append(a)
    return out
mats=[g[n] for n in ['t','x','rho','sigma']]
for a,b in [(2,1),(1,2)]:
    diag=next(t['diag'] for t in g['torus'] if t['a']==a and t['b']==b)
    mats.append([[diag[i] if i==j else 0 for j in range(26)] for i in range(26)])
words=f['orbit_words']+[f['bridge_word']]
traces=[]
for j,w in enumerate(words):
    v=[1]+[0]*25;trace=[v]
    for a in w:v=rowmul(v,mats[a]);trace.append(v)
    assert v==(f['rows'][j] if j<26 else f['bridge_vector'])
    traces.append(trace)
def vec(v):return '!['+', '.join('e'+str(x) for x in v)+']'
def mat(m):return '!!['+';\n    '.join(', '.join('e'+str(x) for x in v) for v in m)+']'
s='''import Kourovka.Problem2153.AmbientFacts.Frame.Linear
import Kourovka.Problem2153.WilsonModel.Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Kourovka.Problem2153.WilsonModel.Frame
open Field8 F8

abbrev Vec := Fin 26 → F8

def basisZero : Vec := '''+vec([1]+[0]*25)+'''\n
def generatorMatrix : Fin 6 → Mat := ![wilsonT, wilsonX, rho, sigma, Matrix.diagonal (torusDiag 1 0), Matrix.diagonal (torusDiag 0 1)]

'''
columns=[]
for m in mats:
    columns.append('!['+',\n    '.join('['+', '.join(f'({i}, e{m[i][j]})' for i in range(26) if m[i][j])+']' for j in range(26))+']')
s+='def generatorColumns : Fin 6 → Sparse.Table (Fin 26) :=\n  !['+',\n  '.join(columns)+']\n\n'
s+='def frameMatrix : Mat :=\n  '+mat(f['rows'])+'\n\n'
s+='def frameInverse : Mat :=\n  '+mat(f['inverse'])+'\n\n'
for name,m in [('frameRows',f['rows']),('inverseRows',f['inverse'])]:
    s+=f'def {name} : Sparse.Table (Fin 26) :=\n  !['+',\n    '.join('['+', '.join(f'({j}, e{a})' for j,a in enumerate(row) if a)+']' for row in m)+']\n\n'
s+='def bridgeVector : Vec := '+vec(f['bridge_vector'])+'\n\n'
s+='def bridgeCoordinates : Vec := '+vec(f['bridge_coordinates'])+'\n\n'
for j in range(27):
    s+=f'def word{j} : Fin 48 → Fin 6 := !['+', '.join(map(str,words[j]))+']\n\n'
    s+=f'def trace{j} : Fin 49 → Vec :=\n  !['+',\n    '.join(vec(v) for v in traces[j])+']\n\n'
s+='def words : Fin 27 → Fin 48 → Fin 6 := !['+', '.join(f'word{j}' for j in range(27))+']\n\n'
s+='def traces : Fin 27 → Fin 49 → Vec := !['+', '.join(f'trace{j}' for j in range(27))+']\n\n'
s+='end Kourovka.Problem2153.WilsonModel.Frame\n'
(HERE/'Data.lean').write_text(s)
s='''import Kourovka.Problem2153.AmbientFacts.Frame.Data
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.WilsonModel.Frame
open Field8 F8

'''
s+='theorem generator_alignment : ∀ j : Fin 6, (generatorMatrix j).transpose = Sparse.eval (generatorColumns j) := by decide +kernel\n\n'
for j in range(27):
    s+=f'theorem trace{j}_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word{j} k)) (trace{j} k.castSucc) = trace{j} k.succ := by decide +kernel\n\n'
s+='''theorem trace_steps (j : Fin 27) (k : Fin 48) :
    sparseRowAction (generatorColumns (words j k)) (traces j k.castSucc) = traces j k.succ := by
  fin_cases j
'''
for j in range(27):s+=f'  · exact trace{j}_step k\n'
s+='''
theorem trace_starts : ∀ j : Fin 27, traces j 0 = basisZero := by decide +kernel

theorem trace_ends_entries : ∀ i j : Fin 26, traces i.castSucc 48 j = frameMatrix i j := by\n  intro i\n  fin_cases i <;> decide +kernel

theorem trace_ends (i : Fin 26) : traces i.castSucc 48 = frameMatrix i := funext (trace_ends_entries i)

theorem bridge_trace_end : traces 26 48 = bridgeVector := by decide +kernel

theorem frame_alignment : frameMatrix = Sparse.eval frameRows := by decide +kernel

theorem inverse_alignment : frameInverse = Sparse.eval inverseRows := by decide +kernel

theorem frame_mul_inverse : frameMatrix * frameInverse = 1 :=
  Sparse.mul_eq_of_check_alignment frameMatrix frameRows frameInverse 1 frame_alignment (by decide +kernel)

theorem inverse_mul_frame : frameInverse * frameMatrix = 1 :=
  Sparse.mul_eq_of_check_alignment frameInverse inverseRows frameMatrix 1 inverse_alignment (by decide +kernel)

theorem bridge_coordinates_check : Matrix.vecMul bridgeCoordinates frameMatrix = bridgeVector := by decide +kernel

theorem bridge_coordinates_nonzero : ∀ i, bridgeCoordinates i ≠ 0 := by decide +kernel

#print axioms trace_steps
#print axioms frame_mul_inverse
#print axioms inverse_mul_frame
#print axioms bridge_coordinates_check
end Kourovka.Problem2153.WilsonModel.Frame
'''
before,after=s.split('theorem trace_starts',1)
(HERE/'Steps.lean').write_text(before+'\n#print axioms trace_steps\nend Kourovka.Problem2153.WilsonModel.Frame\n')
header='''import Kourovka.Problem2153.AmbientFacts.Frame.Steps

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.WilsonModel.Frame
open Field8 F8

'''
(HERE/'Checks.lean').write_text(header+'theorem trace_starts'+after)
print('Generated 27 words, 1296 sparse row transitions, frame inverse and bridge certificates.')
