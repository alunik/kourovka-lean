#!/usr/bin/env python3
"""Emit explicit Lean tables and kernel-checked multiplication certificates.
The Python output is untrusted proof input: Lean checks every claimed product.
"""
import importlib.util
from pathlib import Path
import json
HERE = Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
ROOT = HERE.parents[3]
source = INPUTS / 'wilson_probe.py'
spec = importlib.util.spec_from_file_location('wilson_source', source)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
raw = json.loads(source.with_name('wilson-generators.json').read_text())
matrices = dict(wilsonT=m.t, wilsonX=m.x, rho=m.rho, sigma=m.sigma)
checks = []
def step(name, a, b):
    matrices[name] = m.mm(matrices[a], matrices[b])
    checks.append((name+'_eq', a, b, name))
for name in ['wilsonT','rho','sigma']:
    checks.append((name+'_square',name,name,'1'))
step('x2','wilsonX','wilsonX')
step('x3','x2','wilsonX')
checks.extend([('x_mul_x3','wilsonX','x3','1'),('x3_mul_x','x3','wilsonX','1')])
step('sr','sigma','rho')
step('srs','sr','sigma')
step('srsr','srs','rho')
step('srsrs','srsr','sigma')
step('srsrsr','srsrs','rho')
step('w','srsrsr','sigma')
checks.extend([('srs_square','srs','srs','1'),('w_square','w','w','1')])
step('zxLeft','srs','x2')
step('witnessX','zxLeft','srs')
matrices['h'] = m.torus(2,1)
matrices['hInv'] = m.inv(matrices['h'])
step('zyLeft','hInv','witnessX')
step('witnessY','zyLeft','h')
step('zaLeft','w','witnessX')
step('witnessA','zaLeft','w')
for name in ['witnessX','witnessY','witnessA']:
    checks.append((name+'_square',name,name,'1'))
step('ax','witnessA','witnessX')
step('ax2','ax','ax')
step('ax4','ax2','ax2')
checks.append(('ax_fifth_step','ax4','ax','1'))
step('ay','witnessA','witnessY')
step('ay2','ay','ay')
step('ay4','ay2','ay2')
step('ay6','ay4','ay2')
checks.append(('ay_seventh_step','ay6','ay','1'))
header='''import Kourovka.Problem2153.Field8

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.WilsonModel
open Field8 F8

'''
s=header+'''/-- Wilson's ordered 26-dimensional basis; rows are images of basis vectors. -/
abbrev Mat := Matrix (Fin 26) (Fin 26) F8
abbrev GL26 := Matrix.GeneralLinearGroup (Fin 26) F8

'''
for name,mat in matrices.items():
    s+=f'def {name} : Mat :=\n  !!['+';\n    '.join(', '.join('e'+str(v) for v in row) for row in mat)+']\n\n'
s+='def torusDiag (a b : Fin 7) : Fin 26 → F8 :=\n  (!['
rows=[]
for a in range(1,8):
    cols=[]
    for b in range(1,8):
        cols.append('!['+', '.join('e'+str(v) for v in m.np.diag(m.torus(a,b)))+']')
    rows.append('!['+',\n      '.join(cols)+']')
s+=',\n    '.join(rows)+'] a) b\n\n'
s+='end Kourovka.Problem2153.WilsonModel\n'
(HERE/'Data.lean').write_text(s)
s=header.replace('import Kourovka.Problem2153.Field8','import Kourovka.Problem2153.WilsonModel.Data')
for name,a,b,c in checks:
    assert m.eq(m.mm(matrices[a], matrices[b]), m.I if c=='1' else matrices[c]), name
    s+=f'theorem {name} : {a} * {b} = {c} := by decide +kernel\n\n'
for name in ['witnessX','witnessY','witnessA','ax','ay']:
    s+=f'theorem {name}_ne_one : {name} ≠ 1 := by decide +kernel\n\n'
s+='''theorem witnessX_ne_Y : witnessX ≠ witnessY := by decide +kernel

theorem torusDiag_ne_zero : ∀ a b : Fin 7, ∀ i : Fin 26, torusDiag a b i ≠ 0 := by
  decide +kernel

theorem h_eq_diagonal : h = Matrix.diagonal (torusDiag 1 0) := by decide +kernel

theorem hInv_eq_diagonal : hInv = Matrix.diagonal (fun i => (torusDiag 1 0 i)⁻¹) := by
  decide +kernel

end Kourovka.Problem2153.WilsonModel
'''
(HERE/'Certificates.lean').write_text(s)
print(f'Generated {len(matrices)} matrices and {len(checks)} multiplication certificates.')
