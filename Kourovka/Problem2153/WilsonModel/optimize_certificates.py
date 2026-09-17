#!/usr/bin/env python3
"""Replace dense proof reduction with a proved sparse checker; preserve all statements."""
from pathlib import Path
HERE=Path(__file__).resolve().parent
setup=(HERE/'generate_certificates.py').read_text().split('header=')[0]
exec(compile(setup,str(HERE/'generate_certificates.py'),'exec'),globals())
header='''import Kourovka.Problem2153.WilsonModel.Data
import Kourovka.Problem2153.WilsonModel.Sparse
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel
open Field8 F8
'''
s=header
for name in dict.fromkeys(a for _,a,_,_ in checks):
 mat=matrices[name]
 rows=['['+', '.join(f'({j}, e{v})' for j,v in enumerate(row) if v)+']' for row in mat]
 s+=f'def certRows_{name} : Sparse.Table (Fin 26) := !['+',\n  '.join(rows)+']\n'
 s+=f'theorem certAlignment_{name} : {name} = Sparse.eval certRows_{name} := by decide +kernel\n\n'
s+='end Kourovka.Problem2153.WilsonModel\n'
(HERE/'CertificateRows.lean').write_text(s)
s=header.replace('import Kourovka.Problem2153.WilsonModel.Data\nimport Kourovka.Problem2153.WilsonModel.Sparse','import Kourovka.Problem2153.WilsonModel.CertificateRows')
for name,a,b,c in checks:
 s+=f'''theorem {name} : {a} * {b} = {c} := by
  apply Sparse.mul_eq_of_check_alignment {a} certRows_{a} _ _ certAlignment_{a}
  decide +kernel

'''
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
