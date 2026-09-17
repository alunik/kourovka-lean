#!/usr/bin/env python3
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
r=json.loads((INPUTS/'reduced-collection-certificate.json').read_text())
entries=r['torus_kernel_generators']
s='''import Kourovka.Problem2153.WilsonModel.RootData.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData
open Field8 F8

/-- A generator for the kernel of each root's torus weight; indices are field codes minus one. -/
def kernelParameters : Fin 12 → Fin 7 × Fin 7 :=
  !['''+', '.join(f'({e["torus"][0]-1}, {e["torus"][1]-1})' for e in entries)+''']

/-- Canonical exponent sections supplied by the exact torus-orbit reduction. -/
def sectionExponents : Fin 12 → Fin 7 × Fin 7 :=
  !['''+', '.join(f'({e["section_exponents"][0]}, {e["section_exponents"][1]})' for e in entries)+''']

def kernelLeft (i : Fin 12) : Mat := fun j k =>
  rootMatrix i 1 j k * torusDiag (kernelParameters i).1 (kernelParameters i).2 k

def kernelRight (i : Fin 12) : Mat := fun j k =>
  torusDiag (kernelParameters i).1 (kernelParameters i).2 j * rootMatrix i 1 j k

'''
for i in range(12):s+=f'theorem kernel_matrix_{i} : kernelLeft {i} = kernelRight {i} := by decide +kernel\n\n'
s+='theorem kernel_matrix (i : Fin 12) : kernelLeft i = kernelRight i := by\n  fin_cases i\n'
for i in range(12):s+=f'  · exact kernel_matrix_{i}\n'
s+='''
/-- Actual root-base/kernel commutation in the concrete generated ambient group. -/
theorem rootBase_kernel_commute (i : Fin 12) :
    Commute (RootSystem.rootBase i)
      (RootSystem.torus (kernelParameters i).1 (kernelParameters i).2) := by
  apply matrixHom_injective
  simp only [map_mul, rootBase_alignment]
  change rootMatrix i 1 * Matrix.diagonal (torusDiag (kernelParameters i).1
    (kernelParameters i).2) = Matrix.diagonal (torusDiag (kernelParameters i).1
    (kernelParameters i).2) * rootMatrix i 1
  ext j k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact congrFun (congrFun (kernel_matrix i) j) k

end Kourovka.Problem2153.WilsonModel.RootData
'''
(HERE/'Kernels.lean').write_text(s)
