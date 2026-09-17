#!/usr/bin/env python3
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
sys.path.insert(0, str(INPUTS))
import collection_probe as c
s='''import Kourovka.Problem2153.WilsonModel.RootData.Tables
import Kourovka.Problem2153.WilsonModel.SparseBenchmark
import Kourovka.Problem2153.RootSystem
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData
open Field8 F8

/-- The actual matrix homomorphism of the concrete ambient subgroup. -/
def matrixHom : RootSystem.G →* Mat := (Units.coeHom Mat).comp ambient.subtype

theorem matrix_conj_r (g : RootSystem.G) :
    matrixHom (rightConj g RootSystem.r) = rho * matrixHom g * rho := rfl

theorem matrix_conj_s (g : RootSystem.G) :
    matrixHom (rightConj g RootSystem.s) = sigma * matrixHom g * sigma := rfl

'''
relations={2:(1,'s'),4:(2,'r'),5:(0,'r'),6:(4,'s'),7:(3,'s'),8:(5,'s'),9:(8,'r'),10:(7,'r'),11:(10,'s')}
for i,(j,g) in relations.items():
 mat=c.mm(c.sigma if g=='s' else c.rho,c.RF[j][1])
 rows=['['+', '.join(f'({k}, e{v})' for k,v in enumerate(row) if v)+']' for row in mat]
 s+=f'def baseLeft{i}Rows : Sparse.Table (Fin 26) := !['+',\n    '.join(rows)+']\n'
 s+=f'def baseLeft{i} : Mat := Sparse.eval baseLeft{i}Rows\n'
 gn='sigma' if g=='s' else 'rho'
 s+=f'''theorem baseLeft{i}_eq : {gn} * rootMatrix {j} 1 = baseLeft{i} := by
  apply Sparse.mul_eq_of_check_alignment {gn} {gn}Sparse _ _ {gn}_alignment
  decide +kernel

theorem baseRight{i}_eq : baseLeft{i} * {gn} = rootMatrix {i} 1 := by
  apply Sparse.mul_eq_of_check baseLeft{i}Rows
  decide +kernel

'''
s+='''theorem base_alignment_0 : matrixHom (RootSystem.rootBase 0) = rootMatrix 0 1 := by
  change wilsonT = rootMatrix 0 1
  decide +kernel

theorem base_alignment_1 : matrixHom (RootSystem.rootBase 1) = rootMatrix 1 1 := by
  change wilsonX = rootMatrix 1 1
  decide +kernel

theorem base_alignment_3 : matrixHom (RootSystem.rootBase 3) = rootMatrix 3 1 := by
  change wilsonX ^ 2 = rootMatrix 3 1
  rw [pow_two, x2_eq]
  decide +kernel

'''
exprs={2:'rightConj RootSystem.x RootSystem.s',4:'rightConj RootSystem.x (RootSystem.s * RootSystem.r)',5:'rightConj RootSystem.t RootSystem.r',6:'rightConj RootSystem.x (RootSystem.s * RootSystem.r * RootSystem.s)',7:'rightConj (RootSystem.x ^ 2) RootSystem.s',8:'rightConj RootSystem.t (RootSystem.r * RootSystem.s)',9:'rightConj RootSystem.t (RootSystem.r * RootSystem.s * RootSystem.r)',10:'rightConj (RootSystem.x ^ 2) (RootSystem.s * RootSystem.r)',11:'rightConj (RootSystem.x ^ 2) (RootSystem.s * RootSystem.r * RootSystem.s)'}
for i,(j,g) in relations.items():
 gn='sigma' if g=='s' else 'rho'
 s+=f'theorem base_alignment_{i} : matrixHom (RootSystem.rootBase {i}) = rootMatrix {i} 1 := by\n'
 s+=f'  change matrixHom ({exprs[i]}) = rootMatrix {i} 1\n'
 if i in [4,6,8,9,10,11]: s+='  rw [rightConj_mul]\n'
 s+=f'  rw [matrix_conj_{g}]\n'
 s+=f'  change {gn} * matrixHom (RootSystem.rootBase {j}) * {gn} = rootMatrix {i} 1\n'
 s+=f'  rw [base_alignment_{j}, baseLeft{i}_eq, baseRight{i}_eq]\n\n'
s+='''theorem rootBase_alignment (i : Fin 12) :
    matrixHom (RootSystem.rootBase i) = rootMatrix i 1 := by
  fin_cases i
'''
for i in range(12):s+=f'  · exact base_alignment_{i}\n'
s+='''
def diagonalConj (d : Fin 26 → F8) (m : Mat) : Mat :=
  fun i j => (d i)⁻¹ * m i j * d j

theorem matrix_conj_torus (g : RootSystem.G) (a b : Fin 7) :
    matrixHom (rightConj g (RootSystem.torus a b)) =
      diagonalConj (torusDiag a b) (matrixHom g) := by
  ext i j
  change (Matrix.diagonal (fun k => (torusDiag a b k)⁻¹) * matrixHom g *
    Matrix.diagonal (torusDiag a b)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

def transported (i : Fin 12) (a : Fin 8) : Mat :=
  if a = 0 then 1 else
    diagonalConj (torusDiag (RootSystem.sectionParameters i a).1
      (RootSystem.sectionParameters i a).2) (rootMatrix i 1)

'''
for i in range(12):
 s+=f'theorem curve_equation_{i} : rootMatrix {i} = transported {i} := by decide +kernel\n\n'
s+='''theorem curve_equation (i : Fin 12) : rootMatrix i = transported i := by
  fin_cases i
'''
for i in range(12):s+=f'  · exact curve_equation_{i}\n'
s+='''
/-- All 96 arithmetic tables are identified with actual root elements of the
concrete ambient subgroup; no root-matrix equality is assumed. -/
theorem root_alignment (i : Fin 12) (a : Fin 8) :
    ((RootSystem.root i a).val : Mat) = rootMatrix i a := by
  change matrixHom (RootSystem.root i a) = rootMatrix i a
  rw [congrFun (curve_equation i) a]
  by_cases ha : a = 0
  · subst a
    simp [RootSystem.root_zero, transported]
  · rw [RootSystem.root, if_neg ha, matrix_conj_torus, rootBase_alignment]
    simp only [transported, if_neg ha]

end Kourovka.Problem2153.WilsonModel.RootData
'''
(HERE/'Alignment.lean').write_text(s)
