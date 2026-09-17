import Kourovka.Problem2153.WilsonModel.ClassTests.Base
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
def inverseIndex : Fin 16 → Fin 16 := ![0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 12, 11, 13, 14, 15]
private theorem inverse_index_check : (fun i => Weyl.mulIndex (inverseIndex i) i) = (fun _ => (0 : Fin 16)) := by decide +kernel

theorem rep_inverse (i : Fin 16) : (Weyl.rep i)⁻¹ = Weyl.rep (inverseIndex i) := by
  apply inv_eq_of_mul_eq_one_left
  rw [Weyl.rep_mul, congrFun inverse_index_check i, Weyl.rep_zero]

def classProduct (a : Fin 7) (w : Fin 16) : RootSystem.G :=
  root 11 1 * rightConj (root 11 a.succ) (Weyl.rep w)

theorem classProduct_matrix (a : Fin 7) (w : Fin 16) :
    matrixHom (classProduct a w) = rootMatrix 11 1 *
      (WeylData.matrix (inverseIndex w) * rootMatrix 11 a.succ * WeylData.matrix w) := by
  simp only [classProduct, rightConj, rep_inverse, map_mul, matrixHom_root, matrixHom_rep]

end Kourovka.Problem2153.WilsonModel.ClassTests
