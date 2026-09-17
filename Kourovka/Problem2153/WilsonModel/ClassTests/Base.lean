import Kourovka.Problem2153.WilsonModel.RootData.Words
import Kourovka.Problem2153.Weyl
import Kourovka.Problem2153.TorusAction
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 RootData RootSystem

def centralizerPattern (a c : Fin 7) (w : Fin 16) : Bool :=
  decide (Sparse.mulEval (rootRows 11 (parameterMul a.succ c.succ)) (WeylData.matrix w) =
    Sparse.mulEval (WeylData.rows w) (rootMatrix 11 a.succ))

theorem matrixHom_root (i : Fin 12) (a : Fin 8) :
    matrixHom (root i a) = rootMatrix i a := root_alignment i a

theorem matrixHom_rep (w : Fin 16) : matrixHom (Weyl.rep w) = WeylData.matrix w :=
  Weyl.rep_matrix w

theorem pattern_true_iff (a c : Fin 7) (w : Fin 16) :
    centralizerPattern a c w = true ↔
      root 11 (parameterMul a.succ c.succ) * Weyl.rep w =
        Weyl.rep w * root 11 a.succ := by
  rw [centralizerPattern, decide_eq_true_eq]
  rw [← Sparse.mul_eq_of_check (rootRows 11 (parameterMul a.succ c.succ))
    (WeylData.matrix w) _ rfl]
  rw [← Sparse.mul_eq_of_check (WeylData.rows w) (rootMatrix 11 a.succ) _ rfl]
  have hmap : matrixHom (root 11 (parameterMul a.succ c.succ) * Weyl.rep w) =
      matrixHom (Weyl.rep w * root 11 a.succ) ↔
        root 11 (parameterMul a.succ c.succ) * Weyl.rep w =
          Weyl.rep w * root 11 a.succ := matrixHom_injective.eq_iff
  simpa only [map_mul, matrixHom_root, matrixHom_rep, rootMatrix, WeylData.matrix] using hmap

theorem commute_mul_iff (g h w : RootSystem.G) :
    Commute g (h * w) ↔ rightConj g h * w = w * g := by
  constructor
  · intro hc
    have he := congrArg (h⁻¹ * ·) hc.eq
    simpa [rightConj, mul_assoc] using he
  · intro he
    change g * (h * w) = (h * w) * g
    have hc := congrArg (h * ·) he
    exact (by simpa [rightConj, mul_assoc] using hc)

private theorem central_weight : weightValue 11 = fun c _ => c := by decide +kernel

theorem central_parameterAction (a : Fin 8) (c d : Fin 7) :
    parameterAction 11 c d a = parameterMul a c.succ := by
  rw [parameterAction, central_weight]

theorem commute_torus_weyl_iff (a c d : Fin 7) (w : Fin 16) :
    Commute (root 11 a.succ) (torus c d * Weyl.rep w) ↔
      centralizerPattern a c w = true := by
  rw [commute_mul_iff, root_conj_torus, central_parameterAction]
  exact (pattern_true_iff a c w).symm

end Kourovka.Problem2153.WilsonModel.ClassTests
