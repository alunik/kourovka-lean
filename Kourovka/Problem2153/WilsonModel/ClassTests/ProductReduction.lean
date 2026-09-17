import Kourovka.Problem2153.WilsonModel.ClassTests.ProductBase
import Kourovka.Problem2153.RankOne.SimpleWeyl
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open RootData RootSystem

def evenIndex (i : Fin 8) : Fin 16 := ⟨2 * i.val, by omega⟩
def halfIndex (i : Fin 16) : Fin 8 := ⟨i.val / 2, by omega⟩

private theorem index_pair : ∀ i : Fin 16, i = evenIndex (halfIndex i) ∨
    i = WeylData.leftR (evenIndex (halfIndex i)) := by decide +kernel

theorem classProduct_leftR (a : Fin 7) (w : Fin 16) :
    classProduct a (WeylData.leftR w) = classProduct a w := by
  have hr : rightConj (root 11 a.succ) r = root 11 a.succ :=
    RankOne.root_conj_r 11 (by decide) (by decide) a.succ
  rw [classProduct, ← Weyl.r_mul_rep]
  have hc : rightConj (root 11 a.succ) (r * Weyl.rep w) =
      rightConj (rightConj (root 11 a.succ) r) (Weyl.rep w) := by
    simp [rightConj, mul_assoc]
  rw [hc]
  rw [hr]
  rfl

theorem classProduct_reduce (a : Fin 7) (w : Fin 16) :
    classProduct a w = classProduct a (evenIndex (halfIndex w)) := by
  rcases index_pair w with h | h
  · exact congrArg (classProduct a) h
  · exact (congrArg (classProduct a) h).trans (classProduct_leftR a _)

end Kourovka.Problem2153.WilsonModel.ClassTests
