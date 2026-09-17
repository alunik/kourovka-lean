import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl00
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl01
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl02
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl03
import Kourovka.Problem2153.RankOne.SimpleWeylData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
namespace Kourovka.Problem2153.RootSystem.RankOne
open WilsonModel.RootData

theorem r_base (i : Fin 12) (hi1 : i ≠ 1) (hi3 : i ≠ 3) :
    rightConj (root i 1) r = root (rIndex i) 1 := by
  fin_cases i
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_0
  · contradiction
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_2
  · contradiction
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_5
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_7
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_9
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_11
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_13
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_15
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_17
  · simpa [rightConj, r_inv, rIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_19

theorem s_base (i : Fin 12) (hi : i ≠ 0) :
    rightConj (root i 1) s = root (sIndex i) 1 := by
  fin_cases i
  · contradiction
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_1
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_3
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_4
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_6
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_8
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_10
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_12
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_14
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_16
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_18
  · simpa [rightConj, s_inv, sIndex, Relations.weyl_lhs, Relations.weyl_rhs,
      wordGroup, atomGroup, mul_assoc] using Relations.weyl_20

theorem root_conj_r (i : Fin 12) (hi1 : i ≠ 1) (hi3 : i ≠ 3) (a : Fin 8) :
    rightConj (root i a) r = root (rIndex i) a :=
  root_conj_r_of_base i hi1 hi3 (r_base i hi1 hi3) a

theorem root_conj_s (i : Fin 12) (hi : i ≠ 0) (a : Fin 8) :
    rightConj (root i a) s = root (sIndex i) a :=
  root_conj_s_of_base i hi (s_base i hi) a

end Kourovka.Problem2153.RootSystem.RankOne
