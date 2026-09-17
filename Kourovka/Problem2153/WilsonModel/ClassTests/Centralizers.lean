import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer00
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer01
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer02
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer03
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer04
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer05
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer06
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer07
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer08
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer09
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer10
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer11
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer12
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer13
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer14
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizer15
set_option autoImplicit false
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open RootSystem

theorem pattern_uniform (w : Fin 16) : (fun a c : Fin 7 => centralizerPattern a c w) =
    (fun (_ : Fin 7) (c : Fin 7) => centralizerPattern 0 c w) := by
  fin_cases w
  · exact pattern_uniform_0
  · exact pattern_uniform_1
  · exact pattern_uniform_2
  · exact pattern_uniform_3
  · exact pattern_uniform_4
  · exact pattern_uniform_5
  · exact pattern_uniform_6
  · exact pattern_uniform_7
  · exact pattern_uniform_8
  · exact pattern_uniform_9
  · exact pattern_uniform_10
  · exact pattern_uniform_11
  · exact pattern_uniform_12
  · exact pattern_uniform_13
  · exact pattern_uniform_14
  · exact pattern_uniform_15

/-- All seven nonidentity central root elements have the same commutation test
against every actual torus-Weyl representative. -/
theorem commute_torus_weyl_uniform (a c d : Fin 7) (w : Fin 16) :
    Commute (root 11 a.succ) (torus c d * Weyl.rep w) ↔
      Commute (root 11 1) (torus c d * Weyl.rep w) := by
  change Commute (root 11 a.succ) (torus c d * Weyl.rep w) ↔
    Commute (root 11 (0 : Fin 7).succ) (torus c d * Weyl.rep w)
  rw [commute_torus_weyl_iff, commute_torus_weyl_iff]
  rw [congrFun (congrFun (pattern_uniform w) a) c]

end Kourovka.Problem2153.WilsonModel.ClassTests
