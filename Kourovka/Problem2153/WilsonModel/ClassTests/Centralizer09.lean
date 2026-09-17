import Kourovka.Problem2153.WilsonModel.ClassTests.Base
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
/-- All 49 scalar/torus-weight cases for Weyl representative 9. -/
theorem pattern_uniform_9 : (fun a c : Fin 7 => centralizerPattern a c 9) =
    (fun (_ : Fin 7) (c : Fin 7) => centralizerPattern 0 c 9) := by
  decide +kernel
end Kourovka.Problem2153.WilsonModel.ClassTests
