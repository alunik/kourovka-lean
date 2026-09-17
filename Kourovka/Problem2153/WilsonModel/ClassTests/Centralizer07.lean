import Kourovka.Problem2153.WilsonModel.ClassTests.Base
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
/-- All 49 scalar/torus-weight cases for Weyl representative 7. -/
theorem pattern_uniform_7 : (fun a c : Fin 7 => centralizerPattern a c 7) =
    (fun (_ : Fin 7) (c : Fin 7) => centralizerPattern 0 c 7) := by
  decide +kernel
end Kourovka.Problem2153.WilsonModel.ClassTests
